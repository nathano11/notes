import Reimann.DyadicEulerFactor
import Reimann.SignedStickelberger

/-! The normalized first character moment over all residues t modulo each
power 2^n. Consecutive base moments and descent under multiplication by two
give exact integral coefficients before passing to any finite precision. -/
namespace Reimann.SignedTowerMeasure

open SignedMeasure256 (character character_congr blockSum)
open SignedProjection (total moment)

/-- The character in an arithmetic progression with dyadic step. -/
def fibre (n t k : Nat) : Int := character (t + 2^n*k)

theorem fibre_period (n t k : Nat) : fibre n t (2893+k) = fibre n t k := by
  unfold fibre
  rw [Nat.mul_add, ← Nat.add_assoc]
  apply character_congr <;> omega

/-- The inverse of 2 modulo 2893 is 1447. Descent halves the step and
negates the quadratic character, including at nonunits. -/
theorem fibre_double (n t k : Nat) : fibre (n+1) t k = -fibre n (1447*t) k := by
  unfold fibre
  rw [Nat.pow_succ]
  have he : t + 2^n*2*k + 2893*t = 2*(1447*t+2^n*k) := by grind
  have hc : character (t+2^n*2*k) = character (2*(1447*t+2^n*k)) := by
    rw [← he]
    apply character_congr <;> omega
  rw [hc]
  exact DyadicEulerFactor.character_double _

theorem total_neg (f : Nat → Int) (m : Nat) :
    total (fun k => -f k) m = -total f m := by
  induction m with
  | zero => simp [total]
  | succ n ih => simp only [total, ih]; omega

theorem moment_neg (f : Nat → Int) (m : Nat) :
    moment (fun k => -f k) m = -moment f m := by
  simp only [moment, Int.mul_neg, total_neg]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
/-- The unweighted and first moment at step one and origin zero. -/
theorem base_character_sums :
    total character 2893 = 0 ∧ moment character 2893 = 0 := by decide

theorem base_mass (t : Nat) : total (fibre 0 t) 2893 = 0 := by
  have per (k : Nat) : character (k+2893) = character k := by
    apply character_congr <;> omega
  have he : fibre 0 t = fun k => character (t+k) := by funext k; simp [fibre]
  rw [he, SignedStickelberger.total_block, SignedMeasure256.translate_block]
  rw [SignedMeasure256.periodic_block character 2893 per t, ← SignedStickelberger.total_block]
  exact base_character_sums.1

theorem mass_zero (n t : Nat) : total (fibre n t) 2893 = 0 := by
  induction n generalizing t with
  | zero => exact base_mass t
  | succ n ih =>
    have hf : fibre (n+1) t = fun k => -fibre n (1447*t) k := funext (fibre_double n t)
    rw [hf, total_neg, ih, Int.neg_zero]

/-- Summation by parts for a one-step translation, before invoking periodicity. -/
theorem moment_shift (f : Nat → Int) (m : Nat) :
    moment (fun k => f (k+1)) m + total (fun k => f (k+1)) m =
      moment f m + (m:Int)*f m := by
  unfold moment
  induction m with
  | zero => simp [total]
  | succ n ih =>
    simp only [total, Int.natCast_succ]
    grind

theorem base_moment_step (t : Nat) :
    moment (fibre 0 (t+1)) 2893 = moment (fibre 0 t) 2893 + 2893*character t := by
  have hs : (fun k => fibre 0 t (k+1)) = fibre 0 (t+1) := by
    funext k
    simp only [fibre, Nat.pow_zero, Nat.one_mul]
    congr 1
    omega
  have hp : fibre 0 t 2893 = character t := by
    unfold fibre
    apply character_congr <;> omega
  have h := moment_shift (fibre 0 t) 2893
  rw [hs, base_mass, hp] at h
  simpa using h

theorem base_moment_integral (t : Nat) : (2893:Int) ∣ moment (fibre 0 t) 2893 := by
  induction t with
  | zero =>
    have he : fibre 0 0 = character := by funext k; simp [fibre]
    rw [he, base_character_sums.2]
    exact Int.dvd_zero _
  | succ t ih =>
    rw [base_moment_step]
    exact Int.dvd_add ih (Int.dvd_mul_right _ _)

theorem moment_integral (n t : Nat) : (2893:Int) ∣ moment (fibre n t) 2893 := by
  induction n generalizing t with
  | zero => exact base_moment_integral t
  | succ n ih =>
    have h : fibre (n+1) t = fun k => -fibre n (1447*t) k := funext (fibre_double n t)
    rw [h, moment_neg]
    exact Int.dvd_neg.mpr (ih _)

/-- The signed, half-normalized coefficient on t modulo 2^n. Its
numerator is divisible by the full odd conductor over the integers. -/
def coefficient (n t : Nat) : Int := -moment (fibre n t) 2893 / 2893

theorem coefficient_exact (n t : Nat) :
    -moment (fibre n t) 2893 = 2893 * coefficient n t := by
  obtain ⟨k, hk⟩ := moment_integral n t
  unfold coefficient
  rw [hk]
  omega

theorem child_fibres (n t : Nat) :
    (fun k => fibre n t (2*k)) = fibre (n+1) t ∧
    (fun k => fibre n t (2*k+1)) = fibre (n+1) (t+2^n) := by
  constructor <;> funext k <;> unfold fibre <;> rw [Nat.pow_succ] <;> congr 1 <;> grind

/-- Exact two-term pushforward for the normalized integral coefficients. -/
theorem coefficient_refine (n t : Nat) :
    coefficient n t = coefficient (n+1) t + coefficient (n+1) (t+2^n) := by
  obtain ⟨he, ho⟩ := child_fibres n t
  have oddMass : total (fun k => fibre n t (2*k+1)) 2893 = 0 := by rw [ho, mass_zero]
  have h := SignedProjection.moment_refine (fibre n t) 2893 (fibre_period n t) (mass_zero n t) oddMass
  rw [he, ho] at h
  have e := coefficient_exact n t
  have e0 := coefficient_exact (n+1) t
  have e1 := coefficient_exact (n+1) (t+2^n)
  omega

/-- At modulus 256 the all-level formula specializes exactly to the independent
64-entry integer certificate in the inverse-generator convention. -/
theorem level256_coefficient (j : Fin 64) :
    coefficient 8 (SignedMeasure256.inverseResidue j.val) = SignedMeasure256.row[j.val]! := by
  have h := SignedStickelberger.lift_moment j
  change -moment (fibre 8 (SignedMeasure256.inverseResidue j.val)) 2893 =
    2893 * SignedMeasure256.row[j.val]! at h
  rw [coefficient_exact] at h
  omega

/-- The primitive character is even for every period 2893 times a dyadic modulus. -/
theorem level_reflection (n a : Nat) (ha : a ≤ 2^n * 2893) :
    character (2^n*2893-a) = character a := by
  let b : Fin 2893 := ⟨a%2893, Nat.mod_lt _ (by decide)⟩
  calc
    _ = character (2893-b.val) := by
      apply character_congr <;> dsimp [b] <;> omega
    _ = character b.val := SignedStickelberger.even_character_residues b
    _ = _ := by apply character_congr <;> dsimp [b] <;> omega

/-- Pair a with M-a at level 2^(n+2). Their mod-four signs are opposite. -/
theorem signed_lift_pair (n t h : Nat) (ht : t < 2^(n+2)) (hpos : t%4=1) (hh : h<2893) :
    let d := 2^(n+2)
    let a := t+d*h
    let m := d*2893
    SignedStickelberger.term a + SignedStickelberger.term (m-a) =
      ((m:Int)-(a:Int)-(a:Int)) * fibre (n+2) t h := by
  dsimp only
  let d := 2^(n+2)
  have hd : d = 2^n*4 := by simp [d, Nat.pow_add]
  have hlt : t+d*h < d*2893 := by
    have hs := Nat.mul_le_mul_left d (show h+1≤2893 by omega)
    rw [Nat.mul_add, Nat.mul_one] at hs
    change t<d at ht
    omega
  have hp : (t+d*h)%4=1 := by
    rw [hd, show 2^n*4*h = 4*(2^n*h) by grind]
    omega
  have hn : (d*2893-(t+d*h))%4=3 := by
    have hd4 : d%4=0 := by rw [hd]; omega
    omega
  change SignedStickelberger.term (t+d*h) + SignedStickelberger.term (d*2893-(t+d*h)) = _
  unfold SignedStickelberger.term SignedStickelberger.signFour
  rw [level_reflection (n+2) _ (Nat.le_of_lt hlt), hp, hn, Int.ofNat_sub (Nat.le_of_lt hlt)]
  simp only [ite_true, ite_false, Nat.reduceEqDiff]
  change _ = ((d*2893 : Nat) - (t+d*h : Nat) - (t+d*h : Nat) : Int) * character (t+d*h)
  grind

/-- The raw signed Stickelberger numerator on an arbitrary positive fibre is
exactly 2·2^(n+2)·2893 times its normalized integral coefficient. -/
theorem paired_stickelberger (n t : Nat) (ht : t < 2^(n+2)) (hpos : t%4=1) :
    let d := 2^(n+2)
    total (fun h => SignedStickelberger.term (t+d*h) +
      SignedStickelberger.term (d*2893-(t+d*h))) 2893 =
      2*((d*2893 : Nat):Int)*coefficient (n+2) t := by
  dsimp only
  rw [SignedStickelberger.total_congr_below 2893 (fun h hh => signed_lift_pair n t h ht hpos hh)]
  simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] using
    SignedProjection.paired_normalization (fibre (n+2) t) 2893 (t:Int)
      ((2^(n+2) : Nat):Int) (coefficient (n+2) t)
      (mass_zero (n+2) t) (coefficient_exact (n+2) t)

end Reimann.SignedTowerMeasure
