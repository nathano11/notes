import Reimann.SignedMeasure256
import Reimann.SignedProjection

/-! Exact projection of the level-256 Stickelberger numerator into the
mod-four odd sign, paired over a and M-a at M = 256 * 2893. -/

namespace Reimann.SignedStickelberger

open SignedMeasure256 SignedProjection

/-- The modulus of the finite Dirichlet character sum. -/
def modulus : Nat := 256 * 2893

/-- The mod-four sign, extended by zero on even integers. -/
def signFour (a : Nat) : Int :=
  if a % 4 = 1 then 1 else if a % 4 = 3 then -1 else 0

/-- Entry in the integer numerator of the signed Stickelberger element. -/
def term (a : Nat) : Int := -(a : Int) * character a * signFour a

/-- The positive lift of the j-th inverse-generator representative. -/
def lift (j : Fin 64) (k : Nat) : Nat := inverseResidue j.val + 256*k

theorem lift_bounds (j : Fin 64) {k : Nat} (hk : k < 2893) :
    0 < lift j k ∧ lift j k < modulus ∧ lift j k % 4 = 1 := by
  have h := (inverse_index j).2
  have ht : inverseResidue j.val < 256 := Nat.mod_lt _ (by decide)
  unfold lift modulus
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
/-- Negation fixes the even primitive quadratic character over a full period. -/
theorem even_character_residues (b : Fin 2893) : character (2893-b.val) = character b.val := by
  revert b
  decide

theorem reflected_character (a : Nat) (ha : a ≤ modulus) :
    character (modulus-a) = character a := by
  let b : Fin 2893 := ⟨a%2893, Nat.mod_lt _ (by decide)⟩
  calc
    _ = character (2893-b.val) := by
      apply character_congr <;> dsimp [modulus, b] at * <;> omega
    _ = character b.val := even_character_residues b
    _ = _ := by
      apply character_congr <;> dsimp [b] <;> omega

theorem signed_pair (j : Fin 64) {k : Nat} (hk : k < 2893) :
    term (lift j k) + term (modulus - lift j k) =
      ((modulus : Int) - (lift j k : Int) - (lift j k : Int)) * character (lift j k) := by
  obtain ⟨_,hb,hpos⟩ := lift_bounds j hk
  have hneg : (modulus - lift j k) % 4 = 3 := by unfold modulus at *; omega
  unfold term signFour
  rw [reflected_character _ (Nat.le_of_lt hb), hpos, hneg,
    Int.ofNat_sub (Nat.le_of_lt hb)]
  simp only [ite_true, ite_false, Nat.reduceEqDiff]
  grind

theorem total_block (f : Nat → Int) (n : Nat) : total f n = blockSum f 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, blockSum, ih, Nat.zero_add]

theorem fold_sub_total (f : Nat → Int) (n : Nat) :
    (List.range n).foldl (fun a k => a-f k) 0 = -total f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, total, ih]
    omega

theorem lift_total_zero (j : Fin 64) :
    total (fun k => character (lift j k)) 2893 = 0 := by
  rw [total_block]
  exact mass_zero (inverseResidue j.val)

theorem lift_moment (j : Fin 64) :
    -moment (fun k => character (lift j k)) 2893 = 2893 * row[j.val]! := by
  rw [← row_coefficients, moment, ← fold_sub_total]
  simp only [lift, character, numerator, Int.mul_assoc]

theorem total_congr_below {f g : Nat → Int} (n : Nat) (h : ∀ k, k < n → f k = g k) :
    total f n = total g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold total
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

/-- Full integer numerator at one inverse-generator index before dividing by 2M. -/
def rawNumerator (j : Fin 64) : Int :=
  total (fun k => term (lift j k) + term (modulus - lift j k)) 2893

theorem raw_coefficient (j : Fin 64) :
    rawNumerator j = 2 * (modulus : Int) * row[j.val]! := by
  unfold rawNumerator
  rw [total_congr_below 2893 (fun k hk => signed_pair j hk)]
  simpa only [modulus, lift, Int.natCast_add, Int.natCast_mul,
    show ((256 : Nat) : Int) = (256 : Int) by decide] using
    paired_normalization (fun k => character (lift j k)) 2893
      (inverseResidue j.val : Int) 256 (row[j.val]!) (lift_total_zero j) (lift_moment j)

theorem normalized_coefficient (j : Fin 64) :
    rawNumerator j / (2 * modulus) = row[j.val]! := by
  rw [raw_coefficient]
  change (1481216 * row[j.val]!) / 1481216 = row[j.val]!
  omega

/-- Positive indices have sign +1. The verified signed enumeration supplies the index. -/
theorem positive_index (t : Fin 256) (ht : t.val % 4 = 1) :
    ∃ j : Fin 64, inverseResidue j.val = t.val := by
  have hmem : t.val ∈ signedIndices := List.count_pos_iff.mp (by rw [signed_coverage]; omega)
  unfold signedIndices at hmem
  obtain ⟨i, hi, hpair⟩ := List.mem_flatMap.mp hmem
  let j : Fin 64 := ⟨i, List.mem_range.mp hi⟩
  have hp := (inverse_index j).2
  have hlt : inverseResidue i < 256 := Nat.mod_lt _ (by decide)
  change inverseResidue i % 4 = 1 at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  exact ⟨j, by change inverseResidue i = t.val; omega⟩

theorem positive_lift (a : Nat) (hb : a < modulus) (hpos : a%4 = 1) :
    ∃ j : Fin 64, a/256 < 2893 ∧ lift j (a/256) = a := by
  let t : Fin 256 := ⟨a%256, Nat.mod_lt _ (by decide)⟩
  obtain ⟨j, hj⟩ := positive_index t (by dsimp [t]; omega)
  refine ⟨j, by unfold modulus at hb; omega, ?_⟩
  unfold lift
  rw [hj]
  dsimp [t]
  omega

/-- The two index lifts account for every odd a in the full modulus.
Residues divisible by 11 or 263 have zero coefficient through the character. -/
theorem odd_lift_coverage (a : Nat) (ha : a < modulus) (hs : a%2 = 1) :
    ∃ j : Fin 64, ∃ k : Fin 2893,
      a = lift j k.val ∨ a = modulus - lift j k.val := by
  by_cases hp : a%4 = 1
  · obtain ⟨j, hk, he⟩ := positive_lift a ha hp
    exact ⟨j, ⟨a/256,hk⟩, Or.inl he.symm⟩
  · have hb : modulus-a < modulus := by unfold modulus at *; omega
    have hr : (modulus-a)%4 = 1 := by unfold modulus at *; omega
    obtain ⟨j, hk, he⟩ := positive_lift (modulus-a) hb hr
    refine ⟨j, ⟨(modulus-a)/256,hk⟩, Or.inr ?_⟩
    change a = modulus - lift j ((modulus-a)/256)
    rw [he]
    omega

/-- At primes dividing the modulus the extended character removes the term.
Thus the sum over odd lifts also represents the usual sum over units. -/
theorem term_zero_at_modulus_prime (a : Nat)
    (h : a%2 = 0 ∨ a%11 = 0 ∨ a%263 = 0) : term a = 0 := by
  rcases h with hd | hq | hp
  · have h1 : a%4 ≠ 1 := by omega
    have h3 : a%4 ≠ 3 := by omega
    simp [term, signFour, h1, h3]
  · simp [term, character, Reimann.Dyadic.quadSymbol, hq]
  · simp [term, character, Reimann.Dyadic.quadSymbol, hp]

end Reimann.SignedStickelberger
