import Reimann.WeightClasses

/-! Finite cyclotomic images above a real dyadic layer. -/

namespace Reimann.DyadicCyclotomicImage

open Reimann.Dyadic Reimann.SampleSpacing Reimann.WeightClasses

/-- The factor four adapts the spacing of powers of five to the existing
binary lifting theorem, whose initial modulus is sixteen. -/
def difference (x : Int) (i : Nat) := 4*((5:Int)^i-x)

theorem difference_steps (x : Int) : SiblingSteps (difference x) := by
  intro k i
  obtain ⟨z, hz⟩ := power_gap i k 0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, twoPower_eq_pow] at hz
  refine ⟨z, ?_⟩
  have hpow : (2:Int)^(k+4) = 4*2^(k+2) := by
    rw [show k+4 = (k+2)+2 by omega, Int.pow_add]; grind
  unfold difference
  rw [hpow]
  grind

theorem hit_iff_power_congruence (x : Int) (k i : Nat) :
    hit (difference x) k i ↔ (2:Int)^(k+2) ∣ 5^i-x := by
  have hpow : (2:Int)^(k+4) = 4*2^(k+2) := by
    rw [show k+4 = (k+2)+2 by omega, Int.pow_add]; grind
  unfold hit difference
  rw [hpow]
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v, by rw [Int.mul_assoc] at hv; omega⟩
  · rintro ⟨v,hv⟩
    exact ⟨v, by rw [hv, Int.mul_assoc]⟩

/-- Every unit in 1+4Z has a unique exponent class at every finite depth. -/
theorem principal_unit_class (x : Int) (hx : 4 ∣ 1-x) (k : Nat) :
    ∃ r : Fin (2^k), ∀ i : Nat, (2:Int)^(k+2) ∣ 5^i-x ↔ i%2^k=r.val := by
  have seed := (hit_iff_power_congruence x 0 0).mpr (by simpa using hx)
  obtain ⟨r,hr,hi⟩ := root_at_every_depth _ (difference_steps x) seed k
  exact ⟨⟨r,hr⟩, fun i => (hit_iff_power_congruence _ _ _).symm.trans (hi i)⟩

theorem five_exact_period (k i : Nat) :
    (2:Int)^(k+2) ∣ 5^i-1 ↔ i%2^k=0 := by
  obtain ⟨r,hr⟩ := principal_unit_class 1 (by decide) k
  have h0 := (hr 0).mp (by simp)
  simp only [Nat.zero_mod] at h0
  simpa [← h0] using hr i

theorem layer_generator_period (a n i : Nat) :
    (2:Int)^(a+n+2) ∣ 5^(2^a*i)-1 ↔ i%2^n=0 := by
  rw [five_exact_period, Nat.pow_add, Nat.mul_mod_mul_left]
  have hp : 0 < 2^a := Nat.pow_pos (by decide)
  rw [show 0 = 2^a*0 by simp, Nat.mul_right_inj (Nat.ne_of_gt hp)]
  simp

theorem reduce_precision (a n : Nat) {v : Int} (h : (2:Int)^(a+n+2) ∣ v) :
    (2:Int)^(a+2) ∣ v := by
  apply Int.dvd_trans _ h
  exact ⟨2^n, by rw [← Int.pow_add]; congr 1; omega⟩

/-- In the positive component above real layer a, the exponent is measured
relative to 5^(2^a). This includes n=0, with its single exponent class. -/
theorem layer_principal_class (a n : Nat) (x : Int) (hx : (2:Int)^(a+2) ∣ 1-x) :
    ∃ t : Fin (2^n), ∀ j : Nat,
      (2:Int)^(a+n+2) ∣ 5^(2^a*j)-x ↔ j%2^n=t.val := by
  have h4 : (4:Int) ∣ 1-x := reduce_precision 0 a (by simpa using hx)
  obtain ⟨r,hr⟩ := principal_unit_class x h4 (a+n)
  have hrx := (hr r.val).mpr (Nat.mod_eq_of_lt r.isLt)
  have hbase := reduce_precision a n hrx
  have hdiff : (2:Int)^(a+2) ∣ 5^r.val-1 := by
    have h := Int.dvd_sub hbase hx
    rwa [show (5:Int)^r.val-x-(1-x)=5^r.val-1 by omega] at h
  have hd := Nat.dvd_of_mod_eq_zero ((five_exact_period a r.val).mp hdiff)
  obtain ⟨t, ht⟩ := hd
  have hp : 0 < 2^a := Nat.pow_pos (by decide)
  have htlt : t < 2^n := by
    have h := r.isLt
    rwa [ht, Nat.pow_add, Nat.mul_lt_mul_left hp] at h
  refine ⟨⟨t,htlt⟩, fun j => ?_⟩
  rw [hr, ht, Nat.pow_add, Nat.mul_mod_mul_left, Nat.mul_right_inj (Nat.ne_of_gt hp)]

theorem negative_power_excluded (a n i : Nat) {x : Int} (hx : (2:Int)^(a+2) ∣ 1-x) :
    ¬ (2:Int)^(a+n+2) ∣ -(5:Int)^i-x := by
  intro h
  have hx4 : (4:Int) ∣ 1-x := reduce_precision 0 a (by simpa using hx)
  have h4 : (4:Int) ∣ -(5:Int)^i-x := reduce_precision 0 (a+n) (by simpa using h)
  obtain ⟨u,hu⟩ := five_power_mod_four i
  omega

/-- An element congruent to either sign at the base conductor has exactly
one sign and one exponent modulo 2^n at the higher conductor. A true flag
denotes the negative sign. -/
theorem signed_layer_class (a n : Nat) (x : Int)
    (hx : (2:Int)^(a+2) ∣ 1-x ∨ (2:Int)^(a+2) ∣ 1+x) :
    ∃ (minus : Bool) (t : Fin (2^n)), ∀ (sign : Bool) (j : Nat),
      ((2:Int)^(a+n+2) ∣ (if sign then -(5:Int)^(2^a*j) else (5:Int)^(2^a*j))-x)
        ↔ sign=minus ∧ j%2^n=t.val := by
  rcases hx with hp | hm
  · obtain ⟨t, ht⟩ := layer_principal_class a n x hp
    refine ⟨false,t,?_,⟩
    intro sign j
    cases sign
    · simpa using ht j
    · simp [negative_power_excluded a n (2^a*j) hp]
  · have hm' : (2:Int)^(a+2) ∣ 1-(-x) := by simpa using hm
    obtain ⟨t, ht⟩ := layer_principal_class a n (-x) hm'
    refine ⟨true,t,?_⟩
    intro sign j
    cases sign
    · have h := negative_power_excluded a n (2^a*j) hm'
      have eq : -(5:Int)^(2^a*j)- -x = -((5:Int)^(2^a*j)-x) := by omega
      simpa [eq] using h
    · have eq : -(5:Int)^(2^a*j)-x = -((5:Int)^(2^a*j)- -x) := by omega
      simpa [eq] using ht j

/-- Exact image, in both directions, of the signed generator modulo the
higher conductor. Exponents are restricted to canonical representatives. -/
theorem signed_image_iff (a n : Nat) (x : Int) :
    ((2:Int)^(a+2) ∣ 1-x ∨ (2:Int)^(a+2) ∣ 1+x) ↔
    ∃ (minus : Bool) (t : Fin (2^n)), (2:Int)^(a+n+2) ∣
      (if minus then -(5:Int)^(2^a*t.val) else (5:Int)^(2^a*t.val))-x := by
  constructor
  · intro hx
    obtain ⟨s,t,ht⟩ := signed_layer_class a n x hx
    exact ⟨s,t,(ht s t.val).mpr ⟨rfl,Nat.mod_eq_of_lt t.isLt⟩⟩
  · rintro ⟨s,t,h⟩
    have hbase := reduce_precision a n h
    have hp := (layer_generator_period a 0 t.val).mpr (Nat.mod_one _)
    simp only [Nat.add_zero] at hp
    cases s
    · left
      simp only [Bool.false_eq_true, ↓reduceIte] at hbase
      have u := Int.dvd_sub hbase hp
      rwa [show (5:Int)^(2^a*t.val)-x-(5^(2^a*t.val)-1) = 1-x by omega] at u
    · right
      simp only [↓reduceIte] at hbase
      have u := Int.dvd_add hbase hp
      rwa [show -(5:Int)^(2^a*t.val)-x+(5^(2^a*t.val)-1) = -(1+x) by omega, Int.dvd_neg] at u

end Reimann.DyadicCyclotomicImage
