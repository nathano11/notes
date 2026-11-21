import Std

/-! Residue precision for a coefficient normalized by powers of two and
an odd conductor. All exponents and precision indices may be zero. -/
namespace Reimann.SignedNormalizationPrecision

theorem conductor_coprime (m : Nat) (hm : m%2=1) :
    Int.gcd 2 (m : Int) = 1 := by
  change Nat.gcd 2 m = 1
  rw [Nat.gcd_rec, hm]
  decide

theorem odd_conductor_cancel (m p : Nat) (z : Int) (hm : m%2=1) :
    (2:Int)^p ∣ (m:Int)*z ↔ (2:Int)^p ∣ z := by
  have cop := Int.pow_gcd_pow_of_gcd_eq_one (k:=p) (l:=1) (conductor_coprime m hm)
  rw [Int.pow_one] at cop
  rw [←Int.dvd_gcd_mul_iff_dvd_mul, cop]
  simp

theorem power_scale_cancel (p n : Nat) (z : Int) :
    (2:Int)^(p+n) ∣ 2^n*z ↔ (2:Int)^p ∣ z := by
  rw [Nat.add_comm p n, Int.pow_add]
  exact Int.mul_dvd_mul_iff_left (Int.ne_of_gt (Int.pow_pos (by decide)))

/-- The odd conductor costs zero bits; the 2-primary part costs d+s. -/
theorem scaled_difference_dvd_iff (m d s p : Nat) (x y : Int) (hm : m%2=1) :
    (2:Int)^(p+d+s) ∣ 2^(d+s)*(m:Int)*(x-y) ↔ (2:Int)^p ∣ x-y := by
  rw [Nat.add_assoc, Int.mul_assoc, power_scale_cancel, odd_conductor_cancel m p _ hm]

theorem residue_iff_dvd (m x y : Int) : x%m=y%m ↔ m∣x-y := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact ⟨Int.dvd_of_emod_eq_zero, Int.emod_eq_zero_of_dvd⟩

/-- Compare two integer numerators directly, including negative values. -/
theorem scaled_residue_iff (m d s p : Nat) (x y : Int) (hm : m%2=1) :
    ((2:Int)^(d+s)*m*x)%2^(p+d+s) = (2^(d+s)*m*y)%2^(p+d+s) ↔
      x%2^p=y%2^p := by
  rw [residue_iff_dvd, residue_iff_dvd, ←Int.mul_sub, scaled_difference_dvd_iff m d s p x y hm]

/-- Arbitrary raw expressions R and S can be substituted by their exact
denominator-clearing identities. -/
theorem numerators_compare (m d s p : Nat) (R S x y : Int) (hm : m%2=1)
    (hR : R=2^(d+s)*(m:Int)*x) (hS : S=2^(d+s)*(m:Int)*y) :
    R%(2:Int)^(p+d+s)=S%2^(p+d+s) ↔ x%2^p=y%2^p := by
  rw [hR, hS, scaled_residue_iff m d s p x y hm]

/-- The signed raw numerator has denominator 2·D·m with D=2^d. -/
theorem raw_residue_iff (m d p : Nat) (R S x y : Int) (hm : m%2=1)
    (hR : R=2*(2:Int)^d*m*x) (hS : S=2*(2:Int)^d*m*y) :
    R%(2:Int)^(p+d+1)=S%2^(p+d+1) ↔ x%2^p=y%2^p := by
  apply numerators_compare m d 1 p R S x y hm
  · rw [hR, Int.pow_succ]; grind
  · rw [hS, Int.pow_succ]; grind

/-- The literal centered expression is twice the raw numerator and costs
one further bit of precision. -/
theorem literal_residue_iff (m d p : Nat) (R S x y : Int) (hm : m%2=1)
    (hR : R=4*(2:Int)^d*m*x) (hS : S=4*(2:Int)^d*m*y) :
    R%(2:Int)^(p+d+2)=S%2^(p+d+2) ↔ x%2^p=y%2^p := by
  apply numerators_compare m d 2 p R S x y hm
  · rw [hR, Int.pow_add]; grind
  · rw [hS, Int.pow_add]; grind

theorem next_bit_separates (p : Nat) :
    ¬(2:Int)^(p+1) ∣ (2:Int)^p := by
  have h : ¬(2:Int)^p*2 ∣ (2:Int)^p*1 := by
    rw [Int.mul_dvd_mul_iff_left (Int.ne_of_gt (Int.pow_pos (by decide)))]
    decide
  simpa only [Int.pow_succ,Int.mul_one] using h

/-- The coefficients 0 and 2^p prove that one fewer input bit cannot
determine the requested p+1 output bits, even for a fixed odd conductor. -/
theorem precision_sharp (m d s p : Nat) (hm : m%2=1) :
    ((2:Int)^(d+s)*m*2^p)%2^(p+d+s)=0 ∧ (2:Int)^p%2^(p+1)≠0 := by
  constructor
  · have hp : (2:Int)^p%2^p=(0:Int)%2^p := by simp
    simpa using (scaled_residue_iff m d s p (2^p) 0 hm).mpr hp
  · intro he
    exact next_bit_separates p (Int.dvd_of_emod_eq_zero he)

/-- A common additive offset in the two numerators cancels in the comparison. -/
theorem residues_of_numerator_difference (m d s p : Nat) (R S x y : Int)
    (hm : m%2=1) (h : R-S=2^(d+s)*(m:Int)*(x-y)) :
    R%(2:Int)^(p+d+s)=S%2^(p+d+s) ↔ x%2^p=y%2^p := by
  rw [residue_iff_dvd, residue_iff_dvd, h, scaled_difference_dvd_iff m d s p x y hm]

/-- The two conductor-2893 numerator precisions at D=256 give the same six-bit comparison. -/
theorem level256_six_bits (R S x y : Int)
    (h : R-S=2*256*2893*(x-y)) :
    (R%32768=S%32768 ↔ x%64=y%64) ∧
    ((2*R)%65536=(2*S)%65536 ↔ x%64=y%64) := by
  constructor
  · exact residues_of_numerator_difference 2893 8 1 6 R S x y (by decide) h
  · apply residues_of_numerator_difference 2893 8 2 6 (2*R) (2*S) x y (by decide)
    rw [← Int.mul_sub, h]
    grind

end Reimann.SignedNormalizationPrecision
