import Reimann.SignedProduct
import Reimann.SignedCoefficients
import Reimann.DyadicLattice

/-! The product of the two cleared signed numerators over coherent dyadic
coefficients. A finite valuation is detected at the next binary digit. -/
namespace Reimann.SignedAdicProduct

open Reimann.DyadicLattice

/-- Exact finite valuation n: the low n+1 bits equal the single bit 2^n. -/
def valuationAt (x : Scalar) (n : Nat) : Prop := (x.residue n).toNat = 2^n

theorem integer_digit_iff (x : Int) (n : Nat) :
    (BitVec.ofInt (n+1) x).toNat = 2^n ↔ Dyadic.exactV x n := by
  let k : Nat := 2^n
  have hk : (0:Int) < k := by exact_mod_cast (Nat.pow_pos (by decide : 0 < 2) : 0 < 2^n)
  have next : ((2^(n+1) : Nat) : Int) = 2*(k:Int) := by simp [k, Nat.pow_succ, Int.mul_comm]
  have base : Dyadic.twoPower n = (k:Int) := by rw [WeightClasses.twoPower_eq_pow]; simp [k]
  rw [BitVec.toNat_ofInt, next]
  change (x%(2*(k:Int))).toNat = k ↔ _
  constructor
  · intro h
    have nonneg := Int.emod_nonneg x (by omega : 2*(k:Int) ≠ 0)
    have digit : x%(2*(k:Int)) = k := by omega
    have eqn := Int.emod_add_mul_ediv x (2*(k:Int))
    rw [digit] at eqn
    refine ⟨x/(2*(k:Int)), ?_⟩
    rw [base]
    grind
  · rintro ⟨u, hu⟩
    rw [base] at hu
    have h : x = (k:Int)+(2*(k:Int))*u := by grind
    rw [h, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    simp

/-- The integer representative may depend on the precision. -/
def representative (c : Scalar) (k : Nat) : Int := (c.residue k).toNat

theorem representative_bits (c : Scalar) {i k : Nat} (h : i ≤ k) :
    BitVec.ofInt (i+1) (representative c k) = c.residue i := by
  rw [representative, BitVec.ofInt_natCast, BitVec.ofNat_toNat, c.reduce h]

theorem representative_mod64 (c : Scalar) {k : Nat} (h : 5 ≤ k) :
    representative c k % 64 = ((c.residue 5).toNat : Int) := by
  have eqn := congrArg BitVec.toNat (representative_bits c h)
  rw [BitVec.toNat_ofInt] at eqn
  change (representative c k % 64).toNat = _ at eqn
  have nonneg := Int.emod_nonneg (representative c k) (by decide : (64:Int) ≠ 0)
  omega

/-- Coherent evaluation of the cleared denominator polynomial. -/
def sample (c0 c1 s a : Scalar) : Scalar :=
  let t := add s (neg a)
  add (add (mul t t) (mul (mul c1 a) t)) (mul c0 (mul a a))

theorem sample_bits {c0 c1 s a : Scalar} {x y t b : Int} (n : Nat)
    (h0 : BitVec.ofInt (n+1) x = c0.residue n) (h1 : BitVec.ofInt (n+1) y = c1.residue n)
    (ht : BitVec.ofInt (n+1) t = s.residue n) (hb : BitVec.ofInt (n+1) b = a.residue n) :
    BitVec.ofInt (n+1) (SampleSpacing.numerator x y t b) = (sample c0 c1 s a).residue n := by
  simp only [SampleSpacing.numerator, Int.pow_succ, Int.pow_zero, Int.one_mul, Int.sub_eq_add_neg, BitVec.ofInt_add,
    BitVec.ofInt_mul, BitVec.ofInt_neg, h0, h1, ht, hb, sample, add, mul, neg]

/-- The product of the positive and negative signed numerators at weight r. -/
def product (c0 c1 : Scalar) (r : Nat) : Scalar :=
  let a := natScalar (5^r)
  mul (sample c0 c1 (natScalar 1) a) (sample c0 c1 (neg (natScalar 1)) a)

theorem product_bits {c0 c1 : Scalar} {x y : Int} (n r : Nat)
    (h0 : BitVec.ofInt (n+1) x = c0.residue n) (h1 : BitVec.ofInt (n+1) y = c1.residue n) :
    BitVec.ofInt (n+1) (PairedSigns.positiveBranch x y r * PairedSigns.negativeBranch x y r) =
      (product c0 c1 r).residue n := by
  have ha : BitVec.ofInt (n+1) ((5:Int)^r) = (natScalar (5^r)).residue n := by
    have hh : ((5^r : Nat) : Int) = (5:Int)^r := by simp
    rw [← hh, BitVec.ofInt_natCast]
    rfl
  have hp : BitVec.ofInt (n+1) (1:Int) = (natScalar 1).residue n := rfl
  have hm : BitVec.ofInt (n+1) (-1:Int) = (neg (natScalar 1)).residue n := by
    rw [BitVec.ofInt_neg, hp]
    rfl
  change BitVec.ofInt (n+1) (_ * _) = (sample c0 c1 (natScalar 1) (natScalar (5^r))).residue n *
    (sample c0 c1 (neg (natScalar 1)) (natScalar (5^r))).residue n
  rw [BitVec.ofInt_mul]
  rw [PairedSigns.positiveBranch, PairedSigns.negativeBranch, sample_bits n h0 h1 hp ha,
    sample_bits n h0 h1 hm ha]

/-- At each weight, either direction uses only n+1 bits of each coefficient. -/
theorem transfer (c0 c1 : Scalar) {k n : Nat} (h : n ≤ k) (r : Nat) :
    valuationAt (product c0 c1 r) n ↔
      Dyadic.exactV (PairedSigns.positiveBranch (representative c0 k) (representative c1 k) r *
        PairedSigns.negativeBranch (representative c0 k) (representative c1 k) r) n := by
  unfold valuationAt
  rw [← product_bits n r (representative_bits c0 h) (representative_bits c1 h)]
  exact integer_digit_iff _ _

theorem weight_three_at_precision (c0 c1 : Scalar)
    (h0 : c0.residue 5 = 40) (h1 : c1.residue 5 = 18) {k : Nat} (hk : 5 ≤ k) :
    PairedSigns.WeightThree (representative c0 k) (representative c1 k) := by
  apply SignedCoefficients.weight_three_from_coefficients
  · rw [representative_mod64 c0 hk, h0]
    decide
  · rw [representative_mod64 c1 hk, h1]
    decide

/-- The exact finite valuations attained at positive odd weights for coherent coefficients. -/
theorem product_valuation_spectrum (c0 c1 : Scalar)
    (h0 : c0.residue 5 = 40) (h1 : c1.residue 5 = 18) (n : Nat) :
    (∃ r, r%2 = 1 ∧ valuationAt (product c0 c1 r) n) ↔ n = 8 ∨ 11 ≤ n := by
  let k := max n 5
  have hn : n ≤ k := Nat.le_max_left _ _
  have hk : 5 ≤ k := Nat.le_max_right _ _
  have spec := SignedProduct.product_valuation_spectrum (weight_three_at_precision c0 c1 h0 h1 hk) n
  constructor
  · rintro ⟨r, hr, hv⟩
    exact spec.mp ⟨r, hr, (transfer c0 c1 hn r).mp hv⟩
  · intro h
    obtain ⟨r, hr, hv⟩ := spec.mpr h
    exact ⟨r, hr, (transfer c0 c1 hn r).mpr hv⟩

end Reimann.SignedAdicProduct
