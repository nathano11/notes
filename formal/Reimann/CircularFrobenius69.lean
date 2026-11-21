import Reimann.CircularKernel69
import Reimann.CircularFactor69

/-! The prime 5 splits in the real quadratic coefficient order. In either
reduction of either degree-22 factor, a root has Frobenius period 22. -/

namespace Reimann.CircularFrobenius69

open Lean.Grind Reimann.CircularFactor69 Reimann.CircularKernel69 Reimann.CircularPolynomial69

attribute [local instance] Ring.intCast

theorem five_positive : eta 5 = 1 := by decide

def frobeniusExponents : List Nat := (List.range 22).map (fun k => 5^k % 69)

theorem five_generates_positive :
    frobeniusExponents.Nodup ∧ frobeniusExponents.Perm (exponents 1) := by
  decide +kernel

theorem five_order_mod_69 :
    5^22 % 69 = 1 ∧ ∀ k : Fin 22, k.val ≠ 0 → 5^k.val % 69 ≠ 1 := by
  decide +kernel

/-- A putative fixed point under any earlier Frobenius power would force
x³=1. The multiplier b witnesses the required exponent identity modulo 69. -/
theorem earlier_exponent_witness :
    ∀ k : Fin 22, k.val ≠ 0 →
      ∃ b : Fin 69, ((5^k.val + 68) * b.val) % 69 = 3 := by
  decide +kernel

theorem frobenius_closes {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1) :
    x^(5^22 : Nat) = x := by
  rw [power_period x h69 (5^22), five_order_mod_69.1, Semiring.pow_one]

theorem earlier_frobenius_moves {R : Type} [CommRing R] (x : R)
    (h69 : x^69 = 1) (h3 : x^3 ≠ 1) (k : Fin 22) (hk : k.val ≠ 0) :
    x^(5^k.val : Nat) ≠ x := by
  intro heq
  obtain ⟨b, hb⟩ := earlier_exponent_witness k hk
  have hfix : x^((5^k.val : Nat) + 68) = 1 := by
    rw [Semiring.pow_add, heq]
    calc
      x * x^68 = x^1*x^68 := congrArg (fun y => y*x^68) (Semiring.pow_one x).symm
      _ = x^69 := (Semiring.pow_add x 1 68).symm
      _ = 1 := h69
  apply h3
  calc
    x^3 = x^(((5^k.val+68)*b.val) % 69) := by rw [hb]
    _ = x^((5^k.val+68)*b.val) := (power_period x h69 _).symm
    _ = (x^(5^k.val+68))^b.val := (power_of_power x _ _).symm
    _ = 1 := by rw [hfix, Semiring.one_pow]

/-- The quotient of Φ69 by X³−1 in Euclidean division over ℤ. -/
def cubicQuotient : List Int :=
  [7,-14,8,6,-13,8,5,-12,8,4,-11,8,3,-10,8,2,-9,8,1,-8,8,0,-7,7,0,-6,6,
   0,-5,5,0,-4,4,0,-3,3,0,-2,2,0,-1,1]

theorem cubic_remainder_coefficients :
    phi = add [8,-15,8] (mulInt [-1,0,0,1] cubicQuotient) := by
  decide +kernel

theorem phi_at_cubic_root {R : Type} [CommRing R] (x : R) (h3 : x^3 = 1) :
    eval x phi = 8*x^2 - 15*x + 8 := by
  rw [cubic_remainder_coefficients, eval_add, eval_mulInt]
  simp only [eval, Ring.intCast_neg, Ring.intCast_zero, Ring.intCast_one,
    Semiring.mul_zero, Semiring.add_zero]
  grind only

theorem root_order_divides_69 {R : Type} [CommRing R] (x : R) (hphi : eval x phi = 0) :
    x^69 = 1 := by
  have hf := phi_factorization x
  rw [hphi, Semiring.zero_mul] at hf
  have hg := Reimann.CircularPrimitive69.conductor_factor_identity x
  rw [← hf, Semiring.mul_zero] at hg
  grind only

theorem cubic_excluded_mod_five {R : Type} [Field R] [IsCharP R 5]
    (x : R) (hphi : eval x phi = 0) : x^3 ≠ 1 := by
  intro hx
  have h := phi_at_cubic_root x hx
  rw [hphi] at h
  grind only

theorem order23_excluded_mod_five {R : Type} [Field R] [IsCharP R 5]
    (x : R) (hphi : eval x phi = 0) : x^23 ≠ 1 := by
  intro hx
  have hf := phi_factorization x
  rw [hphi, Semiring.zero_mul, show 46 = 23+23 by decide,
    Semiring.pow_add, hx] at hf
  grind only

theorem quadratic_reductions_at_five {R : Type} [Field R] [IsCharP R 5] (t : R) :
    t^2 = t + 17 ↔ t = 2 ∨ t = 4 := by
  constructor
  · intro ht
    have hp : (t-2)*(t-4) = 0 := by grind only
    rcases Field.of_mul_eq_zero hp with h | h
    · left; grind only
    · right; grind only
  · rintro (rfl | rfl) <;> grind only

theorem factor_root_is_phi_root {R : Type} [Field R] (t x : R)
    (ht : t^2 = t + 17)
    (hx : evalPoly t x positiveCoeffs = 0 ∨ evalPoly t x negativeCoeffs = 0) :
    eval x phi = 0 := by
  rw [← factorization t x ht]
  rcases hx with hx | hx
  · rw [hx, Semiring.zero_mul]
  · rw [hx, Semiring.mul_zero]

/-- Every root of either degree-22 reduction, in every field of characteristic
five, has exact period 22 under the Frobenius map x ↦ x⁵. -/
theorem reduced_factor_root_period {R : Type} [Field R] [IsCharP R 5] (t x : R)
    (ht : t^2 = t + 17)
    (hx : evalPoly t x positiveCoeffs = 0 ∨ evalPoly t x negativeCoeffs = 0) :
    x^(5^22 : Nat) = x ∧ ∀ k : Fin 22, k.val ≠ 0 → x^(5^k.val : Nat) ≠ x := by
  have hphi := factor_root_is_phi_root t x ht hx
  have h69 := root_order_divides_69 x hphi
  exact ⟨frobenius_closes x h69, earlier_frobenius_moves x h69 (cubic_excluded_mod_five x hphi)⟩

/-- For degree 22 the two proper exponents in Rabin's irreducibility criterion
are 22/11=2 and 22/2=11. This is the root form of the test. -/
theorem reduced_factor_rabin_tests {R : Type} [Field R] [IsCharP R 5] (t x : R)
    (ht : t^2 = t + 17)
    (hx : evalPoly t x positiveCoeffs = 0 ∨ evalPoly t x negativeCoeffs = 0) :
    x^(5^22 : Nat) = x ∧ x^(5^2 : Nat) ≠ x ∧ x^(5^11 : Nat) ≠ x := by
  obtain ⟨h, he⟩ := reduced_factor_root_period t x ht hx
  exact ⟨h, he 2 (by decide), he 11 (by decide)⟩

end Reimann.CircularFrobenius69
