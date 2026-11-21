import Reimann.CircularPolynomial69

/-! The three power tests for exact order 69 suffice for the signed norm
products in every field. The geometric factors appear in the two cancellation
steps of the cyclotomic identity. -/

namespace Reimann.CircularPrimitive69

open Lean.Grind Reimann.CircularPolynomial69

theorem cubic_factor_identity {R : Type} [CommRing R] (x : R) :
    (x - 1) * (1 + x + x^2) = x^3 - 1 := by
  grind only

theorem conductor_factor_identity {R : Type} [CommRing R] (x : R) :
    (x^23 - 1) * (1 + x^23 + x^46) = x^69 - 1 := by
  rw [show 69 = 46 + 23 by decide, Semiring.pow_add x 46 23,
      show 46 = 23 + 23 by decide, Semiring.pow_add x 23 23]
  grind only

theorem cubic_factor_nonzero {R : Type} [CommRing R] (x : R) (h3 : x^3 ≠ 1) :
    1 + x + x^2 ≠ 0 := by
  intro h
  have hf := cubic_factor_identity x
  rw [h, Semiring.mul_zero] at hf
  exact h3 (by grind only)

theorem conductor_factor_zero {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) : 1 + x^23 + x^46 = 0 := by
  have hf := conductor_factor_identity x
  rw [h69] at hf
  have hz : (x^23 - 1) * (1 + x^23 + x^46) = 0 := by
    rw [hf]
    grind only
  rcases Field.of_mul_eq_zero hz with h | h
  · exact False.elim (h23 (by grind only))
  · exact h

theorem phi_vanishes_of_order69 {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    eval x phi = 0 := by
  have hf := phi_factorization x
  rw [conductor_factor_zero x h69 h23] at hf
  exact (Field.of_mul_eq_zero hf).resolve_right (cubic_factor_nonzero x h3)

theorem primitive_products_trace {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    signedProduct x 1 + signedProduct x 276 = 25 :=
  norm_products_trace x (phi_vanishes_of_order69 x h69 h23 h3)

theorem primitive_products_norm {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    signedProduct x 1 * signedProduct x 276 = 1 :=
  norm_products_multiply x (phi_vanishes_of_order69 x h69 h23 h3)

/-- The two signed factors lie above the discriminant 25²−4 = 9·69. -/
theorem primitive_product_discriminant {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    (2 * signedProduct x 1 - 25)^2 = 9 * 69 := by
  have ht := primitive_products_trace x h69 h23 h3
  have hn := primitive_products_norm x h69 h23 h3
  grind only

end Reimann.CircularPrimitive69
