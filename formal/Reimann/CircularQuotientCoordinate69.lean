import Reimann.CircularFieldReduction69
import Reimann.CircularPrimitive69

/-! The integral representative of the signed quotient and its labelled reduction. -/
namespace Reimann.CircularQuotientCoordinate69

open Lean.Grind CircularFieldReduction69 CircularPolynomial69

variable {R : Type} [Field R] [IsCharP R 0] {x : R}

theorem signed_product_inverse (hx : Primitive69 x) :
    signedProduct x 1 = (signedProduct x 276)⁻¹ :=
  Field.eq_inv_of_mul_eq_one (norm_products_multiply x
    (CircularPrimitive69.phi_vanishes_of_order69 x hx.order69 hx.not23 hx.not3))

def quotientInOrder (x : R) : IntegralOrder x := orderMul (signedUnit x 1) (signedUnit x 1)

theorem quotient_value (hx : Primitive69 x) :
    (quotientInOrder x).val = signedProduct x 1 / signedProduct x 276 := by
  change (signedUnit x 1).val * (signedUnit x 1).val = _
  rw [signedUnit_value, Field.div_eq_mul_inv, ← signed_product_inverse hx]

theorem quotient_residue (hx : Primitive69 x) : reduction hx (quotientInOrder x) = 75484 := by
  rw [quotientInOrder, reduction_mul, reduction_positive]
  decide +kernel

theorem quotient_projection (hx : Primitive69 x) :
    reduction hx (orderPow (quotientInOrder x) 414) = 42957 := by
  rw [reduction_pow, quotient_residue]
  decide +kernel

theorem base_pow_41 : (49063 : Fin 114679)^41 = 42957 := by decide +kernel

theorem quotient_coordinate (hx : Primitive69 x) (a : Fin 277) :
    (49063 : Fin 114679)^a.val = reduction hx (orderPow (quotientInOrder x) 414) ↔ a = 41 := by
  rw [quotient_projection, ← base_pow_41]
  exact ⟨auxiliary_log_base_injective a 41, fun h => by rw [h]; rfl⟩

end Reimann.CircularQuotientCoordinate69
