import Reimann2893.SignedNativeSeries2893
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Rationalize over the dyadic integers and take the determinant for the
forward operator minus the identity. A finite torsion summand maps to zero. -/
namespace Reimann.SignedRationalCharacteristic2893

open scoped TensorProduct Polynomial
open Polynomial

variable (M : Type*) [AddCommGroup M] [Module ℤ_[2] M]

abbrev Space := ℚ_[2] ⊗[ℤ_[2]] M

noncomputable def forward (g : M ≃ₗ[ℤ_[2]] M) : Module.End ℚ_[2] (Space M) :=
  g.toLinearMap.baseChange ℚ_[2]

theorem forward_tmul (g : M ≃ₗ[ℤ_[2]] M) (a : ℚ_[2]) (m : M) :
    forward M g (a ⊗ₜ[ℤ_[2]] m) = a ⊗ₜ[ℤ_[2]] g m := rfl

noncomputable def augmentation (g : M ≃ₗ[ℤ_[2]] M) : Module.End ℚ_[2] (Space M) :=
  forward M g - 1

variable [FiniteDimensional ℚ_[2] (Space M)]

noncomputable def characteristic (g : M ≃ₗ[ℤ_[2]] M) : ℚ_[2][X] :=
  (augmentation M g).charpoly

theorem determinant_convention (g : M ≃ₗ[ℤ_[2]] M) (t : ℚ_[2]) :
    (characteristic M g).eval t =
      (algebraMap ℚ_[2] (Module.End ℚ_[2] (Space M)) (1+t) - forward M g).det := by
  rw [characteristic, LinearMap.eval_charpoly, augmentation, map_add, map_one]
  congr 1
  abel

theorem characteristic_degree (g : M ≃ₗ[ℤ_[2]] M) :
    (characteristic M g).natDegree = Module.finrank ℚ_[2] (Space M) :=
  (augmentation M g).charpoly_natDegree

theorem monic_quadratic_shape (p : ℚ_[2][X]) (hm : p.Monic) (hd : p.natDegree=2) :
    p = C (p.coeff 0) + C (p.coeff 1)*X + X^2 := by
  have h := p.as_sum_range_C_mul_X_pow
  have lead : p.coeff 2 = 1 := by simpa only [hd] using hm.coeff_natDegree
  rw [hd] at h
  simpa [Finset.sum_range_succ,lead] using h

theorem characteristic_quadratic (g : M ≃ₗ[ℤ_[2]] M) (rank : Module.finrank ℚ_[2] (Space M)=2) :
    let p := characteristic M g
    p = C (p.coeff 0) + C (p.coeff 1)*X + X^2 :=
  monic_quadratic_shape _ (augmentation M g).charpoly_monic ((characteristic_degree M g).trans rank)

def integralCoeff (p : ℚ_[2][X]) (i : ℕ) (h : ‖p.coeff i‖ ≤ 1) : ℤ_[2] :=
  ⟨p.coeff i, h⟩

theorem integralCoeff_value (p : ℚ_[2][X]) (i : ℕ) (h : ‖p.coeff i‖ ≤ 1) :
    ((integralCoeff p i h : ℤ_[2]) : ℚ_[2]) = p.coeff i := rfl

end Reimann.SignedRationalCharacteristic2893
