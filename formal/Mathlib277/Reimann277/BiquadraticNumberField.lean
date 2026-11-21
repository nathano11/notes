import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Reimann277.BiquadraticReal

namespace Reimann.TameBiquadraticField277

open TameRationalField277

/-- The four explicit rational coordinates are linear for the canonical
rational scalar action on the bundled field. -/
noncomputable def coordinateLinearEquiv : Biquadratic ≃ₗ[ℚ] Biquad where
  toFun := Biquadratic.coord
  invFun := Biquadratic.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' q x := by
    rw [Algebra.smul_def, coefficientHom_apply]
    rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩⟩
    change bm (scalar q) ((a,b),(c,d)) = ((q*a,q*b),(q*c,q*d))
    simp [bm,scalar,qm,qa,qs]

theorem biquadraticFiniteDimensional : FiniteDimensional ℚ Biquadratic :=
  FiniteDimensional.of_injective coordinateLinearEquiv.toLinearMap coordinateLinearEquiv.injective

instance biquadraticNumberField : NumberField Biquadratic where
  to_charZero := biquadraticCharZero
  to_finiteDimensional := biquadraticFiniteDimensional

theorem biquadratic_degree : Module.finrank ℚ Biquadratic = 4 := by
  rw [coordinateLinearEquiv.finrank_eq]
  simp [Biquad,Quad,Module.finrank_prod]

theorem rational_expansion (a b c d : ℚ) :
    algebraMap ℚ Biquadratic a + algebraMap ℚ Biquadratic b * sqrtNegThree +
      (algebraMap ℚ Biquadratic c * sqrtNegTwentyThree +
        algebraMap ℚ Biquadratic d * (sqrtNegThree * sqrtNegTwentyThree)) =
      ⟨((a,b),(c,d))⟩ := by
  simp only [coefficientHom_apply]
  exact coord_injective (basis_expansion a b c d)

theorem adjoin_radicals : Algebra.adjoin ℚ ({sqrtNegThree,sqrtNegTwentyThree} : Set Biquadratic) = ⊤ := by
  apply top_unique
  intro x _
  let S := Algebra.adjoin ℚ ({sqrtNegThree,sqrtNegTwentyThree} : Set Biquadratic)
  have h3 : sqrtNegThree ∈ S := Algebra.subset_adjoin (by simp)
  have h23 : sqrtNegTwentyThree ∈ S := Algebra.subset_adjoin (by simp)
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩⟩
  rw [← rational_expansion]
  exact S.add_mem (S.add_mem (S.algebraMap_mem a) (S.mul_mem (S.algebraMap_mem b) h3))
    (S.add_mem (S.mul_mem (S.algebraMap_mem c) h23)
      (S.mul_mem (S.algebraMap_mem d) (S.mul_mem h3 h23)))

end Reimann.TameBiquadraticField277
