import Reimann2893.SignedNativeSeries2893
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A single arithmetic annihilation on a cyclic generator suffices for the
principal inclusion once the quotient by finite torsion is rationalized. -/
namespace Reimann.SignedCyclicCriterion2893

open scoped Polynomial Matrix
open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem second_column (f : Module.End K V) (B : Module.Basis (Fin 2) K V)
    (c0 c1 : K) (first : f (B 0) = B 1)
    (ann : f (f (B 0)) + c1 • f (B 0) + c0 • B 0 = 0) :
    f (B 1) = (-c0) • B 0 + (-c1) • B 1 := by
  rw [first] at ann
  rw [neg_smul,neg_smul]
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc] using ann

theorem generator_matrix (f : Module.End K V) (B : Module.Basis (Fin 2) K V)
    (c0 c1 : K) (first : f (B 0) = B 1)
    (ann : f (f (B 0)) + c1 • f (B 0) + c0 • B 0 = 0) :
    LinearMap.toMatrix B B f = !![0,-c0;1,-c1] := by
  have second := second_column f B c0 c1 first ann
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply,first,second]

theorem characteristic_from_generator (f : Module.End K V) (B : Module.Basis (Fin 2) K V)
    (c0 c1 : K) (first : f (B 0) = B 1)
    (ann : f (f (B 0)) + c1 • f (B 0) + c0 • B 0 = 0) :
    f.charpoly = C c0 + C c1 * X + X^2 := by
  rw [← LinearMap.charpoly_toMatrix f B, generator_matrix f B c0 c1 first ann,
    Matrix.charpoly_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp
  ring

noncomputable def constant : ℤ_[2] :=
  SignedNativeScalar2893.realize (SignedAnalyticPreparation.constant SignedArithmeticProjection.analyticSeries)

noncomputable def linear : ℤ_[2] :=
  SignedNativeScalar2893.realize (SignedAnalyticPreparation.linear SignedArithmeticProjection.analyticSeries)

theorem ideal_from_generator {W : Type*} [AddCommGroup W] [Module ℚ_[2] W] [FiniteDimensional ℚ_[2] W]
    (f : Module.End ℚ_[2] W) (B : Module.Basis (Fin 2) ℚ_[2] W) (first : f (B 0)=B 1)
    (ann : f (f (B 0)) + (linear : ℚ_[2]) • f (B 0) + (constant : ℚ_[2]) • B 0 = 0) :
    ∃ c0 c1 : ℤ_[2], f.charpoly = C (c0 : ℚ_[2]) + C (c1 : ℚ_[2])*X + X^2 ∧
      SignedNativeSeries2893.candidate ∈ Ideal.span {SignedNativeSeries2893.quadratic c0 c1} := by
  refine ⟨constant,linear,characteristic_from_generator f B _ _ first ann,?_⟩
  change SignedNativeSeries2893.candidate ∈ Ideal.span {SignedNativeSeries2893.preparedQuadratic}
  rw [← SignedNativeSeries2893.prepared_principal_ideal]
  exact Ideal.subset_span (by simp)

end Reimann.SignedCyclicCriterion2893
