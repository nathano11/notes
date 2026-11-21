import Mathlib.FieldTheory.AbsoluteGaloisGroup

namespace Reimann.TameCanonicalDecomposition277

variable {K L : Type} [Field K] [Field L]

/-- Restrict along an explicitly chosen isomorphism of algebraic closures over
an isomorphism of the coefficient fields. -/
noncomputable def transport (e : K ≃+* L) (u : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hu : ∀ a, u (algebraMap K _ a) = algebraMap L _ (e a)) :
    Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K :=
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := u.toRingHom.toAlgebra
  letI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    .of_algebraMap_eq (fun a => (hu a).symm)
  Field.absoluteGaloisGroup.mapOfAlgebra K L

theorem transport_commutes (e : K ≃+* L) (u : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hu : ∀ a, u (algebraMap K _ a) = algebraMap L _ (e a))
    (g : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K) :
    u ((show AlgebraicClosure K ≃ₐ[K] _ from transport e u hu g) x) =
      (show AlgebraicClosure L ≃ₐ[L] _ from g) (u x) := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := u.toRingHom.toAlgebra
  letI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L) :=
    .of_algebraMap_eq (fun a => (hu a).symm)
  exact ((show AlgebraicClosure L ≃ₐ[L] _ from g).restrictScalars K).restrictNormal_commutes
    (AlgebraicClosure K) x

theorem inverse_square (e : K ≃+* L) (u : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hu : ∀ a, u (algebraMap K _ a) = algebraMap L _ (e a)) (a : L) :
    u.symm (algebraMap L _ a) = algebraMap K _ (e.symm a) := by
  apply u.injective
  rw [u.apply_symm_apply,hu,e.apply_symm_apply]

theorem transport_surjective (e : K ≃+* L) (u : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hu : ∀ a, u (algebraMap K _ a) = algebraMap L _ (e a)) :
    Function.Surjective (transport e u hu) := by
  intro g
  let v := transport e.symm u.symm (inverse_square e u hu) g
  refine ⟨v,?_⟩
  change (show AlgebraicClosure K ≃ₐ[K] _ from transport e u hu v) =
    (show AlgebraicClosure K ≃ₐ[K] _ from g)
  apply AlgEquiv.ext
  intro z
  apply u.injective
  rw [transport_commutes]
  have h := transport_commutes e.symm u.symm (inverse_square e u hu) g (u z)
  rw [u.symm_apply_apply] at h
  exact (u.symm_apply_eq.mp h)

end Reimann.TameCanonicalDecomposition277
