import Reimann277.CyclotomicLocal

namespace Reimann.TameCutTopology277

open TameBiquadraticField277 TameCyclotomicLocal277

noncomputable def closureComparison (r n : ℕ) :
    AlgebraicClosure Biquadratic ≃ₐ[cutField r n] AlgebraicClosure (cutField r n) :=
  letI := cutField_isAlgClosure r n
  IsAlgClosure.equiv (cutField r n) (AlgebraicClosure Biquadratic) (AlgebraicClosure (cutField r n))

theorem kernel_action (r n : ℕ) (g : globalKernel r n) (z : AlgebraicClosure Biquadratic) :
    asAut (kernelAbsoluteEquiv r n g) (closureComparison r n z) =
      closureComparison r n (asAut g.val z) := by
  change closureComparison r n (kernelAutEquiv r n g ((closureComparison r n).symm
    (closureComparison r n z))) = _
  rw [AlgEquiv.symm_apply_apply,kernelAutEquiv_apply]

theorem closureComparison_on_base (r n : ℕ) (x : Biquadratic) :
    closureComparison r n (algebraMap Biquadratic (AlgebraicClosure Biquadratic) x) =
      algebraMap Biquadratic (AlgebraicClosure (cutField r n)) x :=
  ((closureComparison r n).restrictScalars Biquadratic).commutes x

noncomputable def restrictBase (r n : ℕ) (g : Field.absoluteGaloisGroup (cutField r n)) :
    AlgebraicClosure (cutField r n) ≃ₐ[Biquadratic] AlgebraicClosure (cutField r n) :=
  (asAut g).restrictScalars Biquadratic

/-- Continuous restriction from the absolute group of the fixed field, using the
same identification of closures as the algebraic equivalence of its kernel. -/
noncomputable def cutRestriction (r n : ℕ) : Field.absoluteGaloisGroup (cutField r n) →ₜ* Global :=
  let u := closureComparison r n
  letI : Algebra (AlgebraicClosure Biquadratic) (AlgebraicClosure (cutField r n)) :=
    u.toRingHom.toAlgebra
  letI : IsScalarTower Biquadratic (AlgebraicClosure Biquadratic) (AlgebraicClosure (cutField r n)) :=
    .of_algebraMap_eq (fun x => (closureComparison_on_base r n x).symm)
  Field.absoluteGaloisGroup.mapOfAlgebra Biquadratic (cutField r n)

theorem cutRestriction_commutes (r n : ℕ) (g : Field.absoluteGaloisGroup (cutField r n))
    (z : AlgebraicClosure Biquadratic) :
    closureComparison r n (asAut (cutRestriction r n g) z) = asAut g (closureComparison r n z) := by
  let u := closureComparison r n
  letI : Algebra (AlgebraicClosure Biquadratic) (AlgebraicClosure (cutField r n)) :=
    u.toRingHom.toAlgebra
  letI : IsScalarTower Biquadratic (AlgebraicClosure Biquadratic) (AlgebraicClosure (cutField r n)) :=
    .of_algebraMap_eq (fun x => (closureComparison_on_base r n x).symm)
  exact (restrictBase r n g).restrictNormal_commutes (AlgebraicClosure Biquadratic) z

theorem cutRestriction_kernel (r n : ℕ) (g : globalKernel r n) :
    cutRestriction r n (kernelAbsoluteEquiv r n g) = g.val := by
  change asAut (cutRestriction r n (kernelAbsoluteEquiv r n g)) = asAut g.val
  apply AlgEquiv.ext
  intro z
  apply (closureComparison r n).injective
  rw [cutRestriction_commutes,kernel_action]

theorem continuous_absolute_inverse (r n : ℕ) : Continuous (kernelAbsoluteEquiv r n).symm := by
  have h : (fun x : Field.absoluteGaloisGroup (cutField r n) => ((kernelAbsoluteEquiv r n).symm x).val) =
      (cutRestriction r n : Field.absoluteGaloisGroup (cutField r n) → Global) := by
    funext x
    obtain ⟨g,rfl⟩ := (kernelAbsoluteEquiv r n).surjective x
    rw [MulEquiv.symm_apply_apply,cutRestriction_kernel]
  have hc : Continuous (fun x : Field.absoluteGaloisGroup (cutField r n) =>
      ((kernelAbsoluteEquiv r n).symm x).val) := h ▸ (cutRestriction r n).continuous
  exact hc.subtype_mk _

end Reimann.TameCutTopology277
