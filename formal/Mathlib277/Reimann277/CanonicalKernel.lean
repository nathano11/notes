import Reimann277.CanonicalDecomposition
import Reimann277.CutTopology
import Reimann277.LocalCompositum

namespace Reimann.TameCanonicalDecomposition277

open TameBiquadraticField277 TameFinitePlaces277 TameCyclotomicLocal277
open TameLocalCompositum277 TameCutTopology277

local instance completionFieldCharZero (v : Above Biquadratic) : CharZero (CompletionField v) :=
  (comparison v).toRingHom.charZero

noncomputable def localCutField (r n : ℕ) (v : Above Biquadratic) :
    IntermediateField (CompletionField v) (AlgebraicClosure (CompletionField v)) :=
  localCompositum (closureAt v) (cutField r n)

theorem completionKernel_eq_comap (r n : ℕ) (v : Above Biquadratic) :
    completionKernel r n v = (globalKernel r n).comap (absoluteRestriction v).toMonoidHom := rfl

theorem localCutField_fixing (r n : ℕ) (v : Above Biquadratic) :
    (localCutField r n v).fixingSubgroup = completionKernel r n v := by
  change (localCompositum (closureAt v) (cutField r n)).fixingSubgroup = _
  rw [fixing_localCompositum (closureAt v) (absoluteRestriction v).toMonoidHom
    (absoluteRestriction_commutes v),cutField_fixing,completionKernel_eq_comap] <;> rfl

theorem completionKernel_fixedField (r n : ℕ) (v : Above Biquadratic) :
    IntermediateField.fixedField (completionKernel r n v) = localCutField r n v := by
  rw [← localCutField_fixing,InfiniteGalois.fixedField_fixingSubgroup]

theorem localCutField_finite_galois (r n : ℕ) (v : Above Biquadratic) :
    FiniteDimensional (CompletionField v) (localCutField r n v) ∧
      IsGalois (CompletionField v) (localCutField r n v) := by
  apply (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (localCutField r n v)).mp
  rw [localCutField_fixing,completionKernel_eq_comap]
  exact ⟨(globalKernel_open r n).preimage (absoluteRestriction v).continuous,
    (globalKernelNormal r n).comap (absoluteRestriction v).toMonoidHom⟩

/-- Transport the completed local restrictions to the cut field's chosen absolute Galois group. -/
noncomputable def absoluteCutDecomposition (r n : ℕ) (v : Above Biquadratic) (a : Global) :
    completionKernel r n v →ₜ* Field.absoluteGaloisGroup (cutField r n) :=
  (kernelAbsoluteHomeomorph r n : globalKernel r n →ₜ* Field.absoluteGaloisGroup (cutField r n)).comp
    (conjugatedAt r n v a)

theorem atPlaces_iff_absolute_cut (r n : ℕ) (x : globalKernel r n) :
    x ∈ atPlaces r n ↔ ∃ (v : Above Biquadratic) (a : Global) (g : completionKernel r n v),
      kernelAbsoluteHomeomorph r n x = absoluteCutDecomposition r n v a g := by
  rw [atPlaces_iff_canonical]
  constructor
  · rintro ⟨v,a,g,rfl⟩
    exact ⟨v,a,g,rfl⟩
  · rintro ⟨v,a,g,h⟩
    exact ⟨v,a,g,(kernelAbsoluteHomeomorph r n).injective h⟩

end Reimann.TameCanonicalDecomposition277
