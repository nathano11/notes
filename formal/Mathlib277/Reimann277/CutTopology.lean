import Reimann277.CutRestriction
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Homeomorph.Lemmas

namespace Reimann.TameCutTopology277

open TameBiquadraticField277 TameCyclotomicLocal277

theorem cut_absolute_compact (r n : ℕ) : CompactSpace (Field.absoluteGaloisGroup (cutField r n)) :=
  inferInstanceAs (CompactSpace (AlgebraicClosure (cutField r n) ≃ₐ[cutField r n]
    AlgebraicClosure (cutField r n)))

theorem continuous_kernel_absolute (r n : ℕ) : Continuous (kernelAbsoluteEquiv r n) := by
  let _ := cut_absolute_compact r n
  let _ : T2Space Global := krullTopology_t2 (K := Biquadratic) (L := AlgebraicClosure Biquadratic)
  exact Continuous.continuous_symm_of_equiv_compact_to_t2 (f := (kernelAbsoluteEquiv r n).symm.toEquiv)
    (continuous_absolute_inverse r n)

/-- The topology induced from the global absolute Galois group is precisely the
Krull topology of the finite twist's cut field. -/
noncomputable def kernelAbsoluteHomeomorph (r n : ℕ) :
    globalKernel r n ≃ₜ* Field.absoluteGaloisGroup (cutField r n) where
  toMulEquiv := kernelAbsoluteEquiv r n
  continuous_toFun := continuous_kernel_absolute r n
  continuous_invFun := continuous_absolute_inverse r n

theorem kernelAbsoluteHomeomorph_apply (r n : ℕ) (g : globalKernel r n) :
    kernelAbsoluteHomeomorph r n g = kernelAbsoluteEquiv r n g := rfl

theorem kernel_compact (r n : ℕ) : CompactSpace (globalKernel r n) := by
  let _ := cut_absolute_compact r n
  exact (kernelAbsoluteHomeomorph r n).symm.compactSpace

end Reimann.TameCutTopology277
