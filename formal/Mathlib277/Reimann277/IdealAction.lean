import Reimann277.ArtinBasic
import Mathlib.RingTheory.ClassGroup.ExtendedHom

namespace Reimann.TameIdealAction277

open TameBiquadraticField277 TameCyclotomicLocal277 TameArtin277

noncomputable def onField (r n : ℕ) (g : Global) :
    cutField r n ≃ₐ[Biquadratic] cutField r n := by
  letI := (cutField_finite_galois r n).2
  exact (asAut g).restrictNormal (cutField r n)

noncomputable def onIntegers (r n : ℕ) (g : Global) : CutIntegers r n ≃+* CutIntegers r n :=
  NumberField.RingOfIntegers.mapRingEquiv (onField r n g).toRingEquiv

theorem denominators_fixed (r n : ℕ) (g : Global) :
    (Submonoid.powers (277 : CutIntegers r n)).map (onIntegers r n g).toMonoidHom =
      Submonoid.powers (277 : CutIntegers r n) := by
  rw [Submonoid.map_powers]
  congr 1
  exact map_ofNat (onIntegers r n g) _

noncomputable def onSIntegers (r n : ℕ) (g : Global) : SIntegers r n ≃+* SIntegers r n :=
  IsLocalization.ringEquivOfRingEquiv (SIntegers r n) (SIntegers r n)
    (onIntegers r n g) (denominators_fixed r n g)

/-- Transport fractional ideal classes by the genuine automorphism of the localized ring. -/
noncomputable def onClass (r n : ℕ) (g : Global) : SClassGroup r n ≃* SClassGroup r n :=
  ClassGroup.mulEquiv (onSIntegers r n g)

noncomputable def conjugateKernel {r n : ℕ} (g : Global) (x : globalKernel r n) : globalKernel r n :=
  ⟨g*x.val*g⁻¹, (globalKernelNormal r n).conj_mem _ x.property g⟩

/-- Naturality of inverse Artin for conjugation and transport of fractional ideal classes. -/
def ArtinEquivariant {r n : ℕ} (e : ClassReciprocity r n) : Prop :=
  ∀ (g : Global) (x : globalKernel r n),
    toClassGroup e (conjugateKernel g x) = onClass r n g (toClassGroup e x)

end Reimann.TameIdealAction277
