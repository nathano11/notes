import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.NumberField.Basic

namespace Reimann.TameLocalClass277

open scoped nonZeroDivisors
open NumberField

section Localization

variable {R : Type*} [CommRing R]
variable (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
include M

/-- Extending the contraction of an ideal of the localization returns that ideal. -/
theorem extend_under (J : Ideal S) :
    (J.under R).map (algebraMap R S) = J :=
  IsLocalization.map_under M S J

/-- A nonzero ideal of the localization contracts to a nonzero ideal. -/
theorem under_ne_zero {J : Ideal S} (hJ : J ≠ 0) : J.under R ≠ 0 := by
  intro hz
  have h : (0 : Ideal S) = J := by simpa [hz] using extend_under M S J
  exact hJ h.symm

variable [IsDedekindDomain R]

section Extension

variable [IsDedekindDomain S] [Module.IsTorsionFree R S]

def contractIdeal (J : (Ideal S)⁰) : (Ideal R)⁰ :=
  ⟨J.val.under R, mem_nonZeroDivisors_iff_ne_zero.mpr
    (under_ne_zero M S (mem_nonZeroDivisors_iff_ne_zero.mp J.property))⟩

theorem extend_contract (J : (Ideal S)⁰) :
    ClassGroup.extendedIdeal R S (contractIdeal M S J) = J := by
  apply Subtype.ext
  exact extend_under M S J.val

theorem class_extend_contract (J : (Ideal S)⁰) :
    ClassGroup.extendedHom R S (ClassGroup.mk0 (contractIdeal M S J)) = ClassGroup.mk0 J := by
  rw [ClassGroup.extendedHom_mk0, extend_contract]

/-- Every localized class comes from the class of an actual nonzero ideal of the base. -/
theorem extendedHom_surjective : Function.Surjective (ClassGroup.extendedHom R S) := by
  intro c
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  exact ⟨ClassGroup.mk0 (contractIdeal M S J), class_extend_contract M S J⟩

end Extension

theorem localized_class_finite [IsDomain S] (hM : M ≤ R⁰) [Finite (ClassGroup R)] :
    Finite (ClassGroup S) := by
  letI : IsDedekindDomain S := IsLocalization.isDedekindDomain R hM S
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (IsLocalization.injective S hM)
  exact Finite.of_surjective _ (extendedHom_surjective M S)

end Localization

/-- Finiteness for the full ring of integers by the integer admissible absolute value. -/
theorem ring_integers_class_finite (K : Type*) [Field K] [NumberField K] :
    Finite (ClassGroup (𝓞 K)) := by
  letI : Fintype (ClassGroup (𝓞 K)) :=
    ClassGroup.fintypeOfAdmissibleOfFinite ℚ K AbsoluteValue.absIsAdmissible
  infer_instance

theorem powers_277_regular (K : Type*) [Field K] [NumberField K] :
    Submonoid.powers (277 : 𝓞 K) ≤ (𝓞 K)⁰ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num)

/-- Any number field has a finite class group after inverting 277. -/
theorem class_finite_away_277 (K : Type*) [Field K] [NumberField K]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra (𝓞 K) B]
    [IsLocalization.Away (277 : 𝓞 K) B] : Finite (ClassGroup B) := by
  letI := ring_integers_class_finite K
  exact localized_class_finite (Submonoid.powers (277 : 𝓞 K)) B (powers_277_regular K)

end Reimann.TameLocalClass277
