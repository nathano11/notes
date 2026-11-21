import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.Basic

/-! The relative norm of ideals commutes with automorphisms of a tower of number fields.
Both the field norm and the ideal norm use the inclusion in the given tower. -/
namespace Reimann.SignedIdealNormEquivariance2893

open NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

theorem field_norm (σ : K ≃+* K) (τ : L ≃+* L)
    (square : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (σ x)) (x : L) :
    σ (Algebra.norm K x) = Algebra.norm K (τ x) := by
  have h := Algebra.norm_eq_of_equiv_equiv σ τ
    (RingHom.ext fun y => (square y).symm) x
  exact (congrArg σ h).trans (σ.apply_symm_apply _)

/-- Transport of relative integral norms through the induced isomorphisms of integer rings. -/
theorem int_norm (σ : K ≃+* K) (τ : L ≃+* L)
    (square : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (σ x)) (x : 𝓞 L) :
    RingOfIntegers.mapRingEquiv σ (Algebra.intNorm (𝓞 K) (𝓞 L) x) =
      Algebra.intNorm (𝓞 K) (𝓞 L) (RingOfIntegers.mapRingEquiv τ x) := by
  apply RingOfIntegers.ext
  change σ (algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 L) x)) =
    algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 L) (RingOfIntegers.mapRingEquiv τ x))
  rw [Algebra.algebraMap_intNorm (L := L), Algebra.algebraMap_intNorm (L := L)]
  exact field_norm σ τ square (x : L)

/-- The image of the relative ideal norm is the norm of the image ideal. -/
theorem map_relNorm (σ : K ≃+* K) (τ : L ≃+* L)
    (square : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (σ x)) (I : Ideal (𝓞 L)) :
    (Ideal.relNorm (𝓞 K) I).map (RingOfIntegers.mapRingEquiv σ) =
      Ideal.relNorm (𝓞 K) (I.map (RingOfIntegers.mapRingEquiv τ)) := by
  rw [Ideal.map_relNorm]
  change Ideal.span _ =
    Ideal.span (Algebra.intNorm (𝓞 K) (𝓞 L) '' ((I.map (RingOfIntegers.mapRingEquiv τ)) : Set (𝓞 L)))
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv τ x, Ideal.mem_map_of_mem _ hx, (int_norm σ τ square x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (RingOfIntegers.mapRingEquiv τ).toRingHom (RingOfIntegers.mapRingEquiv τ).surjective).mp hy
    exact ⟨x, hx, int_norm σ τ square x⟩

end Reimann.SignedIdealNormEquivariance2893
