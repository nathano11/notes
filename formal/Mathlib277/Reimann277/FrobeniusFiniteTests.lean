import Reimann277.FrobeniusTower
import Reimann277.AbsoluteFrobenius
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Frobenius

namespace Reimann.TameFrobeniusFiniteTests277

open NumberField TameInertia277 TameFrobeniusTower277 TameAbsoluteFrobenius277

variable {K L : Type} [Field K] [Field L] [Algebra K L] [NumberField K]

/-- Arithmetic Frobenius on the finite Galois stage above the fixed absolute prime. -/
theorem finite_frobenius (P : Ideal (𝓞 L)) (hp : P.IsPrime) (h : P.under (𝓞 K) ≠ 0)
    (E : FiniteGaloisIntermediateField K L) :
    ∃ σ : E ≃ₐ[K] E, ∀ y : 𝓞 E, σ • y - y ^ Nat.card (𝓞 K ⧸ P.under (𝓞 K)) ∈ P.under (𝓞 E) := by
  letI := NumberField.of_module_finite K E
  letI := hp
  letI := finite_residue P h E
  obtain ⟨σ,hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (E ≃ₐ[K] E) (P.under (𝓞 E))
  refine ⟨σ, fun y => ?_⟩
  have hy := hσ y
  rw [contracted_twice P E] at hy
  exact hy

/-- A lift to the top field satisfies every integral residue test from the finite stage. -/
theorem lifted_stage [IsGalois K L] (P : Ideal (𝓞 L)) (hp : P.IsPrime) (h : P.under (𝓞 K) ≠ 0)
    (E : FiniteGaloisIntermediateField K L) :
    ∃ g : L ≃ₐ[K] L, ∀ y : 𝓞 E, g ∈ TestAt P (Nat.card (𝓞 K ⧸ P.under (𝓞 K)))
        (algebraMap (𝓞 E) (𝓞 L) y) := by
  obtain ⟨σ,hσ⟩ := finite_frobenius P hp h E
  obtain ⟨g,hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (E := L) σ
  refine ⟨g, fun y => ?_⟩
  have hy := hσ y
  change algebraMap (𝓞 E) (𝓞 L) _ ∈ P at hy
  change g.restrictNormal E = σ at hg
  rw [← hg, map_sub, map_pow, restrict_act] at hy
  exact (Ideal.Quotient.eq.mpr hy).trans (map_pow (Ideal.Quotient.mk P) _ _)

theorem finite_tests [IsGalois K L] (P : Ideal (𝓞 L)) (hp : P.IsPrime) (h : P.under (𝓞 K) ≠ 0)
    (S : Finset (Integers L)) : ∃ g : L ≃ₐ[K] L, ∀ x ∈ S, g ∈ TestAt P
      (Nat.card (𝓞 K ⧸ P.under (𝓞 K))) x := by
  obtain ⟨E,hE⟩ := finite_set_preimages (K := K) S
  obtain ⟨g,hg⟩ := lifted_stage P hp h E
  refine ⟨g,fun x hx => ?_⟩
  obtain ⟨y,rfl⟩ := hE x hx
  exact hg y

end Reimann.TameFrobeniusFiniteTests277
