import Reimann277.Inertia
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure

namespace Reimann.TameFrobeniusTower277

open NumberField TameInertia277

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem contracted_twice (P : Ideal (𝓞 L)) (E : FiniteGaloisIntermediateField K L) :
    (P.under (𝓞 E)).under (𝓞 K) = P.under (𝓞 K) := by
  rw [Ideal.under, Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]

theorem finite_contraction_nonzero (P : Ideal (𝓞 L)) (h : P.under (𝓞 K) ≠ 0)
    (E : FiniteGaloisIntermediateField K L) : P.under (𝓞 E) ≠ 0 := by
  intro he
  apply h
  rw [← contracted_twice P E, he]
  exact NumberField.RingOfIntegers.ker_algebraMap_eq_bot K E

theorem finite_residue [NumberField K] (P : Ideal (𝓞 L)) (h : P.under (𝓞 K) ≠ 0)
    (E : FiniteGaloisIntermediateField K L) : Finite (𝓞 E ⧸ P.under (𝓞 E)) := by
  letI := NumberField.of_module_finite K E
  exact Ring.HasFiniteQuotients.finiteQuotient (finite_contraction_nonzero P h E)

/-- Each integral element in the intermediate field lifts from its own ring of integers. -/
theorem integral_preimage (E : FiniteGaloisIntermediateField K L) (x : Integers L)
    (hx : x.val ∈ E.toIntermediateField) : ∃ y : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) y = x := by
  let a : E := ⟨x.val,hx⟩
  have ha : IsIntegral ℤ a := (isIntegral_algebraMap_iff (B := L)).mp
    (show IsIntegral ℤ (algebraMap E L a) from x.property)
  exact ⟨⟨a,ha⟩,rfl⟩

theorem finite_set_preimages [IsGalois K L] (S : Finset (Integers L)) :
    ∃ E : FiniteGaloisIntermediateField K L, ∀ x ∈ S, ∃ y : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) y = x := by
  classical
  let T : Finset L := S.image Subtype.val
  let E := FiniteGaloisIntermediateField.adjoin K (T : Set L)
  refine ⟨E,fun x hx => integral_preimage E x ?_⟩
  exact FiniteGaloisIntermediateField.subset_adjoin K (T : Set L) (Finset.mem_image_of_mem _ hx)

theorem restrict_act (E : FiniteGaloisIntermediateField K L) (g : L ≃ₐ[K] L) (y : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 L) (g.restrictNormal E • y) =
      act g (algebraMap (𝓞 E) (𝓞 L) y) := by
  apply Subtype.ext
  exact g.restrictNormal_commutes E (y : E)

end Reimann.TameFrobeniusTower277
