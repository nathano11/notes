import Reimann277.FinitePlaces
import Reimann277.CyclotomicLocal
import Reimann277.GaloisTransport

namespace Reimann.TameCanonicalDecomposition277

open NumberField TameBiquadraticField277 TamePadicEmbeddings277 TameFinitePlaces277
open TameCyclotomicLocal277
open scoped NumberField

local instance finitePrime : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

abbrev CompletionField (v : Above Biquadratic) := v.val.maximalIdeal.adicCompletion Biquadratic

noncomputable def comparison (v : Above Biquadratic) : CompletionField v ≃+* ℚ_[277] :=
  Classical.choose (finite_completion v)

theorem comparison_on_field (v : Above Biquadratic) (x : Biquadratic) :
    comparison v (FinitePlace.embedding v.val.maximalIdeal x) =
      embedding (four_finite_places.symm v) x := (Classical.choose_spec (finite_completion v)).2 x

noncomputable def localClosure (v : Above Biquadratic) :
    AlgebraicClosure ℚ_[277] ≃+* AlgebraicClosure (CompletionField v) :=
  IsAlgClosure.equivOfEquiv _ _ (comparison v).symm

theorem localClosure_on_base (v : Above Biquadratic) (q : ℚ_[277]) :
    localClosure v (algebraMap _ _ q) = algebraMap _ _ ((comparison v).symm q) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ _

/-- Transport local automorphisms through the chosen comparison of algebraic closures. -/
noncomputable def toPadic (v : Above Biquadratic) : Field.absoluteGaloisGroup (CompletionField v) →ₜ* Local :=
  transport (comparison v).symm (localClosure v) (localClosure_on_base v)

theorem toPadic_surjective (v : Above Biquadratic) : Function.Surjective (toPadic v) :=
  transport_surjective _ _ _

/-- An embedding of the bottom algebraic closure in the completion's algebraic closure
over the canonical inclusion of the number field. -/
noncomputable def closureAt (v : Above Biquadratic) :
    AlgebraicClosure Biquadratic →+* AlgebraicClosure (CompletionField v) :=
  (localClosure v).toRingHom.comp (closureEmbedding (four_finite_places.symm v))

theorem closureAt_on_field (v : Above Biquadratic) (x : Biquadratic) :
    closureAt v (algebraMap _ _ x) =
      algebraMap _ _ (FinitePlace.embedding v.val.maximalIdeal x) := by
  change localClosure v (closureEmbedding _ (algebraMap _ _ x)) = _
  rw [closureEmbedding_on_base,localClosure_on_base,← comparison_on_field, RingEquiv.symm_apply_apply]

/-- Absolute restriction from the Galois group of the actual maximal-ideal adic completion. -/
noncomputable def absoluteRestriction (v : Above Biquadratic) :
    Field.absoluteGaloisGroup (CompletionField v) →ₜ* Global :=
  (restriction (four_finite_places.symm v)).comp (toPadic v)

theorem absoluteRestriction_commutes (v : Above Biquadratic)
    (g : Field.absoluteGaloisGroup (CompletionField v)) (z : AlgebraicClosure Biquadratic) :
    closureAt v (asAut (absoluteRestriction v g) z) = asAut g (closureAt v z) := by
  exact (congrArg (localClosure v)
    (restriction_commutes (four_finite_places.symm v) (toPadic v g) z)).trans
    (transport_commutes (comparison v).symm (localClosure v) (localClosure_on_base v) g
      (closureEmbedding (four_finite_places.symm v) z))

theorem four_absolute_decomposition_maps :
    ∃ idx : (Bool × Bool) ≃ Above Biquadratic, ∀ v : Above Biquadratic,
      ∃ (j : AlgebraicClosure Biquadratic →+* AlgebraicClosure (CompletionField v))
        (D : Field.absoluteGaloisGroup (CompletionField v) →ₜ* Global),
      (∀ x : Biquadratic, j (algebraMap _ _ x) =
          algebraMap _ _ (FinitePlace.embedding v.val.maximalIdeal x)) ∧
      (∀ g z, j (asAut (D g) z) = asAut g (j z)) ∧
      D.toMonoidHom.range = (restriction (idx.symm v)).toMonoidHom.range := by
  refine ⟨four_finite_places,fun v => ⟨closureAt v,absoluteRestriction v,
    closureAt_on_field v,absoluteRestriction_commutes v,?_⟩⟩
  ext g
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨toPadic v a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,rfl⟩ := toPadic_surjective v a
    exact ⟨b,rfl⟩

noncomputable def completionKernel (r n : Nat) (v : Above Biquadratic) :
    Subgroup (Field.absoluteGaloisGroup (CompletionField v)) :=
  (localKernel r n (four_finite_places.symm v)).comap (toPadic v).toMonoidHom

noncomputable def toLocalKernel (r n : Nat) (v : Above Biquadratic) :
    completionKernel r n v →ₜ* localKernel r n (four_finite_places.symm v) where
  toMonoidHom := ((toPadic v).toMonoidHom.comp (completionKernel r n v).subtype).codRestrict _
    (fun x => x.property)
  continuous_toFun := ((toPadic v).continuous.comp continuous_subtype_val).subtype_mk _

theorem toLocalKernel_surjective (r n : Nat) (v : Above Biquadratic) :
    Function.Surjective (toLocalKernel r n v) := by
  intro a
  obtain ⟨b,hb⟩ := toPadic_surjective v a.val
  have hk : b ∈ completionKernel r n v := by
    change toPadic v b ∈ localKernel r n _
    rw [hb]
    exact a.property
  exact ⟨⟨b,hk⟩,Subtype.ext hb⟩

noncomputable def conjugatedAt (r n : Nat) (v : Above Biquadratic) (a : Global) :
    completionKernel r n v →ₜ* globalKernel r n :=
  (conjugatedRestriction r n (four_finite_places.symm v) a).comp (toLocalKernel r n v)

/-- The strict quotient's existing relation ranges over precisely the images from
the canonical completions and every conjugate of each image. -/
theorem atPlaces_iff_canonical (r n : Nat) (x : globalKernel r n) :
    x ∈ atPlaces r n ↔ ∃ (v : Above Biquadratic) (a : Global) (y : completionKernel r n v),
      x = conjugatedAt r n v a y := by
  constructor
  · rintro ⟨s,a,y,hy⟩
    let v := four_finite_places s
    have hs : four_finite_places.symm v = s := four_finite_places.symm_apply_apply s
    obtain ⟨z,hz⟩ : ∃ z : localKernel r n (four_finite_places.symm v),
        x = conjugatedRestriction r n (four_finite_places.symm v) a z := by
      rw [hs]
      exact ⟨y,hy⟩
    obtain ⟨w,hw⟩ := toLocalKernel_surjective r n v z
    refine ⟨v,a,w,?_⟩
    change x = conjugatedRestriction r n (four_finite_places.symm v) a (toLocalKernel r n v w)
    rw [hw]
    exact hz
  · rintro ⟨v,a,y,hy⟩
    exact ⟨four_finite_places.symm v,a,toLocalKernel r n v y,hy⟩

end Reimann.TameCanonicalDecomposition277
