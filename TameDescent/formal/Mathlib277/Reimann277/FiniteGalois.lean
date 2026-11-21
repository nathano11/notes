import Reimann277.FinitePlaces
import Reimann277.BottomGalois

namespace Reimann.TameFiniteGalois277

open NumberField TameBiquadraticField277 TamePadicEmbeddings277 TameFinitePlaces277
open TameBottomGalois277
open scoped NumberField

local instance prime277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- The stabilizer of the normalized absolute value at the actual finite place. -/
def decomposition (v : Above Biquadratic) : Subgroup Galois where
  carrier := {g | ∀ x : Biquadratic, v.val (g x) = v.val x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh x
    change v.val (g (h x)) = v.val x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (g.symm x)
    rw [g.apply_symm_apply] at h
    exact h.symm

theorem norm_stabilizer_on_order (v : Above Biquadratic) (g : Galois)
    (hg : g ∈ decomposition v) :
    MapsPrime g (four_finite_places.symm v) (four_finite_places.symm v) := by
  obtain ⟨s,rfl⟩ := four_finite_places.surjective v
  rw [Equiv.symm_apply_apply]
  intro a b h
  have e := hg (integralPoint a)
  rw [h,signed_absolute_value,signed_absolute_value] at e
  rw [← norm_lt_one_iff_prime,← norm_lt_one_iff_prime]
  change ‖embedding s (integralPoint a)‖ < 1 ↔ ‖embedding s (integralPoint b)‖ < 1
  rw [e]

theorem mem_decomposition_iff (v : Above Biquadratic) (g : Galois) :
    g ∈ decomposition v ↔ g = AlgEquiv.refl := by
  constructor
  · intro h
    exact (stabilizer_eq_identity g _).mp (norm_stabilizer_on_order v g h)
  · rintro rfl
    exact (decomposition v).one_mem

theorem decomposition_eq_bot (v : Above Biquadratic) : decomposition v = ⊥ := by
  ext g
  exact (mem_decomposition_iff v g).trans Subgroup.mem_bot.symm

/-- The residue field of the actual ring of integers at v has 277 elements. -/
theorem residue_power_fixed (v : Above Biquadratic) :
    ∀ a : (𝓞 Biquadratic) ⧸ v.val.maximalIdeal.asIdeal, a ^ 277 = a := by
  obtain ⟨s,rfl⟩ := four_finite_places.surjective v
  change ∀ a : (𝓞 Biquadratic) ⧸ (FinitePlace.mk (embeddingPrime (embedding s))).maximalIdeal.asIdeal,
    a ^ 277 = a
  rw [FinitePlace.maximalIdeal_mk]
  intro a
  let e := residue_equiv (embedding s)
  apply e.injective
  rw [map_pow]
  exact TameDecomposition277.residue_frobenius (e a)

/-- A bottom Frobenius fixes the finite place and induces the arithmetic power map
on the full residue field of the maximal order. -/
def IsFrobenius (v : Above Biquadratic) (g : Galois) : Prop :=
  g ∈ decomposition v ∧ ∀ a b : 𝓞 Biquadratic, g (a : Biquadratic) = b →
    Ideal.Quotient.mk v.val.maximalIdeal.asIdeal b =
      (Ideal.Quotient.mk v.val.maximalIdeal.asIdeal a) ^ 277

theorem frobenius_iff_identity (v : Above Biquadratic) (g : Galois) :
    IsFrobenius v g ↔ g = AlgEquiv.refl := by
  constructor
  · exact fun h => (mem_decomposition_iff v g).mp h.1
  · rintro rfl
    refine ⟨(decomposition v).one_mem, ?_⟩
    intro a b he
    have h : a=b := Subtype.ext he
    rw [h,residue_power_fixed]

theorem unique_bottom_artin (v : Above Biquadratic) :
    IsFrobenius v (bottomArtin (four_finite_places.symm v)) ∧
      ∀ g : Galois, IsFrobenius v g → g = bottomArtin (four_finite_places.symm v) := by
  rw [bottom_artin_identity]
  exact ⟨(frobenius_iff_identity v _).mpr rfl, fun g => (frobenius_iff_identity v g).mp⟩

end Reimann.TameFiniteGalois277
