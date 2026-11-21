import Mathlib.NumberTheory.Padics.RingHoms
import Reimann277.FiniteAbsolute

namespace Reimann.TameFiniteResidue277

local instance prime277 : Fact (Nat.Prime 277) := ⟨by decide +kernel⟩

variable {K A : Type*} [Field K] [Algebra ℚ K] [CommRing A] [Algebra A K]
variable (f : K →ₐ[ℚ] ℚ_[277]) (hb : ∀ a : A, ‖f (algebraMap A K a)‖ ≤ 1)

/-- The open unit ball of the embedding on a bounded integral model. -/
def embeddingIdeal : Ideal A where
  carrier := {x | ‖f (algebraMap A K x)‖ < 1}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change ‖f (algebraMap A K (x + y))‖ < 1
    rw [map_add, map_add]
    exact (Padic.nonarchimedean _ _).trans_lt (max_lt hx hy)
  smul_mem' a x hx := by
    change ‖f (algebraMap A K (a * x))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hb a)).trans_lt hx

theorem mem_embeddingIdeal_iff (x : A) :
    x ∈ embeddingIdeal f hb ↔ ‖f (algebraMap A K x)‖ < 1 := Iff.rfl

theorem embeddingIdeal_prime : (embeddingIdeal f hb).IsPrime where
  ne_top' := by
    intro h
    have h1 : (1 : A) ∈ embeddingIdeal f hb := h ▸ Submodule.mem_top
    simp [mem_embeddingIdeal_iff] at h1
  mem_or_mem' {x y} h := by
    by_contra! hn
    have hx : 1 ≤ ‖f (algebraMap A K x)‖ := le_of_not_gt hn.1
    have hy : 1 ≤ ‖f (algebraMap A K y)‖ := le_of_not_gt hn.2
    change ‖f (algebraMap A K (x * y))‖ < 1 at h
    rw [map_mul, map_mul, norm_mul] at h
    exact (not_lt_of_ge (one_le_mul_of_one_le_of_one_le hx hy)) h

theorem prime_mem_embeddingIdeal : (277 : A) ∈ embeddingIdeal f hb := by
  rw [mem_embeddingIdeal_iff, map_ofNat, map_ofNat, TameFiniteAbsolute277.norm_prime]
  norm_num

noncomputable def integralHom : A →+* ℤ_[277] :=
  (f.toRingHom.comp (algebraMap A K)).codRestrict (PadicInt.subring 277) hb

noncomputable def residueHom : A →+* ZMod 277 :=
  PadicInt.toZMod.comp (integralHom f hb)

theorem embeddingIdeal_eq_ker : embeddingIdeal f hb = RingHom.ker (residueHom f hb) := by
  ext x
  change ‖f (algebraMap A K x)‖ < 1 ↔
    integralHom f hb x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[277] →+* ZMod 277)
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  exact PadicInt.norm_lt_one_iff_dvd (integralHom f hb x)

theorem residue_surjective : Function.Surjective (residueHom f hb) :=
  ZMod.ringHom_surjective (residueHom f hb)

noncomputable def residue_equiv : (A ⧸ embeddingIdeal f hb) ≃+* ZMod 277 := by
  rw [embeddingIdeal_eq_ker]
  exact RingHom.quotientKerEquivOfSurjective (residue_surjective f hb)

theorem residue_card : Nat.card (A ⧸ embeddingIdeal f hb) = 277 := by
  rw [Nat.card_congr (residue_equiv f hb).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end Reimann.TameFiniteResidue277
