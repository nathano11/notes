import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.RingTheory.SimpleRing.Basic
import ReimannNative69.CommonRealPart69
import ReimannNative69.CommonConjugation69

/-! Complex conjugation on an embedded cyclotomic field acts by inversion
on its generating root of unity. Rational polynomial generation determines
the action on every other element. -/

namespace Reimann.ComplexCompatibility69

open Polynomial
open scoped ComplexConjugate

theorem normSq_root {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    Complex.normSq z = 1 := by
  apply (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg z) hn).mp
  rw [← map_pow, hz, map_one]

theorem conjugate_root {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    conj z = z⁻¹ := by
  rw [Complex.inv_def, normSq_root hn hz, inv_one, Complex.ofReal_one, mul_one]

theorem conjugate_generator {F : Type} [Field F] (ι : F →+* ℂ)
    (g : F →+* F) {x : F} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1)
    (hrev : g x = x⁻¹) : ι (g x) = conj (ι x) := by
  have hpow : (ι x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  rw [hrev, map_inv₀, conjugate_root hn hpow]

theorem polynomial_agreement {F : Type} [Field F] (ι : F →+* ℂ) (g : F →+* F)
    (f : ℚ[X] →+* F) (hX : ι (g (f X)) = conj (ι (f X))) :
    (ι.comp g).comp f = ((starRingEnd ℂ).comp ι).comp f := by
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · exact hX

theorem embedding_conjugation {F : Type} [Field F] (ι : F →+* ℂ)
    (g : F →+* F) (f : ℚ[X] →+* F) (gen : Function.Surjective f)
    {n : ℕ} (hn : n ≠ 0) (hx : (f X) ^ n = 1) (hrev : g (f X) = (f X)⁻¹) (y : F) :
    ι (g y) = conj (ι y) := by
  obtain ⟨p, rfl⟩ := gen y
  exact RingHom.congr_fun (polynomial_agreement ι g f (conjugate_generator ι g hn hx hrev)) p

theorem real_iff_fixed {F : Type} [Field F] (ι : F →+* ℂ)
    (g : F →+* F) (h : ∀ y, ι (g y) = conj (ι y)) (y : F) :
    g y = y ↔ ∃ r : ℝ, ι y = r := by
  rw [← Complex.conj_eq_iff_real, ← h, ι.injective.eq_iff]

section Concrete

open CommonAmbient69 CommonConjugation69 CommonRealPart69

noncomputable def conductorConjugation : K →+* K :=
  reverseHom root_pow_19113 (by decide) rational_generation

theorem conjugation_on_embedding (ι : K →+* ℂ) (y : K) :
    ι (conjugation.app y) = conj (ι y) := by
  apply embedding_conjugation ι conductorConjugation rationalEvaluation rational_polynomial_surjective
    (n := 19113) (by decide)
  · rw [evaluation_X]
    exact root_pow_19113
  · rw [evaluation_X]
    exact CommonConjugation69.conjugate_root

theorem real_subfield_on_embedding (ι : K →+* ℂ) (u v y : K) :
    y ∈ realCompositum conjugation u v ↔
      y ∈ compositum u v ∧ ∃ r : ℝ, ι y = r := by
  change (y ∈ compositum u v ∧ conjugation.app y = y) ↔ _
  exact and_congr_right' (real_iff_fixed ι conductorConjugation (conjugation_on_embedding ι) y)

end Concrete

end Reimann.ComplexCompatibility69
