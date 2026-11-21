import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

namespace Reimann.TameGenerator277

open Polynomial
open scoped Polynomial

local instance fact277 : Fact (Nat.Prime 277) := ⟨by decide +kernel⟩

/-- Shifting by one makes the constant coefficient exactly 277. -/
noncomputable def shifted (R : Type*) [CommRing R] : R[X] :=
  (cyclotomic 277 R).comp (X+1)

theorem map_shifted {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (shifted R).map f = shifted S := by
  simp [shifted, Polynomial.map_comp, Polynomial.map_cyclotomic]

theorem shifted_monic (R : Type*) [CommRing R] [Nontrivial R] : (shifted R).Monic := by
  simpa [shifted] using (cyclotomic.monic 277 R).comp_X_add_C 1

theorem shifted_degree (R : Type*) [CommRing R] [IsDomain R] :
    (shifted R).natDegree = 276 := by
  unfold shifted
  rw [natDegree_comp, show (X + 1 : R[X]) = X + C 1 by simp, natDegree_X_add_C,
    natDegree_cyclotomic, Nat.totient_prime (Fact.out : Nat.Prime 277), mul_one]

theorem shifted_constant (R : Type*) [CommRing R] : (shifted R).coeff 0 = (277 : R) := by
  rw [shifted, coeff_zero_eq_eval_zero, eval_comp]
  simp

/-- Every coefficient below the leading one is divisible by 277 already over ℤ. -/
theorem integer_lower_coeffs :
    (shifted ℤ).IsWeaklyEisensteinAt (Ideal.span {(277 : ℤ)}) := by
  simpa only [shifted, Ideal.submodule_span_eq] using
    (cyclotomic_comp_X_add_one_isEisensteinAt 277).isWeaklyEisensteinAt

theorem padic_lower_coeffs :
    (shifted ℤ_[277]).IsWeaklyEisensteinAt (Ideal.span {(277 : ℤ_[277])}) := by
  have h := integer_lower_coeffs.map (Int.castRingHom ℤ_[277])
  rw [map_shifted, Ideal.map_span, Set.image_singleton] at h
  simpa using h

theorem padic_prime_span : (Ideal.span {(277 : ℤ_[277])}).IsPrime :=
  (Ideal.span_singleton_prime (PadicInt.prime_p (p := 277)).ne_zero).2 PadicInt.prime_p

theorem prime_square_not_dvd {A : Type*} [CommMonoidWithZero A] [IsCancelMulZero A]
    {p : A} (hp : Prime p) : ¬ p ^ 2 ∣ p := by
  have hd : ¬ p ^ 2 ∣ p ^ 1 := by
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    decide
  simpa only [pow_one] using hd

theorem uniformizer_not_in_square :
    (277 : ℤ_[277]) ∉ (Ideal.span {(277 : ℤ_[277])}) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact prime_square_not_dvd PadicInt.prime_p

theorem shifted_eisenstein :
    (shifted ℤ_[277]).IsEisensteinAt (Ideal.span {(277 : ℤ_[277])}) := by
  apply (shifted_monic _).isEisensteinAt_of_mem_of_notMem padic_prime_span.ne_top
    (fun hn => padic_lower_coeffs.mem hn)
  rw [shifted_constant]
  exact uniformizer_not_in_square

theorem shifted_irreducible_integer : Irreducible (shifted ℤ_[277]) :=
  shifted_eisenstein.irreducible padic_prime_span (shifted_monic _).isPrimitive
    (by rw [shifted_degree]; decide)

theorem shifted_irreducible_field : Irreducible (shifted ℚ_[277]) := by
  have h := ((shifted_monic ℤ_[277]).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ_[277])).mp shifted_irreducible_integer
  rwa [map_shifted] at h

theorem cyclotomic_irreducible : Irreducible (cyclotomic 277 ℚ_[277]) := by
  apply (MulEquiv.irreducible_iff (Polynomial.algEquivAevalXAddC (1 : ℚ_[277]))).mp
  simpa [shifted, Polynomial.algEquivAevalXAddC_apply, ← Polynomial.comp_eq_aeval] using
    shifted_irreducible_field

abbrev Closure := AlgebraicClosure ℚ_[277]

theorem exists_primitive : ∃ ζ : Closure, IsPrimitiveRoot ζ 277 := by
  obtain ⟨ζ,hζ⟩ := IsAlgClosed.exists_root (cyclotomic 277 Closure)
    (ne_of_gt (degree_cyclotomic_pos 277 Closure (by decide)))
  exact ⟨ζ, (isRoot_cyclotomic_iff_charZero (by decide : 0 < 277)).mp hζ⟩

theorem fifth_primitive {ζ : Closure} (hζ : IsPrimitiveRoot ζ 277) :
    IsPrimitiveRoot (ζ ^ 5) 277 :=
  hζ.pow_of_coprime 5 (by decide)

theorem fifth_minpoly {ζ : Closure} (hζ : IsPrimitiveRoot ζ 277) :
    minpoly ℚ_[277] (ζ ^ 5) = minpoly ℚ_[277] ζ :=
  ((fifth_primitive hζ).minpoly_eq_cyclotomic_of_irreducible cyclotomic_irreducible).symm.trans
    (hζ.minpoly_eq_cyclotomic_of_irreducible cyclotomic_irreducible)

theorem fifth_conjugate {ζ : Closure} (hζ : IsPrimitiveRoot ζ 277) :
    ∃ g : Closure ≃ₐ[ℚ_[277]] Closure, g ζ = ζ ^ 5 := by
  obtain ⟨g, hg⟩ :=
    (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[277]) (E := Closure)).mp (fifth_minpoly hζ)
  exact ⟨g, hg⟩

/-- The same absolute automorphism raises every 277th root of unity to its fifth power. -/
theorem exists_local_five :
    ∃ g : Field.absoluteGaloisGroup ℚ_[277], ∀ z : Closure, z^277 = 1 →
      (show Closure ≃ₐ[ℚ_[277]] Closure from g) z = z^5 := by
  obtain ⟨ζ, hζ⟩ := exists_primitive
  obtain ⟨g, hg⟩ := fifth_conjugate hζ
  refine ⟨g, ?_⟩
  intro z hz
  obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [← hi, map_pow, hg, pow_right_comm]

end Reimann.TameGenerator277
