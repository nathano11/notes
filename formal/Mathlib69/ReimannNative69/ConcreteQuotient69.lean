import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharP.Basic
import Reimann.CircularOrder69
import Reimann.CircularNormIdentification69

/-! A characteristic-zero field containing a distinguished primitive 69th root.
The field is a residue field of the rational polynomial ring, and the generator
is the class of X. The norm uses the project's determinant of multiplication. -/
namespace Reimann.ConcreteQuotient69

open CircularPolynomial69 CircularFieldNorm69 CircularFieldReduction69
open Polynomial

local instance rationalGrindRing : Lean.Grind.CommRing ℚ := CommRing.toGrindCommRing ℚ

theorem map_horner {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (u : A) (cs : List ℤ) : f (CircularPolynomial69.eval u cs) = CircularPolynomial69.eval (f u) cs := by
  induction cs with
  | nil => exact f.map_zero
  | cons c cs ih => simp only [CircularPolynomial69.eval, map_add, map_intCast, map_mul, ih]

noncomputable def definingPolynomial : ℚ[X] := CircularPolynomial69.eval X phi

theorem evaluate_defining (a : ℚ) :
    Polynomial.evalRingHom a definingPolynomial = CircularPolynomial69.eval a phi := by
  unfold definingPolynomial
  rw [map_horner]
  simp

theorem defining_values_differ :
    CircularPolynomial69.eval (0 : ℚ) phi ≠ CircularPolynomial69.eval (2 : ℚ) phi := by
  decide +kernel

theorem defining_nonunit : ¬ IsUnit definingPolynomial := by
  intro h
  obtain ⟨q, _, hq⟩ := Polynomial.isUnit_iff.mp h
  apply defining_values_differ
  calc
    CircularPolynomial69.eval (0 : ℚ) phi = Polynomial.evalRingHom 0 definingPolynomial :=
      (evaluate_defining 0).symm
    _ = q := by rw [← hq]; simp
    _ = Polynomial.evalRingHom 2 definingPolynomial := by rw [← hq]; simp
    _ = CircularPolynomial69.eval (2 : ℚ) phi := evaluate_defining 2

theorem defining_ideal_proper : Ideal.span {definingPolynomial} ≠ ⊤ :=
  fun h => defining_nonunit (Ideal.span_singleton_eq_top.mp h)

theorem maximal_ideal_exists :
    ∃ M : Ideal ℚ[X], M.IsMaximal ∧ definingPolynomial ∈ M := by
  obtain ⟨M, hm, hle⟩ := Ideal.exists_le_maximal _ defining_ideal_proper
  exact ⟨M, hm, hle (Ideal.subset_span (Set.mem_singleton _))⟩

noncomputable def chosenIdeal : Ideal ℚ[X] := maximal_ideal_exists.choose

theorem chosen_maximal : chosenIdeal.IsMaximal := maximal_ideal_exists.choose_spec.1

theorem defining_mem : definingPolynomial ∈ chosenIdeal := maximal_ideal_exists.choose_spec.2

abbrev K := ℚ[X] ⧸ chosenIdeal

noncomputable abbrev residueField : Field K := by
  letI : chosenIdeal.IsMaximal := chosen_maximal
  exact Ideal.Quotient.field chosenIdeal

attribute [instance] residueField

noncomputable def quotientMap : ℚ[X] →+* K := Ideal.Quotient.mk chosenIdeal

noncomputable def rationalEmbedding : ℚ →+* K := quotientMap.comp Polynomial.C

theorem rational_embedding_injective : Function.Injective rationalEmbedding := by
  intro a b heq
  by_contra hn
  have hh : rationalEmbedding ((a - b) * (a - b)⁻¹) = 0 := by
    rw [map_mul, map_sub, heq, sub_self, zero_mul]
  rw [mul_inv_cancel₀ (sub_ne_zero.mpr hn), map_one] at hh
  exact one_ne_zero hh

theorem characteristicZero : CharZero K where
  cast_injective := by
    intro a b h
    apply CharZero.cast_injective (R := ℚ)
    apply rational_embedding_injective
    simpa only [map_natCast] using h

attribute [instance] characteristicZero

noncomputable def ζ : K := quotientMap X

theorem rationals_agree (a : ℚ) :
    rationalEmbedding a = Lean.Grind.Field.NormNum.ofRat a := by
  calc
    rationalEmbedding a = rationalEmbedding ((a.num : ℚ) / (a.den : ℚ)) :=
      congrArg rationalEmbedding a.num_div_den.symm
    _ = _ := by rw [map_div₀, map_intCast, map_natCast]

theorem monomial_generated (n : ℕ) (a : ℚ) :
    CircularPolynomialField69.Generated ζ (quotientMap (Polynomial.monomial n a)) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
  change CircularPolynomialField69.Generated ζ (rationalEmbedding a * ζ ^ n)
  rw [rationals_agree]
  simpa only [mul_one] using
    CircularPolynomialField69.generated_shift ζ 1 n a (CircularPolynomialField69.generated_one ζ)

theorem polynomial_generated (p : ℚ[X]) :
    CircularPolynomialField69.Generated ζ (quotientMap p) := by
  refine Polynomial.induction_on' p ?_ monomial_generated
  intro p q hp hq
  rw [map_add]
  exact CircularPolynomialField69.generated_add ζ _ _ hp hq

theorem all_generated (a : K) : CircularPolynomialField69.Generated ζ a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact polynomial_generated p

theorem generator_vanishes : CircularPolynomial69.eval ζ phi = 0 := by
  change CircularPolynomial69.eval (quotientMap X) phi = 0
  exact (map_horner quotientMap X phi).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr defining_mem)

theorem generator_orders : ζ ^ 69 = 1 ∧ ζ ^ 23 ≠ 1 ∧ ζ ^ 3 ≠ 1 :=
  CircularOrder69.primitive_of_phi ζ generator_vanishes

theorem generator_pow_69 : ζ ^ 69 = 1 := generator_orders.1

theorem generator_pow_23_ne_one : ζ ^ 23 ≠ 1 := generator_orders.2.1

theorem generator_pow_three_ne_one : ζ ^ 3 ≠ 1 := generator_orders.2.2

theorem generator_primitive : Primitive69 ζ :=
  ⟨generator_pow_69, generator_pow_23_ne_one, generator_pow_three_ne_one⟩

theorem positive_product_eq_relative_norm :
    signedProduct ζ 1 = CircularRationalPeriod69.evaluate (CircularFactor69.periodTheta ζ)
      (relativeNorm ζ (1 - ζ) generator_pow_69 generator_pow_23_ne_one generator_pow_three_ne_one
        (one_sub_mem ζ)) :=
  CircularNorm69.positive_product_eq_relative_norm ζ generator_pow_69
    generator_pow_23_ne_one generator_pow_three_ne_one

theorem relative_norm_value :
    relativeNorm ζ (1 - ζ) generator_pow_69 generator_pow_23_ne_one generator_pow_three_ne_one
      (one_sub_mem ζ) = 11 + 3 * CircularRational69.theta :=
  CircularFieldNorm69.norm_one_sub ζ generator_pow_69 generator_pow_23_ne_one generator_pow_three_ne_one

theorem labelled_period : reduction generator_primitive (period ζ) = 92746 :=
  CircularFieldReduction69.reduction_period generator_primitive

theorem positive_coordinate (a : Fin 277) :
    (49063 : Fin 114679)^a.val = reduction generator_primitive (orderPow (signedUnit ζ 1) 414) ↔
      a = 159 :=
  CircularFieldReduction69.positive_log_coordinate generator_primitive a

end Reimann.ConcreteQuotient69
