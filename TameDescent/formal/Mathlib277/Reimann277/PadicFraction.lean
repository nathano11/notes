import Reimann277.PadicInteger
import Reimann.TameFractionTarget277

namespace Reimann.TamePadicFraction277

open TameLimit277 TameFractionCompletion277 TameFractionTarget277
open TamePadicInteger277

local instance prime277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- Compose the integer realization with the inclusion of the valuation ring in its field. -/
noncomputable def integralMap : IntegralMap ℚ_[277] where
  app x := (realize x : ℚ_[277])
  zero := by rw [realize_ofInt, PadicInt.coe_intCast, Int.cast_zero]
  add x y := by rw [realize_add, PadicInt.coe_add]
  mul x y := by rw [realize_mul, PadicInt.coe_mul]
  injective h := realize_injective (PadicInt.ext h)

theorem integralMap_ofInt (a : Int) : integralMap.app (ofInt a) = (a : ℚ_[277]) := by
  change ((realize (ofInt a) : ℤ_[277]) : ℚ_[277]) = _
  rw [realize_ofInt, PadicInt.coe_intCast]

theorem integralMap_read (a : ℤ_[277]) : integralMap.app (read a) = (a : ℚ_[277]) := by
  change ((realize (read a) : ℤ_[277]) : ℚ_[277]) = _
  rw [realize_read]

theorem read_denominator_ne_zero (a : ℤ_[277]) (ha : a ≠ 0) :
    read a ≠ ofInt 0 := by
  intro h
  apply ha
  have e := congrArg TamePadicInteger277.realize h
  simpa only [realize_read, realize_ofInt, Int.cast_zero] using e

/-- The existing fraction-field instance supplies a genuine integral numerator and
a nonzero integral denominator for every standard p-adic number. -/
theorem standard_ratio (z : ℚ_[277]) :
    ∃ a b : ℤ_[277], b ≠ 0 ∧ (a : ℚ_[277]) / (b : ℚ_[277]) = z := by
  obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective ℤ_[277] z
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb,
    by simpa only [PadicInt.algebraMap_apply] using h⟩

theorem integralMap_spans (z : ℚ_[277]) :
    ∃ a b : Integer277, b ≠ ofInt 0 ∧ integralMap.app a / integralMap.app b = z := by
  obtain ⟨a, b, hb, h⟩ := standard_ratio z
  exact ⟨read a, read b, read_denominator_ne_zero b hb, by simpa only [integralMap_read] using h⟩

/-- The field comparison uses the existing quotient and its explicit cross-multiplication law. -/
noncomputable def realizeFraction : AdicRatios → ℚ_[277] :=
  evaluate integralMap

theorem realizeFraction_injective : Function.Injective realizeFraction :=
  fun x y h => evaluate_injective integralMap x y h

theorem realizeFraction_surjective : Function.Surjective realizeFraction :=
  evaluate_surjective integralMap integralMap_spans

noncomputable def fractionEquiv : AdicRatios ≃ ℚ_[277] :=
  Equiv.ofBijective realizeFraction ⟨realizeFraction_injective, realizeFraction_surjective⟩

theorem realize_add (x y : AdicRatios) :
    fractionEquiv (ratioAdd x y) = fractionEquiv x + fractionEquiv y :=
  evaluate_add integralMap x y

theorem realize_mul (x y : AdicRatios) :
    fractionEquiv (ratioMul x y) = fractionEquiv x * fractionEquiv y :=
  evaluate_mul integralMap x y

theorem realize_rational (r : ℚ) : fractionEquiv (rational r) = (r : ℚ_[277]) := by
  change evaluate integralMap (rational r) = _
  rw [evaluate_rational, integralMap_ofInt, integralMap_ofInt, Int.cast_natCast, Rat.cast_def]

scoped instance ratioAddition : Add AdicRatios := ⟨ratioAdd⟩
scoped instance ratioMultiplication : Mul AdicRatios := ⟨ratioMul⟩

/-- This equivalence uses the quotient's existing operations on numerator-denominator pairs. -/
noncomputable def fractionRingEquiv : AdicRatios ≃+* ℚ_[277] where
  toEquiv := fractionEquiv
  map_add' := realize_add
  map_mul' := realize_mul

theorem fractionRealization :
    (∀ x y, fractionEquiv (ratioAdd x y) = fractionEquiv x + fractionEquiv y) ∧
    (∀ x y, fractionEquiv (ratioMul x y) = fractionEquiv x * fractionEquiv y) ∧
    (∀ r : ℚ, fractionEquiv (rational r) = (r : ℚ_[277])) :=
  ⟨realize_add, realize_mul, realize_rational⟩

end Reimann.TamePadicFraction277

namespace Reimann.TameArithmetic277

open TameLimit277 TameFractionCompletion277 TameFractionTarget277
open scoped Reimann.TamePadicInteger277 Reimann.TamePadicFraction277

attribute [local instance] TamePadicFraction277.prime277

/-- Both standard 277-adic targets with their coefficient and reduction normalizations. -/
theorem padic_target_realization :
    ∃ (Z : Integer277 ≃+* ℤ_[277]) (Q : AdicRatios ≃+* ℚ_[277]),
      (∀ (x : Integer277) (n : Nat), PadicInt.toZModPow (n+1) (Z x) =
        (x.residue n : ZMod (277 ^ (n+1)))) ∧
      (∀ a : Int, Z (ofInt a) = (a : ℤ_[277])) ∧
      (∀ t : Pair Integer277 (ofInt 0), Q (Quot.mk (Cross mul) t) =
        (Z t.num : ℚ_[277]) / (Z t.den : ℚ_[277])) ∧
      (∀ x y, Q (ratioAdd x y) = Q x + Q y) ∧
      (∀ x y, Q (ratioMul x y) = Q x * Q y) ∧
      (∀ r : ℚ, Q (rational r) = (r : ℚ_[277])) :=
  ⟨TamePadicInteger277.integerRingEquiv, TamePadicFraction277.fractionRingEquiv,
   TamePadicInteger277.realize_reduction, TamePadicInteger277.realize_ofInt,
   fun _ => rfl, TamePadicFraction277.fractionRealization⟩

end Reimann.TameArithmetic277
