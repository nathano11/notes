import Reimann.SignedMeasure256
import Reimann.SignedPreparation

/-! Explicit mutually inverse multipliers for the conductor-2893 row at level
256, with coefficients modulo 64 and group relation X^64 = 1. -/
namespace Reimann.SignedFiniteFactor

open Reimann.SignedPreparation

/-- The ordinary polynomial quotient, in ascending powers of X. -/
def quotient : List Int :=
  [8,50,2,45,26,44,37,41,54,43,29,14,8,47,45,8,
   23,53,42,35,4,8,19,56,11,56,22,52,44,32,1,40,
   50,22,24,2,42,34,17,34,5,32,17,57,2,59,3,58,
   52,48,51,49,53,50,3,46,48,7,25,46,58,52]

/-- The inverse multiplier for cyclic multiplication at precision 64. -/
def inverse : List Int :=
  [25,62,34,15,45,39,8,43,49,35,46,20,25,18,26,42,
   53,57,31,52,26,28,15,6,37,8,36,19,29,30,52,40,
   14,46,38,57,45,45,32,0,22,23,5,27,10,0,63,7,
   40,18,18,41,14,19,35,62,6,30,25,19,2,5,15,43]

theorem quotient_augmentation : quotient.sum % 64 = 61 := by decide

/-- A bounded coefficient comparison plus the degree bounds covers all indices. -/
theorem coefficients_of_bounded {as bs : List Int} {bound : Nat}
    (ha : as.length ≤ bound) (hb : bs.length ≤ bound)
    (h : ∀ i : Fin bound, as[i.val]?.getD 0 % 64 = bs[i.val]?.getD 0 % 64)
    (n : Nat) : as[n]?.getD 0 % 64 = bs[n]?.getD 0 % 64 := by
  by_cases hn : n < bound
  · exact h ⟨n, hn⟩
  · have h₁ : as.length ≤ n := by omega
    have h₂ : bs.length ≤ n := by omega
    rw [List.getElem?_eq_none h₁, List.getElem?_eq_none h₂]

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
/-- Already in the ordinary polynomial ring modulo 64 the row equals UQ. -/
theorem ordinary_factor (n : Nat) :
    SignedMeasure256.row[n]?.getD 0 % 64 =
      (productPoly quotient (quadratic 40 18))[n]?.getD 0 % 64 := by
  apply coefficients_of_bounded (bound := 64) (by decide) (by decide) _ n
  decide +kernel

/-- The quotient-divisibility hypothesis used by the preparation calculation. -/
theorem row_cyclic_factor : CyclicFactor 40 18 SignedMeasure256.row := by
  refine ⟨quotient, [], ?_⟩
  intro n
  have right (p : List Int) : sumPoly p [] = p := by cases p <;> rfl
  simpa only [productPoly, right] using ordinary_factor n

/-- For a product of two polynomials of degree below 64, moving its high
coefficients into the low positions means adding this multiple of X^64-1. -/
def correction (p : List Int) : List Int := (p.drop 64).map (fun c => -c)

/-- An integer representative after using the relation X^64=1. -/
def wrapProduct (a b : List Int) : List Int :=
  let p := productPoly a b
  sumPoly p (productPoly (correction p) cycle)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
/-- Direct multiplication by the displayed inverse yields 1 in the cyclic ring. -/
theorem quotient_unit (n : Nat) :
    ([1] : List Int)[n]?.getD 0 % 64 = (wrapProduct inverse quotient)[n]?.getD 0 % 64 := by
  apply coefficients_of_bounded (bound := 128) (by decide) (by decide) _ n
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
/-- The inverse multiplier takes the full character row back to its monic quadratic. -/
theorem quadratic_from_row (n : Nat) :
    (quadratic 40 18)[n]?.getD 0 % 64 = (wrapProduct inverse SignedMeasure256.row)[n]?.getD 0 % 64 := by
  apply coefficients_of_bounded (bound := 128) (by decide) (by decide) _ n
  decide +kernel

/-- Mutual principal ideal membership in (ℤ/64)[X]/(X^64-1), recorded as integer
polynomial witnesses in exactly the same coefficient convention as CyclicFactor. -/
theorem mutual_divisibility :
    CyclicFactor 40 18 SignedMeasure256.row ∧
    ∃ u v : List Int, ∀ n : Nat, (quadratic 40 18)[n]?.getD 0 % 64 =
      (sumPoly (productPoly u SignedMeasure256.row) (productPoly v cycle))[n]?.getD 0 % 64 :=
  ⟨row_cyclic_factor, inverse, correction (productPoly inverse SignedMeasure256.row),
    quadratic_from_row⟩

end Reimann.SignedFiniteFactor
