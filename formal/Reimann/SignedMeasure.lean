import Reimann.Character2893

/-! Finite level 64 coefficients at conductor 11*263. We index the subgroup
1 mod 4 by inverse powers of 5. The signs in the weight-three evaluations
correspond to the untwisted character and its conductor-eight twist. -/
namespace Reimann.SignedMeasure

open Reimann.Dyadic

def conductor : Nat := 11 * 263

/-- The residue attached to the coefficient of X^j. -/
def representative (j : Nat) : Nat := 13^j % 64

/-- All representatives are 1 mod 4 and inverse to 5^j mod 64. -/
theorem inverse_orientation : ∀ j : Fin 16,
    representative j % 4 = 1 ∧ (5^(j : Nat) * representative j) % 64 = 1 := by
  decide

/-- Each residue 1 mod 4 modulo 64 appears among the sixteen coefficients. -/
theorem cover_one_mod_four : ∀ k : Fin 16,
    (List.range 16).any (fun j => representative j == 1 + 4*(k : Nat)) = true := by
  decide

/-- Normalized integral coefficients, in ascending inverse-generator index. -/
def row : List Int := [4, 5, 6, -30, 34, 11, 17, -17, -10, -9, -15, 9, -3, -5, -9, 20]

/-- Horner evaluation of a coefficient row with the constant coefficient first. -/
def evaluate (coeffs : List Int) (x : Int) : Int :=
  coeffs.foldr (fun c acc => c + x * acc) 0

theorem signed_points : (125 * 21 : Int) % 64 = 1 ∧
    (-21 : Int) % 64 = 43 ∧ (21 : Int)^16 % 64 = 1 ∧ (-21 : Int)^16 % 64 = 1 := by
  decide

/-- The positive point uses the third power of the representative, and the
conductor-eight twist supplies the sign at the negative point. -/
theorem weights_at_points : ∀ j : Fin 16,
    (21 : Int)^(j : Nat) % 64 = (representative j : Int)^3 % 64 ∧
    (-21 : Int)^(j : Nat) % 64 =
      (Character2893.oddTwist (representative j) * (representative j : Int)^3) % 64 := by
  decide

theorem signed_residues :
    evaluate row 21 % 64 = 32 ∧ evaluate row (-21) % 64 = 0 := by
  decide

/-- Agreement with the separately computed weight-three Bernoulli sums. -/
theorem equals_normalized_moments :
    evaluate row 21 % 64 =
      (Character2893.sums.weightThree / (240 * (Character2893.modulus : Int))) % 64 ∧
    evaluate row (-21) % 64 =
      (Character2893.sums.twistedThree / (240 * (Character2893.modulus : Int))) % 64 := by
  rw [signed_residues.1, signed_residues.2, Character2893.normalized_table,
    Character2893.modulus_value]
  decide

/-- Zeroth character moment and negative first moment in h for b=t+64h,
0 ≤ h < 2893. The quadratic character is the product for 11 and 263. -/
def classMoments (j : Nat) : Int × Int :=
  let t := representative j
  (List.range conductor).foldl (fun acc h =>
    let b := t + 64*h
    let chi := quadSymbol 11 b * quadSymbol 263 b
    (acc.1 + chi, acc.2 - (h : Int)*chi)) (0, 0)

/-- If the zeroth moment vanishes and the negative first moment in h is f*c,
then the negative first moment in b=t+64h is 64*f*c. -/
theorem lift_first_moment (ts : List (Int × Int)) (t : Int) :
    (ts.map (fun hw => -((t + 64*hw.1) * hw.2))).sum =
    -t * (ts.map Prod.snd).sum + 64 * (ts.map (fun hw => -(hw.1*hw.2))).sum := by
  induction ts with
  | nil => simp
  | cons hw xs ih =>
    simp only [List.map_cons, List.sum_cons] at *
    rw [ih]
    grind

set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
/-- Each component has zeroth moment zero and negative first moment in h
equal to 2893 times the displayed integral coefficient. This verifies exact
division by the conductor entry by entry. -/
theorem coefficient_formula :
    (List.range 16).map classMoments = row.map (fun c => ((0 : Int), (conductor : Int) * c)) := by
  decide

/-- Dividing the computed negative moments by the conductor recovers the row
used in both evaluations. -/
theorem normalized_coefficients :
    ((List.range 16).map classMoments).map (fun zn => zn.2 / (conductor : Int)) = row := by
  rw [coefficient_formula]
  decide

end Reimann.SignedMeasure
