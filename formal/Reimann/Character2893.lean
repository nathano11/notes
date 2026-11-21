import Reimann.Dyadic

/-! Finite Euler-criterion sums for the weight-one and weight-three table in §8 of
Dyadic_Window_Orders.md. The common modulus is 8·11·263. Summing odd representatives
already removes the Euler factor at 2. Analytic interpolation is a separate obligation. -/

namespace Reimann.Character2893

open Reimann.Dyadic

def modulus : Nat := 8 * 11 * 263

theorem modulus_value : modulus = 23144 := by decide

def oddTwist (b : Nat) : Int := if b%8 = 1 ∨ b%8 = 7 then 1 else -1

/-- 6m² B₂(b/m). -/
def scaledB2 (m b : Int) : Int := 6*b^2-6*m*b+m^2

/-- 30m⁴ B₄(b/m). -/
def scaledB4 (m b : Int) : Int := 30*b^4-60*m*b^3+30*m^2*b^2-m^4

structure WeightedSums where
  weightOne : Int
  twistedOne : Int
  weightThree : Int
  twistedThree : Int
  deriving DecidableEq

/-- Add one odd representative, with both Euler-criterion characters and both weights. -/
def addOdd (acc : WeightedSums) (b : Nat) : WeightedSums :=
  let χ := quadSymbol 11 b * quadSymbol 263 b
  let w₁ := -χ * scaledB2 modulus b
  let w₃ := -χ * scaledB4 modulus b
  let τ := oddTwist b
  ⟨acc.weightOne+w₁, acc.twistedOne+τ*w₁,
   acc.weightThree+w₃, acc.twistedThree+τ*w₃⟩

/-- The four odd representatives in the block [8i,8i+7]. -/
def residueBlock (acc : WeightedSums) (i : Nat) : WeightedSums :=
  let b := 8*i+1
  addOdd (addOdd (addOdd (addOdd acc b) (b+2)) (b+4)) (b+6)

/-- Enumerate each odd residue modulo 8·11·263 once. -/
def sums : WeightedSums :=
  (List.range (modulus/8)).foldl residueBlock ⟨0,0,0,0⟩

/-- Odd parts after clearing the powers 2⁴, 2⁴, 2⁵ and 2⁷
from the proposed normalized entries. -/
theorem valuation_factors :
    exactV (-10416) 4 ∧ exactV (-85584) 4 ∧
    exactV 42946927776 5 ∧ exactV 7186575033984 7 := by
  refine ⟨⟨-326, ?_⟩, ⟨-2675, ?_⟩, ⟨671045746, ?_⟩, ⟨28072558726, ?_⟩⟩ <;> decide

set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
/-- Exact signed sums, including the common Bernoulli denominators
24m for weight one and 240m for weight three. -/
theorem normalized_table :
    sums = ⟨24*(modulus : Int)*(-10416), 24*(modulus : Int)*(-85584),
            240*(modulus : Int)*42946927776, 240*(modulus : Int)*7186575033984⟩ := by
  decide

end Reimann.Character2893
