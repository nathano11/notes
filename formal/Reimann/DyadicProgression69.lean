import Reimann.DyadicHalfPrecision
import Reimann.DyadicDistribution69

/-! The depth-three projection of the conductor-69 distribution. We index
the two real cosets by the inverses of the powers of 5 modulo eight. -/

namespace Reimann.DyadicProgression69

open Reimann.DyadicZeroValues Reimann.DyadicStickelberger69 Reimann.DyadicHalfPrecision
open Reimann.SignedProjection

/-- The inverse exponent representatives for j=0 and j=1. -/
def representative (j : Fin 2) : Nat := 1+4*j.val

theorem inverse_exponent_orientation :
    ∀ j : Fin 2, (representative j) % 4 = 1 ∧
      (5^j.val * representative j) % 8 = 1 ∧
      (inGeneratorCoset (representative j) = (j.val == 1)) := by decide

/-- The progressions t+8k and 552−(t+8k) give the two halves of each
real coset exactly once. For positive representatives below 552, membership
in the odd coset of j is equivalent to one of the two explicit remainders. -/
theorem paired_roster (j : Fin 2) (a : Nat) (ha : 0 < a ∧ a < 552) :
    (a%2=1 ∧ inGeneratorCoset a = (j.val == 1)) ↔
    (∃ k : Fin 69, a=representative j+8*k.val) ∨
    (∃ k : Fin 69, a=552-(representative j+8*k.val)) := by
  obtain ⟨j,hj⟩ := j
  have casesJ : j=0 ∨ j=1 := by omega
  rcases casesJ with rfl|rfl <;> simp only [representative, inGeneratorCoset] <;>
    constructor
  all_goals
    first
    | rintro (⟨k,rfl⟩|⟨k,rfl⟩) <;> simp <;> omega
    | rintro ⟨ho,hgen⟩; simp at hgen
      first
      | by_cases h : a%8=1
        · exact Or.inl ⟨⟨a/8, by omega⟩, by dsimp; omega⟩
        · exact Or.inr ⟨⟨(551-a)/8, by omega⟩, by dsimp; omega⟩
      | by_cases h : a%8=5
        · exact Or.inl ⟨⟨a/8, by omega⟩, by dsimp; omega⟩
        · exact Or.inr ⟨⟨(547-a)/8, by omega⟩, by dsimp; omega⟩

theorem pair_parametrization_injective (j : Fin 2) (i k : Fin 69) (s t : Bool) :
    (if s then 552-(representative j+8*i.val) else representative j+8*i.val) =
    (if t then 552-(representative j+8*k.val) else representative j+8*k.val) →
    s=t ∧ i=k := by
  have hj := j.isLt
  have hi := i.isLt
  have hk := k.isLt
  unfold representative
  cases s <;> cases t <;> simp <;> intro h
  all_goals first | exact Fin.ext (by omega) | omega

/-- χ₆₉ on the residue progression indexed by the inverse power 5^j. -/
def fibre8 (j : Fin 2) (k : Nat) : Int :=
  let a := representative j+8*k
  Reimann.Dyadic.quadSymbol 3 a * Reimann.Dyadic.quadSymbol 23 a

theorem opposite_character_values :
    ∀ (j : Fin 2) (k : Fin 69), let a := representative j+8*k.val
      chi276 a = fibre8 j k.val ∧ chi276 (552-a) = -fibre8 j k.val := by decide

/-- Zeroth and first moments in the progression index k. -/
theorem progression_moments :
    (total (fibre8 0) 69,moment (fibre8 0) 69) = (0,-276) ∧
    (total (fibre8 1) 69,moment (fibre8 1) 69) = (0,0) := by decide

/-- The two Bernoulli numerators at a and 552−a are equal. Their sum
after clearing 2·552 is twice the contribution at the positive representative. -/
theorem pair_term (j : Fin 2) (k : Fin 69) :
    let a := representative j + 8*k.val
    chi276 a * (552-2*(a:Int)) + chi276 (552-a) * (552-2*((552-a:Nat):Int))
      = 2*((552-(a:Int))-(a:Int))*fibre8 j k.val := by
  have ht := opposite_character_values j k
  dsimp only at ht ⊢
  rw [ht.1,ht.2]
  have hk := k.isLt
  have hj := j.isLt
  have bound : representative j+8*k.val ≤ 552 := by unfold representative; omega
  rw [Int.natCast_sub bound]
  grind

theorem literal_numerator_from_moment (j : Fin 2) :
    signedNumerator (j.val==1) = -32 * moment (fibre8 j) 69 := by
  have h := progression_moments
  have hs := signed_row_exact
  have hj : j=0 ∨ j=1 := by
    have := j.isLt
    by_cases hj : j.val=0
    · exact Or.inl (Fin.ext hj)
    · exact Or.inr (Fin.ext (by change j.val=1; omega))
  rcases hj with rfl|rfl
  · change signedNumerator false = _
    rw [hs.1, (Prod.mk.inj h.1).2]
    decide
  · change signedNumerator true = _
    rw [hs.2, (Prod.mk.inj h.2).2]
    decide

theorem depth_three_fibre (j : Fin 2) :
    fibre8 j = DyadicDistribution69.fibre 3 (representative j) := rfl

/-- The normalized inverse-generator row in the integer distribution,
with its odd conductor denominator retained. -/
theorem depth_three_coefficients :
    (DyadicDistribution69.coefficient 3 (representative 0),
     DyadicDistribution69.coefficient 3 (representative 1)) = (4,0) := by
  unfold DyadicDistribution69.coefficient
  rw [← depth_three_fibre 0, ← depth_three_fibre 1,
      (Prod.mk.inj progression_moments.1).2, (Prod.mk.inj progression_moments.2).2]
  decide

/-- Comparing the two integer numerators clears all denominators before
reduction. The progression coefficient has normalization −1/69. -/
theorem conductor_normalization (j : Fin 2) :
    signedNumerator (j.val==1) =
      (4*552:Int) * DyadicDistribution69.coefficient 3 (representative j) := by
  have h := DyadicDistribution69.coefficient_exact 3 (representative j)
  rw [← depth_three_fibre j] at h
  rw [literal_numerator_from_moment]
  omega

/-- The depth-three distribution row gives both the half row modulo eight
and the ordinary (unhalved) Stickelberger row modulo sixteen. -/
theorem stickelberger_row_comparison :
    let x := DyadicDistribution69.coefficient 3 (representative 0)
    let y := DyadicDistribution69.coefficient 3 (representative 1)
    (BitVec.ofInt 3 x,BitVec.ofInt 3 y) = halfRow ∧
    (BitVec.ofInt 4 (2*x),BitVec.ofInt 4 (2*y)) = literalRow16 := by
  dsimp only
  obtain ⟨hx,hy⟩ := Prod.mk.inj depth_three_coefficients
  rw [hx,hy,half_row_exact,literal_row_exact]
  decide

end Reimann.DyadicProgression69
