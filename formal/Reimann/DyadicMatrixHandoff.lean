import Reimann.DyadicMatrixImage
import Reimann.DyadicBaseFactors
import Reimann.DyadicPositiveFactors

/-! Additive invariant factors of the companion quotient for the two
weight-one samples of (3,23), uniformly from the base layer onwards. -/
namespace Reimann.DyadicMatrixHandoff

open Reimann.DyadicLattice Reimann.DyadicOrder

abbrev Factors (a : Nat) := BitVec a × BitVec (a+1)

/-- The coefficient of 2b is the surviving bit at the bottom. Positive
layers reduce the coefficients of 2b and c to a and a+1 bits. -/
def coordinates : (a : Nat) → (Scalar × Scalar) → Factors a
  | 0 => DyadicBaseFactors.bottomFactors
  | n+1 => DyadicQuotient.residuePair n

theorem coordinates_add (a : Nat) (x y : Scalar × Scalar) :
    coordinates a (add x.1 y.1, add x.2 y.2) =
      ((coordinates a x).1 + (coordinates a y).1, (coordinates a x).2 + (coordinates a y).2) := by
  cases a with
  | zero => exact DyadicBaseFactors.bottomFactors_add x y
  | succ n => exact DyadicQuotient.residuePair_add n x y

theorem coset_iff_coordinates {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r a : Nat) (x y : Scalar × Scalar) :
    latticeCoset c0 c1 r a x y ↔ coordinates a x = coordinates a y := by
  cases a with
  | zero =>
    exact DyadicBaseFactors.bottomCoset_iff_factors _ _ _ (moment_coefficient_bits H).1
      (moment_coefficient_bits H).2 (inverse_weight_mod_four r) x y
  | succ n => exact DyadicPositiveFactors.related_iff H r n x y

/-- An additive classification with explicit inverses. The use of arbitrary
lattice representatives in the final clause pins down the quotient group law. -/
theorem lattice_invariant_factors {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r a : Nat) :
    ∃ read : Quot (latticeCoset c0 c1 r a) → Factors a,
    ∃ write : Factors a → Quot (latticeCoset c0 c1 r a),
    ∃ plus : Quot (latticeCoset c0 c1 r a) → Quot (latticeCoset c0 c1 r a) →
        Quot (latticeCoset c0 c1 r a),
      Function.LeftInverse write read ∧ Function.RightInverse write read ∧
      (∀ x, read (Quot.mk _ x) = coordinates a x) ∧
      (∀ x y, read (plus x y) = ((read x).1 + (read y).1, (read x).2 + (read y).2)) ∧
      (∀ x y : Scalar × Scalar, plus (Quot.mk _ x) (Quot.mk _ y) =
        Quot.mk _ (add x.1 y.1, add x.2 y.2)) := by
  cases a with
  | zero =>
    obtain ⟨h0,h1⟩ := moment_coefficient_bits H
    have hs := inverse_weight_mod_four r
    exact ⟨DyadicBaseFactors.bottomEncode _ _ _ h0 h1 hs,
      DyadicBaseFactors.bottomDecode _ _ _, DyadicBaseFactors.bottomAdd _ _ _ h0 h1 hs,
      DyadicBaseFactors.bottomDecode_encode _ _ _ h0 h1 hs,
      DyadicBaseFactors.bottomEncode_decode _ _ _ h0 h1 hs,
      DyadicBaseFactors.bottomEncode_mk _ _ _ h0 h1 hs,
      DyadicBaseFactors.bottomEncode_add _ _ _ h0 h1 hs,
      DyadicBaseFactors.bottomAdd_mk _ _ _ h0 h1 hs⟩
  | succ n =>
    obtain ⟨left, right, preserves⟩ := DyadicPositiveFactors.positive_invariant_factors H r n
    exact ⟨DyadicPositiveFactors.encode H r n, DyadicPositiveFactors.decode _ _ r n,
      DyadicPositiveFactors.quotientAdd H r n, left, right,
      DyadicPositiveFactors.encode_mk H r n, preserves, DyadicPositiveFactors.quotientAdd_mk H r n⟩

end Reimann.DyadicMatrixHandoff
