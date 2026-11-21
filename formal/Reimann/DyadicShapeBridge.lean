import Reimann.DyadicStrictDualAdapter

/-! The sample hypothesis of the matrix chain is a shape, not a field.

`WeightOneSamples c0 c1` was introduced for `(3,23)` through its two weight-one
moments. It is equivalent to the two residue conditions `c0 ≡ 4 (mod 8)`,
`c1 ≡ 2 (mod 4)`: the inert shape of `Dyadic_Residue_Shape.md` §2. Hence every
theorem of the chain holds verbatim for every pair of that shape. -/

namespace Reimann.DyadicShapeBridge

open Reimann.DyadicLattice Reimann.DyadicOrder Reimann.DyadicMatrixHandoff Reimann.DyadicMoments
open Reimann.Transfer (GroupLaw)

universe u

/-- Shape IIa: `C0 ≡ 4 (mod 8)` and `C1 ≡ 2 (mod 4)`. -/
def InertShape (c0 c1 : Scalar) : Prop := c0.residue 2 = 4 ∧ c1.residue 1 = 2

theorem samples_of_inert_shape {c0 c1 : Scalar} (h : InertShape c0 c1) :
    WeightOneSamples c0 c1 := by
  obtain ⟨h0, h1⟩ := h
  have hb : c1.residue 2 = 2 ∨ c1.residue 2 = 6 := by
    have hr := c1.reduce (by decide : 1 ≤ 2)
    rw [h1] at hr
    exact (by decide : ∀ w : BitVec 3, w.setWidth 2 = 2 → w = 2 ∨ w = 6) _ hr
  unfold WeightOneSamples
  rw [inverse_weight_one_mod_eight, h0, normalized_real_moments_3_23]
  rcases hb with e | e <;> rw [e] <;> exact ⟨1, 1, by decide, by decide, by decide, by decide⟩

theorem samples_iff_inert_shape (c0 c1 : Scalar) : WeightOneSamples c0 c1 ↔ InertShape c0 c1 :=
  ⟨moment_coefficient_bits, samples_of_inert_shape⟩

/-- `DyadicMatrixHandoff.lattice_invariant_factors` for every pair of the inert shape. -/
theorem inert_lattice_invariant_factors {c0 c1 : Scalar} (h : InertShape c0 c1) (r a : Nat) :
    ∃ read : Quot (latticeCoset c0 c1 r a) → Factors a,
    ∃ write : Factors a → Quot (latticeCoset c0 c1 r a),
    ∃ plus : Quot (latticeCoset c0 c1 r a) → Quot (latticeCoset c0 c1 r a) →
        Quot (latticeCoset c0 c1 r a),
      Function.LeftInverse write read ∧ Function.RightInverse write read ∧
      (∀ x, read (Quot.mk _ x) = coordinates a x) ∧
      (∀ x y, read (plus x y) = ((read x).1 + (read y).1, (read x).2 + (read y).2)) ∧
      (∀ x y : Scalar × Scalar, plus (Quot.mk _ x) (Quot.mk _ y) =
        Quot.mk _ (add x.1 y.1, add x.2 y.2)) :=
  lattice_invariant_factors (samples_of_inert_shape h) r a

/-- `DyadicStrictDualAdapter.strict_dual_invariant_factors` for every pair of the inert shape. -/
theorem inert_strict_dual_invariant_factors {c0 c1 : Scalar}
    {w : DyadicStrictDualAdapter.OddWeight} {a : Nat} {S : Type u} {G : GroupLaw S}
    (h : InertShape c0 c1) (A : DyadicStrictDualAdapter.Presentation c0 c1 w a G) :
    ∃ read : S → Factors a, ∃ write : Factors a → S,
      Function.LeftInverse write read ∧ Function.RightInverse write read ∧
      (∀ x, read (A.project x) = coordinates a x) ∧
      (∀ z t, read (G.add z t) = ((read z).1 + (read t).1, (read z).2 + (read t).2)) :=
  DyadicStrictDualAdapter.strict_dual_invariant_factors (samples_of_inert_shape h) A

end Reimann.DyadicShapeBridge
