import Reimann.DyadicSeriesProjection

/-! The double of a projected coefficient at precision 16 retains exactly
the three bits of the original coefficient at precision 8. -/

namespace Reimann.DyadicHalfPrecision

open Reimann.DyadicSeriesProjection Reimann.DyadicStickelberger69 Reimann.DyadicLattice

/-- Double the canonical lift of a word modulo 8 into a word modulo 16. -/
def doubleWord (a : BitVec 3) : BitVec 4 := 2*a.setWidth 4

theorem double_word_lift_independent (a : BitVec 4) :
    doubleWord (a.setWidth 3) = 2*a := by
  exact (by decide : ∀ a : BitVec 4, doubleWord (a.setWidth 3) = 2*a) a

theorem double_word_injective (a b : BitVec 3) :
    doubleWord a = doubleWord b ↔ a=b := by
  exact (by decide : ∀ a b : BitVec 3, doubleWord a = doubleWord b ↔ a=b) a b

/-- The coordinates of 2(γ−1)^j in (Z/16)[C₂].
Multiplication by γ−1 sends (x,y) to (y−x,x−y). -/
def twicePower : Nat → BitVec 4 × BitVec 4
  | 0 => (2,0)
  | j+1 => let p := twicePower j; (p.2-p.1,p.1-p.2)

theorem twice_fourth_zero : twicePower 4 = (0,0) := by decide

theorem twice_higher_zero (j : Nat) : twicePower (j+4) = (0,0) := by
  induction j with
  | zero => exact twice_fourth_zero
  | succ j ih =>
    change ((twicePower (j+4)).2-(twicePower (j+4)).1,
      (twicePower (j+4)).1-(twicePower (j+4)).2) = (0,0)
    rw [ih]
    decide

/-- Direct finite group-ring evaluation of a truncation of 2Φ modulo 16. -/
def partialDouble (f : Series) : Nat → BitVec 4 × BitVec 4
  | 0 => (0,0)
  | j+1 => let s := partialDouble f j
           let p := twicePower j
           let c := (f j).residue 3
           (s.1 + c*p.1,s.2 + c*p.2)

theorem four_coefficient_lift (a b c d : BitVec 4) :
    (2*a-2*b+4*c-8*d, 2*b-4*c+8*d) =
      (doubleWord (a.setWidth 3-b.setWidth 3+2*c.setWidth 3-4*d.setWidth 3),
       doubleWord (b.setWidth 3-2*c.setWidth 3+4*d.setWidth 3)) := by
  have sub : ∀ x y : BitVec 4, (x-y).setWidth 3 = x.setWidth 3-y.setWidth 3 := by decide
  have h₁ := double_word_lift_independent (a-b+2*c-4*d)
  have h₂ := double_word_lift_independent (b-2*c+4*d)
  simp only [sub, BitVec.setWidth_add _ _ (by decide : 3 ≤ 4),
    BitVec.setWidth_mul _ _ (by decide : 3 ≤ 4),
    show (2 : BitVec 4).setWidth 3 = 2 from rfl,
    show (4 : BitVec 4).setWidth 3 = 4 from rfl] at h₁ h₂
  rw [h₁,h₂]
  apply Prod.ext <;> grind

theorem first_four_double (f : Series) :
    partialDouble f 4 = (doubleWord (evaluate f).1,doubleWord (evaluate f).2) := by
  have h := four_coefficient_lift ((f 0).residue 3) ((f 1).residue 3)
    ((f 2).residue 3) ((f 3).residue 3)
  rw [(f 0).reduce (by decide : 2 ≤ 3), (f 1).reduce (by decide : 2 ≤ 3),
      (f 2).reduce (by decide : 2 ≤ 3), (f 3).reduce (by decide : 2 ≤ 3)] at h
  simp only [evaluate]
  rw [← h]
  simp only [partialDouble,twicePower]
  apply Prod.ext <;> grind

theorem all_truncations_double (f : Series) (j : Nat) :
    partialDouble f (j+4) = (doubleWord (evaluate f).1,doubleWord (evaluate f).2) := by
  induction j with
  | zero => exact first_four_double f
  | succ j ih =>
    change ((partialDouble f (j+4)).1+(f (j+4)).residue 3*(twicePower (j+4)).1,
        (partialDouble f (j+4)).2+(f (j+4)).residue 3*(twicePower (j+4)).2) = _
    rw [ih,twice_higher_zero]
    simp

/-- The unhalved signed row at conductor 552, rounded only after the exact
integer numerator is divided by the Bernoulli denominator 2·552. -/
def literalRow16 : BitVec 4 × BitVec 4 :=
  (BitVec.ofInt 4 (signedNumerator false / (2*552)),
   BitVec.ofInt 4 (signedNumerator true / (2*552)))

theorem literal_row_exact : literalRow16 = (8,0) := by
  obtain ⟨hp,hm⟩ := signed_row_exact
  unfold literalRow16
  rw [hp,hm]
  decide

theorem half_row_iff_unhalved (f : Series) (j : Nat) :
    evaluate f = halfRow ↔ partialDouble f (j+4) = literalRow16 := by
  rw [half_row_exact,all_truncations_double,literal_row_exact]
  constructor
  · intro h
    rw [h]
    decide
  · intro h
    obtain ⟨a,b⟩ := Prod.mk.inj h
    exact Prod.ext ((double_word_injective _ 4).mp a) ((double_word_injective _ 0).mp b)

/-- Handoff from a full-series ideal equality and one unhalved finite
Stickelberger comparison at precision 16. -/
theorem projected_ideal_of_unhalved (c0 c1 : Scalar) (phi : Series)
    (hideal : ∃ u v : Series, quadraticSeries c0 c1 = convolution u phi ∧
      phi = convolution v (quadraticSeries c0 c1))
    (hrow : partialDouble phi 4 = literalRow16) : ProjectedIdeal69 c0 c1 :=
  projected_ideal_of_full_series c0 c1 phi hideal ((half_row_iff_unhalved phi 0).mpr hrow)

theorem lattice_order_of_unhalved (c0 c1 : Scalar) (phi : Series)
    (hideal : ∃ u v : Series, quadraticSeries c0 c1 = convolution u phi ∧
      phi = convolution v (quadraticSeries c0 c1))
    (hrow : partialDouble phi 4 = literalRow16) (r a : Nat) :
    ∃ encode : Quot (Reimann.DyadicOrder.latticeCoset c0 c1 r a) → Fin (2^(2*a+1)),
    ∃ decode : Fin (2^(2*a+1)) → Quot (Reimann.DyadicOrder.latticeCoset c0 c1 r a),
      (∀ x, decode (encode x) = x) ∧ (∀ i, encode (decode i) = i) :=
  lattice_order_of_projected_ideal c0 c1 (projected_ideal_of_unhalved c0 c1 phi hideal hrow) r a

end Reimann.DyadicHalfPrecision
