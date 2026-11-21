import Reimann.DyadicOrder

/-! The images of the actual companion differences in the ambient (b,c)
coordinates of the two-dimensional dyadic lattice. -/
namespace Reimann.DyadicMatrixImage

open Reimann.DyadicLattice Reimann.DyadicOrder Reimann.DyadicLayers

def imageAt (c0 c1 : Scalar) (r a : Nat) (y : Scalar × Scalar) : Prop :=
  let p := powerPair (companion c0 c1) (inverseWeight r) a
  ∃ x, act (difference p.1 p.2) x = y

/-- In ambient coordinates the base image is 4ℤ₂ × ℤ₂. -/
theorem base_image {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r : Nat) (y : Scalar × Scalar) :
    imageAt c0 c1 r 0 y ↔ ∃ t, y.1 = mul (natScalar 4) t := by
  obtain ⟨h0, h1⟩ := moment_coefficient_bits H
  obtain ⟨h, hh⟩ := (DyadicQuotient.residue_eq_iff_multiple 2 c0 (natScalar 4)).mp h0
  obtain ⟨k, hk⟩ := (DyadicQuotient.residue_eq_iff_multiple 1 c1 (natScalar 2)).mp h1
  obtain ⟨v, hv⟩ := (DyadicQuotient.residue_eq_iff_multiple 1 _ (natScalar 1)).mp
    (inverse_weight_mod_four r)
  apply DyadicBottom.coherent_bottom_image c0 c1 _ h (add (natScalar 1) (mul (natScalar 2) k)) v _ _ hv
  · rw [hh]
    apply scalar_ext
    intro n
    simp only [add, mul, natScalar]
    grind
  · rw [hk]
    apply scalar_ext
    intro n
    simp only [add, mul, natScalar]
    grind

/-- At a=n+1 the companion difference has image 2^(n+2) Y. -/
theorem positive_image {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r n : Nat) (y : Scalar × Scalar) :
    imageAt c0 c1 r (n+1) y ↔ ∃ z, scaleVector (natScalar (2^(n+2))) z = y :=
  positive_layer_image_of_residues _ _ _ (moment_coefficient_bits H).1
    (moment_coefficient_bits H).2 (inverse_weight_mod_four r) n y

theorem first_image {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r : Nat) (y : Scalar × Scalar) :
    imageAt c0 c1 r 1 y ↔ ∃ z, scaleVector (natScalar 4) z = y :=
  positive_image H r 0 y

theorem scale_successor (m : Nat) (z : Scalar × Scalar) :
    scaleVector (natScalar (2*m)) z =
      scaleVector (natScalar 2) (scaleVector (natScalar m) z) := by
  rw [nat_scale_product]
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [scaleVector, mul, BitVec.mul_assoc]

/-- From layer one onwards, squaring doubles the preceding image as a sublattice. -/
theorem square_doubles_image {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r n : Nat) (y : Scalar × Scalar) :
    imageAt c0 c1 r (n+2) y ↔
      ∃ z, imageAt c0 c1 r (n+1) z ∧ scaleVector (natScalar 2) z = y := by
  rw [positive_image H r (n+1)]
  have hpow : 2^(n+1+2) = 2 * 2^(n+2) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (positive_image H r n _).mpr ⟨x, rfl⟩, (scale_successor _ x).symm.trans hx⟩
  · rintro ⟨z, hz, hy⟩
    obtain ⟨x, rfl⟩ := (positive_image H r n z).mp hz
    exact ⟨x, (scale_successor _ x).trans hy⟩

end Reimann.DyadicMatrixImage
