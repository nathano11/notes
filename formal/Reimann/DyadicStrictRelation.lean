import Reimann.DyadicMatrixImage

/-! Translation between ambient companion images and coset equality in the
basis (2b,c) of the index-two sublattice. -/
namespace Reimann.DyadicStrictRelation

open Reimann.DyadicLattice
open Reimann.DyadicQuotient (inAmbient)
open Reimann.DyadicOrder (latticeCoset inverseWeight)
open Reimann.DyadicMatrixImage (imageAt)

def ambientDifference (x y : Scalar × Scalar) : Scalar × Scalar :=
  (add (inAmbient x).1 (neg (inAmbient y).1), add (inAmbient x).2 (neg (inAmbient y).2))

def strictRelation (c0 c1 : Scalar) (r a : Nat) (x y : Scalar × Scalar) : Prop :=
  imageAt c0 c1 r a (ambientDifference x y)

/-- The first ambient coordinate is twice the difference in the first
sublattice coordinate, while the second coordinate is unchanged. -/
theorem ambientDifference_base (x y : Scalar × Scalar) :
    let dx := add x.1 (neg y.1)
    ambientDifference x y = (add dx dx, add x.2 (neg y.2)) := by
  apply Prod.ext
  · apply scalar_ext
    intro n
    simp only [ambientDifference, inAmbient, add, neg, mul, natScalar]
    grind
  · rfl

private theorem difference_iff_sum (x y u : Scalar) :
    u = add x (neg y) ↔ x = add y u := by
  constructor
  · rintro rfl
    apply scalar_ext
    intro n
    simp only [add, neg]
    grind
  · rintro rfl
    apply scalar_ext
    intro n
    simp only [add, neg]
    grind

theorem ambientDifference_iff_translate (x y u : Scalar × Scalar) :
    u = ambientDifference x y ↔ inAmbient x =
      (add (inAmbient y).1 u.1, add (inAmbient y).2 u.2) := by
  constructor
  · intro h
    exact Prod.ext ((difference_iff_sum _ _ _).mp (congrArg Prod.fst h))
      ((difference_iff_sum _ _ _).mp (congrArg Prod.snd h))
  · intro h
    exact Prod.ext ((difference_iff_sum _ _ _).mpr (congrArg Prod.fst h))
      ((difference_iff_sum _ _ _).mpr (congrArg Prod.snd h))

theorem strictRelation_zero (c0 c1 : Scalar) (r : Nat) (x y : Scalar × Scalar) :
    strictRelation c0 c1 r 0 x y ↔ DyadicBottom.bottomClassRel c0 c1 (inverseWeight r) x y := by
  unfold strictRelation
  rw [ambientDifference_base]
  rfl

theorem strictRelation_succ (c0 c1 : Scalar) (r n : Nat) (x y : Scalar × Scalar) :
    strictRelation c0 c1 r (n+1) x y ↔ DyadicOrder.positiveCoset c0 c1 r n x y := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v, (ambientDifference_iff_translate x y _).mp hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨v, (ambientDifference_iff_translate x y _).mpr hv⟩

/-- The intrinsic image relation agrees at every layer with the relation
used by the additive invariant-factor classifier. -/
theorem strictRelation_iff_latticeCoset (c0 c1 : Scalar) (r a : Nat) (x y : Scalar × Scalar) :
    strictRelation c0 c1 r a x y ↔ latticeCoset c0 c1 r a x y := by
  cases a with
  | zero => exact strictRelation_zero c0 c1 r x y
  | succ n => exact strictRelation_succ c0 c1 r n x y

theorem strictRelation_eq_latticeCoset (c0 c1 : Scalar) (r a : Nat) :
    strictRelation c0 c1 r a = latticeCoset c0 c1 r a := by
  funext x y
  exact propext (strictRelation_iff_latticeCoset c0 c1 r a x y)

/-- Every image vector lifts to the index-two sublattice. At layer zero
its first coordinate is a multiple of four. At layer n+1 the common
scalar factor is twice 2^(n+1). -/
theorem image_lies_in_sublattice {c0 c1 : Scalar} (H : DyadicOrder.WeightOneSamples c0 c1)
    (r a : Nat) (y : Scalar × Scalar) (hy : imageAt c0 c1 r a y) :
    ∃ x, inAmbient x = y := by
  have lift (m : Nat) (p : Scalar) (hp : y.1 = mul (natScalar (2*m)) p) :
      ∃ x, inAmbient x = y := by
    refine ⟨(mul (natScalar m) p, y.2), Prod.ext ?_ rfl⟩
    change mul (natScalar 2) (mul (natScalar m) p) = y.1
    rw [hp, DyadicLayers.nat_scale_product]
    apply scalar_ext
    intro k
    simp only [mul, BitVec.mul_assoc]
  cases a with
  | zero =>
    obtain ⟨p,hp⟩ := (DyadicMatrixImage.base_image H r y).mp hy
    exact lift 2 p hp
  | succ n =>
    obtain ⟨z,hz⟩ := (DyadicMatrixImage.positive_image H r n y).mp hy
    apply lift (2^(n+1)) z.1
    rw [Nat.mul_comm 2 (2^(n+1)), ← Nat.pow_succ]
    exact (congrArg Prod.fst hz).symm

end Reimann.DyadicStrictRelation
