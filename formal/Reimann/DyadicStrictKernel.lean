import Reimann.DyadicStrictRelation
import Reimann.Transfer

namespace Reimann.DyadicStrictKernel

open Reimann.DyadicLattice
open Reimann.DyadicQuotient (inAmbient)
open Reimann.DyadicMatrixImage (imageAt)
open Reimann.DyadicStrictRelation (strictRelation ambientDifference)

/-- An additive map whose kernel is the companion image in the ambient
lattice has precisely the fibres specified by the strict relation. -/
theorem fibres_of_exact_kernel (c0 c1 : Scalar) (r a : Nat)
    (G : Transfer.GroupLaw A) (π : Scalar × Scalar → A)
    (map_add : ∀ x y : Scalar × Scalar,
      π (add x.1 y.1, add x.2 y.2) = G.add (π x) (π y))
    (kernel : ∀ z, π z = G.zero ↔ imageAt c0 c1 r a (inAmbient z))
    (x y : Scalar × Scalar) : π x = π y ↔ strictRelation c0 c1 r a x y := by
  let z : Scalar × Scalar := (add x.1 (neg y.1), add x.2 (neg y.2))
  have translate : (add z.1 y.1, add z.2 y.2) = x := by
    apply Prod.ext <;> apply scalar_ext <;> intro n <;>
      simp only [z, add, neg] <;> grind
  have ambient : inAmbient z = ambientDifference x y := by
    apply Prod.ext
    · apply scalar_ext
      intro n
      simp only [z, inAmbient, ambientDifference, add, mul, neg, natScalar]
      grind
    · rfl
  have mapped : G.add (π z) (π y) = π x :=
    (map_add z y).symm.trans (congrArg π translate)
  change π x = π y ↔ imageAt c0 c1 r a (ambientDifference x y)
  rw [← ambient, ← kernel]
  constructor
  · intro h
    have cancel := congrArg (fun t => G.add t (G.neg (π y))) (mapped.trans h)
    simpa only [G.assoc, G.add_neg, G.add_zero] using cancel
  · intro h
    simpa only [h, G.zero_add] using mapped.symm

end Reimann.DyadicStrictKernel
