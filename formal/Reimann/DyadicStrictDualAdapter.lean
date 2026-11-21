import Reimann.DyadicMatrixHandoff
import Reimann.DyadicStrictKernel

/-! Transport from the two-place strict dual to its two cyclic factors.
The field construction supplies the displayed projection from the lattice
in the (2b,c) basis. Its kernel is measured in the ambient (b,c) basis. -/
namespace Reimann.DyadicStrictDualAdapter

open Reimann.DyadicLattice Reimann.DyadicOrder Reimann.DyadicMatrixHandoff
open Reimann.DyadicQuotient (inAmbient)
open Reimann.DyadicMatrixImage (imageAt)
open Reimann.Transfer (GroupLaw)

abbrev OddWeight := {r : Nat // 0 < r ∧ r % 2 = 1}

/-- Arithmetic input at one layer of E_a=Q_a(√−3,√−23). Instantiate S with
the dual of classes vanishing at both dyadic places, and G with its group law.
The kernel equality uses the image of D_a on the whole ambient lattice Y. -/
structure Presentation (c0 c1 : Scalar) (w : OddWeight) (a : Nat)
    {S : Type u} (G : GroupLaw S) where
  project : Scalar × Scalar → S
  onto : Function.Surjective project
  map_add : ∀ x y, project (add x.1 y.1, add x.2 y.2) = G.add (project x) (project y)
  kernel : ∀ z, project z = G.zero ↔ imageAt c0 c1 w.val a (inAmbient z)

variable {c0 c1 : Scalar} {w : OddWeight} {a : Nat} {S : Type u} {G : GroupLaw S}

theorem same_fibre (A : Presentation c0 c1 w a G) (x y : Scalar × Scalar) :
    A.project x = A.project y ↔ latticeCoset c0 c1 w.val a x y :=
  (DyadicStrictKernel.fibres_of_exact_kernel c0 c1 w.val a G A.project A.map_add A.kernel x y).trans
    (DyadicStrictRelation.strictRelation_iff_latticeCoset c0 c1 w.val a x y)

def fromQuot (A : Presentation c0 c1 w a G) : Quot (latticeCoset c0 c1 w.val a) → S :=
  Quot.lift A.project (fun x y h => (same_fibre A x y).mpr h)

theorem fromQuot_bijective (A : Presentation c0 c1 w a G) :
    Function.Injective (fromQuot A) ∧ Function.Surjective (fromQuot A) := by
  constructor
  · intro x y
    induction x using Quot.ind with
    | mk p =>
      induction y using Quot.ind with
      | mk q => exact fun h => Quot.sound ((same_fibre A p q).mp h)
  · intro z
    obtain ⟨x,hx⟩ := A.onto z
    exact ⟨Quot.mk _ x,hx⟩

/-- The classifier reads an arithmetic class by its lattice representative.
Its inverse and addition are for the supplied group law on S. -/
theorem strict_dual_invariant_factors (samples : WeightOneSamples c0 c1)
    (A : Presentation c0 c1 w a G) :
    ∃ read : S → Factors a, ∃ write : Factors a → S,
      Function.LeftInverse write read ∧ Function.RightInverse write read ∧
      (∀ x, read (A.project x) = coordinates a x) ∧
      (∀ z t, read (G.add z t) = ((read z).1 + (read t).1, (read z).2 + (read t).2)) := by
  obtain ⟨encode,decode,_,left,right,onRep,_,_⟩ := lattice_invariant_factors samples w.val a
  obtain ⟨inj,onto⟩ := fromQuot_bijective A
  let lift (z : S) := Classical.choose (onto z)
  have sectionEq (z : S) : fromQuot A (lift z) = z := Classical.choose_spec (onto z)
  have retractEq (q) : lift (fromQuot A q) = q := inj (sectionEq (fromQuot A q))
  let read (z : S) := encode (lift z)
  let write (p : Factors a) := fromQuot A (decode p)
  have readRep (x : Scalar × Scalar) : read (A.project x) = coordinates a x := by
    change encode (lift (fromQuot A (Quot.mk _ x))) = coordinates a x
    rw [retractEq,onRep]
  refine ⟨read,write,?_,?_,readRep,?_⟩
  · intro z
    change fromQuot A (decode (encode (lift z))) = z
    rw [left,sectionEq]
  · intro p
    change encode (lift (fromQuot A (decode p))) = p
    rw [retractEq,right]
  · intro z t
    obtain ⟨x,rfl⟩ := A.onto z
    obtain ⟨y,rfl⟩ := A.onto t
    rw [← A.map_add,readRep,readRep,readRep,coordinates_add]

end Reimann.DyadicStrictDualAdapter
