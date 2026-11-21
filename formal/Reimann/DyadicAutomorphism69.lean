import Reimann.DyadicLocalRestriction69
import Reimann.DyadicArtinImage69

/-! Composition of actual field automorphisms acts on prime predicates by
pullback along the inverse. The group commutator uses this same action. -/

namespace Reimann.DyadicAutomorphism69

open Lean.Grind Reimann.Transfer Reimann.DyadicLocalRestriction69
open Reimann.DyadicRestrictionTower69 Reimann.DyadicPlaceProduct Reimann.TameRestriction

variable {F : Type} [Field F]

theorem auto_ext {g h : Automorphism F} (eq : ∀ x, g.app x = h.app x) : g=h := by
  cases g
  cases h
  congr
  exact funext eq

def identity (F : Type) [Field F] : Automorphism F where
  app x := x
  injective := fun _ _ h => h
  surjective := fun x => ⟨x, rfl⟩
  zero := rfl
  one := rfl
  add _ _ := rfl
  mul _ _ := rfl

def compose (g h : Automorphism F) : Automorphism F where
  app x := g.app (h.app x)
  injective := fun _ _ e => h.injective (g.injective e)
  surjective := by
    intro y
    obtain ⟨z, rfl⟩ := g.surjective y
    obtain ⟨x, rfl⟩ := h.surjective z
    exact ⟨x, rfl⟩
  zero := by rw [h.zero, g.zero]
  one := by rw [h.one, g.one]
  add x y := by rw [h.add, g.add]
  mul x y := by rw [h.mul, g.mul]

noncomputable def preimage (g : Automorphism F) (y : F) : F := Classical.choose (g.surjective y)

theorem apply_preimage (g : Automorphism F) (y : F) : g.app (preimage g y) = y :=
  Classical.choose_spec (g.surjective y)

theorem preimage_apply (g : Automorphism F) (x : F) : preimage g (g.app x) = x :=
  g.injective (apply_preimage g _)

noncomputable def inverse (g : Automorphism F) : Automorphism F where
  app := preimage g
  injective := fun x y e => (apply_preimage g x).symm.trans ((congrArg g.app e).trans (apply_preimage g y))
  surjective := fun x => ⟨g.app x, preimage_apply g x⟩
  zero := g.injective ((apply_preimage g 0).trans g.zero.symm)
  one := g.injective ((apply_preimage g 1).trans g.one.symm)
  add x y := g.injective (by rw [apply_preimage, g.add, apply_preimage, apply_preimage])
  mul x y := g.injective (by rw [apply_preimage, g.mul, apply_preimage, apply_preimage])

noncomputable def law (F : Type) [Field F] : GroupLaw (Automorphism F) where
  zero := identity F
  add := compose
  neg := inverse
  assoc _ _ _ := auto_ext (fun _ => rfl)
  zero_add _ := auto_ext (fun _ => rfl)
  add_zero _ := auto_ext (fun _ => rfl)
  add_neg g := auto_ext (apply_preimage g)
  neg_add g := auto_ext (preimage_apply g)

noncomputable def push (g : Automorphism F) (p : F → Prop) (x : F) : Prop := p ((inverse g).app x)

theorem push_image (g : Automorphism F) (p : F → Prop) (x : F) : push g p (g.app x) ↔ p x := by
  change p (preimage g (g.app x)) ↔ p x
  rw [preimage_apply]

theorem push_identity (p : F → Prop) : push (identity F) p = p := by
  funext x
  exact propext (push_image (identity F) p x)

theorem push_compose (g h : Automorphism F) (p : F → Prop) :
    push (compose g h) p = push g (push h p) := by
  funext y
  obtain ⟨z, rfl⟩ := g.surjective y
  obtain ⟨x, rfl⟩ := h.surjective z
  change push (compose g h) p ((compose g h).app x) = push g (push h p) (g.app (h.app x))
  exact propext ((push_image _ _ _).trans (((push_image g _ _).trans (push_image h p x)).symm))

noncomputable def primeAction (F : Type) [Field F] : PlaceAction (law F) (F → Prop) where
  move := push
  one := push_identity
  comp := push_compose

theorem stabilizes_iff (g : Automorphism F) (p : F → Prop) :
    push g p = p ↔ ∀ x, p (g.app x) ↔ p x := by
  constructor
  · intro eq x
    rw [← eq] at ⊢
    exact (push_image g p x).trans (Iff.of_eq (congrFun eq x).symm)
  · intro h
    funext y
    obtain ⟨x, rfl⟩ := g.surjective y
    exact propext ((push_image g p x).trans (h x).symm)

theorem conjugate_stabilizes (B d : Automorphism F) (p : F → Prop) (hd : push d p = p) :
    push (conjugate (law F) B d) (push B p) = push B p := by
  let A := primeAction F
  change A.move (conjugate (law F) B d) (A.move B p) = A.move B p
  rw [← A.comp, conjugate_times, A.comp]
  exact congrArg (A.move B) hd

theorem commutator_apply (B d : Automorphism F) (x : F) :
    (commutator (law F) B d).app x = B.app (d.app ((inverse B).app ((inverse d).app x))) := rfl

theorem map_neg (g : Automorphism F) (x : F) : g.app (-x) = -(g.app x) := by
  have h := g.add x (-x)
  rw [show x + -x = 0 by grind only, g.zero] at h
  grind only

theorem inverse_negates (g : Automorphism F) (x : F) (h : g.app x = -x) : (inverse g).app x = -x := by
  apply g.injective
  change g.app (preimage g x) = g.app (-x)
  rw [apply_preimage, map_neg, h]
  grind only

theorem supports_pull (V : DyadicDecomposition69.DyadicValue F) (g : Automorphism F) (x : F) :
    Supports (pull V g) x ↔ Supports V (g.app x) :=
  or_congr ⟨fun e => e ▸ g.zero, fun e => g.injective (e.trans g.zero.symm)⟩ Iff.rfl

theorem push_supports (g : Automorphism F) (V : DyadicDecomposition69.DyadicValue F) :
    push g (Supports V) = Supports (pull V (inverse g)) := by
  funext x
  exact propext (supports_pull V (inverse g) x).symm

theorem push_of_reverse_pull (g : Automorphism F) (V W : DyadicDecomposition69.DyadicValue F)
    (h : pull W g = V) : push g (Supports V) = Supports W := by
  funext y
  obtain ⟨x,rfl⟩ := g.surjective y
  apply propext
  rw [push_image, ← h]
  exact supports_pull W g x

/-- Transport and contraction of prime predicates commute when the upper
field automorphism restricts to the lower automorphism on j(F). -/
theorem push_contraction {Ω : Type} [Field Ω] (j : F → Ω) (B : Automorphism Ω) (b : Automorphism F)
    (h : ∀ x, B.app (j x) = j (b.app x)) (p : Ω → Prop) :
    (fun x => push B p (j x)) = push b (fun x => p (j x)) := by
  funext y
  obtain ⟨x, rfl⟩ := b.surjective y
  apply propext
  change push B p (j (b.app x)) ↔ push b (fun y => p (j y)) (b.app x)
  rw [← h, push_image, push_image]

end Reimann.DyadicAutomorphism69
