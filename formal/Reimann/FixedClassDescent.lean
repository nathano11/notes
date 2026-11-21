import Reimann.Transfer

/-!
Quadratic descent on groups of odd exponent. The motivating maps in
`scratch_tw_units/Odd_Prime_Descent.md`, equation (1), are extension and
norm of ideal classes from the maximal real subfield. Those arithmetic
maps and their two composite identities are explicit inputs here.
-/

namespace Reimann.FixedClassDescent

open Reimann.Transfer

/-- The two identities for extension and norm. -/
structure QuadraticMaps (G : GroupLaw A) (H : GroupLaw B) where
  extend : Hom G H
  norm : Hom H G
  conj : Hom H H
  norm_extend : ∀ x, norm.app (extend.app x) = G.add x x
  extend_norm : ∀ y, extend.app (norm.app y) = H.add y (conj.app y)

/-- The norm and extension identities alone force every extended class to be fixed. -/
theorem extend_fixed {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H) (x : A) :
    d.conj.app (d.extend.app x) = d.extend.app x := by
  have heq := d.extend_norm (d.extend.app x)
  rw [d.norm_extend, d.extend.preserves_add] at heq
  have hcancel := congrArg (H.add (H.neg (d.extend.app x))) heq
  simpa only [← H.assoc, H.neg_add, H.zero_add] using hcancel.symm

/-- On a class killed by 2k+1, multiplying its double by k+1 recovers the class. -/
theorem half_double (G : GroupLaw A) (k : Nat) (x : A)
    (hk : multiple G (2*k+1) x = G.zero) :
    multiple G (k+1) (G.add x x) = x := by
  have htwo : multiple G 2 x = G.add x x := by simp [multiple, G.zero_add]
  rw [← htwo, ← multiple_mul, show (k+1)*2 = (2*k+1)+1 by omega]
  change G.add (multiple G (2*k+1) x) x = x
  rw [hk, G.zero_add]

/-- The fixed elements form a subgroup, with the law inherited from upstairs. -/
def fixedGroup (H : GroupLaw B) (c : Hom H H) : GroupLaw {y : B // c.app y = y} where
  zero := ⟨H.zero, c.preserves_zero⟩
  add x y := ⟨H.add x.val y.val, by rw [c.preserves_add, x.property, y.property]⟩
  neg x := ⟨H.neg x.val, by rw [c.preserves_neg, x.property]⟩
  assoc x y z := Subtype.ext (H.assoc x.val y.val z.val)
  zero_add x := Subtype.ext (H.zero_add x.val)
  add_zero x := Subtype.ext (H.add_zero x.val)
  add_neg x := Subtype.ext (H.add_neg x.val)
  neg_add x := Subtype.ext (H.neg_add x.val)

/-- Extension, with its codomain restricted to the fixed group. -/
def extendToFixed {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H) :
    Hom G (fixedGroup H d.conj) where
  app x := ⟨d.extend.app x, extend_fixed d x⟩
  preserves_zero := Subtype.ext d.extend.preserves_zero
  preserves_add x y := Subtype.ext (d.extend.preserves_add x y)
  preserves_neg x := Subtype.ext (d.extend.preserves_neg x)

/-- The inverse candidate is (k+1) times the norm. -/
def halfNorm {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H)
    (k : Nat) (y : {y : B // d.conj.app y = y}) : A :=
  multiple G (k+1) (d.norm.app y.val)

theorem halfNorm_extend {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H)
    (k : Nat) (x : A) (hk : multiple G (2*k+1) x = G.zero) :
    halfNorm d k ((extendToFixed d).app x) = x := by
  change multiple G (k+1) (d.norm.app (d.extend.app x)) = x
  rw [d.norm_extend]
  exact half_double G k x hk

theorem extend_halfNorm {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H)
    (k : Nat) (y : {y : B // d.conj.app y = y}) (hk : multiple H (2*k+1) y.val = H.zero) :
    (extendToFixed d).app (halfNorm d k y) = y := by
  apply Subtype.ext
  change d.extend.app (multiple G (k+1) (d.norm.app y.val)) = y.val
  rw [hom_multiple, d.extend_norm, y.property]
  exact half_double H k y.val hk

/-- The exponent need only annihilate the fixed subgroup upstairs. -/
def fixedClassBijection {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H)
    (k : Nat) (down : ∀ x, multiple G (2*k+1) x = G.zero)
    (up : ∀ y : {y : B // d.conj.app y = y}, multiple H (2*k+1) y.val = H.zero) :
    Bijection A {y : B // d.conj.app y = y} where
  forward := (extendToFixed d).app
  backward := halfNorm d k
  left_inv x := halfNorm_extend d k x (down x)
  right_inv y := extend_halfNorm d k y (up y)

/-- The inverse of the homomorphism on these fixed classes also preserves the
group law. This uses injectivity of extension, so no commutativity assumption
on the ambient group is needed. -/
def halfNormHom {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H)
    (k : Nat) (down : ∀ x, multiple G (2*k+1) x = G.zero)
    (up : ∀ y : {y : B // d.conj.app y = y}, multiple H (2*k+1) y.val = H.zero) :
    Hom (fixedGroup H d.conj) G := by
  let e := fixedClassBijection d k down up
  let f := extendToFixed d
  have inj {x z : A} (heq : f.app x = f.app z) : x = z := by
    exact (e.left_inv x).symm.trans ((congrArg e.backward heq).trans (e.left_inv z))
  have inv (y) : f.app (halfNorm d k y) = y := e.right_inv y
  refine ⟨halfNorm d k, ?_, ?_, ?_⟩
  · apply inj
    rw [inv, f.preserves_zero]
  · intro y z
    apply inj
    rw [inv, f.preserves_add, inv, inv]
  · intro y
    apply inj
    rw [inv, f.preserves_neg, inv]

/-- Every power of an odd residue has the required form, with k obtained by
integer division even when the depth is zero. -/
theorem odd_power_exponent (p n : Nat) (hp : p % 2 = 1) :
    2 * (p^n / 2) + 1 = p^n := by
  have hmod : p^n % 2 = 1 := by rw [Nat.pow_mod, hp, Nat.one_pow]
  omega

/-- At an odd prime-power depth, extension has a two-sided inverse
homomorphism on the fixed subgroup, with the stated formula on classes.
Oddness is sufficient for this algebraic implication. -/
theorem fixedClassIsoAtOddPower {G : GroupLaw A} {H : GroupLaw B} (d : QuadraticMaps G H)
    (p n : Nat) (hp : p % 2 = 1) (down : ∀ x, multiple G (p^n) x = G.zero)
    (up : ∀ y : {y : B // d.conj.app y = y}, multiple H (p^n) y.val = H.zero) :
    ∃ inv : Hom (fixedGroup H d.conj) G,
      (∀ x, inv.app ((extendToFixed d).app x) = x) ∧
      (∀ y, (extendToFixed d).app (inv.app y) = y) ∧
      (∀ y, inv.app y = multiple G (p^n / 2 + 1) (d.norm.app y.val)) := by
  let k := p^n / 2
  have hk : 2*k+1 = p^n := odd_power_exponent p n hp
  have hdown (x) : multiple G (2*k+1) x = G.zero := hk.symm ▸ down x
  have hup (y : {y : B // d.conj.app y = y}) : multiple H (2*k+1) y.val = H.zero :=
    hk.symm ▸ up y
  exact ⟨halfNormHom d k hdown hup, fun x => halfNorm_extend d k x (hdown x),
    fun y => extend_halfNorm d k y (hup y), fun _ => rfl⟩

end Reimann.FixedClassDescent
