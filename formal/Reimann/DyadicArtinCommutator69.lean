import Reimann.DyadicLocal
import Reimann.DyadicPlaceProduct

/-! The Artin-side calculation on N/D before restricting to X. In the
tower D is the full dyadic decomposition subgroup over k∞. Multiplication
is written `add` even in a nonabelian source group. -/

namespace Reimann.DyadicArtinCommutator69

open Reimann.Transfer Reimann.TameRestriction Reimann.DyadicLift Reimann.DyadicPlaceProduct

variable {S : Type} {G : GroupLaw S}

def Coset (D : Subgroup G) (x y : S) : Prop :=
  ∃ a : Subtype D.mem, x = G.add a.val y

def cosetSetoid (D : Subgroup G) : Setoid S where
  r := Coset D
  iseqv := {
    refl := fun x => ⟨⟨G.zero,D.identity⟩,(G.zero_add x).symm⟩
    symm := by
      rintro x y ⟨a,rfl⟩
      exact ⟨⟨G.neg a.val,D.inverse a.property⟩,(cancel_inside G a.val y).symm⟩
    trans := by
      rintro x y z ⟨a,rfl⟩ ⟨b,rfl⟩
      exact ⟨⟨G.add a.val b.val,D.product a.property b.property⟩,(G.assoc _ _ _).symm⟩ }

def Normal (D : Subgroup G) : Prop := ∀ y (a : Subtype D.mem), D.mem (conjugate G y a.val)

theorem coset_mul (D : Subgroup G) (hD : Normal D) {x y x' y' : S}
    (hx : Coset D x x') (hy : Coset D y y') : Coset D (G.add x y) (G.add x' y') := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  refine ⟨⟨G.add a.val (conjugate G x' b.val),D.product a.property (hD x' b)⟩,?_⟩
  simp only [conjugate,G.assoc,cancel_inside]

theorem inverse_product (x y : S) : G.neg (G.add x y) = G.add (G.neg y) (G.neg x) := by
  apply right_cancel G _ _ (G.add x y)
  simp only [G.neg_add,G.assoc,cancel_inside]

theorem coset_inverse (D : Subgroup G) (hD : Normal D) {x y : S}
    (hx : Coset D x y) : Coset D (G.neg x) (G.neg y) := by
  obtain ⟨a,rfl⟩ := hx
  let b : Subtype D.mem := ⟨G.neg a.val,D.inverse a.property⟩
  exact ⟨⟨conjugate G (G.neg y) b.val,hD (G.neg y) b⟩,
    (inverse_product _ _).trans (conjugate_times G _ _).symm⟩

abbrev Target (D : Subgroup G) := Quotient (cosetSetoid D)

def cls (D : Subgroup G) (x : S) : Target D := Quotient.mk (cosetSetoid D) x

def targetAdd (D : Subgroup G) (hD : Normal D) (x y : Target D) : Target D :=
  Quotient.liftOn₂ x y (fun a b => cls D (G.add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (coset_mul D hD ha hb))

def targetNeg (D : Subgroup G) (hD : Normal D) (x : Target D) : Target D :=
  Quotient.liftOn x (fun a => cls D (G.neg a))
    (fun _ _ he => Quotient.sound (coset_inverse D hD he))

def targetLaw (D : Subgroup G) (hD : Normal D) : GroupLaw (Target D) where
  zero := cls D G.zero
  add := targetAdd D hD
  neg := targetNeg D hD
  assoc x y z := by
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        induction z using Quotient.inductionOn with | _ c =>
          exact congrArg (cls D) (G.assoc a b c)
  zero_add x := Quotient.inductionOn x (fun a => congrArg (cls D) (G.zero_add a))
  add_zero x := Quotient.inductionOn x (fun a => congrArg (cls D) (G.add_zero a))
  add_neg x := Quotient.inductionOn x (fun a => congrArg (cls D) (G.add_neg a))
  neg_add x := Quotient.inductionOn x (fun a => congrArg (cls D) (G.neg_add a))

def projection (D : Subgroup G) (hD : Normal D) : Hom G (targetLaw D hD) where
  app := cls D
  preserves_zero := rfl
  preserves_add _ _ := rfl
  preserves_neg _ := rfl

theorem projection_kernel (D : Subgroup G) (x : S) :
    cls D x = cls D G.zero ↔ D.mem x := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := Quotient.exact h
    rw [G.add_zero] at ha
    exact ha ▸ a.property
  · intro hx
    exact Quotient.sound ⟨⟨x,hx⟩,(G.add_zero x).symm⟩

/-- In the unramified tower the commutators are contained in the dyadic
decomposition subgroup. This hypothesis yields an abelian quotient. -/
theorem target_comm (D : Subgroup G) (hD : Normal D)
    (hcomm : ∀ x y, D.mem (commutator G x y)) (p q : Target D) :
    (targetLaw D hD).add p q = (targetLaw D hD).add q p := by
  induction p using Quotient.inductionOn with | _ x =>
    induction q using Quotient.inductionOn with | _ y =>
      exact Quotient.sound ⟨⟨commutator G x y,hcomm x y⟩,(commutator_swap G x y).symm⟩

/-- Universal map out of N/D when the given homomorphism kills D. -/
def descend {V : Type} {H : GroupLaw V} (D : Subgroup G) (hD : Normal D)
    (f : Hom G H) (hf : ∀ a : Subtype D.mem, f.app a.val = H.zero) :
    Hom (targetLaw D hD) H where
  app := Quotient.lift f.app (by
    rintro x y ⟨a,rfl⟩
    rw [f.preserves_add,hf a,H.zero_add])
  preserves_zero := f.preserves_zero
  preserves_add x y := Quotient.inductionOn₂ x y (fun a b => f.preserves_add a b)
  preserves_neg x := Quotient.inductionOn x (fun a => f.preserves_neg a)

theorem descend_unique {V : Type} {H : GroupLaw V} (D : Subgroup G) (hD : Normal D)
    (u v : Hom (targetLaw D hD) H) (h : ∀ x, u.app (cls D x) = v.app (cls D x)) :
    ∀ z, u.app z = v.app z := fun z => Quotient.inductionOn z h

/-- Any endomorphism preserving D induces its action on the quotient. -/
def induced (D : Subgroup G) (hD : Normal D) (f : Hom G G)
    (hf : ∀ a : Subtype D.mem, D.mem (f.app a.val)) : Hom (targetLaw D hD) (targetLaw D hD) :=
  let φ : Hom G (targetLaw D hD) := {
    app := fun x => cls D (f.app x)
    preserves_zero := congrArg (cls D) f.preserves_zero
    preserves_add := fun x y => congrArg (cls D) (f.preserves_add x y)
    preserves_neg := fun x => congrArg (cls D) (f.preserves_neg x) }
  descend D hD φ (fun a => (projection_kernel D _).mpr (hf a))

/-- This convention is B d B⁻¹ d⁻¹, factored with both terms over k∞. -/
theorem commutator_factor (B d : S) :
    commutator G B d = G.add B (G.neg (conjugate G d B)) := by
  rw [← conjugate_inverse]
  simp only [commutator,conjugate,G.assoc]

variable {Ω : Type} {P : GroupLaw Ω}

/-- The prime-switching lift B lives in N, with no membership requirement in X.
The commutator returns to N since d normalizes N. -/
def commInN (N : Subgroup P) (B : Subtype N.mem) (d : Ω)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val)) : Subtype N.mem :=
  ⟨commutator P B.val d, by rw [commutator_factor]; exact N.product B.property (N.inverse (hd B))⟩

theorem class_commutator (N : Subgroup P) (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (B : Subtype N.mem) (d : Ω) (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val)) :
    cls D (commInN N B d hd) = (targetLaw D hD).add (cls D B)
      ((targetLaw D hD).neg (cls D ((ambientConjugation N d hd).app B))) :=
  DyadicLocal.commutator_projects_to_difference P (targetLaw D hD) N.mem N.product (cls D)
    (fun _ _ => rfl) B.val d B.property (hd B) (commInN N B d hd).property

/-- With t induced from conjugation by d, the projected commutator is b-t(b). -/
theorem artin_commutator (N : Subgroup P) (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (B : Subtype N.mem) (d : Ω) (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (ha : ∀ a : Subtype D.mem, D.mem ((ambientConjugation N d hd).app a.val)) :
    cls D (commInN N B d hd) = (targetLaw D hD).add (cls D B)
      ((targetLaw D hD).neg ((induced D hD (ambientConjugation N d hd) ha).app (cls D B))) :=
  class_commutator N D hD B d hd

theorem conjugate_composite (k d g : S) :
    conjugate G (G.add k d) g = conjugate G k (conjugate G d g) := by
  simp only [conjugate,inverse_product,G.assoc]

theorem class_inner (D : Subgroup G) (hcomm : ∀ k x, D.mem (commutator G k x)) (k x : S) :
    cls D (conjugate G k x) = cls D x :=
  Quotient.sound ⟨⟨commutator G k x,hcomm k x⟩,(commutator_times G k x).symm⟩

/-- Replacing d by k*d for k in N preserves the class even if k survives in Y.
Inner conjugation acts trivially on the abelian quotient. -/
theorem replace_lift (N : Subgroup P) (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (hcomm : ∀ k x, D.mem (commutator (subgroupLaw N) k x))
    (B k : Subtype N.mem) (d : Ω) (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (hkd : ∀ x : Subtype N.mem, N.mem (conjugate P (P.add k.val d) x.val)) :
    cls D (commInN N B (P.add k.val d) hkd) = cls D (commInN N B d hd) := by
  have he : (ambientConjugation N (P.add k.val d) hkd).app B =
      conjugate (subgroupLaw N) k ((ambientConjugation N d hd).app B) :=
    Subtype.ext (conjugate_composite _ _ _)
  rw [class_commutator N D hD B (P.add k.val d) hkd,class_commutator N D hD B d hd,
      he,class_inner D hcomm]

/-- A common image in the cyclotomic/genus-field quotient supplies the
required k. It suffices that the kernel of restriction is contained in N. -/
theorem lift_independent {Q : Type} {U : GroupLaw Q} (π : Hom P U)
    (N : Subgroup P) (hk : ∀ k, π.app k = U.zero → N.mem k)
    (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (hcomm : ∀ k x, D.mem (commutator (subgroupLaw N) k x))
    (B : Subtype N.mem) (d e : Ω) (hde : π.app e = π.app d)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (he : ∀ x : Subtype N.mem, N.mem (conjugate P e x.val)) :
    cls D (commInN N B e he) = cls D (commInN N B d hd) := by
  let k : Subtype N.mem := ⟨P.add e (P.neg d), hk _ (by
    rw [π.preserves_add,π.preserves_neg,hde,U.add_neg])⟩
  have hkd : P.add k.val d = e := difference_times (P := P) e d
  have hnorm : ∀ x : Subtype N.mem, N.mem (conjugate P (P.add k.val d) x.val) := hkd ▸ he
  have h := replace_lift N D hD hcomm B k d hd hnorm
  simpa only [hkd] using h

theorem inverse_inverse (x : S) : G.neg (G.neg x) = x := by
  apply right_cancel G _ _ (G.neg x)
  rw [G.neg_add,G.add_neg]

/-- Mizusawa writes B⁻¹d⁻¹Bd. In this module that word is the commutator
of the inverse generators, so the second term acts by d⁻¹. -/
theorem paper_convention (B d : S) :
    G.add (G.add (G.add (G.neg B) (G.neg d)) B) d =
      commutator G (G.neg B) (G.neg d) := by
  simp only [commutator,inverse_inverse]

theorem paper_projected (N : Subgroup P) (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (B : Subtype N.mem) (d : Ω)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P (P.neg d) x.val))
    (ha : ∀ a : Subtype D.mem, D.mem ((ambientConjugation N (P.neg d) hd).app a.val)) :
    cls D (commInN N ((subgroupLaw N).neg B) (P.neg d) hd) =
      (targetLaw D hD).add ((targetLaw D hD).neg (cls D B))
        ((induced D hD (ambientConjugation N (P.neg d) hd) ha).app (cls D B)) := by
  let t := induced D hD (ambientConjugation N (P.neg d) hd) ha
  rw [artin_commutator N D hD _ _ hd ha]
  change (targetLaw D hD).add _ ((targetLaw D hD).neg (t.app ((targetLaw D hD).neg (cls D B)))) = _
  rw [t.preserves_neg,inverse_inverse]
  rfl

end Reimann.DyadicArtinCommutator69
