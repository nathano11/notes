import Reimann.DyadicArtinCommutator69

/-! The subgroup image of the two-place discrepancy in a possibly nonsplit tower. -/

namespace Reimann.DyadicArtinImage69

open Reimann.Transfer Reimann.DyadicLift Reimann.DyadicPlaceProduct
open Reimann.TameRestriction Reimann.DyadicArtinCommutator69

variable {S : Type} {G : GroupLaw S}

/-- Intersection viewed inside H, so its quotient has the intended domain. -/
def intersection (H D : Subgroup G) : Subgroup (subgroupLaw H) where
  mem x := D.mem x.val
  identity := D.identity
  product := fun hx hy => D.product hx hy
  inverse := fun hx => D.inverse hx

theorem intersection_normal (H D : Subgroup G) (hD : Normal D) : Normal (intersection H D) :=
  fun y a => hD y.val ⟨a.val.val,a.property⟩

theorem coset_in_subgroup (H D : Subgroup G) (a b : Subtype H.mem) :
    Coset D a.val b.val ↔ Coset (intersection H D) a b := by
  constructor
  · rintro ⟨k,hk⟩
    have e : G.add a.val (G.neg b.val)=k.val := by rw [hk,G.assoc,G.add_neg,G.add_zero]
    have hH : H.mem k.val := e ▸ H.product a.property (H.inverse b.property)
    exact ⟨⟨⟨k.val,hH⟩,k.property⟩,Subtype.ext hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨⟨k.val.val,k.property⟩,congrArg Subtype.val hk⟩

def imageSubgroup (H D : Subgroup G) (hD : Normal D) : Subgroup (targetLaw D hD) where
  mem z := ∃ h : Subtype H.mem, cls D h.val = z
  identity := ⟨⟨G.zero,H.identity⟩,rfl⟩
  product := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨⟨G.add x.val y.val,H.product x.property y.property⟩,rfl⟩
  inverse := by rintro _ ⟨x,rfl⟩; exact ⟨⟨G.neg x.val,H.inverse x.property⟩,rfl⟩

def inclusion (H D : Subgroup G) (hD : Normal D) :
    Hom (targetLaw (intersection H D) (intersection_normal H D hD)) (targetLaw D hD) where
  app := Quotient.lift (fun x => cls D x.val) (fun x y h => Quotient.sound ((coset_in_subgroup H D x y).mpr h))
  preserves_zero := rfl
  preserves_add x y := Quotient.inductionOn₂ x y (fun _ _ => rfl)
  preserves_neg x := Quotient.inductionOn x (fun _ => rfl)

theorem inclusion_injective (H D : Subgroup G) (hD : Normal D) (x y : Target (intersection H D))
    (h : (inclusion H D hD).app x = (inclusion H D hD).app y) : x=y := by
  induction x using Quotient.inductionOn with | _ a =>
    induction y using Quotient.inductionOn with | _ b =>
      exact Quotient.sound ((coset_in_subgroup H D a b).mp (Quotient.exact h))

/-- The inclusion with codomain restricted to the image of H in N/D. -/
def ontoImage (H D : Subgroup G) (hD : Normal D) :
    Hom (targetLaw (intersection H D) (intersection_normal H D hD))
        (subgroupLaw (imageSubgroup H D hD)) where
  app z := ⟨(inclusion H D hD).app z,
    Quotient.inductionOn z (fun a => ⟨a,rfl⟩)⟩
  preserves_zero := Subtype.ext rfl
  preserves_add x y := Subtype.ext ((inclusion H D hD).preserves_add x y)
  preserves_neg x := Subtype.ext ((inclusion H D hD).preserves_neg x)

/-- The displayed homomorphism has a two-sided inverse on its image. -/
theorem subgroup_quotient_iso_image (H D : Subgroup G) (hD : Normal D) :
    ∃ inv : Subtype (imageSubgroup H D hD).mem → Target (intersection H D),
      (∀ x, inv ((ontoImage H D hD).app x)=x) ∧
      (∀ y, (ontoImage H D hD).app (inv y)=y) := by
  let f := ontoImage H D hD
  have onto (y : Subtype (imageSubgroup H D hD).mem) : ∃ x, f.app x=y := by
    obtain ⟨a,ha⟩ := y.property
    exact ⟨cls _ a,Subtype.ext ha⟩
  let inv y := Classical.choose (onto y)
  have right y : f.app (inv y)=y := Classical.choose_spec (onto y)
  exact ⟨inv,fun x => inclusion_injective H D hD _ _ (congrArg Subtype.val (right (f.app x))),right⟩

variable {Ω Q : Type} {P : GroupLaw Ω} {U : GroupLaw Q}

/-- The subgroup of N fixing the genus layer by restriction. -/
def genusKernel (N : Subgroup P) (ρ : Hom P U) : Subgroup (subgroupLaw N) where
  mem x := ρ.app x.val = U.zero
  identity := ρ.preserves_zero
  product := by intro x y hx hy; change ρ.app (P.add x.val y.val)=_; rw [ρ.preserves_add,hx,hy,U.zero_add]
  inverse := by
    intro x hx
    change ρ.app (P.neg x.val)=_
    rw [ρ.preserves_neg,hx]
    have h := U.neg_add U.zero
    rwa [U.add_zero] at h

theorem comm_in_genus_kernel (N : Subgroup P) (ρ : Hom P U) (B : Subtype N.mem) (d : Ω)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (commute : U.add (ρ.app B.val) (ρ.app d) = U.add (ρ.app d) (ρ.app B.val)) :
    (genusKernel N ρ).mem (commInN N B d hd) := by
  change ρ.app (commutator P B.val d) = U.zero
  simp only [commutator,ρ.preserves_add,ρ.preserves_neg]
  rw [commute,U.assoc (ρ.app d) (ρ.app B.val) (U.neg (ρ.app B.val)),U.add_neg,U.add_zero,U.add_neg]

/-- The actual class of B d B⁻¹ d⁻¹ inside H/(H∩D). -/
def switchClass (N : Subgroup P) (ρ : Hom P U) (D : Subgroup (subgroupLaw N))
    (B : Subtype N.mem) (d : Ω) (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (hc : U.add (ρ.app B.val) (ρ.app d) = U.add (ρ.app d) (ρ.app B.val)) :
    Target (intersection (genusKernel N ρ) D) :=
  cls _ ⟨commInN N B d hd,comm_in_genus_kernel N ρ B d hd hc⟩

theorem image_switchClass (N : Subgroup P) (ρ : Hom P U) (D : Subgroup (subgroupLaw N))
    (hD : Normal D) (B : Subtype N.mem) (d : Ω)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (ha : ∀ a : Subtype D.mem, D.mem ((ambientConjugation N d hd).app a.val))
    (hc : U.add (ρ.app B.val) (ρ.app d) = U.add (ρ.app d) (ρ.app B.val)) :
    (inclusion (genusKernel N ρ) D hD).app (switchClass N ρ D B d hd hc) =
      (targetLaw D hD).add (cls D B)
        ((targetLaw D hD).neg ((induced D hD (ambientConjugation N d hd) ha).app (cls D B))) :=
  artin_commutator N D hD B d hd ha

theorem switchClass_independent {Q' : Type} {U' : GroupLaw Q'} (π : Hom P U')
    (N : Subgroup P) (ρ : Hom P U) (hk : ∀ k, π.app k = U'.zero → N.mem k)
    (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (hcomm : ∀ k x, D.mem (commutator (subgroupLaw N) k x))
    (B : Subtype N.mem) (d e : Ω) (hde : π.app e = π.app d)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (he : ∀ x : Subtype N.mem, N.mem (conjugate P e x.val))
    (cd : U.add (ρ.app B.val) (ρ.app d) = U.add (ρ.app d) (ρ.app B.val))
    (ce : U.add (ρ.app B.val) (ρ.app e) = U.add (ρ.app e) (ρ.app B.val)) :
    switchClass N ρ D B e he ce = switchClass N ρ D B d hd cd := by
  apply inclusion_injective (genusKernel N ρ) D hD
  exact lift_independent π N hk D hD hcomm B d e hde hd he

/-- Values in Y of the section-change operator 1−t add in an abelian target. -/
theorem displacement_add (T : Hom G G) (abelian : ∀ x y, G.add x y=G.add y x) (a b : S) :
    G.add (G.add a b) (G.neg (T.app (G.add a b))) =
      G.add (G.add a (G.neg (T.app a))) (G.add b (G.neg (T.app b))) := by
  rw [T.preserves_add,inverse_product]
  let c := G.add b (G.neg (T.app b))
  calc
    _ = G.add a (G.add c (G.neg (T.app a))) := by simp only [c,G.assoc]
    _ = _ := by rw [abelian c (G.neg (T.app a)),← G.assoc]

/-- The same element occurs in the comparison of the two actual local
restrictions whenever B normalizes the global group fixing Eₐ. -/
theorem switchClass_is_local_discrepancy (N K : Subgroup P) (ρ : Hom P U)
    (D : Subgroup (subgroupLaw N)) (B : Subtype N.mem) (d : Subtype K.mem)
    (hK : ∀ x : Subtype K.mem, K.mem (conjugate P B.val x.val))
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d.val x.val))
    (hc : U.add (ρ.app B.val) (ρ.app d.val) = U.add (ρ.app d.val) (ρ.app B.val)) :
    ∃ h : Subtype (genusKernel N ρ).mem,
      h.val.val = (discrepancy (ambientConjugation K B.val hK) d).val ∧
      cls (intersection (genusKernel N ρ) D) h = switchClass N ρ D B d.val hd hc :=
  ⟨⟨commInN N B d.val hd,comm_in_genus_kernel N ρ B d.val hd hc⟩,
    (ambient_discrepancy K B.val hK d).symm,rfl⟩

/-- Changing the prime-switcher by h in H adds (1−t)[h] at every t.
The correction is allowed to be nonzero in Y. -/
theorem change_switcher (N : Subgroup P) (ρ : Hom P U) (D : Subgroup (subgroupLaw N))
    (hD : Normal D) (hcomm : ∀ k x, D.mem (commutator (subgroupLaw N) k x))
    (B : Subtype N.mem) (h : Subtype (genusKernel N ρ).mem) (d : Ω)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (ha : ∀ a : Subtype D.mem, D.mem ((ambientConjugation N d hd).app a.val))
    (hc : U.add (ρ.app B.val) (ρ.app d) = U.add (ρ.app d) (ρ.app B.val)) :
    let Bh := (subgroupLaw N).add B h.val
    ∃ hc' : U.add (ρ.app Bh.val) (ρ.app d) = U.add (ρ.app d) (ρ.app Bh.val),
      let incl := inclusion (genusKernel N ρ) D hD
      let Y := targetLaw D hD
      let t := induced D hD (ambientConjugation N d hd) ha
      incl.app (switchClass N ρ D Bh d hd hc') =
        Y.add (incl.app (switchClass N ρ D B d hd hc))
          (Y.add (cls D h.val) (Y.neg (t.app (cls D h.val)))) := by
  dsimp only
  have hh : ρ.app h.val.val=U.zero := h.property
  have hc' : U.add (ρ.app (P.add B.val h.val.val)) (ρ.app d) =
      U.add (ρ.app d) (ρ.app (P.add B.val h.val.val)) := by
    rw [ρ.preserves_add,hh,U.add_zero,hc]
  refine ⟨hc',?_⟩
  rw [image_switchClass _ _ _ hD _ d hd ha hc',image_switchClass _ _ _ hD B d hd ha hc]
  exact displacement_add _ (target_comm D hD hcomm) (cls D B) (cls D h.val)

/-- Pull an equality of discrepancies in Y back through an equivariant
injection X → Y, then evaluate the character on X. One h is used for all t. -/
theorem evaluate_switcher_change {X Y T M : Type} [Lean.Grind.IntModule M]
    (GX : GroupLaw X) (GY : GroupLaw Y) (ι : Hom GX GY) (inj : ∀ x y, ι.app x=ι.app y → x=y)
    (tx : T → Hom GX GX) (ty : T → Hom GY GY) (equiv : ∀ t x, ι.app ((tx t).app x)=(ty t).app (ι.app x))
    (f : X → M) (addf : ∀ x y, f (GX.add x y)=f x+f y) (negf : ∀ x, f (GX.neg x)= -(f x))
    (act : T → M → M) (ef : ∀ t x, f ((tx t).app x)=act t (f x))
    (h : X) (u v : T → X)
    (changed : ∀ t, ι.app (v t)=GY.add (ι.app (u t))
      (GY.add (ι.app h) (GY.neg ((ty t).app (ι.app h))))) :
    ∀ t, f (v t) = f (u t) + (f h-act t (f h)) := by
  intro t
  have e : v t = GX.add (u t) (GX.add h (GX.neg ((tx t).app h))) := by
    apply inj
    rw [ι.preserves_add,ι.preserves_add,ι.preserves_neg,equiv,changed]
  rw [e,addf,addf,negf,ef]
  grind

/-- With the (1−t) sign convention, a common primitive y changes to y+m.
Existence is unchanged, and neither primitive may be selected separately at
different t. -/
theorem simultaneous_coboundary_iff {T M : Type} [Lean.Grind.IntModule M]
    (op : T → M → M) (addOp : ∀ t x y, op t (x+y)=op t x+op t y)
    (subOp : ∀ t x y, op t (x-y)=op t x-op t y)
    (m : M) (p q : T → M) (change : ∀ t, q t=p t+(m-op t m)) :
    (∃ y, ∀ t, p t=y-op t y) ↔ ∃ y, ∀ t, q t=y-op t y := by
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨y+m,fun t => ?_⟩
    rw [change,hy,addOp]; grind
  · rintro ⟨y,hy⟩
    refine ⟨y-m,fun t => ?_⟩
    have e := (change t).symm.trans (hy t)
    rw [subOp]; grind

theorem same_switcher_class (N : Subgroup P) (ρ : Hom P U) (D : Subgroup (subgroupLaw N))
    (hD : Normal D) (B B' : Subtype N.mem) (same : cls D B'=cls D B) (d : Ω)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (ha : ∀ a : Subtype D.mem, D.mem ((ambientConjugation N d hd).app a.val))
    (hc : U.add (ρ.app B.val) (ρ.app d)=U.add (ρ.app d) (ρ.app B.val))
    (hc' : U.add (ρ.app B'.val) (ρ.app d)=U.add (ρ.app d) (ρ.app B'.val)) :
    switchClass N ρ D B' d hd hc' = switchClass N ρ D B d hd hc := by
  apply inclusion_injective (genusKernel N ρ) D hD
  rw [image_switchClass _ _ _ hD _ d hd ha hc',image_switchClass _ _ _ hD _ d hd ha hc,same]

/-- A single chosen lift of each quotient element suffices for testing a
single common primitive over the whole first decomposition group. -/
theorem simultaneous_section_iff {J T X M : Type}
    (π : J → T) (s : T → J) (section_spec : ∀ t, π (s t)=t)
    (difference : J → X) (independent : ∀ d e, π d=π e → difference d=difference e)
    (f : X → M) (principal : T → M → M) :
    (∃ y, ∀ d, f (difference d)=principal (π d) y) ↔
      ∃ y, ∀ t, f (difference (s t))=principal t y := by
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y,fun t => (hy (s t)).trans (congrArg (fun z => principal z y) (section_spec t))⟩
  · rintro ⟨y,hy⟩
    refine ⟨y,fun d => ?_⟩
    rw [independent d (s (π d)) (section_spec _).symm,hy]

end Reimann.DyadicArtinImage69
