import Reimann277.StrictReciprocity
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Reimann.TameStrictCohomology277

open TameRestriction TameArtin277 TameCyclotomicLocal277 TameStrictLocal277
open TameArithmeticSymbol277 TameStrictArtin277 TameStrictReciprocity277

abbrev Coeff (n : ℕ) := ZMod (277^(n+1))

/-- Finite-coefficient continuous crossed homomorphisms, unramified away from 277
and zero on the local kernels at all places over 277. -/
noncomputable def cocycles (r n : ℕ) : AddSubgroup (Global → Coeff n) where
  carrier := {c | (∀ g h, c (g*h) = c g + (finiteTwist r n g : Coeff n) * c h) ∧
    Continuous c ∧ ∀ x ∈ localRelations r n, c x.val = 0}
  zero_mem' := ⟨by simp, continuous_const, by simp⟩
  add_mem' := by
    rintro c d ⟨hc,cc,lc⟩ ⟨hd,cd,ld⟩
    refine ⟨?_,cc.add cd,?_⟩
    · intro g h
      simp only [Pi.add_apply,hc,hd,mul_add]
      abel
    · intro x hx
      simp only [Pi.add_apply,lc x hx,ld x hx,add_zero]
  neg_mem' := by
    rintro c ⟨hc,cc,lc⟩
    refine ⟨?_,cc.neg,fun x hx => by simp [lc x hx]⟩
    intro g h
    simp only [Pi.neg_apply,hc,mul_neg]
    abel

/-- One coefficient supplies a single coboundary on the entire global group. -/
noncomputable def principal (r n : ℕ) : AddSubgroup (cocycles r n) where
  carrier := {c | ∃ b : Coeff n, ∀ g, c.val g = ((finiteTwist r n g : Coeff n)-1)*b}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro c d ⟨b,hb⟩ ⟨a,ha⟩
    exact ⟨b+a,fun g => by change c.val g + d.val g = _; rw [hb,ha,mul_add]⟩
  neg_mem' := by
    rintro c ⟨b,hb⟩
    exact ⟨-b,fun g => by change -(c.val g) = _; rw [hb,mul_neg]⟩

abbrev StrictH1 (r n : ℕ) := (cocycles r n) ⧸ principal r n

/-- Pointwise additive characters satisfying the inverse cyclotomic twist. -/
noncomputable def characters (r n : ℕ) : AddSubgroup (Additive (SClassGroup r n) →+ Coeff n) where
  carrier := {f | ∀ g C, f (Additive.ofMul (TameIdealAction277.onClass r n g C)) =
    (finiteTwist r n g : Coeff n) * f (Additive.ofMul C)}
  zero_mem' := by simp
  add_mem' := by
    intro f k hf hk g C
    rw [AddMonoidHom.add_apply,hf g C,hk g C,AddMonoidHom.add_apply,mul_add]
  neg_mem' := by
    intro f hf g C
    rw [AddMonoidHom.neg_apply,hf g C,AddMonoidHom.neg_apply,mul_neg]

def representative {r n : ℕ} (c : cocycles r n) (g : Global) : ℤ := (c.val g).val

theorem cast_rep {r n : ℕ} (c : cocycles r n) (g : Global) :
    (representative c g : Coeff n) = c.val g := TameResidueCharacter277.cast_representative _

theorem crossed_rep {r n : ℕ} (w : Witness r n) (c : cocycles r n) :
    Crossed (data w) (representative c) := by
  intro g h
  apply (TameResidueCharacter277.difference_iff _ _).mpr
  change (representative c (g*h) : Coeff n) =
    ((representative c g + scalar r n g * representative c h : ℤ) : Coeff n)
  rw [Int.cast_add,Int.cast_mul,scalar_cast,cast_rep,cast_rep,cast_rep]
  exact c.property.1 g h

theorem continuous_rep {r n : ℕ} (c : cocycles r n) :
    Continuous (fun g => (representative c g : Coeff n)) := by
  simpa only [cast_rep] using c.property.2.1

theorem rep_at_relations {r n : ℕ} (c : cocycles r n) (x : globalKernel r n)
    (hx : x ∈ localRelations r n) : modulus n ∣ representative c x.val := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [cast_rep,c.property.2.2 x hx]

theorem exists_character {r n : ℕ} (hr : ¬276 ∣ r) (a : Input r n) (c : cocycles r n) :
    ∃ f : characters r n, ∀ x : globalKernel r n, f.val (Additive.ofMul (toClassGroup (reciprocity a) x)) = c.val x.val := by
  let w := tameWitness r n hr
  have h := (strict_class_character_of_symbol r n hr a (crossed_rep w c) (continuous_rep c)).mp
    ⟨fun x hx => rep_at_relations c x (Or.inl hx),
      (strict_iff_split w (crossed_rep w c)).mpr (fun x hx => rep_at_relations c x (Or.inr hx))⟩
  obtain ⟨η,⟨hη,hh⟩,_⟩ := h
  refine ⟨⟨η.toAdditiveLeft,hη⟩,fun x => ?_⟩
  exact (congrArg Multiplicative.toAdd (hh x)).trans (cast_rep c _)

variable {r n : ℕ} (hr : ¬276 ∣ r) (a : Input r n)

noncomputable def descended (c : cocycles r n) : characters r n :=
  (exists_character hr a c).choose

theorem descended_apply (c : cocycles r n) (x : globalKernel r n) :
    (descended hr a c).val (Additive.ofMul (toClassGroup (reciprocity a) x)) = c.val x.val :=
  (exists_character hr a c).choose_spec x

theorem characters_ext {f k : characters r n}
    (h : ∀ x, f.val (Additive.ofMul (toClassGroup (reciprocity a) x)) =
      k.val (Additive.ofMul (toClassGroup (reciprocity a) x))) : f = k := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro C
  obtain ⟨D,rfl⟩ := Additive.ofMul.surjective C
  obtain ⟨x,rfl⟩ := toClassGroup_surjective (reciprocity a) D
  exact h x

noncomputable def descend : cocycles r n →+ characters r n where
  toFun := descended hr a
  map_zero' := characters_ext a (fun x => descended_apply hr a 0 x)
  map_add' c d := characters_ext a (fun x => by
    change (descended hr a (c+d)).val _ = (descended hr a c).val _ + (descended hr a d).val _
    rw [descended_apply,descended_apply,descended_apply]
    rfl)

theorem descend_surjective : Function.Surjective (descend hr a) := by
  intro f
  let η := f.val.toMultiplicativeRight
  have hη : Twisted η := f.property
  obtain ⟨c,hc,cc,ha,hs,hf⟩ := twisted_character_has_representative r n hr a η hη
  let w := tameWitness r n hr
  let d : Global → Coeff n := fun g => (c g : Coeff n)
  have hd : d ∈ cocycles r n := by
    refine ⟨?_,cc,?_⟩
    · intro g h
      have eq := (TameResidueCharacter277.difference_iff _ _).mp (hc g h)
      change (c (g*h) : Coeff n) = ((c g + scalar r n g*c h : ℤ) : Coeff n) at eq
      simpa only [d,Int.cast_add,Int.cast_mul,scalar_cast] using eq
    · intro x hx
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (hx.elim (ha x) ((strict_iff_split w hc).mp hs x))
  refine ⟨⟨d,hd⟩,characters_ext a (fun x => ?_)⟩
  exact (descended_apply hr a ⟨d,hd⟩ x).trans (hf x)

theorem kernel_eq_principal : (descend hr a).ker = principal r n := by
  ext c
  change descend hr a c = 0 ↔ ∃ b : Coeff n, ∀ g, c.val g = ((finiteTwist r n g : Coeff n)-1)*b
  constructor
  · intro h
    let w := tameWitness r n hr
    have hk (x : globalKernel r n) : c.val x.val = 0 := by
      rw [← descended_apply hr a c x]
      change (descend hr a c).val _ = 0
      rw [h]
      rfl
    have hres : ∀ x : globalKernel r n, (representative c x.val : Coeff n) =
        (representative (0 : cocycles r n) x.val : Coeff n) := by
      intro x
      simpa only [cast_rep,AddSubgroup.coe_zero,Pi.zero_apply] using hk x
    obtain ⟨b,hb⟩ := (TameResidueCharacter277.restrictions_equal_iff_principal
      (crossed_rep w c) (crossed_rep w 0)).mp hres
    refine ⟨(b : Coeff n),fun g => ?_⟩
    have eq := (TameResidueCharacter277.difference_iff _ _).mp (hb g)
    change (((representative c g - representative (0 : cocycles r n) g : ℤ) : Coeff n)) =
      (((scalar r n g - 1)*b : ℤ) : Coeff n) at eq
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one,cast_rep,scalar_cast,
      AddSubgroup.coe_zero,Pi.zero_apply,sub_zero] using eq
  · rintro ⟨b,hb⟩
    apply characters_ext a
    intro x
    change (descended hr a c).val _ = 0
    rw [descended_apply,hb,(mem_globalKernel_iff r n _).mp x.property]
    simp

/-- The arithmetic symbol identifies strict first cohomology, modulo actual global
coboundaries, with the inverse-twisted subgroup of localized ideal-class characters. -/
noncomputable def strict_class_group_equiv : StrictH1 r n ≃+ characters r n :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq_principal hr a).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (descend hr a) (descend_surjective hr a))

theorem strict_class_group_equiv_apply (c : cocycles r n) (x : globalKernel r n) :
    ((strict_class_group_equiv hr a (QuotientAddGroup.mk c)).val
      (Additive.ofMul (toClassGroup (reciprocity a) x))) = c.val x.val :=
  descended_apply hr a c x

end Reimann.TameStrictCohomology277
