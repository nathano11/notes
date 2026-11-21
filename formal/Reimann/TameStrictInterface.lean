import Reimann.TameRestriction
import Reimann.TameLocal
import Reimann.TameClassField

namespace Reimann.TameStrictInterface

open Transfer TameRestriction

variable {G B : Type} {P : GroupLaw G} {t : G} {m : Int}

theorem identity_in_kernel (T : TameData P t m) : T.kernel P.zero := by
  have h := T.comm_in P.zero
  simpa only [commutator, P.add_zero, P.add_neg, P.zero_add,
    show P.neg P.zero = P.zero from (P.zero_add _).symm.trans (P.add_neg _)] using h

def kernelGroup (T : TameData P t m) : GroupLaw (Subtype T.kernel) where
  zero := ⟨P.zero, identity_in_kernel T⟩
  add x y := ⟨P.add x.val y.val, T.mul_in x.property y.property⟩
  neg x := ⟨P.neg x.val, T.inv_in x.property⟩
  assoc x y z := Subtype.ext (P.assoc x.val y.val z.val)
  zero_add x := Subtype.ext (P.zero_add x.val)
  add_zero x := Subtype.ext (P.add_zero x.val)
  add_neg x := Subtype.ext (P.add_neg x.val)
  neg_add x := Subtype.ext (P.neg_add x.val)

/-- Canonical coefficient modulo m. -/
def res (m x : Int) : {a : Int // a % m = a} :=
  ⟨x % m, Int.emod_emod _ _⟩

theorem res_eq {x y : Int} : res m x = res m y ↔ m ∣ x-y := by
  constructor
  · intro h
    exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
      (congrArg Subtype.val h))
  · intro h
    exact Subtype.ext (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h))

theorem character_add {T : TameData P t m} (f : KernelCharacter T)
    (x y : Subtype T.kernel) :
    res m (f.value ((kernelGroup T).add x y)) =
    (TameClassField.residueGroup m).add (res m (f.value x)) (res m (f.value y)) := by
  have he := (res_eq.mpr (f.additive x.property y.property))
  apply Subtype.ext
  simpa [res, TameClassField.residueGroup, kernelGroup] using congrArg Subtype.val he

def characterHom {T : TameData P t m} (f : KernelCharacter T) :
    Hom (kernelGroup T) (TameClassField.residueGroup m) := by
  let N := kernelGroup T
  let R := TameClassField.residueGroup m
  let F := fun x => res m (f.value x)
  have ha (x y) : F (N.add x y) = R.add (F x) (F y) := character_add f x y
  have hz : F N.zero = R.zero := by
    apply right_cancel R _ _ (F N.zero)
    rw [← ha, N.zero_add, R.zero_add]
  refine ⟨F,hz,ha,?_⟩
  intro x
  apply right_cancel R _ _ (F x)
  rw [← ha, N.neg_add, hz, R.neg_add]

/-- Local group maps and unit-difference elements. Arithmetic instantiation
supplies the places, their decomposition maps, and membership in the kernel. -/
structure Places (T : TameData P t m) where
  index : Type
  carrier : index → Type
  law : ∀ v, GroupLaw (carrier v)
  embed : ∀ v, Hom (law v) P
  tame : ∀ v, carrier v
  inverse : index → Int
  isUnit : ∀ v, m ∣ inverse v * (T.scalar ((embed v).app (tame v))-1)-1
  comm_in : ∀ v g, T.kernel ((embed v).app
    (TameLocal.swapCommutator (law v).add (law v).neg (tame v) g))

def localPrimeElement {T : TameData P t m} (L : Places T) (v : L.index) (g : L.carrier v) :
    Subtype T.kernel := ⟨_, L.comm_in v g⟩

def Strict {T : TameData P t m} (L : Places T) (c : G → Int) : Prop :=
  ∀ v, TameLocal.Principal m (fun x => T.scalar ((L.embed v).app x))
    (fun x => c ((L.embed v).app x))

theorem strict_iff_commutators {T : TameData P t m} (L : Places T)
    {c : G → Int} (hc : Crossed T c) :
    Strict L c ↔ ∀ v g, m ∣ c (localPrimeElement L v g).val := by
  have test (v : L.index) := TameLocal.principal_iff_vanishes_on_swapCommutators
    (m := m) (mul := (L.law v).add) (inv := (L.law v).neg) (e := (L.law v).zero)
    (a := fun x => T.scalar ((L.embed v).app x)) (c := fun x => c ((L.embed v).app x))
    (fun x y => by simpa only [(L.embed v).preserves_add] using (T.scalar_mul ((L.embed v).app x) ((L.embed v).app y)))
    (fun x y => by simpa only [(L.embed v).preserves_add] using (hc ((L.embed v).app x) ((L.embed v).app y)))
    (by rw [(L.embed v).preserves_zero]; exact T.trivial_on_kernel (identity_in_kernel T))
    (L.law v).assoc (L.law v).add_zero (L.law v).neg_add (L.tame v) (L.isUnit v)
  exact ⟨fun h v => (test v).mp (h v), fun h v => (test v).mpr (h v)⟩

/-- Kernel elements in the images of the supplied local group maps. -/
def LocalKernel {T : TameData P t m} (L : Places T) (x : Subtype T.kernel) : Prop :=
  ∃ v, ∃ g : L.carrier v, (L.embed v).app g = x.val

theorem strict_iff_local_kernel {T : TameData P t m} (L : Places T)
    {c : G → Int} (hc : Crossed T c) :
    Strict L c ↔ ∀ x : Subtype T.kernel, LocalKernel L x → m ∣ c x.val := by
  constructor
  · intro hs x h
    obtain ⟨v,g,hg⟩ := h
    have hk : m ∣ T.scalar ((L.embed v).app g)-1 := hg.symm ▸ T.trivial_on_kernel x.property
    have h0 := TameLocal.principal_vanishes_on_kernel (hs v) g hk
    exact hg ▸ h0
  · intro h
    apply (strict_iff_commutators L hc).mpr
    intro v g
    exact h (localPrimeElement L v g) ⟨v,_,rfl⟩

/-- A supplied Artin quotient. Its kernel test is the arithmetic assertion
that every admissible character trivial on the designated local groups kills
the Artin kernel. In a profinite application admissibility means continuity into
the finite discrete coefficient group. Class character pullbacks must be admissible. -/
structure ArtinData {T : TameData P t m} (L : Places T) (H : GroupLaw B) where
  quotient : TameClassField.ArtinQuotient (kernelGroup T) H
  action : G → B → B
  conjugation : ∀ g (x : Subtype T.kernel),
    quotient.proj.app ⟨conjugate P g x.val, T.conj_in g x.property⟩ =
      action g (quotient.proj.app x)
  local_zero : ∀ x, LocalKernel L x → quotient.proj.app x = H.zero
  admissible : Hom (kernelGroup T) (TameClassField.residueGroup m) → Prop
  pullback_admissible : ∀ (ψ : Hom H (TameClassField.residueGroup m))
    (χ : Hom (kernelGroup T) (TameClassField.residueGroup m)),
    (∀ x, χ.app x = ψ.app (quotient.proj.app x)) → admissible χ
  kernel_test : ∀ χ : Hom (kernelGroup T) (TameClassField.residueGroup m),
    admissible χ → (∀ x, LocalKernel L x → χ.app x = (TameClassField.residueGroup m).zero) →
    TameClassField.KillsKernel quotient χ

variable {T : TameData P t m} {L : Places T} {H : GroupLaw B}

theorem strict_kills_artin (A : ArtinData L H) {c : G → Int}
    (hc : Crossed T c) (hs : Strict L c) (ha : A.admissible (characterHom (restrictCharacter hc))) :
    TameClassField.KillsKernel A.quotient (characterHom (restrictCharacter hc)) := by
  apply A.kernel_test _ ha
  intro x hx
  exact Subtype.ext (Int.emod_eq_zero_of_dvd ((strict_iff_local_kernel L hc).mp hs x hx))

/-- The target uses genuine homomorphisms with a literal twisted action. -/
def ClassCharacter (A : ArtinData L H) :=
  {ψ : Hom H (TameClassField.residueGroup m) //
    ∀ g b, (ψ.app (A.action g b)).val = (T.scalar g*(ψ.app b).val) % m}

noncomputable def descendStrict (A : ArtinData L H) {c : G → Int}
    (hc : Crossed T c) (hs : Strict L c)
    (ha : A.admissible (characterHom (restrictCharacter hc))) : ClassCharacter A := by
  let χ := characterHom (restrictCharacter hc)
  let hk := strict_kills_artin A hc hs ha
  refine ⟨TameClassField.descend A.quotient χ hk, ?_⟩
  intro g b
  apply congrArg Subtype.val
    (TameClassField.descended_equivariance A.quotient χ hk
      (fun x => ⟨conjugate P g x.val,T.conj_in g x.property⟩)
      (A.action g) (fun r => res m (T.scalar g*r.val)) (A.conjugation g) ?_ b)
  intro x
  have he := res_eq.mpr ((restrictCharacter hc).equivariant g x.property)
  apply Subtype.ext
  have hmod (a b : Int) : a*(b%m)%m = a*b%m := by
    rw [Int.mul_emod a (b%m), Int.emod_emod, ← Int.mul_emod]
  simpa [χ,characterHom,res,hmod] using congrArg Subtype.val he

theorem descend_evaluates (A : ArtinData L H) {c : G → Int} (hc : Crossed T c)
    (hs : Strict L c) (ha : A.admissible (characterHom (restrictCharacter hc))) (x : Subtype T.kernel) :
    ((descendStrict A hc hs ha).val.app (A.quotient.proj.app x)).val = c x.val % m :=
  congrArg Subtype.val (TameClassField.descend_projects A.quotient
    (characterHom (restrictCharacter hc)) (strict_kills_artin A hc hs ha) x)

def pullCharacter (A : ArtinData L H) (ψ : ClassCharacter A) : KernelCharacter T where
  value x := (ψ.val.app (A.quotient.proj.app x)).val
  additive := by
    intro x y hx hy
    let a : Subtype T.kernel := ⟨x,hx⟩
    let b : Subtype T.kernel := ⟨y,hy⟩
    change m ∣ (ψ.val.app (A.quotient.proj.app ((kernelGroup T).add a b))).val-_
    rw [A.quotient.proj.preserves_add, ψ.val.preserves_add]
    apply Int.dvd_of_emod_eq_zero
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
    exact Int.emod_emod _ _
  equivariant := by
    intro g x hx
    rw [A.conjugation g ⟨x,hx⟩, ψ.property g (A.quotient.proj.app ⟨x,hx⟩)]
    exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (Int.emod_emod _ _))

theorem lift_is_strict (A : ArtinData L H) (ψ : ClassCharacter A) :
    Strict L (extend (pullCharacter A ψ)) := by
  apply (strict_iff_local_kernel L (extend_crossed _)).mpr
  intro x hx
  have he := extend_restrict (pullCharacter A ψ) x.property
  change m ∣ extend (pullCharacter A ψ) x.val - (ψ.val.app (A.quotient.proj.app x)).val at he
  rw [A.local_zero x hx, ψ.val.preserves_zero] at he
  simpa [TameClassField.residueGroup] using he

/-- The restriction of the normalized lift is the pullback of the finite
class character, so it is admissible by the Artin continuity hypothesis. -/
theorem lift_is_admissible (A : ArtinData L H) (ψ : ClassCharacter A) :
    A.admissible (characterHom (restrictCharacter (extend_crossed (pullCharacter A ψ)))) := by
  apply A.pullback_admissible ψ.val
  intro x
  apply Subtype.ext
  have he := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.emod_eq_zero_of_dvd (extend_restrict (pullCharacter A ψ) x.property))
  exact he.trans (ψ.val.app (A.quotient.proj.app x)).property

/-- Equality of one-cohomology classes is a single global coboundary. -/
def PrincipalDifference (T : TameData P t m) (c d : G → Int) : Prop :=
  ∃ b : Int, ∀ g, m ∣ c g-d g-(T.scalar g-1)*b

theorem descent_fibres (A : ArtinData L H) {c d : G → Int}
    (hc : Crossed T c) (hd : Crossed T d) (sc : Strict L c) (sd : Strict L d)
    (ac : A.admissible (characterHom (restrictCharacter hc)))
    (ad : A.admissible (characterHom (restrictCharacter hd))) :
    descendStrict A hc sc ac = descendStrict A hd sd ad ↔ PrincipalDifference T c d := by
  constructor
  · intro he
    apply (fibres_iff hc hd).mp
    intro g hg
    let x : Subtype T.kernel := ⟨g,hg⟩
    have h := congrArg (fun z : ClassCharacter A => (z.val.app (A.quotient.proj.app x)).val) he
    rw [descend_evaluates, descend_evaluates] at h
    exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)
  · intro he
    apply Subtype.ext
    apply TameClassField.descent_unique A.quotient
    intro x
    apply Subtype.ext
    rw [descend_evaluates, descend_evaluates]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      (Int.emod_eq_zero_of_dvd ((fibres_iff hc hd).mpr he x.val x.property))

theorem descent_of_lift (A : ArtinData L H) (ψ : ClassCharacter A) :
    descendStrict A (extend_crossed (pullCharacter A ψ)) (lift_is_strict A ψ) (lift_is_admissible A ψ) = ψ := by
  apply Subtype.ext
  apply TameClassField.descent_unique A.quotient
  intro x
  apply Subtype.ext
  apply (descend_evaluates A (extend_crossed (pullCharacter A ψ)) (lift_is_strict A ψ) (lift_is_admissible A ψ) x).trans
  have h := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.emod_eq_zero_of_dvd (extend_restrict (pullCharacter A ψ) x.property))
  exact h.trans (ψ.val.app (A.quotient.proj.app x)).property

/-- A representative carries the admissibility of its restricted character,
alongside its global cocycle law and its local conditions. -/
structure StrictRep (A : ArtinData L H) where
  value : G → Int
  crossed : Crossed T value
  strict : Strict L value
  admissible : A.admissible (characterHom (restrictCharacter crossed))

/-- Quotient of locally principal admissible cocycles by global principal differences. -/
def StrictClass (A : ArtinData L H) :=
  Quot (fun a b : StrictRep A => PrincipalDifference T a.value b.value)

noncomputable def toClassCharacter (A : ArtinData L H) : StrictClass A → ClassCharacter A :=
  Quot.lift (fun c => descendStrict A c.crossed c.strict c.admissible)
    (fun c d h => (descent_fibres A c.crossed d.crossed c.strict d.strict c.admissible d.admissible).mpr h)

def fromClassCharacter (A : ArtinData L H) (ψ : ClassCharacter A) : StrictClass A :=
  Quot.mk _ ⟨extend (pullCharacter A ψ), extend_crossed _, lift_is_strict A ψ, lift_is_admissible A ψ⟩

/-- Strict descent for the specified admissibility predicate. For a number
field the Artin quotient, its continuity input, and its kernel test for
continuous characters are supplied by the arithmetic realization. -/
theorem strict_class_character_roundtrips (A : ArtinData L H) :
    (∀ x : StrictClass A, fromClassCharacter A (toClassCharacter A x) = x) ∧
    (∀ ψ : ClassCharacter A, toClassCharacter A (fromClassCharacter A ψ) = ψ) := by
  constructor
  · intro x
    induction x using Quot.ind with
    | mk c =>
      let ψ := descendStrict A c.crossed c.strict c.admissible
      apply Quot.sound
      exact (descent_fibres A (extend_crossed (pullCharacter A ψ)) c.crossed
        (lift_is_strict A ψ) c.strict (lift_is_admissible A ψ) c.admissible).mp (descent_of_lift A ψ)
  · intro ψ
    exact descent_of_lift A ψ

end Reimann.TameStrictInterface
