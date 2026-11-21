import Reimann.TameStrictInterface

namespace Reimann.TameAdditivity

open Transfer TameRestriction TameStrictInterface

variable {G B : Type} {P : GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} {L : Places T} {H : GroupLaw B}

/-- Values add on all class elements whenever the representatives add modulo m
on the kernel. The weaker kernel hypothesis follows in particular from
pointwise addition on the whole source group. -/
theorem descended_sum_on_representatives (A : ArtinData L H) (c d s : StrictRep A)
    (hs : ∀ x : Subtype T.kernel, m ∣ s.value x.val - (c.value x.val + d.value x.val))
    (b : B) : ((toClassCharacter A (Quot.mk _ s)).val.app b).val =
      (((toClassCharacter A (Quot.mk _ c)).val.app b).val +
        ((toClassCharacter A (Quot.mk _ d)).val.app b).val) % m := by
  obtain ⟨x,rfl⟩ := A.quotient.onto b
  change ((descendStrict A s.crossed s.strict s.admissible).val.app _).val =
    (((descendStrict A c.crossed c.strict c.admissible).val.app _).val +
     ((descendStrict A d.crossed d.strict d.admissible).val.app _).val) % m
  rw [descend_evaluates, descend_evaluates, descend_evaluates]
  exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.emod_eq_zero_of_dvd (hs x))).trans (Int.add_emod _ _ _)

theorem crossed_add {c d : G → Int} (hc : Crossed T c) (hd : Crossed T d) :
    Crossed T (fun g => c g+d g) := by
  intro g h
  obtain ⟨x,hx⟩ := hc g h
  obtain ⟨y,hy⟩ := hd g h
  exact ⟨x+y, by grind⟩

theorem strict_add {c d : G → Int} (hc : Strict L c) (hd : Strict L d) :
    Strict L (fun g => c g+d g) := by
  intro v
  obtain ⟨a,ha⟩ := hc v
  obtain ⟨b,hb⟩ := hd v
  refine ⟨a+b,?_⟩
  intro x
  obtain ⟨i,hi⟩ := ha x
  obtain ⟨j,hj⟩ := hb x
  exact ⟨i+j, by grind⟩

theorem coefficient_interchange (a b c d : {z : Int // z%m=z}) :
    (TameClassField.residueGroup m).add ((TameClassField.residueGroup m).add a b)
      ((TameClassField.residueGroup m).add c d) =
    (TameClassField.residueGroup m).add ((TameClassField.residueGroup m).add a c)
      ((TameClassField.residueGroup m).add b d) := by
  apply Subtype.ext
  simp [TameClassField.residueGroup]
  apply congrArg (· % m)
  omega

def addHom (χ ψ : Hom H (TameClassField.residueGroup m)) :
    Hom H (TameClassField.residueGroup m) := by
  let R := TameClassField.residueGroup m
  let F := fun b => R.add (χ.app b) (ψ.app b)
  have hz : F H.zero = R.zero := by
    dsimp only [F]; rw [χ.preserves_zero, ψ.preserves_zero, R.zero_add]
  have ha (b c) : F (H.add b c) = R.add (F b) (F c) := by
    dsimp only [F]
    rw [χ.preserves_add, ψ.preserves_add]
    exact coefficient_interchange _ _ _ _
  refine ⟨F,hz,ha,?_⟩
  intro x
  apply right_cancel R _ _ (F x)
  rw [← ha,H.neg_add,hz,R.neg_add]

/-- An admissible strict sum follows from the Artin pullback property, even
when admissibility has no closure postulate for sums of arbitrary characters. -/
theorem admissible_add (A : ArtinData L H) (c d : StrictRep A) :
    A.admissible (characterHom (restrictCharacter (crossed_add c.crossed d.crossed))) := by
  let χ := descendStrict A c.crossed c.strict c.admissible
  let ψ := descendStrict A d.crossed d.strict d.admissible
  apply A.pullback_admissible (addHom χ.val ψ.val)
  intro x
  apply Subtype.ext
  change (c.value x.val + d.value x.val) % m =
    ((χ.val.app (A.quotient.proj.app x)).val+(ψ.val.app (A.quotient.proj.app x)).val)%m
  dsimp only [χ,ψ]
  rw [descend_evaluates, descend_evaluates]
  exact Int.add_emod _ _ _

def addRep (A : ArtinData L H) (c d : StrictRep A) : StrictRep A where
  value g := c.value g+d.value g
  crossed := crossed_add c.crossed d.crossed
  strict := strict_add c.strict d.strict
  admissible := admissible_add A c d

theorem principal_add {a a' b b' : G → Int}
    (ha : PrincipalDifference T a a') (hb : PrincipalDifference T b b') :
    PrincipalDifference T (fun g => a g + b g) (fun g => a' g + b' g) := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  refine ⟨i+j,?_⟩
  intro g
  obtain ⟨u,hu⟩ := hi g
  obtain ⟨v,hv⟩ := hj g
  exact ⟨u+v,by grind⟩

theorem principal_refl (c : G → Int) : PrincipalDifference T c c :=
  ⟨0, fun g => by simp⟩

/-- Addition on strict classes descends actual pointwise addition of cocycles. -/
def addClass (A : ArtinData L H) : StrictClass A → StrictClass A → StrictClass A :=
  Quot.lift (fun c => Quot.lift (fun d => (Quot.mk _ (addRep A c d) : StrictClass A))
    (fun d e h => Quot.sound (principal_add (principal_refl c.value) h)))
    (by
      intro c e h
      funext y
      induction y using Quot.ind with
      | mk d => exact Quot.sound (principal_add h (principal_refl d.value)))

theorem descent_add (A : ArtinData L H) (x y : StrictClass A) (b : B) :
    ((toClassCharacter A (addClass A x y)).val.app b).val =
      (((toClassCharacter A x).val.app b).val+((toClassCharacter A y).val.app b).val)%m := by
  induction x using Quot.ind with
  | mk c =>
    induction y using Quot.ind with
    | mk d =>
      exact descended_sum_on_representatives A c d (addRep A c d)
        (fun k => by change m ∣ (c.value k.val+d.value k.val)-(c.value k.val+d.value k.val); simp) b

def addClassCharacter (A : ArtinData L H) (χ ψ : ClassCharacter A) : ClassCharacter A := by
  refine ⟨addHom χ.val ψ.val,?_⟩
  intro g b
  change ((χ.val.app (A.action g b)).val+(ψ.val.app (A.action g b)).val)%m =
    (T.scalar g * (((χ.val.app b).val+(ψ.val.app b).val)%m))%m
  rw [χ.property g b, ψ.property g b, ← Int.add_emod, ← Int.mul_add]
  rw [Int.mul_emod (T.scalar g) (((χ.val.app b).val+(ψ.val.app b).val)%m),
    Int.emod_emod, ← Int.mul_emod]

theorem toCharacter_add (A : ArtinData L H) (x y : StrictClass A) :
    toClassCharacter A (addClass A x y) =
      addClassCharacter A (toClassCharacter A x) (toClassCharacter A y) := by
  apply Subtype.ext
  apply TameClassField.descent_unique A.quotient
  intro k
  exact Subtype.ext (descent_add A x y (A.quotient.proj.app k))

theorem fromCharacter_add (A : ArtinData L H) (χ ψ : ClassCharacter A) :
    fromClassCharacter A (addClassCharacter A χ ψ) =
      addClass A (fromClassCharacter A χ) (fromClassCharacter A ψ) := by
  obtain ⟨left,right⟩ := strict_class_character_roundtrips A
  have h := toCharacter_add A (fromClassCharacter A χ) (fromClassCharacter A ψ)
  rw [right, right] at h
  exact (congrArg (fromClassCharacter A) h.symm).trans (left _)

end Reimann.TameAdditivity
