import Reimann.TameRestriction
import Reimann.TameCoefficients

/-!
Normalize a lift of a character by forcing its value on the first dyadic
decomposition group to be zero. The global group need not split over its
quotient. All statements are algebraic; continuity is an additional question
when the groups are profinite.
-/

namespace Reimann.DyadicLift

open Lean.Grind Reimann.Transfer Reimann.TameCoefficients Reimann.TameRestriction

structure Subgroup (P : GroupLaw G) where
  mem : G → Prop
  identity : mem P.zero
  product : ∀ {g h}, mem g → mem h → mem (P.add g h)
  inverse : ∀ {g}, mem g → mem (P.neg g)

/-- The factorization condition says the first decomposition group maps onto
the quotient by the normal kernel. Factors are allowed to be nonunique. -/
structure LocalProduct (P : GroupLaw G) where
  kernel : Subgroup P
  first : Subgroup P
  normal : ∀ g {k}, kernel.mem k → kernel.mem (conjugate P g k)
  factor : ∀ g, ∃ (k : Subtype kernel.mem) (d : Subtype first.mem), P.add k.val d.val = g

variable {G M : Type} [IntModule M] {P : GroupLaw G}
variable {A : Action G M P.add} {T : LocalProduct P}

/-- Character of the kernel, with its equivariance for the global group action. -/
structure Character (T : LocalProduct P) (A : Action G M P.add) where
  value : Subtype T.kernel.mem → M
  additive : ∀ (k l : Subtype T.kernel.mem), value ⟨P.add k.val l.val, T.kernel.product k.property l.property⟩ =
    value k + value l
  equivariant : ∀ g (k : Subtype T.kernel.mem), value ⟨conjugate P g k.val, T.normal g k.property⟩ = A.act g (value k)

def KillsIntersection (f : Character T A) : Prop :=
  ∀ k : Subtype T.kernel.mem, T.first.mem k.val → f.value k = 0

/-- For kd = le the discrepancy between the two kernel factors is in the
first decomposition group as well, since l⁻¹k = ed⁻¹. -/
theorem difference_of_factors {k d l e : G} (h : P.add k d = P.add l e) :
    P.add (P.neg l) k = P.add e (P.neg d) := by
  have he := congrArg (fun z => P.add (P.neg l) (P.add z (P.neg d))) h
  simpa only [P.assoc, P.add_neg, P.add_zero, cancel_inside] using he

theorem factor_value_unique (f : Character T A) (hf : KillsIntersection f)
    (k l : Subtype T.kernel.mem) (d e : Subtype T.first.mem)
    (h : P.add k.val d.val = P.add l.val e.val) : f.value k = f.value l := by
  let diff : Subtype T.kernel.mem :=
    ⟨P.add (P.neg l.val) k.val, T.kernel.product (T.kernel.inverse l.property) k.property⟩
  have hfirst : T.first.mem diff.val := by
    change T.first.mem (P.add (P.neg l.val) k.val)
    rw [difference_of_factors h]
    exact T.first.product e.property (T.first.inverse d.property)
  have hprod : (⟨P.add l.val diff.val, T.kernel.product l.property diff.property⟩ :
      Subtype T.kernel.mem) = k := by
    apply Subtype.ext
    change P.add l.val (P.add (P.neg l.val) k.val) = k.val
    rw [← P.assoc, P.add_neg, P.zero_add]
  have hv := f.additive l diff
  rw [hprod, hf diff hfirst] at hv
  grind

noncomputable def extend (f : Character T A) (g : G) : M :=
  f.value (Classical.choose (T.factor g))

theorem extend_product (f : Character T A) (hf : KillsIntersection f)
    (k : Subtype T.kernel.mem) (d : Subtype T.first.mem) :
    extend f (P.add k.val d.val) = f.value k := by
  let g := P.add k.val d.val
  obtain ⟨e,he⟩ := Classical.choose_spec (T.factor g)
  exact factor_value_unique f hf _ k e d he

theorem extend_restrict (f : Character T A) (hf : KillsIntersection f) (k : Subtype T.kernel.mem) :
    extend f k.val = f.value k := by
  simpa only [P.add_zero] using extend_product f hf k ⟨P.zero,T.first.identity⟩

theorem extend_first_zero (f : Character T A) (hf : KillsIntersection f) (d : Subtype T.first.mem) :
    extend f d.val = 0 := by
  let e : Subtype T.kernel.mem := ⟨P.zero,T.kernel.identity⟩
  have hz := hf e T.first.identity
  simpa only [e,P.zero_add] using (extend_product f hf e d).trans hz

theorem multiply_factors (k d l e : G) :
    P.add (P.add k d) (P.add l e) =
      P.add (P.add k (conjugate P d l)) (P.add d e) := by
  simp only [conjugate, P.assoc, cancel_inside]

/-- The product law follows by conjugating the second kernel factor. No
homomorphic section and no uniqueness of group factorizations are required. -/
theorem extend_cocycle (f : Character T A) (hf : KillsIntersection f)
    (hact : ∀ k : Subtype T.kernel.mem, ∀ x, A.act k.val x = x) :
    Cocycle A (extend f) := by
  intro g h
  obtain ⟨k,d,rfl⟩ := T.factor g
  obtain ⟨l,e,rfl⟩ := T.factor h
  let z : Subtype T.kernel.mem := ⟨conjugate P d.val l.val,T.normal _ l.property⟩
  let kz : Subtype T.kernel.mem := ⟨P.add k.val z.val,T.kernel.product k.property z.property⟩
  let de : Subtype T.first.mem := ⟨P.add d.val e.val,T.first.product d.property e.property⟩
  rw [multiply_factors, extend_product f hf kz de, extend_product f hf k d,
    extend_product f hf l e, A.act_mul, hact k]
  exact (f.additive k z).trans (congrArg (fun y => f.value k + y) (f.equivariant d.val l))

theorem normalized_unique (f : Character T A) (hf : KillsIntersection f) {c : G → M}
    (hc : Cocycle A c) (hk : ∀ k : Subtype T.kernel.mem, c k.val = f.value k)
    (hd : ∀ d : Subtype T.first.mem, c d.val = 0)
    (hact : ∀ k : Subtype T.kernel.mem, ∀ x, A.act k.val x = x) : c = extend f := by
  funext g
  obtain ⟨k,d,rfl⟩ := T.factor g
  rw [hc, hk k, hd d, hact k, extend_product f hf k d]
  grind

def PrincipalOn (A : Action G M P.add) (D : Subgroup P) (c : G → M) : Prop :=
  ∃ b : M, ∀ d : Subtype D.mem, c d.val = delta A b d.val

theorem strict_kills_intersection (f : Character T A) {c : G → M}
    (hk : ∀ k : Subtype T.kernel.mem, c k.val = f.value k)
    (hd : PrincipalOn A T.first c)
    (hact : ∀ k : Subtype T.kernel.mem, ∀ x, A.act k.val x = x) : KillsIntersection f := by
  obtain ⟨b,hb⟩ := hd
  intro k hkd
  rw [← hk k, hb ⟨k.val,hkd⟩]
  change A.act k.val b - b = 0
  rw [hact k, AddCommGroup.sub_self]

theorem normalize_local_primitive (f : Character T A) (hf : KillsIntersection f) {c : G → M}
    (hc : Cocycle A c) (hk : ∀ k : Subtype T.kernel.mem, c k.val = f.value k)
    (b : M) (hb : ∀ d : Subtype T.first.mem, c d.val = delta A b d.val)
    (hact : ∀ k : Subtype T.kernel.mem, ∀ x, A.act k.val x = x) :
    (fun g => c g - delta A b g) = extend f := by
  apply normalized_unique f hf (subtract_cocycles hc (delta_cocycle A b)) _ _ hact
  · intro k
    change c k.val - (A.act k.val b - b) = f.value k
    rw [hk k, hact k]
    grind
  · intro d
    rw [hb d]
    grind

/-- Primitivity on the second dyadic subgroup is tested on all products kd
lying in that subgroup, with a single common primitive. -/
theorem second_principal_iff (f : Character T A) (hf : KillsIntersection f) (second : Subgroup P) :
    PrincipalOn A second (extend f) ↔
      ∃ b : M, ∀ (k : Subtype T.kernel.mem) (d : Subtype T.first.mem),
        second.mem (P.add k.val d.val) → f.value k = delta A b (P.add k.val d.val) := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b, fun k d hkd => ?_⟩
    exact (extend_product f hf k d).symm.trans (hb ⟨_, hkd⟩)
  · rintro ⟨b,hb⟩
    refine ⟨b, fun s => ?_⟩
    obtain ⟨k,d,hkd⟩ := T.factor s.val
    rw [← hkd, extend_product f hf k d]
    exact hb k d (hkd.symm ▸ s.property)

/-- A global lift restricting to principal cocycles at both places exists
exactly when the character kills the first intersection and the second
factor test admits a common primitive. -/
theorem strict_lift_iff (f : Character T A) (second : Subgroup P)
    (hact : ∀ k : Subtype T.kernel.mem, ∀ x, A.act k.val x = x) :
    (∃ c : G → M, Cocycle A c ∧ (∀ k : Subtype T.kernel.mem, c k.val = f.value k) ∧
      PrincipalOn A T.first c ∧ PrincipalOn A second c) ↔
    KillsIntersection f ∧ ∃ b : M, ∀ (k : Subtype T.kernel.mem) (d : Subtype T.first.mem),
      second.mem (P.add k.val d.val) → f.value k = delta A b (P.add k.val d.val) := by
  constructor
  · rintro ⟨c,hc,hk,hd,hs⟩
    have hf := strict_kills_intersection f hk hd hact
    obtain ⟨v,hv⟩ := hd
    obtain ⟨w,hw⟩ := hs
    have he := normalize_local_primitive f hf hc hk v hv hact
    refine ⟨hf, (second_principal_iff f hf second).mp ⟨w-v, fun s => ?_⟩⟩
    rw [← he, delta_sub]
    exact congrArg (fun t => t - delta A v s.val) (hw s)
  · rintro ⟨hf,hs⟩
    refine ⟨extend f, extend_cocycle f hf hact, extend_restrict f hf,
      ⟨0, fun d => ?_⟩, (second_principal_iff f hf second).mpr hs⟩
    rw [extend_first_zero f hf, delta, action_zero]
    grind

def factor_projection (T : LocalProduct P) (p : Subtype T.kernel.mem × Subtype T.first.mem) : G :=
  P.add p.1.val p.2.val

/-- Continuity descends along the multiplication quotient K × D → P.
For profinite P and closed K,D this surjective map is quotient by compactness
and Hausdorffness. The topological inputs are written using open predicates. -/
theorem continuous_quotient_descent (f : Character T A) (hf : KillsIntersection f)
    (openGlobal : (G → Prop) → Prop)
    (openProduct : ((Subtype T.kernel.mem × Subtype T.first.mem) → Prop) → Prop)
    (openCoeff : (M → Prop) → Prop)
    (quotientOpen : ∀ U, openProduct (fun p => U (factor_projection T p)) → openGlobal U)
    (continuousFirst : ∀ U, openCoeff U → openProduct (fun p => U (f.value p.1))) :
    ∀ U, openCoeff U → openGlobal (fun g => U (extend f g)) := by
  intro U hU
  apply quotientOpen
  have he : (fun p => U (extend f (factor_projection T p))) =
      (fun p : Subtype T.kernel.mem × Subtype T.first.mem => U (f.value p.1)) := by
    funext p
    rw [factor_projection, extend_product f hf p.1 p.2]
  rw [he]
  exact continuousFirst U hU

end Reimann.DyadicLift
