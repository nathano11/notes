import Reimann.DyadicArtinCommutator69

/-! Arithmetic Frobenius is characterized by x ↦ x^q modulo the chosen
prime. Its conjugation law is derived before taking the Artin quotient. -/

namespace Reimann.DyadicArtinFrobenius69

open Lean.Grind
open Reimann.Transfer Reimann.TameRestriction Reimann.DyadicLift Reimann.DyadicPlaceProduct
open Reimann.DyadicArtinCommutator69

variable {Ω R : Type} {G : GroupLaw Ω} [CommRing R]

structure RingAction (G : GroupLaw Ω) (R : Type) [CommRing R] where
  act : Ω → R → R
  identity : ∀ x, act G.zero x = x
  compose : ∀ g h x, act (G.add g h) x = act g (act h x)
  sub_map : ∀ g x y, act g (x-y) = act g x - act g y
  one_map : ∀ g, act g 1 = 1
  mul_map : ∀ g x y, act g (x*y) = act g x * act g y

theorem act_inverse_left (A : RingAction G R) (d : Ω) (x : R) :
    A.act (G.neg d) (A.act d x) = x := by rw [← A.compose,G.neg_add,A.identity]

theorem act_inverse_right (A : RingAction G R) (d : Ω) (x : R) :
    A.act d (A.act (G.neg d) x) = x := by rw [← A.compose,G.add_neg,A.identity]

theorem act_pow (A : RingAction G R) (d : Ω) (x : R) (n : Nat) :
    A.act d (x^n) = (A.act d x)^n := by
  induction n with
  | zero => simpa only [Semiring.pow_zero] using A.one_map d
  | succ n ih => rw [Semiring.pow_succ,Semiring.pow_succ,A.mul_map,ih]

/-- The transported prime dP is specified through inverse image of membership. -/
def push (A : RingAction G R) (d : Ω) (P : R → Prop) (x : R) : Prop := P (A.act (G.neg d) x)

theorem push_image (A : RingAction G R) (d : Ω) (P : R → Prop) (x : R) :
    push A d P (A.act d x) ↔ P x := by unfold push; rw [act_inverse_left]

def Stabilizes (A : RingAction G R) (P : R → Prop) (f : Ω) : Prop :=
  ∀ x, P (A.act f x) ↔ P x

/-- The norm q is the size of the base residue field. -/
def IsFrobenius (A : RingAction G R) (P : R → Prop) (q : Nat) (f : Ω) : Prop :=
  Stabilizes A P f ∧ ∀ x, P (A.act f x - x^q)

def InInertia (A : RingAction G R) (P : R → Prop) (f : Ω) : Prop :=
  Stabilizes A P f ∧ ∀ x, P (A.act f x - x)

theorem act_conjugate_at_image (A : RingAction G R) (d f : Ω) (x : R) :
    A.act (conjugate G d f) (A.act d x) = A.act d (A.act f x) := by
  rw [← A.compose, conjugate_times, A.compose]

theorem stabilizes_push (A : RingAction G R) (d f : Ω) (P : R → Prop)
    (hf : Stabilizes A P f) : Stabilizes A (push A d P) (conjugate G d f) := by
  intro y
  have h (x : R) : push A d P (A.act (conjugate G d f) (A.act d x)) ↔ push A d P (A.act d x) := by
    rw [act_conjugate_at_image, push_image, push_image]
    exact hf x
  simpa only [act_inverse_right] using h (A.act (G.neg d) y)

theorem frobenius_push (A : RingAction G R) (d f : Ω) (P : R → Prop) (q : Nat)
    (hf : IsFrobenius A P q f) : IsFrobenius A (push A d P) q (conjugate G d f) := by
  refine ⟨stabilizes_push A d f P hf.1, ?_⟩
  intro y
  have h (x : R) : push A d P (A.act (conjugate G d f) (A.act d x) - (A.act d x)^q) := by
    rw [act_conjugate_at_image, ← act_pow, ← A.sub_map, push_image]
    exact hf.2 x
  simpa only [act_inverse_right] using h (A.act (G.neg d) y)

theorem stabilizes_inverse (A : RingAction G R) (P : R → Prop) (f : Ω)
    (hf : Stabilizes A P f) : Stabilizes A P (G.neg f) := by
  intro x
  simpa only [act_inverse_right] using (hf (A.act (G.neg f) x)).symm

theorem stabilizes_product (A : RingAction G R) (P : R → Prop) (f g : Ω)
    (hf : Stabilizes A P f) (hg : Stabilizes A P g) : Stabilizes A P (G.add f g) := by
  intro x
  rw [A.compose]
  exact (hf (A.act g x)).trans (hg x)

theorem difference_in_inertia (A : RingAction G R) (P : R → Prop) (q : Nat) (f g : Ω)
    (closed : ∀ x y, P x → P y → P (x-y))
    (hf : IsFrobenius A P q f) (hg : IsFrobenius A P q g) :
    InInertia A P (G.add (G.neg g) f) := by
  refine ⟨stabilizes_product A P _ _ (stabilizes_inverse A P g hg.1) hf.1, ?_⟩
  intro x
  apply (hg.1 _).mp
  rw [A.sub_map, A.compose, act_inverse_right]
  have h := closed _ _ (hf.2 x) (hg.2 x)
  have he : (A.act f x-x^q) - (A.act g x-x^q) = A.act f x - A.act g x := by grind
  exact he ▸ h

theorem frobenius_unique (A : RingAction G R) (N : Subgroup G) (P : R → Prop) (q : Nat)
    (closed : ∀ x y, P x → P y → P (x-y))
    (unramified : ∀ u : Subtype N.mem, InInertia A P u.val → u.val = G.zero)
    (f g : Subtype N.mem) (hf : IsFrobenius A P q f.val) (hg : IsFrobenius A P q g.val) :
    f.val = g.val := by
  have hz := unramified ⟨_, N.product (N.inverse g.property) f.property⟩
    (difference_in_inertia A P q _ _ closed hf hg)
  have he := congrArg (G.add g.val) hz
  change G.add g.val (G.add (G.neg g.val) f.val) = G.add g.val G.zero at he
  simpa only [← G.assoc, G.add_neg, G.zero_add, G.add_zero] using he

theorem push_sub (A : RingAction G R) (d : Ω) (P : R → Prop)
    (closed : ∀ x y, P x → P y → P (x-y)) (x y : R)
    (hx : push A d P x) (hy : push A d P y) : push A d P (x-y) := by
  unfold push at *
  rw [A.sub_map]
  exact closed _ _ hx hy

theorem frobenius_natural (A : RingAction G R) (N : Subgroup G) (d : Ω) (P : R → Prop) (q : Nat)
    (hn : ∀ x : Subtype N.mem, N.mem (conjugate G d x.val))
    (closed : ∀ x y, P x → P y → P (x-y))
    (unramified : ∀ u : Subtype N.mem, InInertia A (push A d P) u.val → u.val = G.zero)
    (f g : Subtype N.mem) (hf : IsFrobenius A P q f.val)
    (hg : IsFrobenius A (push A d P) q g.val) : g.val = conjugate G d f.val :=
  frobenius_unique A N _ q (push_sub A d P closed) unramified g ⟨_, hn f⟩ hg
    (frobenius_push A d _ P q hf)

/-- Two selections of relative Frobenius at transported primes, with the same
base residue norm. The only uniqueness input is relative unramifiedness. -/
structure PrimePair (A : RingAction G R) (N : Subgroup G) (d : Ω) where
  prime : R → Prop
  norm : Nat
  source : Subtype N.mem
  target : Subtype N.mem
  sub_mem : ∀ x y, prime x → prime y → prime (x-y)
  sourceFrob : IsFrobenius A prime norm source.val
  targetFrob : IsFrobenius A (push A d prime) norm target.val
  unramified : ∀ u : Subtype N.mem, InInertia A (push A d prime) u.val → u.val = G.zero

theorem prime_transport (A : RingAction G R) (N : Subgroup G) (d : Ω)
    (hn : ∀ x : Subtype N.mem, N.mem (conjugate G d x.val)) (p : PrimePair A N d) :
    p.target = (ambientConjugation N d hn).app p.source :=
  Subtype.ext (frobenius_natural A N d p.prime p.norm hn p.sub_mem p.unramified
    p.source p.target p.sourceFrob p.targetFrob)

/-- A signed word presents a fractional ideal supported on the specified
unramified primes. A true flag selects inverse Frobenius. -/
def word {I S : Type} (H : GroupLaw S) (F : I → S) : List (I × Bool) → S
  | [] => H.zero
  | (i, inv)::w => H.add (if inv then H.neg (F i) else F i) (word H F w)

theorem word_hom {I S T : Type} {H : GroupLaw S} {K : GroupLaw T} (φ : Hom H K)
    (F : I → S) (w : List (I × Bool)) :
    φ.app (word H F w) = word K (fun i => φ.app (F i)) w := by
  induction w with
  | nil => exact φ.preserves_zero
  | cons p w ih =>
    obtain ⟨i, b⟩ := p
    cases b <;> simp only [word, Bool.false_eq_true, ↓reduceIte, φ.preserves_add, φ.preserves_neg, ih]

theorem frobenius_words {I : Type} (A : RingAction G R) (N : Subgroup G) (d : Ω)
    (hn : ∀ x : Subtype N.mem, N.mem (conjugate G d x.val)) (p : I → PrimePair A N d)
    (w : List (I × Bool)) :
    word (subgroupLaw N) (fun i => (p i).target) w =
      (ambientConjugation N d hn).app (word (subgroupLaw N) (fun i => (p i).source) w) := by
  rw [word_hom]
  exact congrArg (fun F => word (subgroupLaw N) F w)
    (funext (fun i => prime_transport A N d hn (p i)))

theorem arithmetic_commutator {I : Type} (A : RingAction G R) (N : Subgroup G)
    (D : Subgroup (subgroupLaw N)) (hD : Normal D) (d : Ω)
    (hn : ∀ x : Subtype N.mem, N.mem (conjugate G d x.val)) (p : I → PrimePair A N d)
    (w : List (I × Bool)) :
    cls D (commInN N (word (subgroupLaw N) (fun i => (p i).source) w) d hn) =
      (targetLaw D hD).add (cls D (word (subgroupLaw N) (fun i => (p i).source) w))
        ((targetLaw D hD).neg (cls D (word (subgroupLaw N) (fun i => (p i).target) w))) := by
  rw [class_commutator, ← frobenius_words A N d hn p w]

/-- Inverting the chosen arithmetic Artin element changes b-tb into
-b+tb. The target prime word still uses the arithmetic residue-power convention. -/
theorem inverse_arithmetic_commutator {I : Type} (A : RingAction G R) (N : Subgroup G)
    (D : Subgroup (subgroupLaw N)) (hD : Normal D) (d : Ω)
    (hn : ∀ x : Subtype N.mem, N.mem (conjugate G d x.val)) (p : I → PrimePair A N d)
    (w : List (I × Bool)) :
    cls D (commInN N ((subgroupLaw N).neg (word (subgroupLaw N) (fun i => (p i).source) w)) d hn) =
      (targetLaw D hD).add ((targetLaw D hD).neg (cls D (word (subgroupLaw N) (fun i => (p i).source) w)))
        (cls D (word (subgroupLaw N) (fun i => (p i).target) w)) := by
  rw [class_commutator N D hD, (ambientConjugation N d hn).preserves_neg, ← frobenius_words A N d hn p w]
  change (targetLaw D hD).add _ ((targetLaw D hD).neg ((targetLaw D hD).neg
    (cls D (word (subgroupLaw N) (fun i => (p i).target) w)))) = _
  rw [inverse_inverse]
  rfl

/-- For a prime ideal P this is its residue quotient. -/
abbrev Residue (P : R → Prop) := Quot (fun x y : R => P (x-y))

def transportResidue (A : RingAction G R) (d : Ω) (P : R → Prop) :
    Residue P → Residue (push A d P) :=
  Quot.lift (fun x => Quot.mk _ (A.act d x)) (by
    intro x y h
    apply Quot.sound
    change push A d P (A.act d x - A.act d y)
    rw [← A.sub_map, push_image]
    exact h)

def returnResidue (A : RingAction G R) (d : Ω) (P : R → Prop) :
    Residue (push A d P) → Residue P :=
  Quot.lift (fun x => Quot.mk _ (A.act (G.neg d) x)) (by
    intro x y h
    apply Quot.sound
    change P (A.act (G.neg d) x - A.act (G.neg d) y)
    rw [← A.sub_map]
    exact h)

theorem residue_bijection (A : RingAction G R) (d : Ω) (P : R → Prop) :
    (∀ z, returnResidue A d P (transportResidue A d P z) = z) ∧
      (∀ z, transportResidue A d P (returnResidue A d P z) = z) := by
  constructor
  · intro z
    induction z using Quot.ind with | _ x =>
      exact congrArg (Quot.mk _) (act_inverse_left A d x)
  · intro z
    induction z using Quot.ind with | _ x =>
      exact congrArg (Quot.mk _) (act_inverse_right A d x)

theorem residue_power_transport (A : RingAction G R) (d : Ω) (P : R → Prop) (x : R) (q : Nat) :
    transportResidue A d P (Quot.mk _ (x^q)) = Quot.mk _ ((A.act d x)^q) :=
  congrArg (Quot.mk _) (act_pow A d x q)

theorem hom_conjugate {S T : Type} {H : GroupLaw S} {K : GroupLaw T}
    (φ : Hom H K) (d x : S) : φ.app (conjugate H d x) = conjugate K (φ.app d) (φ.app x) := by
  simp only [conjugate, φ.preserves_add, φ.preserves_neg]

/-- Ambient extension, relative subgroup, normal Artin kernel, and prime
data for one level. Its chosen lift normalizes both subgroup and kernel. -/
structure ArtinLevel (I : Type) where
  groupType : Type
  law : GroupLaw groupType
  integers : Type
  ring : CommRing integers
  action : @RingAction groupType law integers ring
  N : Subgroup law
  D : Subgroup (subgroupLaw N)
  normal : Normal D
  d : groupType
  normalizeN : ∀ x : Subtype N.mem, N.mem (conjugate law d x.val)
  normalizeD : ∀ a : Subtype D.mem, D.mem ((ambientConjugation N d normalizeN).app a.val)
  prime : I → @PrimePair groupType integers law ring action N d

structure LevelRestriction {I : Type} (U L : ArtinLevel I) where
  map : Hom U.law L.law
  mapsN : ∀ x : Subtype U.N.mem, L.N.mem (map.app x.val)
  mapsD : ∀ a : Subtype U.D.mem, L.D.mem ⟨map.app a.val.val, mapsN a.val⟩
  lift : map.app U.d = L.d

def restrictN {I : Type} {U L : ArtinLevel I} (f : LevelRestriction U L) :
    Hom (subgroupLaw U.N) (subgroupLaw L.N) where
  app x := ⟨f.map.app x.val, f.mapsN x⟩
  preserves_zero := Subtype.ext f.map.preserves_zero
  preserves_add x y := Subtype.ext (f.map.preserves_add x.val y.val)
  preserves_neg x := Subtype.ext (f.map.preserves_neg x.val)

def restrictClass {I : Type} {U L : ArtinLevel I} (f : LevelRestriction U L) :
    Hom (targetLaw U.D U.normal) (targetLaw L.D L.normal) :=
  let r := restrictN f
  let φ : Hom (subgroupLaw U.N) (targetLaw L.D L.normal) := {
    app := fun x => cls L.D (r.app x)
    preserves_zero := congrArg (cls L.D) r.preserves_zero
    preserves_add := fun x y => congrArg (cls L.D) (r.preserves_add x y)
    preserves_neg := fun x => congrArg (cls L.D) (r.preserves_neg x) }
  descend U.D U.normal φ (fun a => (projection_kernel L.D _).mpr (f.mapsD a))

def levelAction {I : Type} (L : ArtinLevel I) :
    Hom (targetLaw L.D L.normal) (targetLaw L.D L.normal) :=
  induced L.D L.normal (ambientConjugation L.N L.d L.normalizeN) L.normalizeD

theorem restriction_action {I : Type} {U L : ArtinLevel I} (f : LevelRestriction U L)
    (z : Target U.D) :
    (restrictClass f).app ((levelAction U).app z) = (levelAction L).app ((restrictClass f).app z) := by
  induction z using Quotient.inductionOn with | _ x =>
    apply congrArg (cls L.D)
    apply Subtype.ext
    change f.map.app (conjugate U.law U.d x.val) = conjugate L.law L.d (f.map.app x.val)
    rw [hom_conjugate, f.lift]

def sourceClass {I : Type} (L : ArtinLevel I) (w : List (I × Bool)) : Target L.D := by
  letI := L.ring
  exact cls L.D (word (subgroupLaw L.N) (fun i => (L.prime i).source) w)

def targetClass {I : Type} (L : ArtinLevel I) (w : List (I × Bool)) : Target L.D := by
  letI := L.ring
  exact cls L.D (word (subgroupLaw L.N) (fun i => (L.prime i).target) w)

theorem level_transport {I : Type} (L : ArtinLevel I) (w : List (I × Bool)) :
    targetClass L w = (levelAction L).app (sourceClass L w) := by
  letI := L.ring
  exact congrArg (cls L.D) (frobenius_words L.action L.N L.d L.normalizeN L.prime w)

/-- In a tower, source Artin classes may be coherent without their chosen
nonabelian Frobenius representatives being compatible. Coherence descends
on quotient classes and also holds for their transported prime words. -/
theorem coherent_artin_classes {I : Type} (L : Nat → ArtinLevel I)
    (r : ∀ n, LevelRestriction (L (n+1)) (L n)) (w : Nat → List (I × Bool))
    (h : ∀ n, (restrictClass (r n)).app (sourceClass (L (n+1)) (w (n+1))) = sourceClass (L n) (w n)) :
    ∀ n, (restrictClass (r n)).app (targetClass (L (n+1)) (w (n+1))) = targetClass (L n) (w n) := by
  intro n
  rw [level_transport, restriction_action, h, level_transport]

theorem coherent_commutator {I : Type} (L : Nat → ArtinLevel I)
    (r : ∀ n, LevelRestriction (L (n+1)) (L n)) (w : Nat → List (I × Bool))
    (h : ∀ n, (restrictClass (r n)).app (sourceClass (L (n+1)) (w (n+1))) = sourceClass (L n) (w n)) :
    let c n := cls (L n).D (commInN (L n).N
      (word (subgroupLaw (L n).N) (fun i => (@PrimePair.source _ _ _ (L n).ring _ _ _ ((L n).prime i))) (w n)) (L n).d (L n).normalizeN)
    ∀ n, (restrictClass (r n)).app (c (n+1)) = c n := by
  let diff (n : Nat) := (targetLaw (L n).D (L n).normal).add
    (sourceClass (L n) (w n)) ((targetLaw (L n).D (L n).normal).neg (targetClass (L n) (w n)))
  have hdiff (n : Nat) : cls (L n).D (commInN (L n).N
      (word (subgroupLaw (L n).N) (fun i => (@PrimePair.source _ _ _ (L n).ring _ _ _ ((L n).prime i))) (w n)) (L n).d (L n).normalizeN) = diff n := by
    letI := (L n).ring
    exact arithmetic_commutator (L n).action (L n).N (L n).D (L n).normal (L n).d
      (L n).normalizeN (L n).prime (w n)
  dsimp only
  intro n
  rw [hdiff (n+1), hdiff n]
  unfold diff
  rw [(restrictClass (r n)).preserves_add, (restrictClass (r n)).preserves_neg, h,
    coherent_artin_classes L r w h]

structure IsPrimeIdeal (P : R → Prop) : Prop where
  zero_mem : P 0
  proper : ¬ P 1
  sub_mem : ∀ x y, P x → P y → P (x-y)
  absorb : ∀ x y, P x → P (x*y)
  prime : ∀ x y, P (x*y) → P x ∨ P y

theorem push_prime (A : RingAction G R) (d : Ω) (P : R → Prop) (hP : IsPrimeIdeal P) :
    IsPrimeIdeal (push A d P) := by
  have hz : A.act (G.neg d) 0 = 0 := by
    have h := A.sub_map (G.neg d) (1 : R) 1
    have self (x : R) : x-x=0 := by grind
    simpa only [self] using h
  constructor
  · change P (A.act (G.neg d) 0)
    rw [hz]
    exact hP.zero_mem
  · change ¬ P (A.act (G.neg d) 1)
    rw [A.one_map]
    exact hP.proper
  · exact push_sub A d P hP.sub_mem
  · intro x y hx
    change P (A.act (G.neg d) (x*y))
    rw [A.mul_map]
    exact hP.absorb _ _ hx
  · intro x y hxy
    change P (A.act (G.neg d) (x*y)) at hxy
    rw [A.mul_map] at hxy
    exact hP.prime _ _ hxy

/-- The base prime has norm q when its residue classes are enumerated by Fin q. -/
def HasNorm (p : R → Prop) (q : Nat) : Prop :=
  ∃ e : Residue p → Fin q, ∃ s : Fin q → Residue p,
    (∀ x, s (e x) = x) ∧ (∀ i, e (s i) = i)

theorem base_norm_transport (A : RingAction G R) (d : Ω) (p : R → Prop) (q : Nat)
    (h : HasNorm p q) : HasNorm (push A d p) q := by
  obtain ⟨e, s, h₁, h₂⟩ := h
  obtain ⟨hl, hr⟩ := residue_bijection A d p
  refine ⟨fun y => e (returnResidue A d p y), fun i => transportResidue A d p (s i), ?_, ?_⟩
  · intro y
    exact (congrArg (transportResidue A d p) (h₁ _)).trans (hr y)
  · intro i
    exact (congrArg e (hl _)).trans (h₂ i)

/-- Under an equivariant inclusion of base integers into extension integers,
contraction carries the transported upper prime to the transported base prime. -/
theorem push_contraction {S : Type} [CommRing S] (A : RingAction G R) (B : RingAction G S)
    (includeBase : S → R) (equivariant : ∀ f x, A.act f (includeBase x) = includeBase (B.act f x))
    (d : Ω) (P : R → Prop) :
    (fun x => push A d P (includeBase x)) = push B d (fun x => P (includeBase x)) := by
  funext x
  unfold push
  rw [equivariant]

theorem contracted_norm_transport {S : Type} [CommRing S] (A : RingAction G R) (B : RingAction G S)
    (includeBase : S → R) (equivariant : ∀ f x, A.act f (includeBase x) = includeBase (B.act f x))
    (d : Ω) (P : R → Prop) (q : Nat) (h : HasNorm (fun x => P (includeBase x)) q) :
    HasNorm (fun x => push A d P (includeBase x)) q := by
  rw [push_contraction A B includeBase equivariant d P]
  exact base_norm_transport B d _ q h

/-- Frobenius at dP lies over the base prime of norm q and is the conjugate
of Frobenius at P. No equivariance assumption on Frobenius is used. -/
theorem unramified_prime_transport {S : Type} [CommRing S] (A : RingAction G R) (B : RingAction G S)
    (includeBase : S → R) (equivariant : ∀ f x, A.act f (includeBase x) = includeBase (B.act f x))
    (N : Subgroup G) (d : Ω) (P : R → Prop) (hP : IsPrimeIdeal P) (q : Nat)
    (hbase : HasNorm (fun x => P (includeBase x)) q)
    (hn : ∀ x : Subtype N.mem, N.mem (conjugate G d x.val))
    (unramified : ∀ u : Subtype N.mem, InInertia A (push A d P) u.val → u.val = G.zero)
    (f g : Subtype N.mem) (hf : IsFrobenius A P q f.val) (hg : IsFrobenius A (push A d P) q g.val) :
    IsPrimeIdeal (push A d P) ∧ HasNorm (fun x => push A d P (includeBase x)) q ∧
      g.val = conjugate G d f.val :=
  ⟨push_prime A d P hP, contracted_norm_transport A B includeBase equivariant d P q hbase,
    frobenius_natural A N d P q hn hP.sub_mem unramified f g hf hg⟩

theorem inverse_word {I S : Type} (H : GroupLaw S) (hc : ∀ x y, H.add x y = H.add y x)
    (F : I → S) (w : List (I × Bool)) :
    word H (fun i => H.neg (F i)) w = H.neg (word H F w) := by
  induction w with
  | nil =>
    change H.zero = H.neg H.zero
    exact (H.zero_add _).symm.trans (H.add_neg _)
      |>.symm
  | cons p w ih =>
    obtain ⟨i, b⟩ := p
    cases b <;> simp only [word, Bool.false_eq_true, ↓reduceIte, ih, inverse_product, inverse_inverse] <;>
      apply hc

/-- Replacing each local arithmetic symbol by its inverse negates the whole
Artin class after abelianization, even for a noncommutative relative group. -/
theorem geometric_word_class {I S : Type} {H : GroupLaw S}
    (D : Subgroup H) (hD : Normal D) (hc : ∀ x y, D.mem (commutator H x y))
    (F : I → S) (w : List (I × Bool)) :
    cls D (word H (fun i => H.neg (F i)) w) = (targetLaw D hD).neg (cls D (word H F w)) := by
  let π := projection D hD
  change π.app (word H _ w) = (targetLaw D hD).neg (π.app (word H F w))
  rw [word_hom, word_hom]
  change word (targetLaw D hD) (fun i => (targetLaw D hD).neg (π.app (F i))) w = _
  exact inverse_word _ (target_comm D hD hc) _ w

theorem geometric_artin_commutator {I : Type} (A : RingAction G R) (N : Subgroup G)
    (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (hc : ∀ x y, D.mem (commutator (subgroupLaw N) x y)) (d : Ω)
    (hn : ∀ x : Subtype N.mem, N.mem (conjugate G d x.val)) (p : I → PrimePair A N d)
    (w : List (I × Bool)) :
    cls D (commInN N (word (subgroupLaw N) (fun i => (subgroupLaw N).neg (p i).source) w) d hn) =
      (targetLaw D hD).add ((targetLaw D hD).neg (cls D (word (subgroupLaw N) (fun i => (p i).source) w)))
        (cls D (word (subgroupLaw N) (fun i => (p i).target) w)) := by
  let φ := ambientConjugation N d hn
  have hmove : φ.app (word (subgroupLaw N) (fun i => (subgroupLaw N).neg (p i).source) w) =
      word (subgroupLaw N) (fun i => (subgroupLaw N).neg (p i).target) w := by
    rw [word_hom]
    apply congrArg (fun F => word (subgroupLaw N) F w)
    funext i
    rw [φ.preserves_neg, prime_transport A N d hn (p i)]
  rw [class_commutator N D hD]
  change (targetLaw D hD).add _ ((targetLaw D hD).neg (cls D (φ.app _))) = _
  rw [hmove, geometric_word_class D hD hc, geometric_word_class D hD hc, inverse_inverse]

end Reimann.DyadicArtinFrobenius69
