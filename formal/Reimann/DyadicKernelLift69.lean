import Reimann.DyadicPrimeConjugacy69
import Reimann.DyadicProfiniteLift69

/-! Prime transitivity along a countable normal tower. The orbit norm is
taken in each finite integral order. A compatible family acts on the union
of the fields by evaluating at a finite level containing the given element. -/

namespace Reimann.DyadicKernelLift69

open Lean.Grind
open Reimann.DyadicUnramifiedBase69 (RingMap)
open Reimann.DyadicPrimeConjugacy69 (ResidueMaximal orbitNorm finite_prime_conjugacy)
open Reimann.DyadicProfiniteLift69 (coherent_lifts)

variable {O G F : Nat → Type} {A L : Type} [∀ n, CommRing (O n)]

/-- Finite conjugacy data over a fixed lower order A. The lists may repeat
automorphisms provided the displayed orbit norms still descend. -/
structure FiniteOrbits (A : Type) (O G : Nat → Type) [∀ n, CommRing (O n)] where
  base : ∀ n, A → O n
  all : ∀ n, List (G n)
  contains : ∀ n (g : G n), g ∈ all n
  identity : ∀ n, G n
  act : ∀ n, G n → RingMap (O n) (O n)
  onto : ∀ n g y, ∃ x, (act n g).app x = y
  acts_id : ∀ n x, (act n (identity n)).app x = x
  norm_base : ∀ n x, ∃ a, base n a = orbitNorm (act n) (all n) x

def Conjugates (C : FiniteOrbits A O G) (P Q : ∀ n, O n → Prop) (n : Nat) (g : G n) : Prop :=
  ∀ x, Q n x ↔ P n ((C.act n g).app x)

theorem finite_level_conjugator (C : FiniteOrbits A O G) (P Q : ∀ n, O n → Prop)
    (p : ∀ n, ResidueMaximal (P n)) (q : ∀ n, ResidueMaximal (Q n))
    (same : ∀ n a, P n (C.base n a) ↔ Q n (C.base n a)) (n : Nat) :
    ∃ g ∈ C.all n, Conjugates C P Q n g :=
  finite_prime_conjugacy (C.base n) (p n) (q n) (C.act n) (C.onto n) (C.all n)
    (C.identity n) (C.contains n _) (C.acts_id n) (C.norm_base n) (same n)

/-- One conjugator per level is insufficient until the choices are compatible.
Finite compactness gives a coherent family without surjectivity of the maps
between the sets of conjugators. -/
theorem compatible_prime_conjugators (C : FiniteOrbits A O G) (P Q : ∀ n, O n → Prop)
    (p : ∀ n, ResidueMaximal (P n)) (q : ∀ n, ResidueMaximal (Q n))
    (same : ∀ n a, P n (C.base n a) ↔ Q n (C.base n a))
    (down : ∀ n, G (n+1) → G n)
    (restricts : ∀ n g, Conjugates C P Q (n+1) g → Conjugates C P Q n (down n g)) :
    ∃ s : ∀ n, G n, (∀ n, Conjugates C P Q n (s n)) ∧ ∀ n, down n (s (n+1)) = s n := by
  classical
  let candidates (n : Nat) := (C.all n).filter (fun g => decide (Conjugates C P Q n g))
  have mem (n : Nat) (g : G n) : g ∈ candidates n ↔ Conjugates C P Q n g := by
    simp [candidates,C.contains]
  obtain ⟨s,hs,hd⟩ := coherent_lifts down candidates
    (fun n g hg => (mem n _).mpr (restricts n g ((mem (n+1) g).mp hg))) (by
      intro n
      obtain ⟨g,_,hg⟩ := finite_level_conjugator C P Q p q same n
      exact ⟨g,(mem n g).mpr hg⟩)
  exact ⟨s,fun n => (mem n _).mp (hs n),hd⟩

variable [∀ n, CommRing (F n)] [CommRing L]

/-- This presentation applies to the field union as well as to a ring union.
The maps up and down are adjacent inclusions and automorphism restrictions. -/
structure UnionTower (F G : Nat → Type) (L : Type) [∀ n, CommRing (F n)] [CommRing L] where
  inc : ∀ n, RingMap (F n) L
  inj : ∀ n, Function.Injective (inc n).app
  exhaust : ∀ z : L, ∃ n x, (inc n).app x = z
  up : ∀ n, F n → F (n+1)
  inc_up : ∀ n x, (inc (n+1)).app (up n x) = (inc n).app x
  down : ∀ n, G (n+1) → G n
  act : ∀ n, G n → RingMap (F n) (F n)
  bijective : ∀ n g, Function.Injective (act n g).app ∧ Function.Surjective (act n g).app
  restrict : ∀ n g x, (act (n+1) g).app (up n x) = up n ((act n (down n g)).app x)

theorem raise_representative (T : UnionTower F G L) (s : ∀ n, G n)
    (hs : ∀ n, T.down n (s (n+1)) = s n) {i j : Nat} (hij : i ≤ j) (x : F i) :
    ∃ y : F j, (T.inc j).app y = (T.inc i).app x ∧
      (T.inc j).app ((T.act j (s j)).app y) = (T.inc i).app ((T.act i (s i)).app x) := by
  induction hij with
  | refl => exact ⟨x,rfl,rfl⟩
  | @step j _ ih =>
    obtain ⟨y,hy,he⟩ := ih
    exact ⟨T.up j y,(T.inc_up j y).trans hy,by rw [T.restrict,hs,T.inc_up,he]⟩

theorem representative_independent (T : UnionTower F G L) (s : ∀ n, G n)
    (hs : ∀ n, T.down n (s (n+1)) = s n) {i j : Nat} {x : F i} {y : F j}
    (h : (T.inc i).app x = (T.inc j).app y) :
    (T.inc i).app ((T.act i (s i)).app x) = (T.inc j).app ((T.act j (s j)).app y) := by
  obtain ⟨a,ha,ea⟩ := raise_representative T s hs (Nat.le_max_left i j) x
  obtain ⟨b,hb,eb⟩ := raise_representative T s hs (Nat.le_max_right i j) y
  have hab := T.inj _ (ha.trans (h.trans hb.symm))
  rw [← ea,← eb,hab]

noncomputable def unionValue (T : UnionTower F G L) (s : ∀ n, G n) (z : L) : L :=
  let n := Classical.choose (T.exhaust z)
  let x := Classical.choose (Classical.choose_spec (T.exhaust z))
  (T.inc n).app ((T.act n (s n)).app x)

theorem unionValue_at_level (T : UnionTower F G L) (s : ∀ n, G n)
    (hs : ∀ n, T.down n (s (n+1)) = s n) (n : Nat) (x : F n) :
    unionValue T s ((T.inc n).app x) = (T.inc n).app ((T.act n (s n)).app x) := by
  apply representative_independent T s hs
  exact Classical.choose_spec (Classical.choose_spec (T.exhaust ((T.inc n).app x)))

theorem common_representatives (T : UnionTower F G L) (s : ∀ n, G n)
    (hs : ∀ n, T.down n (s (n+1)) = s n) (x y : L) :
    ∃ (n : Nat) (a b : F n), (T.inc n).app a = x ∧ (T.inc n).app b = y := by
  obtain ⟨i,a,rfl⟩ := T.exhaust x
  obtain ⟨j,b,rfl⟩ := T.exhaust y
  obtain ⟨u,hu,_⟩ := raise_representative T s hs (Nat.le_max_left i j) a
  obtain ⟨v,hv,_⟩ := raise_representative T s hs (Nat.le_max_right i j) b
  exact ⟨_,u,v,hu,hv⟩

noncomputable def unionMap (T : UnionTower F G L) (s : ∀ n, G n)
    (hs : ∀ n, T.down n (s (n+1)) = s n) : RingMap L L where
  app := unionValue T s
  zero := by simpa only [(T.inc 0).zero,(T.act 0 (s 0)).zero] using unionValue_at_level T s hs 0 0
  one := by simpa only [(T.inc 0).one,(T.act 0 (s 0)).one] using unionValue_at_level T s hs 0 1
  add x y := by
    obtain ⟨n,a,b,rfl,rfl⟩ := common_representatives T s hs x y
    rw [← (T.inc n).add,unionValue_at_level T s hs,(T.act n (s n)).add,(T.inc n).add,
      unionValue_at_level T s hs,unionValue_at_level T s hs]
  neg x := by
    obtain ⟨n,a,rfl⟩ := T.exhaust x
    rw [← (T.inc n).neg,unionValue_at_level T s hs,(T.act n (s n)).neg,(T.inc n).neg,
      unionValue_at_level T s hs]
  mul x y := by
    obtain ⟨n,a,b,rfl,rfl⟩ := common_representatives T s hs x y
    rw [← (T.inc n).mul,unionValue_at_level T s hs,(T.act n (s n)).mul,(T.inc n).mul,
      unionValue_at_level T s hs,unionValue_at_level T s hs]

theorem unionMap_bijective (T : UnionTower F G L) (s : ∀ n, G n)
    (hs : ∀ n, T.down n (s (n+1)) = s n) :
    Function.Injective (unionMap T s hs).app ∧ Function.Surjective (unionMap T s hs).app := by
  constructor
  · intro x y he
    obtain ⟨n,a,b,ha,hb⟩ := common_representatives T s hs x y
    change unionValue T s x = unionValue T s y at he
    rw [← ha, ← hb,unionValue_at_level T s hs,unionValue_at_level T s hs] at he
    exact ha.symm.trans ((congrArg (T.inc n).app ((T.bijective n (s n)).1 (T.inj n he))).trans hb)
  · intro y
    obtain ⟨n,b,rfl⟩ := T.exhaust y
    obtain ⟨a,ha⟩ := (T.bijective n (s n)).2 b
    exact ⟨(T.inc n).app a,(unionValue_at_level T s hs n a).trans (congrArg (T.inc n).app ha)⟩

/-- The finite integral orders used for orbit norms sit in the finite fields
where the automorphisms are glued. Each integral element remains integral
in the next field, and the two actions agree on it. -/
structure IntegralLevels (C : FiniteOrbits A O G) (T : UnionTower F G L) where
  includeOrder : ∀ n, O n → F n
  acts : ∀ n g o, includeOrder n ((C.act n g).app o) = (T.act n g).app (includeOrder n o)
  next : ∀ n o, ∃ t, includeOrder (n+1) t = T.up n (includeOrder n o)

def inUnion {C : FiniteOrbits A O G} {T : UnionTower F G L} (I : IntegralLevels C T)
    (n : Nat) (x : O n) : L := (T.inc n).app (I.includeOrder n x)

variable {C : FiniteOrbits A O G} {T : UnionTower F G L}

theorem order_action_restricts (I : IntegralLevels C T) (n : Nat) (g : G (n+1))
    (o : O n) (t : O (n+1)) (ht : I.includeOrder (n+1) t = T.up n (I.includeOrder n o)) :
    inUnion I (n+1) ((C.act (n+1) g).app t) = inUnion I n ((C.act n (T.down n g)).app o) := by
  simp only [inUnion,I.acts,ht,T.restrict,T.inc_up]

theorem conjugator_restricts (I : IntegralLevels C T) (P Q : L → Prop) (n : Nat) (g : G (n+1))
    (h : Conjugates C (fun i o => P (inUnion I i o)) (fun i o => Q (inUnion I i o)) (n+1) g) :
    Conjugates C (fun i o => P (inUnion I i o)) (fun i o => Q (inUnion I i o)) n (T.down n g) := by
  intro o
  obtain ⟨t,ht⟩ := I.next n o
  have e : inUnion I (n+1) t = inUnion I n o := by simp only [inUnion,ht,T.inc_up]
  have hh := h t
  change Q (inUnion I (n+1) t) ↔ P (inUnion I (n+1) ((C.act (n+1) g).app t)) at hh
  rwa [e,order_action_restricts I n g o t ht] at hh

theorem unionMap_at_order (I : IntegralLevels C T) (s : ∀ n, G n)
    (hs : ∀ n, T.down n (s (n+1)) = s n) (n : Nat) (o : O n) :
    (unionMap T s hs).app (inUnion I n o) = inUnion I n ((C.act n (s n)).app o) := by
  change unionValue T s ((T.inc n).app (I.includeOrder n o)) = _
  rw [unionValue_at_level T s hs, inUnion, I.acts]

/-- All elements belonging to either prime lie in a finite integral order.
Surjectivity on those orders supplies an integral representative in the
reverse implication, even though the ambient union can be a field. -/
theorem carries_union_prime (I : IntegralLevels C T) (P Q : L → Prop)
    (exP : ∀ x, P x → ∃ (n : Nat) (o : O n), inUnion I n o = x)
    (exQ : ∀ x, Q x → ∃ (n : Nat) (o : O n), inUnion I n o = x)
    (s : ∀ n, G n) (hs : ∀ n, T.down n (s (n+1)) = s n)
    (hm : ∀ n, Conjugates C (fun i o => P (inUnion I i o)) (fun i o => Q (inUnion I i o)) n (s n)) :
    ∀ x, Q x ↔ P ((unionMap T s hs).app x) := by
  intro x
  constructor
  · intro hq
    obtain ⟨n,o,rfl⟩ := exQ x hq
    rw [unionMap_at_order]
    exact (hm n o).mp hq
  · intro hp
    obtain ⟨n,t,ht⟩ := exP _ hp
    obtain ⟨o,ho⟩ := C.onto n (s n) t
    have he : (unionMap T s hs).app (inUnion I n o) = (unionMap T s hs).app x := by
      rw [unionMap_at_order,ho,ht]
    have eqx := (unionMap_bijective T s hs).1 he
    have hq := (hm n o).mpr (show P (inUnion I n ((C.act n (s n)).app o)) by rw [ho,ht]; exact hp)
    exact eqx ▸ hq

/-- Two prolongations of the same lower prime are conjugate by an actual
bijective ring homomorphism on the exhausted union L, fixing the specified
bottom field B. Take Fₙ and L to be fields in the arithmetic application. -/
theorem kernel_transitive_on_prolongations {B : Type} (I : IntegralLevels C T) (base : B → F 0)
    (fixBase : ∀ g b, (T.act 0 g).app (base b) = base b) (P Q : L → Prop)
    (p : ∀ n, ResidueMaximal (fun o => P (inUnion I n o)))
    (q : ∀ n, ResidueMaximal (fun o => Q (inUnion I n o)))
    (same : ∀ n a, P (inUnion I n (C.base n a)) ↔ Q (inUnion I n (C.base n a)))
    (exP : ∀ x, P x → ∃ (n : Nat) (o : O n), inUnion I n o = x)
    (exQ : ∀ x, Q x → ∃ (n : Nat) (o : O n), inUnion I n o = x) :
    ∃ f : RingMap L L, Function.Injective f.app ∧ Function.Surjective f.app ∧
      (∀ b, f.app ((T.inc 0).app (base b)) = (T.inc 0).app (base b)) ∧ ∀ x, Q x ↔ P (f.app x) := by
  obtain ⟨s,hm,hs⟩ := compatible_prime_conjugators C (fun n o => P (inUnion I n o))
    (fun n o => Q (inUnion I n o)) p q same T.down (conjugator_restricts I P Q)
  obtain ⟨hi,ho⟩ := unionMap_bijective T s hs
  refine ⟨unionMap T s hs,hi,ho,?_,carries_union_prime I P Q exP exQ s hs hm⟩
  intro b
  exact (unionValue_at_level T s hs 0 (base b)).trans (congrArg (T.inc 0).app (fixBase _ b))

end Reimann.DyadicKernelLift69
