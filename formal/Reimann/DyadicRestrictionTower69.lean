import Reimann.Transfer

/-! Restriction of dyadic places and of decomposition groups in a Galois tower. -/

namespace Reimann.DyadicRestrictionTower69

open Reimann.Transfer (GroupLaw Hom)

/-- Finite places with restriction between successive fields and to Eₐ.
In the application B is the two-element set of primes above 2 in Eₐ. -/
structure Tower (B : Type u) where
  Place : Nat → Type v
  down : ∀ n, Place (n+1) → Place n
  bottom : ∀ n, Place n → B
  down_bottom : ∀ n p, bottom n (down n p) = bottom (n+1) p

structure Branch {B : Type u} (T : Tower B) where
  place : ∀ n, T.Place n
  compatible : ∀ n, T.down n (place (n+1)) = place n

theorem branch_bottom {B : Type u} {T : Tower B} (b : Branch T) (n : Nat) :
    T.bottom n (b.place n) = T.bottom 0 (b.place 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← T.down_bottom,b.compatible,ih]

theorem branches_equal {B : Type u} {T : Tower B} (p q : Branch T)
    (unique : ∀ n (x y : T.Place n), T.bottom n x = T.bottom n y → x=y)
    (same : T.bottom 0 (p.place 0) = T.bottom 0 (q.place 0)) : p=q := by
  have e : p.place = q.place := funext fun n => unique n _ _
    ((branch_bottom p n).trans (same.trans (branch_bottom q n).symm))
  cases p; cases q; congr

/-- Unique finite primes above v are automatically compatible under restriction. -/
theorem unique_tower_place {B : Type u} (T : Tower B) (v : B)
    (above : ∀ n, ∃ p : T.Place n, T.bottom n p = v)
    (unique : ∀ n (p q : T.Place n), T.bottom n p=v → T.bottom n q=v → p=q) :
    ∃ b : Branch T, (∀ n, T.bottom n (b.place n)=v) ∧
      ∀ c : Branch T, T.bottom 0 (c.place 0)=v → c=b := by
  let p (n : Nat) := Classical.choose (above n)
  have hp (n : Nat) : T.bottom n (p n)=v := Classical.choose_spec (above n)
  let b : Branch T := ⟨p, fun n => unique n _ _ ((T.down_bottom n _).trans (hp (n+1))) (hp n)⟩
  refine ⟨b, hp, fun c hc => ?_⟩
  have h : c.place = b.place := funext fun n => unique n _ _ ((branch_bottom c n).trans hc) (hp n)
  have ext (x y : Branch T) (e : x.place = y.place) : x=y := by cases x; cases y; congr
  exact ext _ _ h

/-- Uniqueness of the prime at each finite conductor forces invariance
at every conductor for any base-preserving permutation of places. -/
theorem finite_stabilizers_full {B : Type u} (T : Tower B) (v : B) (b : Branch T)
    (hb : T.bottom 0 (b.place 0)=v)
    (unique : ∀ n (p q : T.Place n), T.bottom n p=v → T.bottom n q=v → p=q)
    {U : Type w} (move : ∀ n, U → T.Place n → T.Place n)
    (over_base : ∀ n g p, T.bottom n (move n g p) = T.bottom n p) :
    ∀ n g, move n g (b.place n) = b.place n := by
  intro n g
  have h := (branch_bottom b n).trans hb
  exact unique n _ _ ((over_base n g _).trans h) h

/-- Ideals or valuation predicates on the union are determined by restriction
to the finite orders. Membership is checked on an actual element of a level. -/
theorem union_membership_fixed {L : Type u} (E : Nat → Type v) (incl : ∀ n, E n → L)
    (exhaust : ∀ z : L, ∃ n x, incl n x = z) (g : L → L) (P : L → Prop)
    (at_level : ∀ n x, P (g (incl n x)) ↔ P (incl n x)) :
    ∀ z, P (g z) ↔ P z := by
  intro z
  obtain ⟨n,x,rfl⟩ := exhaust z
  exact at_level n x

/-- An action on places, using the project's group law for composition. -/
structure PlaceAction {G : Type u} (H : GroupLaw G) (V : Type v) where
  move : G → V → V
  one : ∀ p, move H.zero p = p
  comp : ∀ g h p, move (H.add g h) p = move g (move h p)

/-- Correct an arbitrary lift on the left by an element of the restriction
kernel taking its moved prolongation back to the chosen prolongation. -/
theorem correct_lift {G : Type u} {U : Type v} {W : Type w}
    {H : GroupLaw G} {Q : GroupLaw U} (res : Hom H Q) (A : PlaceAction H W)
    (p : W) (g k : G) (hk : res.app k=Q.zero) (move_back : A.move k (A.move g p)=p) :
    res.app (H.add k g) = res.app g ∧ A.move (H.add k g) p=p := by
  rw [res.preserves_add,hk,Q.zero_add,A.comp,move_back]
  exact ⟨rfl,rfl⟩

/-- Restriction maps the *absolute* decomposition subgroup onto the relative
stabilizer. The extension-of-automorphisms and transitivity-on-prolongations
theorems are explicit inputs from Galois and valuation theory. -/
theorem decomposition_image_iff {G : Type u} {U : Type v} {W : Type w} {V : Type z}
    {H : GroupLaw G} {Q : GroupLaw U} (res : Hom H Q)
    (A : PlaceAction H W) (C : PlaceAction Q V) (below : W → V) (p : W)
    (equivariant : ∀ g w, below (A.move g w)=C.move (res.app g) (below w))
    (extend : ∀ t : U, ∃ g, res.app g=t)
    (transitive : ∀ w : W, below w=below p → ∃ k, res.app k=Q.zero ∧ A.move k w=p)
    (t : U) : (∃ g, res.app g=t ∧ A.move g p=p) ↔ C.move t (below p)=below p := by
  constructor
  · rintro ⟨g,rfl,hg⟩
    rw [← equivariant,hg]
  · intro ht
    obtain ⟨g,hg⟩ := extend t
    have hs : below (A.move g p) = below p := by rw [equivariant,hg,ht]
    obtain ⟨k,hk,hm⟩ := transitive (A.move g p) hs
    obtain ⟨hres,hfix⟩ := correct_lift res A p g k hk hm
    exact ⟨H.add k g,hres.trans hg,hfix⟩

/-- At either dyadic label, uniqueness at all finite conductors suffices
for all of U to occur in the absolute decomposition image. -/
theorem absolute_decomposition_full {G : Type u} {U : Type v} {W : Type w}
    {H : GroupLaw G} {Q : GroupLaw U} (T : Tower Bool) (res : Hom H Q)
    (A : PlaceAction H W) (C : PlaceAction Q (Branch T)) (below : W → Branch T) (p : W)
    (unique : ∀ n (x y : T.Place n), T.bottom n x = T.bottom n y → x=y)
    (fix_bottom : ∀ t b, T.bottom 0 ((C.move t b).place 0)=T.bottom 0 (b.place 0))
    (equivariant : ∀ g w, below (A.move g w)=C.move (res.app g) (below w))
    (extend : ∀ t : U, ∃ g, res.app g=t)
    (transitive : ∀ w : W, below w=below p → ∃ k, res.app k=Q.zero ∧ A.move k w=p)
    (t : U) : ∃ g, res.app g=t ∧ A.move g p=p := by
  apply (decomposition_image_iff res A C below p equivariant extend transitive t).mpr
  exact branches_equal _ _ unique (fix_bottom _ _)

def stabilizer {G : Type u} {H : GroupLaw G} {W : Type v} (A : PlaceAction H W) (p : W) :
    GroupLaw {g : G // A.move g p=p} where
  zero := ⟨H.zero,A.one p⟩
  add x y := ⟨H.add x.val y.val, by rw [A.comp,y.property,x.property]⟩
  neg x := ⟨H.neg x.val, by
    have h := A.comp (H.neg x.val) x.val p
    rw [H.neg_add,A.one,x.property] at h
    exact h.symm⟩
  assoc x y z := Subtype.ext (H.assoc _ _ _)
  zero_add x := Subtype.ext (H.zero_add _)
  add_zero x := Subtype.ext (H.add_zero _)
  add_neg x := Subtype.ext (H.add_neg _)
  neg_add x := Subtype.ext (H.neg_add _)

def restrictDecomposition {G : Type u} {U : Type v} {W : Type w}
    {H : GroupLaw G} {Q : GroupLaw U} (A : PlaceAction H W) (p : W) (res : Hom H Q) :
    Hom (stabilizer A p) Q where
  app g := res.app g.val
  preserves_zero := res.preserves_zero
  preserves_add g h := res.preserves_add _ _
  preserves_neg g := res.preserves_neg _

theorem same_restriction_iff_kernel {G : Type u} {U : Type v}
    {H : GroupLaw G} {Q : GroupLaw U} (res : Hom H Q) (x y : G) :
    res.app x=res.app y ↔ res.app (H.add x (H.neg y))=Q.zero := by
  rw [res.preserves_add,res.preserves_neg]
  constructor
  · intro h; rw [h,Q.add_neg]
  · intro h
    have h' := congrArg (fun z => Q.add z (res.app y)) h
    simpa only [Q.assoc,Q.neg_add,Q.add_zero,Q.zero_add] using h'

/-- The absolute dyadic decomposition group modulo its subgroup over L is
identified with U when restriction is onto. These are quotient types. -/
theorem decomposition_quotient {G : Type u} {U : Type v} {W : Type w}
    {H : GroupLaw G} {Q : GroupLaw U} (A : PlaceAction H W) (p : W) (res : Hom H Q)
    (onto : ∀ t, ∃ g, res.app g=t ∧ A.move g p=p) :
    let D := stabilizer A p
    let π := restrictDecomposition A p res
    let rel := fun x y => π.app (D.add x (D.neg y))=Q.zero
    ∃ f : Quot rel → U, ∃ j : U → Quot rel,
      (∀ g, f (Quot.mk rel g)=π.app g) ∧ (∀ u, f (j u)=u) ∧ (∀ c, j (f c)=c) := by
  let D := stabilizer A p
  let π := restrictDecomposition A p res
  let rel := fun x y => π.app (D.add x (D.neg y))=Q.zero
  let f := Quot.lift π.app (fun x y h => (same_restriction_iff_kernel π x y).mpr h)
  have surj (t : U) : ∃ d, π.app d=t := by
    obtain ⟨g,hg,hp⟩ := onto t
    exact ⟨⟨g,hp⟩,hg⟩
  let pick (t : U) := Classical.choose (surj t)
  have chosen (t : U) : π.app (pick t)=t := Classical.choose_spec (surj t)
  refine ⟨f,fun t => Quot.mk rel (pick t),fun _ => rfl,chosen,?_⟩
  intro c
  induction c using Quot.ind with
  | mk d =>
    apply Quot.sound
    exact (same_restriction_iff_kernel π _ _).mp (chosen (π.app d))

/-- A coboundary on the absolute decomposition group detects a coboundary
on U after inflation. The primitive m is the very same element in both
directions; M may be the full discrete twisted Q₂/Z₂ coefficient group. -/
theorem local_inflation_detects_principal {G : Type u} {U : Type v} {W : Type w} {M : Type z}
    {H : GroupLaw G} {Q : GroupLaw U} (A : PlaceAction H W) (p : W) (res : Hom H Q)
    (onto : ∀ t, ∃ g, res.app g=t ∧ A.move g p=p) (c : U → M) (principal : U → M → M) :
    (∃ m, ∀ d : {g // A.move g p=p},
      c ((restrictDecomposition A p res).app d) = principal ((restrictDecomposition A p res).app d) m)
      ↔ ∃ m, ∀ t, c t=principal t m := by
  constructor
  · rintro ⟨m,hm⟩
    refine ⟨m, fun t => ?_⟩
    obtain ⟨g,rfl,hg⟩ := onto t
    exact hm ⟨g,hg⟩
  · rintro ⟨m,hm⟩
    exact ⟨m,fun d => hm _⟩

/-- A branch of prime ideals on subrings of one ring, viewed as predicates
on ambient elements. Compatibility is extension and contraction along the
inclusions, stated only on elements present at the lower level. -/
structure PrimeChain (R : Type u) (zero one : R) (add mul : R → R → R) where
  level : Nat → R → Prop
  increasing : ∀ {i j}, i ≤ j → ∀ {x}, level i x → level j x
  exhaustive : ∀ x, ∃ i, level i x
  zero_mem : ∀ i, level i zero
  one_mem : ∀ i, level i one
  add_mem : ∀ {i x y}, level i x → level i y → level i (add x y)
  mul_mem : ∀ {i x y}, level i x → level i y → level i (mul x y)
  prime : Nat → R → Prop
  contracts : ∀ {i j}, i ≤ j → ∀ {x}, level i x → (prime j x ↔ prime i x)
  prime_zero : ∀ i, prime i zero
  proper : ∀ i, ¬ prime i one
  prime_add : ∀ {i x y}, level i x → level i y → prime i x → prime i y → prime i (add x y)
  absorb : ∀ {i x y}, level i x → level i y → prime i x → prime i (mul x y)
  prime_mul : ∀ {i x y}, level i x → level i y → prime i (mul x y) → prime i x ∨ prime i y

def unionPrime {R : Type u} {zero one : R} {add mul : R → R → R}
    (C : PrimeChain R zero one add mul) (x : R) : Prop := ∃ i, C.level i x ∧ C.prime i x

theorem union_contracts {R : Type u} {zero one : R} {add mul : R → R → R}
    (C : PrimeChain R zero one add mul) {i : Nat} {x : R} (hi : C.level i x) :
    unionPrime C x ↔ C.prime i x := by
  constructor
  · rintro ⟨j,hj,hp⟩
    exact (C.contracts (Nat.le_max_left i j) hi).mp
      ((C.contracts (Nat.le_max_right i j) hj).mpr hp)
  · intro h
    exact ⟨i,hi,h⟩

theorem common_level {R : Type u} {zero one : R} {add mul : R → R → R}
    (C : PrimeChain R zero one add mul) (x y : R) : ∃ i, C.level i x ∧ C.level i y := by
  obtain ⟨j,hj⟩ := C.exhaustive x
  obtain ⟨k,hk⟩ := C.exhaustive y
  exact ⟨max j k,C.increasing (Nat.le_max_left j k) hj,C.increasing (Nat.le_max_right j k) hk⟩

theorem union_is_prime {R : Type u} {zero one : R} {add mul : R → R → R}
    (C : PrimeChain R zero one add mul) :
    unionPrime C zero ∧ ¬unionPrime C one ∧
    (∀ x y, unionPrime C x → unionPrime C y → unionPrime C (add x y)) ∧
    (∀ x y, unionPrime C x → unionPrime C (mul x y)) ∧
    (∀ x y, unionPrime C (mul x y) → unionPrime C x ∨ unionPrime C y) := by
  refine ⟨(union_contracts C (C.zero_mem 0)).mpr (C.prime_zero 0),
    fun h => C.proper 0 ((union_contracts C (C.one_mem 0)).mp h), ?_, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨i,xi,yi⟩ := common_level C x y
    exact (union_contracts C (C.add_mem xi yi)).mpr (C.prime_add xi yi
      ((union_contracts C xi).mp hx) ((union_contracts C yi).mp hy))
  · intro x y hx
    obtain ⟨i,xi,yi⟩ := common_level C x y
    exact (union_contracts C (C.mul_mem xi yi)).mpr (C.absorb xi yi ((union_contracts C xi).mp hx))
  · intro x y h
    obtain ⟨i,xi,yi⟩ := common_level C x y
    exact (C.prime_mul xi yi ((union_contracts C (C.mul_mem xi yi)).mp h)).imp
      (union_contracts C xi).mpr (union_contracts C yi).mpr

end Reimann.DyadicRestrictionTower69
