import Reimann.DyadicKernelLift69

/-! Correction of prescribed finite automorphisms by the relative Galois
group and gluing of the resulting prime-preserving lifts. -/
namespace Reimann.DyadicFiniteRestriction69

open Lean.Grind
open DyadicPrimeConjugacy69 (ResidueMaximal orbitNorm pullback_maximal finite_prime_conjugacy)
open DyadicUnramifiedBase69 (RingMap)
open DyadicKernelLift69 (UnionTower unionMap unionMap_bijective unionValue_at_level)

/-- A finite upper integral order and its lower integral subring. The
listed relative automorphisms fix the lower order pointwise. -/
structure Stage (A O G : Type) [CommRing O] where
  base : A → O
  law : Transfer.GroupLaw G
  act : G → RingMap O O
  identity : ∀ x, (act law.zero).app x=x
  compose : ∀ g h x, (act (law.add g h)).app x = (act g).app ((act h).app x)
  all : List G
  enumerates : ∀ g, g ∈ all
  kernelList : List G
  kernelOne : law.zero ∈ kernelList
  kernelFixes : ∀ k ∈ kernelList, ∀ a, (act k).app (base a)=base a
  kernelNorm : ∀ x, ∃ a, base a=orbitNorm act kernelList x

def Agrees {A O G : Type} [CommRing O] (D : Stage A O G) (g : G) (t : A → A) : Prop :=
  ∀ a, (D.act g).app (D.base a) = D.base (t a)

def Stabilizes {A O G : Type} [CommRing O] (D : Stage A O G) (g : G) (P : O → Prop) : Prop :=
  ∀ x, P ((D.act g).app x) ↔ P x

theorem action_onto {A O G : Type} [CommRing O] (D : Stage A O G) (g : G) (y : O) :
    ∃ x, (D.act g).app x=y := by
  exact ⟨(D.act (D.law.neg g)).app y,by rw [←D.compose,D.law.add_neg,D.identity]⟩

theorem pullback_agrees_below {A O G : Type} [CommRing O] (D : Stage A O G)
    (g : G) (t : A → A) (P : O → Prop) (hg : Agrees D g t)
    (below : ∀ a, P (D.base (t a)) ↔ P (D.base a)) (a : A) :
    P ((D.act g).app (D.base a)) ↔ P (D.base a) := by rw [hg a]; exact below a

/-- Start with any lift g of t. Conjugate the pulled-back prime x↦P(gx)
against P using a relative automorphism k. The corrected lift g∘k acts
on the lower order exactly as g does. -/
theorem corrected_lift {A O G : Type} [CommRing O] (D : Stage A O G)
    (g : G) (t : A → A) {P : O → Prop} (p : ResidueMaximal P)
    (hg : Agrees D g t) (below : ∀ a, P (D.base (t a)) ↔ P (D.base a)) :
    ∃ k ∈ D.kernelList, Agrees D (D.law.add g k) t ∧ Stabilizes D (D.law.add g k) P := by
  let Q : O → Prop := fun x => P ((D.act g).app x)
  have q : ResidueMaximal Q := pullback_maximal p (D.act g) (action_onto D g)
  obtain ⟨k,hk,conjugates⟩ := finite_prime_conjugacy D.base q p D.act (action_onto D)
    D.kernelList D.law.zero D.kernelOne D.identity D.kernelNorm (pullback_agrees_below D g t P hg below)
  refine ⟨k,hk,?_,?_⟩
  · intro a
    rw [D.compose,D.kernelFixes k hk,hg]
  · intro x
    rw [D.compose]
    exact (conjugates x).symm

/-- The adjacent upper inclusions are injective. Restriction of finite
automorphisms commutes with these inclusions on actual integral elements. -/
structure Tower (A O G : Nat → Type) [∀ n, CommRing (O n)] where
  stage : ∀ n, Stage (A n) (O n) (G n)
  up : ∀ n, O n → O (n+1)
  up_inj : ∀ n, Function.Injective (up n)
  lowerUp : ∀ n, A n → A (n+1)
  base_up : ∀ n a, up n ((stage n).base a) = (stage (n+1)).base (lowerUp n a)
  down : ∀ n, G (n+1) → G n
  act_up : ∀ n g x, ((stage (n+1)).act g).app (up n x) = up n (((stage n).act (down n g)).app x)

theorem restrict_agrees {A O G : Nat → Type} [∀ n, CommRing (O n)] (T : Tower A O G)
    (t : ∀ n, A n → A n) (compatible : ∀ n a, t (n+1) (T.lowerUp n a)=T.lowerUp n (t n a))
    (n : Nat) (g : G (n+1)) (hg : Agrees (T.stage (n+1)) g (t (n+1))) :
    Agrees (T.stage n) (T.down n g) (t n) := by
  intro a
  apply T.up_inj n
  rw [←T.act_up,T.base_up,hg,compatible,T.base_up]

theorem restrict_stabilizes {A O G : Nat → Type} [∀ n, CommRing (O n)] (T : Tower A O G)
    (P : ∀ n, O n → Prop) (contracts : ∀ n x, P (n+1) (T.up n x) ↔ P n x)
    (n : Nat) (g : G (n+1)) (hg : Stabilizes (T.stage (n+1)) g (P (n+1))) :
    Stabilizes (T.stage n) (T.down n g) (P n) := by
  intro x
  rw [←contracts n,←T.act_up,hg,contracts]

theorem coherent_corrected_lifts {A O G : Nat → Type} [∀ n, CommRing (O n)] (T : Tower A O G)
    (t : ∀ n, A n → A n) (compatible : ∀ n a, t (n+1) (T.lowerUp n a)=T.lowerUp n (t n a))
    (P : ∀ n, O n → Prop) (p : ∀ n, ResidueMaximal (P n))
    (contracts : ∀ n x, P (n+1) (T.up n x) ↔ P n x)
    (lift : ∀ n, ∃ g, Agrees (T.stage n) g (t n))
    (below : ∀ n a, P n ((T.stage n).base (t n a)) ↔ P n ((T.stage n).base a)) :
    ∃ s : ∀ n, G n, (∀ n, Agrees (T.stage n) (s n) (t n) ∧ Stabilizes (T.stage n) (s n) (P n)) ∧
      ∀ n, T.down n (s (n+1))=s n := by
  let image (n : Nat) (g : G n) := fun a => ((T.stage n).act g).app ((T.stage n).base a)
  let target (n : Nat) := fun a => (T.stage n).base (t n a)
  obtain ⟨s,hs,hd⟩ := DyadicProfiniteLift69.prescribed_prime_lifts
    (fun n => (T.stage n).all) (fun n => (T.stage n).enumerates) T.down image target
    (fun n g => Stabilizes (T.stage n) g (P n)) (by
      intro n
      obtain ⟨g,hg⟩ := lift n
      obtain ⟨k,_,he,hp⟩ := corrected_lift (T.stage n) g (t n) (p n) hg (below n)
      exact ⟨(T.stage n).law.add g k,funext he,hp⟩) (by
      intro n g he hp
      exact ⟨funext (restrict_agrees T t compatible n g (congrFun he)),
        restrict_stabilizes T P contracts n g hp⟩)
  exact ⟨s,fun n => ⟨congrFun (hs n).1,(hs n).2⟩,hd⟩

/-- The finite upper orders act on the same field tower automorphisms and
their embeddings intertwine the actions on integral elements. -/
structure EmbeddedOrders {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] (T : Tower A O G) (U : UnionTower F G L) where
  embed : ∀ n, RingMap (O n) (F n)
  injective : ∀ n, Function.Injective (embed n).app
  compatible : ∀ n x, (embed (n+1)).app (T.up n x)=U.up n ((embed n).app x)
  equivariant : ∀ n g x, (U.act n g).app ((embed n).app x) = (embed n).app (((T.stage n).act g).app x)
  sameDown : ∀ n g, U.down n g = T.down n g

def point {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (n : Nat) (x : O n) : L := (U.inc n).app ((E.embed n).app x)

def InUnionPrime {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (P : ∀ n, O n → Prop) (z : L) : Prop :=
  ∃ n x, point E n x=z ∧ P n x

theorem acts_on_order {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (s : ∀ n, G n) (hs : ∀ n, U.down n (s (n+1))=s n)
    (n : Nat) (x : O n) : (unionMap U s hs).app (point E n x) =
      point E n (((T.stage n).act (s n)).app x) := by
  exact (unionValue_at_level U s hs n ((E.embed n).app x)).trans (congrArg (U.inc n).app (E.equivariant n (s n) x))

theorem stabilizes_union_prime {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (P : ∀ n, O n → Prop)
    (s : ∀ n, G n) (hs : ∀ n, U.down n (s (n+1))=s n)
    (stabilizes : ∀ n, Stabilizes (T.stage n) (s n) (P n)) (z : L) :
    InUnionPrime E P ((unionMap U s hs).app z) ↔ InUnionPrime E P z := by
  constructor
  · rintro ⟨n,y,hy,hp⟩
    obtain ⟨x,hx⟩ := action_onto (T.stage n) (s n) y
    have h := acts_on_order E s hs n x
    rw [hx,hy] at h
    exact ⟨n,x,(unionMap_bijective U s hs).1 h,(stabilizes n x).mp (by rwa [hx])⟩
  · rintro ⟨n,x,rfl,hx⟩
    exact ⟨n,_,(acts_on_order E s hs n x).symm,(stabilizes n x).mpr hx⟩

theorem field_map_nonzero {K L : Type} [Field K] [Field L] (f : RingMap K L)
    {z : K} (hz : z≠0) : f.app z≠0 := by
  intro he
  have h := f.mul z z⁻¹
  rw [Field.mul_inv_cancel hz,f.one,he,Semiring.zero_mul] at h
  exact Field.zero_ne_one h.symm

/-- Every lower field element is a quotient of two elements of one finite
lower order. The displayed square relates those elements to the upper
integral orders inside the union field. -/
structure LowerField {A O G F : Nat → Type} {K L : Type} [Field K] [Field L]
    [∀ n, CommRing (O n)] [∀ n, CommRing (F n)]
    {T : Tower A O G} {U : UnionTower F G L} (E : EmbeddedOrders T U) where
  includeBase : RingMap K L
  element : ∀ n, A n → K
  square : ∀ n a, point E n ((T.stage n).base a) = includeBase.app (element n a)
  fractions : ∀ z : K, ∃ (n : Nat) (a b : A n), element n b≠0 ∧ z*element n b=element n a

theorem agrees_on_fractions {A O G F : Nat → Type} {K L : Type} [Field K] [Field L]
    [∀ n, CommRing (O n)] [∀ n, CommRing (F n)] {T : Tower A O G} {U : UnionTower F G L}
    {E : EmbeddedOrders T U} (B : LowerField (K:=K) E) (σ : RingMap K K) (f : RingMap L L)
    (agree : ∀ n a, f.app (B.includeBase.app (B.element n a))=B.includeBase.app (σ.app (B.element n a)))
    (z : K) : f.app (B.includeBase.app z) = B.includeBase.app (σ.app z) := by
  obtain ⟨n,a,b,hb,hab⟩ := B.fractions z
  have hprod : f.app (B.includeBase.app z)*B.includeBase.app (σ.app (B.element n b)) =
      B.includeBase.app (σ.app z)*B.includeBase.app (σ.app (B.element n b)) := by
    calc
      _ = f.app (B.includeBase.app (z*B.element n b)) := by
        rw [B.includeBase.mul,f.mul,agree]
      _ = B.includeBase.app (σ.app (z*B.element n b)) := by rw [hab,agree]
      _ = _ := by rw [σ.mul,B.includeBase.mul]
  have h := congrArg (fun y => y*(B.includeBase.app (σ.app (B.element n b)))⁻¹) hprod
  have hn := field_map_nonzero B.includeBase (field_map_nonzero σ hb)
  simpa only [Semiring.mul_assoc,Field.mul_inv_cancel hn,Semiring.mul_one] using h

/-- A bijective field endomorphism of the union extending the prescribed
lower field map and stabilizing the chosen union prime. -/
theorem union_automorphism_lifting {A O G F : Nat → Type} {K L : Type} [Field K] [Field L]
    [∀ n, CommRing (O n)] [∀ n, CommRing (F n)] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (B : LowerField (K:=K) E) (σ : RingMap K K)
    (t : ∀ n, A n → A n) (onLower : ∀ n a, B.element n (t n a)=σ.app (B.element n a))
    (compatible : ∀ n a, t (n+1) (T.lowerUp n a)=T.lowerUp n (t n a))
    (P : ∀ n, O n → Prop) (p : ∀ n, ResidueMaximal (P n))
    (contracts : ∀ n x, P (n+1) (T.up n x) ↔ P n x)
    (lift : ∀ n, ∃ g, Agrees (T.stage n) g (t n))
    (below : ∀ n a, P n ((T.stage n).base (t n a)) ↔ P n ((T.stage n).base a)) :
    ∃ f : RingMap L L, Function.Injective f.app ∧ Function.Surjective f.app ∧
      (∀ z : K, f.app (B.includeBase.app z)=B.includeBase.app (σ.app z)) ∧
      ∀ z, InUnionPrime E P (f.app z) ↔ InUnionPrime E P z := by
  obtain ⟨s,hs,hd⟩ := coherent_corrected_lifts T t compatible P p contracts lift below
  have hu (n : Nat) : U.down n (s (n+1)) = s n := (E.sameDown n _).trans (hd n)
  obtain ⟨hi,ho⟩ := unionMap_bijective U s hu
  refine ⟨unionMap U s hu,hi,ho,agrees_on_fractions B σ _ ?_,stabilizes_union_prime E P s hu (fun n => (hs n).2)⟩
  intro n a
  rw [←B.square,acts_on_order,(hs n).1,B.square,onLower]

theorem point_up {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (n : Nat) (x : O n) : point E (n+1) (T.up n x)=point E n x := by
  unfold point
  rw [E.compatible,U.inc_up]

theorem raise_prime_test {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (P : ∀ n, O n → Prop)
    (contracts : ∀ n x, P (n+1) (T.up n x) ↔ P n x)
    {i j : Nat} (le : i ≤ j) (x : O i) :
    ∃ y : O j, point E j y=point E i x ∧ (P j y ↔ P i x) := by
  induction le with
  | refl => exact ⟨x,rfl,Iff.rfl⟩
  | @step j _ ih =>
    obtain ⟨y,hy,hp⟩ := ih
    exact ⟨T.up j y,(point_up E _ _).trans hy,(contracts _ _).trans hp⟩

/-- Membership in the union prime agrees with the original test on every
finite upper order. -/
theorem union_prime_contracts {A O G F : Nat → Type} {L : Type} [∀ n, CommRing (O n)]
    [∀ n, CommRing (F n)] [CommRing L] {T : Tower A O G} {U : UnionTower F G L}
    (E : EmbeddedOrders T U) (P : ∀ n, O n → Prop)
    (contracts : ∀ n x, P (n+1) (T.up n x) ↔ P n x) (n : Nat) (x : O n) :
    InUnionPrime E P (point E n x) ↔ P n x := by
  constructor
  · rintro ⟨m,y,hy,hp⟩
    obtain ⟨u,hu,pu⟩ := raise_prime_test E P contracts (Nat.le_max_left m n) y
    obtain ⟨v,hv,pv⟩ := raise_prime_test E P contracts (Nat.le_max_right m n) x
    have e := (hu.trans hy).trans hv.symm
    have eq := E.injective _ (U.inj _ e)
    exact pv.mp (eq ▸ pu.mpr hp)
  · intro hp
    exact ⟨n,x,rfl,hp⟩

end Reimann.DyadicFiniteRestriction69
