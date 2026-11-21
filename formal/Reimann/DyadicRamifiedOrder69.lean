import Std

/-! Ramification and integral saturation for embedded quadratic cyclotomic orders. -/
namespace Reimann.DyadicRamifiedOrder69

open Lean.Grind

universe u
variable {R : Type u} [CommRing R]

/-- An embedded subring; arithmetic and polynomial evaluation take place
in the common ambient ring. -/
structure Order (R : Type u) [CommRing R] where
  mem : R → Prop
  zero : mem 0
  one : mem 1
  add : ∀ {x y}, mem x → mem y → mem (x+y)
  neg : ∀ {x}, mem x → mem (-x)
  mul : ∀ {x y}, mem x → mem y → mem (x*y)

theorem sub_mem (A : Order R) {x y : R} (hx : A.mem x) (hy : A.mem y) : A.mem (x-y) := by
  have h := A.add hx (A.neg hy)
  rwa [show x+(-y)=x-y by grind] at h

theorem two_mem (A : Order R) : A.mem 2 := by
  have h := A.add A.one A.one
  rwa [show (1:R)+1=2 by grind] at h

theorem pow_mem (A : Order R) {x : R} (hx : A.mem x) (n : Nat) : A.mem (x^n) := by
  induction n with
  | zero => simpa [Semiring.pow_zero] using A.one
  | succ n ih => simpa [Semiring.pow_succ] using A.mul ih hx

def Multiple (A : Order R) (d x : R) : Prop := ∃ y, A.mem y ∧ x=d*y

def Radical (A : Order R) (d : R) : Prop :=
  ∀ x, A.mem x → ∀ n : Nat, Multiple A d (x^n) → Multiple A d x

/-- A monic polynomial with coefficients in increasing order. -/
def monicAt (z : R) : List R → R
  | [] => 1
  | c :: cs => c+z*monicAt z cs

/-- After clearing the denominator d, the top monomial is the only
contribution modulo d. The quotient by d belongs to the base order. -/
theorem homogeneous_remainder (A : Order R) (d z : R) (hd : A.mem d)
    (hy : A.mem (d*z)) (cs : List R) (hc : ∀ c ∈ cs, A.mem c) :
    ∃ w, A.mem w ∧ d^cs.length*monicAt z cs=(d*z)^cs.length+d*w := by
  induction cs with
  | nil => exact ⟨0,A.zero,by simp [monicAt,Semiring.pow_zero]; grind⟩
  | cons c cs ih =>
    obtain ⟨w,hw,he⟩ := ih (fun a ha => hc a (List.mem_cons_of_mem c ha))
    refine ⟨d^cs.length*c+(d*z)*w,A.add (A.mul (pow_mem A hd _) (hc c (by simp))) (A.mul hy hw),?_⟩
    simp only [List.length_cons,monicAt,Semiring.pow_succ]
    grind

/-- A radical uniformizer removes every scalar power denominator from a
monic-integral element of the ambient ring. No integral-closure hypothesis on
the enlarged order is assumed. -/
theorem monic_saturation (A : Order R) (t z : R) (ht : A.mem t) (rad : Radical A t)
    (cancel : ∀ x y : R, t*x=t*y → x=y) (cs : List R)
    (hc : ∀ c ∈ cs, A.mem c) (hz : monicAt z cs=0) (n : Nat) (h : A.mem (t^n*z)) :
    A.mem z := by
  induction n with
  | zero => simpa [Semiring.pow_zero,Semiring.one_mul] using h
  | succ n ih =>
    obtain ⟨w,hw,he⟩ := homogeneous_remainder A (t^(n+1)) z (pow_mem A ht _) h cs hc
    rw [hz] at he
    have hd : Multiple A t ((t^(n+1)*z)^cs.length) := by
      refine ⟨-(t^n*w), A.neg (A.mul (pow_mem A ht _) hw), ?_⟩
      rw [Semiring.pow_succ t n] at he ⊢
      grind
    obtain ⟨v,hv,eq⟩ := rad _ h _ hd
    apply ih
    have hv' : t*(t^n*z)=t*v := by rw [Semiring.pow_succ t n] at eq; grind
    rwa [cancel _ _ hv']

/-- The embedded order obtained by adjoining t with t²=2t−d. -/
def adjoin (A : Order R) (d t : R) (hd : A.mem d) (ht : t*t=2*t-d) : Order R where
  mem x := ∃ a b, A.mem a ∧ A.mem b ∧ x=a+t*b
  zero := ⟨0,0,A.zero,A.zero,by grind⟩
  one := ⟨1,0,A.one,A.zero,by grind⟩
  add := by
    rintro _ _ ⟨a,b,ha,hb,rfl⟩ ⟨c,e,hc,he,rfl⟩
    exact ⟨a+c,b+e,A.add ha hc,A.add hb he,by grind⟩
  neg := by
    rintro _ ⟨a,b,ha,hb,rfl⟩
    exact ⟨-a,-b,A.neg ha,A.neg hb,by grind⟩
  mul := by
    rintro _ _ ⟨a,b,ha,hb,rfl⟩ ⟨c,e,hc,he,rfl⟩
    exact ⟨a*c-d*(b*e),a*e+b*c+2*(b*e),sub_mem A (A.mul ha hc) (A.mul hd (A.mul hb he)),
      A.add (A.add (A.mul ha he) (A.mul hb hc)) (A.mul (two_mem A) (A.mul hb he)),by grind⟩

theorem base_mem (A : Order R) {d t : R} (hd : A.mem d) (ht : t*t=2*t-d)
    {x : R} (hx : A.mem x) : (adjoin A d t hd ht).mem x :=
  ⟨x,0,hx,A.zero,by grind⟩

theorem root_mem (A : Order R) {d t : R} (hd : A.mem d) (ht : t*t=2*t-d) :
    (adjoin A d t hd ht).mem t := ⟨0,1,A.zero,A.one,by grind⟩

/-- Modulo the new uniformizer, the constant coefficient is well-defined
modulo the old one. The proof also works over a semilocal base. -/
theorem constant_iff (A : Order R) {d t : R} (hd : A.mem d) (ht : t*t=2*t-d)
    (rad : Radical A d) (h2 : Multiple A d 2) {a b : R} (ha : A.mem a) (hb : A.mem b) :
    Multiple (adjoin A d t hd ht) t (a+t*b) ↔ Multiple A d a := by
  obtain ⟨q,hq,eq2⟩ := h2
  constructor
  · rintro ⟨_,⟨u,v,hu,hv,rfl⟩,eq⟩
    let l := u+2*v-b
    let m := a+d*v
    have hl : A.mem l := sub_mem A (A.add hu (A.mul (two_mem A) hv)) hb
    have hm : A.mem m := A.add ha (A.mul hd hv)
    have hrel : m=t*l := by dsimp [m,l]; grind
    have hsquare : m^2=d*(q*m*l-l*l) := by
      have hsq : m*m=(t*t)*(l*l) := by rw [hrel]; grind
      rw [ht] at hsq
      have hcross : t*(l*l)=m*l := by rw [hrel]; grind
      grind
    obtain ⟨w,hw,eqw⟩ := rad _ hm 2
      ⟨q*m*l-l*l,sub_mem A (A.mul (A.mul hq hm) hl) (A.mul hl hl),hsquare⟩
    exact ⟨w-v,sub_mem A hw hv,by dsimp [m] at eqw; grind⟩
  · rintro ⟨k,hk,eq⟩
    refine ⟨(2*k+b)+t*(-k),⟨2*k+b,-k,A.add (A.mul (two_mem A) hk) hb,A.neg hk,rfl⟩,?_⟩
    grind

theorem power_remainder (A : Order R) {x a b t : R} (hx : A.mem x) (ha : A.mem a)
    (hb : A.mem b) (h : x=a+t*b) (n : Nat) :
    ∃ s, A.mem s ∧ x^n=a^n+t*s := by
  induction n with
  | zero => exact ⟨0,A.zero,by simp [Semiring.pow_zero]; grind⟩
  | succ n ih =>
    obtain ⟨s,hs,es⟩ := ih
    refine ⟨a^n*b+s*x,A.add (A.mul (pow_mem A ha _) hb) (A.mul hs hx),?_⟩
    rw [Semiring.pow_succ,Semiring.pow_succ,es]
    grind

theorem adjoin_radical (A : Order R) {d t : R} (hd : A.mem d) (ht : t*t=2*t-d)
    (rad : Radical A d) (h2 : Multiple A d 2) : Radical (adjoin A d t hd ht) t := by
  let B := adjoin A d t hd ht
  intro x hx n hn
  obtain ⟨a,b,ha,hb,e⟩ := hx
  obtain ⟨v,hv,ev⟩ := hn
  obtain ⟨s,hs,es⟩ := power_remainder B (show B.mem x from ⟨a,b,ha,hb,e⟩)
    (base_mem A hd ht ha) (base_mem A hd ht hb) e n
  have hv' : Multiple B t (a^n+t*0) :=
    ⟨v-s,sub_mem B hv hs,by grind⟩
  have hpow := (constant_iff A hd ht rad h2 (pow_mem A ha n) A.zero).mp hv'
  rw [e]
  exact (constant_iff A hd ht rad h2 ha hb).mpr (rad a ha n hpow)

theorem two_in_new_prime (A : Order R) {d t : R} (hd : A.mem d) (ht : t*t=2*t-d)
    (rad : Radical A d) (h2 : Multiple A d 2) : Multiple (adjoin A d t hd ht) t 2 := by
  have e := (constant_iff A hd ht rad h2 (two_mem A) A.zero).mpr h2
  rwa [show (2:R)+t*0=2 by grind] at e

theorem square_doubles_exponent (t : R) (n : Nat) : (t*t)^n = t^(n+n) := by
  induction n with
  | zero => simp [Semiring.pow_zero]
  | succ n ih =>
    rw [Semiring.pow_succ,ih,show n+1+(n+1)=n+n+1+1 by omega,Semiring.pow_succ,Semiring.pow_succ]
    grind

/-- If d^e is divisible by 2, then t^(2e) is divisible by 2 in the next order. -/
theorem dyadic_denominator_step (A : Order R) {d t : R} (hd : A.mem d) (ht : t*t=2*t-d)
    (e : Nat) (he : Multiple A 2 (d^e)) : Multiple (adjoin A d t hd ht) 2 (t^(e+e)) := by
  let B := adjoin A d t hd ht
  have htm := root_mem A hd ht
  have hdm := base_mem A hd ht hd
  obtain ⟨w,hw,ew⟩ := he
  obtain ⟨s,hs,es⟩ := power_remainder B (B.mul htm htm) hdm (sub_mem B htm hdm)
    (show t*t=d+2*(t-d) by grind) e
  refine ⟨w+s,B.add (base_mem A hd ht hw) hs,?_⟩
  rw [square_doubles_exponent] at es
  grind

/-- The radical principal ideal and the two denominator comparisons at depth n. -/
structure Stage (n : Nat) (t : R) where
  order : Order R
  root : order.mem t
  radical : Radical order t
  overTwo : Multiple order t 2
  power : Multiple order 2 (t^(2^n))

def baseStage (A : Order R) (rad : Radical A 2) : Stage 0 (2:R) where
  order := A
  root := two_mem A
  radical := rad
  overTwo := ⟨1,A.one,by grind⟩
  power := ⟨1,A.one,by simp [Semiring.pow_one]; grind⟩

def nextStage {n : Nat} {d : R} (S : Stage n d) (t : R) (ht : t*t=2*t-d) : Stage (n+1) t where
  order := adjoin S.order d t S.root ht
  root := root_mem _ _ _
  radical := adjoin_radical _ _ _ S.radical S.overTwo
  overTwo := two_in_new_prime _ _ _ S.radical S.overTwo
  power := by
    have h := dyadic_denominator_step _ S.root ht _ S.power
    rwa [show 2^(n+1)=2^n+2^n by rw [Nat.pow_succ]; omega]

theorem squared_root_condition (z : R) (n : Nat) (h : z^(2^(n+1) : Nat)= -1) :
    (z*z)^(2^n : Nat)= -1 := by
  rw [square_doubles_exponent,show 2^n+2^n=2^(n+1) by rw [Nat.pow_succ]; omega]
  exact h

/-- Embedded order A[ζ] for an actual root in the ambient ring. The tower
uses ζ² at every lower step and the uniformizer 1−ζ. -/
def cyclotomicStage (A : Order R) (rad : Radical A 2) :
    (n : Nat) → (z : R) → z^(2^n : Nat) = -1 → Stage n (1-z)
  | 0,z,h => by
    have hz : z= -1 := by simpa [Semiring.pow_one] using h
    rw [hz,show (1:R)-(-1)=2 by grind]
    exact baseStage A rad
  | n+1,z,h => nextStage (cyclotomicStage A rad n (z*z) (squared_root_condition z n h))
      (1-z) (by grind)

theorem denominator_power (A : Order R) (t : R) (e s : Nat)
    (he : Multiple A 2 (t^e)) :
    ∃ m : Nat, Multiple A ((2:R)^s) (t^m) := by
  obtain ⟨w,hw,ew⟩ := he
  induction s with
  | zero => exact ⟨0,1,A.one,by simp [Semiring.pow_zero]; grind⟩
  | succ s ih =>
    obtain ⟨m,v,hv,ev⟩ := ih
    exact ⟨m+e,v*w,A.mul hv hw,by rw [Semiring.pow_add,Semiring.pow_succ,ev,ew]; grind⟩

/-- Inside its dyadic fraction localization the actual root-generated order
is integrally closed. Each monic coefficient may lie anywhere in this order. -/
theorem integral_of_dyadic_denominator {n : Nat} {t : R} (S : Stage n t)
    (cancel : ∀ x y : R, t*x=t*y → x=y) (z : R) (s : Nat)
    (hs : S.order.mem ((2:R)^s*z)) (cs : List R) (hc : ∀ c ∈ cs, S.order.mem c)
    (hz : monicAt z cs = 0) : S.order.mem z := by
  obtain ⟨m,w,hw,he⟩ := denominator_power S.order t _ s S.power
  apply monic_saturation S.order t z S.root S.radical cancel cs hc hz m
  have e : t^m*z=w*(2^s*z) := by rw [he]; grind
  rw [e]
  exact S.order.mul hw hs

/-- Prime ideal of an embedded order. Membership is false outside the order. -/
structure Prime (A : Order R) (P : R → Prop) : Prop where
  inside : ∀ {x}, P x → A.mem x
  zero : P 0
  proper : ¬P 1
  add : ∀ {x y}, P x → P y → P (x+y)
  neg : ∀ {x}, P x → P (-x)
  absorb : ∀ {x y}, P x → A.mem y → P (x*y)
  prime : ∀ {x y}, A.mem x → A.mem y → P (x*y) → P x ∨ P y

/-- The canonical prolongation specified by the old prime on constant coefficients. -/
def liftPrime (A : Order R) (t : R) (P : R → Prop) (x : R) : Prop :=
  ∃ a b, A.mem a ∧ A.mem b ∧ x=a+t*b ∧ P a

theorem lift_on_coordinates {n : Nat} {d t : R} (S : Stage n d) (ht : t*t=2*t-d)
    {P : R → Prop} (hP : Prime S.order P) (pd : P d)
    {a b : R} (ha : S.order.mem a) (hb : S.order.mem b) :
    liftPrime S.order t P (a+t*b) ↔ P a := by
  constructor
  · rintro ⟨c,e,hc,he,eq,pc⟩
    let B := (nextStage S t ht).order
    have div : Multiple B t ((a-c)+t*0) :=
      ⟨e-b,base_mem _ S.root ht (sub_mem _ he hb),by grind⟩
    obtain ⟨w,hw,ew⟩ := (constant_iff _ S.root ht S.radical S.overTwo
      (sub_mem _ ha hc) S.order.zero).mp div
    have p := hP.add pc (hP.absorb pd hw)
    rwa [show c+d*w=a by grind] at p
  · intro pa
    exact ⟨a,b,ha,hb,rfl,pa⟩

theorem lifted_prime {n : Nat} {d t : R} (S : Stage n d) (ht : t*t=2*t-d)
    {P : R → Prop} (hp : Prime S.order P) (pd : P d) :
    Prime (nextStage S t ht).order (liftPrime S.order t P) := by
  let A := S.order
  have coord := @lift_on_coordinates _ _ n d t S ht P hp pd
  constructor
  · rintro _ ⟨a,b,ha,hb,e,_⟩; exact ⟨a,b,ha,hb,e⟩
  · exact ⟨0,0,A.zero,A.zero,by grind,hp.zero⟩
  · intro hx
    apply hp.proper
    apply (coord A.one A.zero).mp
    rwa [show (1:R)+t*0=1 by grind]
  · rintro _ _ ⟨a,b,ha,hb,rfl,pa⟩ ⟨c,f,hc,hf,rfl,pc⟩
    exact ⟨a+c,b+f,A.add ha hc,A.add hb hf,by grind,hp.add pa pc⟩
  · rintro _ ⟨a,b,ha,hb,rfl,pa⟩
    exact ⟨-a,-b,A.neg ha,A.neg hb,by grind,hp.neg pa⟩
  · rintro _ _ ⟨a,b,ha,hb,rfl,pa⟩ ⟨c,f,hc,hf,rfl⟩
    refine ⟨a*c-d*(b*f),a*f+b*c+2*(b*f),sub_mem A (A.mul ha hc) (A.mul S.root (A.mul hb hf)),
      A.add (A.add (A.mul ha hf) (A.mul hb hc)) (A.mul (two_mem A) (A.mul hb hf)),by grind,?_⟩
    have h := hp.add (hp.absorb pa hc) (hp.neg (hp.absorb pd (A.mul hb hf)))
    rwa [show a*c+ -(d*(b*f))=a*c-d*(b*f) by grind] at h
  · rintro _ _ ⟨a,b,ha,hb,rfl⟩ ⟨c,f,hc,hf,rfl⟩ hz
    have e : (a+t*b)*(c+t*f)=(a*c-d*(b*f))+t*(a*f+b*c+2*(b*f)) := by grind
    rw [e] at hz
    have hpc := (coord (sub_mem A (A.mul ha hc) (A.mul S.root (A.mul hb hf)))
      (A.add (A.add (A.mul ha hf) (A.mul hb hc)) (A.mul (two_mem A) (A.mul hb hf)))).mp hz
    have hp0 := hp.add hpc (hp.absorb pd (A.mul hb hf))
    rw [show a*c-d*(b*f)+d*(b*f)=a*c by grind] at hp0
    rcases hp.prime ha hc hp0 with p | p
    · exact Or.inl ((coord ha hb).mpr p)
    · exact Or.inr ((coord hc hf).mpr p)

theorem lift_restricts {n : Nat} {d t : R} (S : Stage n d) (ht : t*t=2*t-d)
    {P : R → Prop} (hP : Prime S.order P) (pd : P d) (x : R) (hx : S.order.mem x) :
    liftPrime S.order t P x ↔ P x := by
  have h := lift_on_coordinates S ht hP pd hx S.order.zero
  rwa [show x+t*0=x by grind] at h

theorem one_step_unique {n : Nat} {d t : R} (S : Stage n d) (ht : t*t=2*t-d)
    {P Q : R → Prop} (hp : Prime S.order P) (pd : P d) (hq : Prime (nextStage S t ht).order Q)
    (contract : ∀ x, S.order.mem x → (Q x ↔ P x)) : Q=liftPrime S.order t P := by
  let B := (nextStage S t ht).order
  have mt : B.mem t := root_mem S.order S.root ht
  obtain ⟨w,hw,ew⟩ := S.overTwo
  have p2 : P 2 := ew ▸ hp.absorb pd hw
  have q2 := (contract 2 (two_mem _)).mpr p2
  have qd := (contract d S.root).mpr pd
  have h := hq.add (hq.absorb q2 mt) (hq.neg qd)
  have ht' : 2*t+ -d=t*t := by grind
  rw [ht'] at h
  have qt : Q t := (hq.prime mt mt h).elim id id
  funext x
  apply propext
  constructor
  · intro qx
    obtain ⟨a,b,ha,hb,ex⟩ := hq.inside qx
    have hqa := hq.add qx (hq.neg (hq.absorb qt (base_mem _ S.root ht hb)))
    rw [show x+ -(t*b)=a by grind] at hqa
    exact ⟨a,b,ha,hb,ex,(contract a ha).mp hqa⟩
  · rintro ⟨a,b,ha,hb,rfl,pa⟩
    exact hq.add ((contract a ha).mpr pa) (hq.absorb qt (base_mem _ S.root ht hb))

theorem prime_contraction (A B : Order R) (incl : ∀ x, A.mem x → B.mem x)
    {Q : R → Prop} (h : Prime B Q) : Prime A (fun x => A.mem x ∧ Q x) where
  inside hx := hx.1
  zero := ⟨A.zero,h.zero⟩
  proper hx := h.proper hx.2
  add hx hy := ⟨A.add hx.1 hy.1,h.add hx.2 hy.2⟩
  neg hx := ⟨A.neg hx.1,h.neg hx.2⟩
  absorb hx hy := ⟨A.mul hx.1 hy,h.absorb hx.2 (incl _ hy)⟩
  prime hx hy hz := (h.prime (incl _ hx) (incl _ hy) hz.2).imp (fun v => ⟨hx,v⟩) (fun v => ⟨hy,v⟩)

/-- A single prime above the chosen lower prime together with its contraction. -/
structure Labelled (A : Order R) (P : R → Prop) {n : Nat} {t : R} (S : Stage n t) where
  incl : ∀ x, A.mem x → S.order.mem x
  label : R → Prop
  prime : Prime S.order label
  point : label t
  restricts : ∀ x, A.mem x → (label x ↔ P x)
  unique : ∀ Q, Prime S.order Q → (∀ x, A.mem x → (Q x ↔ P x)) → Q=label

def baseLabel (A : Order R) (rad : Radical A 2) (P : R → Prop) (hp : Prime A P) (p2 : P 2) :
    Labelled A P (baseStage A rad) where
  incl _ hx := hx
  label := P
  prime := hp
  point := p2
  restricts _ _ := Iff.rfl
  unique Q hq hr := by
    funext x
    apply propext
    exact ⟨fun h => (hr x (hq.inside h)).mp h,fun h => (hr x (hp.inside h)).mpr h⟩

def nextLabel {A : Order R} {P : R → Prop} {n : Nat} {d : R} {S : Stage n d}
    (L : Labelled A P S) (t : R) (ht : t*t=2*t-d) : Labelled A P (nextStage S t ht) where
  incl x hx := base_mem S.order S.root ht (L.incl x hx)
  label := liftPrime S.order t L.label
  prime := lifted_prime S ht L.prime L.point
  point := ⟨0,1,S.order.zero,S.order.one,by grind,L.prime.zero⟩
  restricts x hx := (lift_restricts S ht L.prime L.point x (L.incl x hx)).trans (L.restricts x hx)
  unique Q hq hr := by
    let Qlo := fun x => S.order.mem x ∧ Q x
    have qp : Prime S.order Qlo := prime_contraction S.order (nextStage S t ht).order
      (fun _ hx => base_mem S.order S.root ht hx) hq
    have qr (x : R) (hx : A.mem x) : Qlo x ↔ P x :=
      ⟨fun h => (hr x hx).mp h.2,fun h => ⟨L.incl x hx,(hr x hx).mpr h⟩⟩
    have qe := L.unique Qlo qp qr
    apply one_step_unique S ht L.prime L.point hq
    intro x hx
    rw [← qe]
    exact ⟨fun h => ⟨hx,h⟩,And.right⟩

def cyclotomicLabel (A : Order R) (rad : Radical A 2) (P : R → Prop) (hp : Prime A P) (p2 : P 2) :
    (n : Nat) → (z : R) → (h : z^(2^n : Nat)= -1) → Labelled A P (cyclotomicStage A rad n z h)
  | 0,z,h => by
    have e : z= -1 := by simpa [Semiring.pow_one] using h
    subst z
    have tr {a b : R} (e : a=b) (s : Stage 0 a) (L : Labelled A P s) :
        Labelled A P (cast (congrArg (Stage 0) e) s) := by cases e; exact L
    exact tr (by grind : (2:R)=1-(-1)) (baseStage A rad) (baseLabel A rad P hp p2)
  | n+1,z,h => nextLabel (cyclotomicLabel A rad P hp p2 n (z*z) (squared_root_condition z n h))
      (1-z) (by grind)

/-- Every prime of the base above two has exactly one prolongation to this
root-generated order. The new prime contains 1−ζ and contracts to its label. -/
theorem unique_prime_at_root (A : Order R) (rad : Radical A 2) (P : R → Prop) (hp : Prime A P)
    (p2 : P 2) (n : Nat) (z : R) (h : z^(2^n : Nat)= -1) :
    let B := (cyclotomicStage A rad n z h).order
    ∃ Q : R → Prop, Prime B Q ∧ Q (1-z) ∧ (∀ x, A.mem x → (Q x ↔ P x)) ∧
      ∀ Q', Prime B Q' → (∀ x, A.mem x → (Q' x ↔ P x)) → Q'=Q := by
  let L := cyclotomicLabel A rad P hp p2 n z h
  exact ⟨L.label,L.prime,L.point,L.restricts,L.unique⟩

end Reimann.DyadicRamifiedOrder69
