import Reimann.CircularAmbient69
import Reimann.DyadicRealLayer

/-! The prime above two in the pure cyclotomic presentation at conductor
2^(n+1), with uniformizer 1-ζ and ramification exponent 2^n. -/
namespace Reimann.DyadicCyclotomicRamification69

open Lean.Grind
open CircularAmbient69 (geometric geometric_identity)

attribute [local instance] Ring.intCast

theorem geometric_append {R : Type} [CommRing R] (z : R) (a b : Nat) :
    geometric z (a+b) = geometric z a + z^a*geometric z b := by
  induction a with
  | zero => simp [geometric, Semiring.pow_zero, Semiring.one_mul] <;> grind only
  | succ a ih =>
    rw [Nat.succ_add, geometric, ih, geometric, Semiring.pow_succ]
    grind only

theorem geometric_blocks {R : Type} [CommRing R] (z : R) (d k : Nat) :
    geometric z (d*k) = geometric z d * geometric (z^d) k := by
  induction k with
  | zero => simp [geometric, Semiring.mul_zero]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (d*k) d, geometric_append, ih, geometric]
    grind only

theorem geometric_period {R : Type} [CommRing R] {z : R} {e : Nat} (hz : z^e = -1) :
    geometric z (2*e) = 0 ∧ z^(2*e) = 1 := by
  rw [Nat.two_mul, geometric_append, Semiring.pow_add, hz]
  constructor <;> grind only

theorem geometric_one_mod_period {R : Type} [CommRing R] {z : R} {e : Nat}
    (hz : z^e = -1) (k : Nat) : geometric z ((2*e)*k+1) = 1 := by
  rw [Nat.add_comm, geometric_append, geometric_blocks, (geometric_period hz).1]
  simp only [geometric, Semiring.pow_one, Semiring.mul_zero, Semiring.zero_mul, Semiring.add_zero]

/-- The geometric sum for the odd exponent e+1 carries 1-ζ to 1+ζ.
Its inverse is the same sum at ζ^(e+1). -/
theorem odd_geometric_unit {R : Type} [CommRing R] {z : R} (d : Nat)
    (hz : z^(2*d) = -1) :
    geometric z (2*d+1)*geometric (z^(2*d+1)) (2*d+1) = 1 ∧
    (1-z)*geometric z (2*d+1) = 1+z := by
  constructor
  · rw [←geometric_blocks, show (2*d+1)*(2*d+1) = (2*(2*d))*(d+1)+1 by grind only]
    exact geometric_one_mod_period hz _
  · have h := geometric_identity z (2*d+1)
    rw [Semiring.pow_succ, hz] at h
    grind only

/-- For a root of X^(2^n)+1 the ideal (2) is the 2^n-th power of
(1-ζ). Both the multiplier and its inverse are constructed within R. -/
theorem ramification_factor {R : Type} [CommRing R] (n : Nat) (z : R)
    (hz : z^(2^n : Nat) = -1) :
    ∃ u v : R, u*v=1 ∧ (2:R)=(1-z)^(2^n : Nat)*u := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.pow_zero, Semiring.pow_one] at hz ⊢
    exact ⟨1,1,by grind only,by rw [hz]; grind only⟩
  | succ n ih =>
    have he : 2^(n+1) = 2*(2^n) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hs : (z*z)^(2^n : Nat) = -1 := by
      rw [CommSemiring.mul_pow, ←Semiring.pow_add, ←Nat.two_mul, ←he, hz]
    obtain ⟨u,v,hu,h⟩ := ih (z*z) hs
    have hg := odd_geometric_unit (2^n) (he ▸ hz)
    let g := geometric z (2*(2^n)+1)
    let j := geometric (z^(2*(2^n)+1)) (2*(2^n)+1)
    have hgj : g*j=1 := hg.1
    have hplus : (1-z)*g = 1+z := hg.2
    have heq : 1-z*z = ((1-z)*(1-z))*g := by
      calc
        _ = (1-z)*(1+z) := by grind only
        _ = _ := by rw [←hplus]; grind only
    refine ⟨g^(2^n : Nat)*u,j^(2^n : Nat)*v,?_,?_⟩
    · have hpow : g^(2^n : Nat)*j^(2^n : Nat)=1 := by
        rw [←CommSemiring.mul_pow, hgj, Semiring.one_pow]
      calc
        _ = (g^(2^n : Nat)*j^(2^n : Nat))*(u*v) := by grind only
        _ = 1 := by rw [hpow, hu]; grind only
    · rw [h,heq,CommSemiring.mul_pow,CommSemiring.mul_pow,he,Nat.two_mul,Semiring.pow_add]
      grind only

theorem principal_ideal_equality {R : Type} [CommRing R] (n : Nat) (z : R)
    (hz : z^(2^n : Nat) = -1) (x : R) :
    (∃ a, x=2*a) ↔ ∃ b, x=(1-z)^(2^n : Nat)*b := by
  obtain ⟨u,v,hu,h⟩ := ramification_factor n z hz
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨u*a,by rw [h]; grind only⟩
  · rintro ⟨b,rfl⟩
    refine ⟨v*b,?_⟩
    rw [h]
    calc
      _ = (1-z)^(2^n : Nat)*(u*v)*b := by rw [hu]; grind only
      _ = _ := by grind only

/-- Equality of two integral polynomials in the algebra presented by
Z and one generator subject to X^(2^n)=-1, tested in all its models. -/
def presentation (n : Nat) : Setoid (List Int) where
  r p q := ∀ (R : Type) [CommRing R] (z : R), z^(2^n : Nat) = -1 →
    CircularPolynomial69.eval z p = CircularPolynomial69.eval z q
  iseqv := ⟨fun _ _ _ _ _ => rfl, fun h R _ z hz => (h R z hz).symm,
    fun h k R _ z hz => (h R z hz).trans (k R z hz)⟩

abbrev Order (n : Nat) := Quotient (presentation n)

def poly (n : Nat) (p : List Int) : Order n := Quotient.mk _ p

def atRoot {n : Nat} {R : Type} [CommRing R] (z : R) (hz : z^(2^n : Nat) = -1) :
    Order n → R := Quotient.lift (CircularPolynomial69.eval z) (fun _ _ h => h R z hz)

theorem order_ext {n : Nat} {a b : Order n}
    (h : ∀ (R : Type) [CommRing R] (z : R) (hz : z^(2^n : Nat) = -1),
      atRoot z hz a = atRoot z hz b) : a=b := by
  induction a using Quotient.inductionOn with
  | _ p =>
    induction b using Quotient.inductionOn with
    | _ q => exact Quotient.sound h

def add {n : Nat} (a b : Order n) : Order n := Quotient.liftOn₂ a b
  (fun p q => poly n (CircularPolynomial69.add p q)) (by
    intro p q p' q' h k
    apply Quotient.sound
    intro R _ z hz
    simp only [CircularPolynomial69.eval_add, h R z hz, k R z hz])

def mul {n : Nat} (a b : Order n) : Order n := Quotient.liftOn₂ a b
  (fun p q => poly n (CircularReduction69.mul p q)) (by
    intro p q p' q' h k
    apply Quotient.sound
    intro R _ z hz
    simp only [CircularReduction69.eval_mul, h R z hz, k R z hz])

theorem atRoot_add {n : Nat} {R : Type} [CommRing R] (z : R) (hz : z^(2^n : Nat) = -1)
    (a b : Order n) : atRoot z hz (add a b) = atRoot z hz a + atRoot z hz b :=
  Quotient.inductionOn₂ a b (CircularPolynomial69.eval_add z)

theorem atRoot_mul {n : Nat} {R : Type} [CommRing R] (z : R) (hz : z^(2^n : Nat) = -1)
    (a b : Order n) : atRoot z hz (mul a b) = atRoot z hz a * atRoot z hz b :=
  Quotient.inductionOn₂ a b (CircularReduction69.eval_mul z)

theorem atRoot_scalar {n : Nat} {R : Type} [CommRing R] (z : R) (hz : z^(2^n : Nat) = -1)
    (a : Int) : atRoot z hz (poly n [a]) = (a : R) := by
  change CircularPolynomial69.eval z [a] = _
  simp [CircularPolynomial69.eval, Semiring.mul_zero, Semiring.add_zero]

def power {n : Nat} (a : Order n) : Nat → Order n
  | 0 => poly n [1]
  | k+1 => mul (power a k) a

theorem atRoot_power {n : Nat} {R : Type} [CommRing R] (z : R) (hz : z^(2^n : Nat) = -1)
    (a : Order n) (k : Nat) : atRoot z hz (power a k) = (atRoot z hz a)^k := by
  induction k with
  | zero => rw [power, atRoot_scalar, Ring.intCast_one, Semiring.pow_zero]
  | succ k ih => rw [power, atRoot_mul, ih, Semiring.pow_succ]

@[instance_reducible]
def orderRing (n : Nat) : CommRing (Order n) := by
  refine {
    add := add
    mul := mul
    neg := fun x => mul (poly n [-1]) x
    sub := fun x y => add x (mul (poly n [-1]) y)
    intCast := ⟨fun a => poly n [a]⟩
    natCast := ⟨fun a => poly n [a]⟩
    ofNat := fun a => ⟨poly n [a]⟩
    nsmul := ⟨fun a x => mul (poly n [a]) x⟩
    zsmul := ⟨fun a x => mul (poly n [a]) x⟩
    npow := ⟨power⟩
    pow_zero := fun _ => rfl
    pow_succ := fun _ _ => rfl
    sub_eq_add_neg := fun _ _ => rfl
    add_zero := fun a => show add a (poly n [0]) = a from ?_
    add_comm := fun a b => show add a b=add b a from ?_
    add_assoc := fun a b c => show add (add a b) c=add a (add b c) from ?_
    mul_assoc := fun a b c => show mul (mul a b) c=mul a (mul b c) from ?_
    mul_one := fun a => show mul a (poly n [1])=a from ?_
    one_mul := fun a => show mul (poly n [1]) a=a from ?_
    mul_comm := fun a b => show mul a b=mul b a from ?_
    zero_mul := fun a => show mul (poly n [0]) a=poly n [0] from ?_
    mul_zero := fun a => show mul a (poly n [0])=poly n [0] from ?_
    left_distrib := fun a b c => show mul a (add b c)=add (mul a b) (mul a c) from ?_
    right_distrib := fun a b c => show mul (add a b) c=add (mul a c) (mul b c) from ?_
    ofNat_succ := fun i => show poly n [((i+1 : Nat) : Int)] = add (poly n [i]) (poly n [1]) from ?_
    neg_add_cancel := fun a => show add (mul (poly n [-1]) a) a=poly n [0] from ?_
    intCast_neg := fun i => show poly n [-i]=mul (poly n [-1]) (poly n [i]) from ?_
    neg_zsmul := fun i a => show mul (poly n [-i]) a=mul (poly n [-1]) (mul (poly n [i]) a) from ?_ }
  all_goals
    intros
    apply order_ext
    intro R _ z hz
    simp only [atRoot_add,atRoot_mul,atRoot_scalar,Ring.intCast_neg,Ring.intCast_zero,
      Ring.intCast_one,Int.natCast_succ,Ring.intCast_add] <;> grind only

attribute [instance] orderRing

def zeta (n : Nat) : Order n := poly n [0,1]

theorem atRoot_zeta {n : Nat} {R : Type} [CommRing R] (z : R)
    (hz : z^(2^n : Nat) = -1) : atRoot z hz (zeta n) = z := by
  change CircularPolynomial69.eval z [0,1] = z
  simp only [CircularPolynomial69.eval, Ring.intCast_zero, Ring.intCast_one]
  grind only

theorem zeta_half_order (n : Nat) : (zeta n)^(2^n : Nat) = -1 := by
  apply order_ext
  intro R _ z hz
  change atRoot z hz (power (zeta n) _) = atRoot z hz (mul (poly n [-1]) (poly n [1]))
  rw [atRoot_power, atRoot_zeta, hz, atRoot_mul, atRoot_scalar, atRoot_scalar,
    Ring.intCast_neg, Ring.intCast_one, Semiring.mul_one]

theorem order_ramification (n : Nat) :
    ∃ u v : Order n, u*v=1 ∧ (2 : Order n)=(1-zeta n)^(2^n : Nat)*u :=
  ramification_factor n _ (zeta_half_order n)

/-- The residue specialization sends ζ to one in F₂. -/
def residue (n : Nat) : Order n → Fin 2 :=
  atRoot 1 (by rw [Semiring.one_pow]; decide +kernel)

theorem residue_surjective (n : Nat) (b : Fin 2) : ∃ x, residue n x = b := by
  have H : ∀ i : Fin 2, (Int.cast (R := Fin 2) (i.val : Int)) = i := by decide +kernel
  exact ⟨poly n [b.val], (atRoot_scalar _ _ _).trans (H b)⟩

/-- Coefficient list for (f(X)-f(1))/(1-X). -/
def difference : List Int → List Int
  | [] => []
  | _::p => CircularPolynomial69.add (difference p) (p.map (fun a => (-1 : Int)*a))

theorem difference_identity {R : Type} [CommRing R] (z : R) (p : List Int) :
    CircularPolynomial69.eval z p =
      (p.sum : R) + (1-z)*CircularPolynomial69.eval z (difference p) := by
  induction p with
  | nil => simp only [difference, CircularPolynomial69.eval, List.sum_nil, Ring.intCast_zero]; grind only
  | cons c p ih =>
    simp only [difference, CircularPolynomial69.eval_add, CircularPolynomial69.eval_scale,
      CircularPolynomial69.eval, List.sum_cons, Ring.intCast_add, Ring.intCast_neg, Ring.intCast_one]
    grind only

theorem translate_to_one (n : Nat) (p : List Int) : poly n p =
    poly n [p.sum] + (1-zeta n)*poly n (difference p) := by
  apply order_ext
  intro R _ z hz
  change CircularPolynomial69.eval z p = atRoot z hz (add (poly n [p.sum])
    (mul (add (poly n [1]) (mul (poly n [-1]) (zeta n))) (poly n (difference p))))
  rw [atRoot_add,atRoot_mul,atRoot_add,atRoot_mul,atRoot_zeta,atRoot_scalar,atRoot_scalar,
    atRoot_scalar,Ring.intCast_neg,Ring.intCast_one]
  change _ = _ + (1 + -1*z)*CircularPolynomial69.eval z (difference p)
  rw [show 1 + -1*z = 1-z by grind only]
  exact difference_identity z p

theorem two_multiple (n : Nat) : ∃ q : Order n, 2=(1-zeta n)*q := by
  refine ⟨geometric (zeta n) (2^n),?_⟩
  have h := geometric_identity (zeta n) (2^n)
  rw [zeta_half_order] at h
  grind only

/-- Every element of Z[ζ] is zero or one modulo 1-ζ. -/
theorem two_cosets (n : Nat) (x : Order n) :
    (∃ q, x=(1-zeta n)*q) ∨ (∃ q, x=1+(1-zeta n)*q) := by
  induction x using Quotient.inductionOn with
  | _ p =>
    obtain ⟨d,hd⟩ := two_multiple n
    have hx := translate_to_one n p
    let k := p.sum/2
    have hc : p.sum = 2*k ∨ p.sum = 1+2*k := by dsimp [k]; omega
    rcases hc with h | h
    · left
      refine ⟨d*(k : Order n)+poly n (difference p),?_⟩
      change poly n p = _
      have e := congrArg (fun a : Int => (a : Order n)) h
      change (p.sum : Order n) = ((2*k : Int) : Order n) at e
      rw [Ring.intCast_mul,Ring.intCast_ofNat,hd] at e
      change poly n [p.sum] = _ at e
      rw [hx,e]
      grind only
    · right
      refine ⟨d*(k : Order n)+poly n (difference p),?_⟩
      change poly n p = _
      have e := congrArg (fun a : Int => (a : Order n)) h
      change (p.sum : Order n) = ((1+2*k : Int) : Order n) at e
      rw [Ring.intCast_add,Ring.intCast_one,Ring.intCast_mul,Ring.intCast_ofNat,hd] at e
      change poly n [p.sum] = _ at e
      rw [hx,e]
      grind only

theorem residue_constants (n : Nat) : residue n 0=0 ∧ residue n 1=1 ∧
    residue n 2=0 ∧ residue n (1-zeta n)=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (atRoot_scalar _ _ 0).trans (by decide +kernel)
  · exact (atRoot_scalar _ _ 1).trans (by decide +kernel)
  · exact (atRoot_scalar _ _ 2).trans (by decide +kernel)
  · unfold residue
    change atRoot (1 : Fin 2) _ (add (poly n [1]) (mul (poly n [-1]) (zeta n))) = 0
    rw [atRoot_add,atRoot_mul,atRoot_scalar,atRoot_scalar,atRoot_zeta]
    decide +kernel

theorem kernel_is_uniformizer (n : Nat) (x : Order n) :
    residue n x = 0 ↔ ∃ q, x=(1-zeta n)*q := by
  have rd := (residue_constants n).2.2.2
  have ro := (residue_constants n).2.1
  have ha (a b : Order n) : residue n (a+b) = residue n a + residue n b := atRoot_add _ _ _ _
  have hm (a b : Order n) : residue n (a*b) = residue n a * residue n b := atRoot_mul _ _ _ _
  constructor
  · intro hx
    rcases two_cosets n x with h | ⟨q,h⟩
    · exact h
    · rw [h,ha,hm,rd,ro,Semiring.zero_mul,Semiring.add_zero] at hx
      exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hx)
  · rintro ⟨q,rfl⟩
    rw [hm,rd,Semiring.zero_mul]

structure PrimeAboveTwo {n : Nat} (P : Order n → Prop) : Prop where
  proper : ¬ P 1
  above : P 2
  add_mem : ∀ x y, P x → P y → P (x+y)
  neg_mem : ∀ x, P x → P (-x)
  absorb : ∀ x y, P x → P (x*y)
  prime : ∀ x y, P (x*y) → P x ∨ P y

theorem residue_prime (n : Nat) : PrimeAboveTwo (fun x => residue n x=0) := by
  have ha (a b : Order n) : residue n (a+b) = residue n a + residue n b := atRoot_add _ _ _ _
  have hm (a b : Order n) : residue n (a*b) = residue n a * residue n b := atRoot_mul _ _ _ _
  refine ⟨?_,(residue_constants n).2.2.1,?_,?_,?_,?_⟩
  · rw [(residue_constants n).2.1]; decide
  · intro x y hx hy
    rw [ha,hx,hy]; rfl
  · intro x hx
    change residue n ((poly n [-1])*x)=0
    rw [hm,hx,Semiring.mul_zero]
  · intro x y hx
    rw [hm,hx,Semiring.zero_mul]
  · intro x y h
    rw [hm] at h
    have zero_product : ∀ a b : Fin 2, a*b=0 → a=0 ∨ b=0 := by decide +kernel
    exact zero_product _ _ h

theorem uniformizer_mem {n : Nat} {P : Order n → Prop} (hp : PrimeAboveTwo P) :
    P (1-zeta n) := by
  obtain ⟨u,v,hunit,h⟩ := order_ramification n
  have hh := hp.absorb 2 v hp.above
  have eq : (2 : Order n)*v = (1-zeta n)^(2^n : Nat) := by
    rw [h, Semiring.mul_assoc, hunit, Semiring.mul_one]
  rw [eq] at hh
  have descend (k : Nat) : P ((1-zeta n)^(2^k : Nat)) → P (1-zeta n) := by
    induction k with
    | zero => simpa only [Nat.pow_zero,Semiring.pow_one] using (fun h : P (1-zeta n) => h)
    | succ k ih =>
      intro h
      rw [DyadicRealLayer.square_power] at h
      exact ih ((hp.prime _ _ h).elim id id)
  exact descend n hh

/-- The only prime containing 2 in the cyclotomic order is the kernel of
the surjective specialization ζ↦1 in F₂. -/
theorem unique_prime {n : Nat} {P : Order n → Prop} (hp : PrimeAboveTwo P) (x : Order n) :
    P x ↔ residue n x=0 := by
  have hd := uniformizer_mem hp
  rw [kernel_is_uniformizer]
  constructor
  · intro hx
    rcases two_cosets n x with h | ⟨q,hq⟩
    · exact h
    · have h := hp.add_mem _ _ hx (hp.neg_mem _ (hp.absorb _ q hd))
      rw [hq,show 1+(1-zeta n)*q + -((1-zeta n)*q) = 1 by grind only] at h
      exact False.elim (hp.proper h)
  · rintro ⟨q,rfl⟩
    exact hp.absorb _ q hd

/-- The two exact-order tests in a field imply the cyclotomic equation
used throughout, including the primitive generator at conductor two. -/
theorem half_order_of_primitive {K : Type} [Field K] (n : Nat) (z : K)
    (full : z^(2^(n+1) : Nat)=1) (primitive : z^(2^n : Nat)≠1) : z^(2^n : Nat) = -1 := by
  rw [DyadicRealLayer.square_power] at full
  have h : (z^(2^n : Nat)-1)*(z^(2^n : Nat)+1)=0 := by grind only
  obtain h | h := Field.of_mul_eq_zero h
  · exact False.elim (primitive (by grind only))
  · grind only

theorem lower_root (n : Nat) : (zeta (n+1)*zeta (n+1))^(2^n : Nat) = -1 := by
  rw [CommSemiring.mul_pow, ←DyadicRealLayer.square_power, zeta_half_order]

/-- Inclusion of the lower generator as the square of the next generator. -/
def transition (n : Nat) : Order n → Order (n+1) := atRoot _ (lower_root n)

theorem residue_transition (n : Nat) (x : Order n) : residue (n+1) (transition n x) = residue n x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    change residue (n+1) (CircularPolynomial69.eval (zeta (n+1)*zeta (n+1)) p) =
      CircularPolynomial69.eval (1 : Fin 2) p
    have hζ : residue (n+1) (zeta (n+1))=1 := atRoot_zeta _ _
    have ha (a b : Order (n+1)) : residue (n+1) (a+b) = residue (n+1) a + residue (n+1) b :=
      atRoot_add _ _ _ _
    have hm (a b : Order (n+1)) : residue (n+1) (a*b) = residue (n+1) a * residue (n+1) b :=
      atRoot_mul _ _ _ _
    have hc (c : Int) : residue (n+1) (c : Order (n+1)) = (c : Fin 2) := atRoot_scalar _ _ _
    induction p with
    | nil => exact (residue_constants _).1
    | cons c p ih => rw [CircularPolynomial69.eval,ha,hm,hm,hζ,hc,ih,CircularPolynomial69.eval]; grind only

theorem compatible_primes (n : Nat) (x : Order n) :
    (∃ q, transition n x=(1-zeta (n+1))*q) ↔ ∃ r, x=(1-zeta n)*r := by
  rw [←kernel_is_uniformizer, ←kernel_is_uniformizer, residue_transition]

/-- The same pair of integer polynomials gives the factor and inverse at
every root of the given conductor. In particular both lie in Z[ζ] itself. -/
theorem integral_unit_polynomials (n : Nat) :
    ∃ p q : List Int, ∀ (R : Type) [CommRing R] (z : R), z^(2^n : Nat) = -1 →
      CircularPolynomial69.eval z p * CircularPolynomial69.eval z q = 1 ∧
      (2 : R)=(1-z)^(2^n : Nat)*CircularPolynomial69.eval z p := by
  obtain ⟨u,v,hu,h⟩ := order_ramification n
  obtain ⟨p,rfl⟩ := Quotient.exists_rep u
  obtain ⟨q,rfl⟩ := Quotient.exists_rep v
  refine ⟨p,q,?_⟩
  intro R _ z hz
  have eu := congrArg (atRoot z hz) hu
  change atRoot z hz (mul (poly n p) (poly n q)) = atRoot z hz (poly n [1]) at eu
  rw [atRoot_mul,atRoot_scalar,Ring.intCast_one] at eu
  have eh := congrArg (atRoot z hz) h
  change atRoot z hz (poly n [2]) = atRoot z hz (mul
    (power (add (poly n [1]) (mul (poly n [-1]) (zeta n))) _) (poly n p)) at eh
  rw [atRoot_scalar, Ring.intCast_ofNat, atRoot_mul, atRoot_power, atRoot_add,
    atRoot_mul, atRoot_zeta, atRoot_scalar, atRoot_scalar, Ring.intCast_neg,
    Ring.intCast_one,show 1+ -1*z = 1-z by grind only] at eh
  exact ⟨eu,eh⟩

/-- On an actual generated integral order in any field, a prime above 2
has this same pullback, regardless of how the root is realized. -/
theorem generated_order_prime {K : Type} [Field K] (n : Nat) (z : K)
    (hfull : z^(2^(n+1) : Nat)=1) (hprim : z^(2^n : Nat)≠1)
    (P : K → Prop) (hp : PrimeAboveTwo (fun a => P (atRoot z (half_order_of_primitive n z hfull hprim) a)))
    (p : List Int) : P (CircularPolynomial69.eval z p) ↔ CircularPolynomial69.eval (1 : Fin 2) p=0 :=
  unique_prime hp (poly n p)

end Reimann.DyadicCyclotomicRamification69
