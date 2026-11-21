import Reimann.CircularReduction69
import Reimann.CircularPrimitive69
import Reimann.CircularNonpower69

/-! The integral two-generator presentation at the coprime conductors
69 and 277. Elements are taken modulo polynomial multiples of Φ69(X) and
Φ277(Y), independently of the chosen auxiliary residue. -/

namespace Reimann.CircularAmbient69

open Lean.Grind Reimann.CircularPolynomial69

attribute [local instance] Ring.intCast

/-- Polynomials in the second generator with integer polynomials in X as atoms. -/
inductive Term where
  | base (p : List Int)
  | Y
  | plus (a b : Term)
  | times (a b : Term)

def value {R : Type} [CommRing R] (x y : R) : Term → R
  | .base p => eval x p
  | .Y => y
  | .plus a b => value x y a + value x y b
  | .times a b => value x y a * value x y b

def geometric {R : Type} [CommRing R] (y : R) : Nat → R
  | 0 => 0
  | n + 1 => 1 + y * geometric y n

theorem geometric_identity {R : Type} [CommRing R] (y : R) (n : Nat) :
    (y-1) * geometric y n = y^n - 1 := by
  induction n with
  | zero => simp only [geometric, Semiring.mul_zero, Semiring.pow_zero]; grind only
  | succ n ih =>
    rw [geometric, Semiring.pow_succ]
    calc
      _ = y - 1 + y * ((y - 1) * geometric y n) := by grind only
      _ = _ := by rw [ih]; grind only

/-- An explicit pair of ideal-membership witnesses, with identity at all
values of both variables in every commutative ring. -/
def Related (a b : Term) : Prop :=
  ∃ c d : Term, ∀ (R : Type) [CommRing R] (x y : R),
    value x y a = value x y b + eval x phi * value x y c + geometric y 277 * value x y d

theorem value_integer {R : Type} [CommRing R] (x y : R) (n : Int) :
    value x y (.base [n]) = Int.cast n := by
  simp [value, eval, Semiring.mul_zero, Semiring.add_zero]

theorem related_refl (a : Term) : Related a a := by
  refine ⟨.base [], .base [], ?_⟩
  intro R _ x y
  simp [value, eval, Semiring.mul_zero, Semiring.add_zero]

theorem related_symm {a b : Term} (h : Related a b) : Related b a := by
  obtain ⟨c,d,h⟩ := h
  refine ⟨.times (.base [-1]) c, .times (.base [-1]) d, ?_⟩
  intro R _ x y
  rw [h R x y]
  change _ = _ + _ * (value x y (.base [-1]) * _) + _ * (value x y (.base [-1]) * _)
  rw [value_integer, Ring.intCast_neg, Ring.intCast_one]
  grind only

theorem related_trans {a b c : Term} (h : Related a b) (k : Related b c) : Related a c := by
  obtain ⟨d,e,hd⟩ := h
  obtain ⟨f,g,hf⟩ := k
  refine ⟨.plus d f, .plus e g, ?_⟩
  intro R _ x y
  rw [hd R x y, hf R x y]
  simp only [value]
  grind only

theorem related_times {a b c d : Term} (h : Related a b) (k : Related c d) :
    Related (.times a c) (.times b d) := by
  obtain ⟨s,t,hs⟩ := h
  obtain ⟨u,v,hu⟩ := k
  refine ⟨.plus (.times s c) (.times b u), .plus (.times t c) (.times b v), ?_⟩
  intro R _ x y
  simp only [value, hs R x y, hu R x y]
  grind only

def ambientSetoid : Setoid Term where
  r := Related
  iseqv := ⟨related_refl, related_symm, related_trans⟩

abbrev Ambient := Quotient ambientSetoid

def termClass (a : Term) : Ambient := Quotient.mk ambientSetoid a

theorem entry_compatible {p q : List Int} (h : CircularReduction69.Congruent p q) :
    Related (.base p) (.base q) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.base c, .base [], ?_⟩
  intro R _ x y
  simpa only [value, eval, Semiring.mul_zero, Semiring.add_zero] using hc R x

/-- Map the old integral presentation into the two-generator presentation. -/
def from69 : CircularReduction69.ResidueOrder → Ambient :=
  Quotient.lift (fun p => termClass (.base p))
    (fun _ _ h => Quotient.sound (s := ambientSetoid) (entry_compatible h))

def times (u v : Ambient) : Ambient :=
  Quotient.liftOn₂ u v (fun a b => termClass (.times a b))
    (fun _ _ _ _ h k => Quotient.sound (s := ambientSetoid) (related_times h k))

def power (u : Ambient) : Nat → Ambient
  | 0 => termClass (.base [1])
  | n+1 => times (power u n) u

theorem value_at_roots {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0)
    {a b : Term} (h : Related a b) : value x y a = value x y b := by
  obtain ⟨c,d,hd⟩ := h
  simpa only [hx, hy, Semiring.zero_mul, Semiring.add_zero] using hd R x y

def atRoots {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) : Ambient → R :=
  Quotient.lift (value x y) (fun _ _ h => value_at_roots x y hx hy h)

theorem atRoots_from69 {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) (u : CircularReduction69.ResidueOrder) :
    atRoots x y hx hy (from69 u) = CircularReduction69.atRoot x hx u :=
  Quotient.inductionOn u (fun _ => rfl)

theorem atRoots_times {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) (u v : Ambient) :
    atRoots x y hx hy (times u v) = atRoots x y hx hy u * atRoots x y hx hy v :=
  Quotient.inductionOn₂ u v (fun _ _ => rfl)

theorem atRoots_power {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) (u : Ambient) (n : Nat) :
    atRoots x y hx hy (power u n) = (atRoots x y hx hy u)^n := by
  induction n with
  | zero =>
    change value x y (.base [1]) = _^0
    rw [value_integer, Ring.intCast_one, Semiring.pow_zero]
  | succ n ih => rw [power, atRoots_times, ih, Semiring.pow_succ]

theorem auxiliary_root_277 : geometric (49063 : Fin 114679) 277 = 0 := by
  decide +kernel

def reduce : Ambient → Fin 114679 :=
  atRoots 21767 49063 CircularReduction69.auxiliary_root auxiliary_root_277

theorem reduce_from69 (u : CircularReduction69.ResidueOrder) :
    reduce (from69 u) = CircularReduction69.reduce u := atRoots_from69 ..

theorem reduce_power (u : Ambient) (n : Nat) :
    reduce (power u n) = (reduce u)^n := atRoots_power ..

theorem signed_residues :
    reduce (from69 (CircularReduction69.signedClass 1)) = 48891 ∧
    reduce (from69 (CircularReduction69.signedClass 276)) = 65813 :=
  ⟨(reduce_from69 _).trans CircularReduction69.reduce_positive,
   (reduce_from69 _).trans CircularReduction69.reduce_negative⟩

theorem signed_nonpowers_in_ambient (u : Ambient) :
    power u 277 ≠ from69 (CircularReduction69.signedClass 1) ∧
    power u 277 ≠ from69 (CircularReduction69.signedClass 276) := by
  obtain ⟨hp,hn⟩ := CircularNonpower69.signed_nonpowers (reduce u)
  constructor
  · intro h
    exact hp ((reduce_power u 277).symm.trans ((congrArg reduce h).trans signed_residues.1))
  · intro h
    exact hn ((reduce_power u 277).symm.trans ((congrArg reduce h).trans signed_residues.2))

theorem first_generator_power {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    x^69 = 1 := by
  have h := phi_factorization x
  rw [hx, Semiring.zero_mul] at h
  have g := CircularPrimitive69.conductor_factor_identity x
  rw [← h, Semiring.mul_zero] at g
  grind only

theorem second_generator_power {R : Type} [CommRing R] (y : R) (hy : geometric y 277 = 0) :
    y^277 = 1 := by
  have h := geometric_identity y 277
  rw [hy, Semiring.mul_zero] at h
  grind only

theorem iterated_power {R : Type} [CommRing R] (u : R) (m n : Nat) :
    (u^m)^n = u^(m*n) := by
  induction n with
  | zero => simp [Semiring.pow_zero]
  | succ n ih => rw [Semiring.pow_succ, ih, Nat.mul_succ, Semiring.pow_add]

theorem periodic_power {R : Type} [CommRing R] (u : R) (m k n : Nat) (hu : u^m = 1) :
    u^(m*k + n) = u^n := by
  rw [Semiring.pow_add, ← iterated_power, hu, Semiring.one_pow, Semiring.one_mul]

/-- 277 - 4*69 = 1. The generator is X times the inverse fourth power of Y. -/
def jointGenerator : Ambient := times (termClass (.base [0,1])) (power (termClass .Y) 273)

theorem atRoots_jointGenerator {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) :
    atRoots x y hx hy jointGenerator = x*y^273 := by
  rw [jointGenerator, atRoots_times, atRoots_power]
  change eval x [0,1] * y^273 = _
  rw [← CircularReduction69.atRoot_polyClass x hx [0,1],
    CircularReduction69.atRoot_generator x hx]

theorem recover_first_generator {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) :
    (x*y^273)^277 = x := by
  rw [CommSemiring.mul_pow, iterated_power]
  have h := periodic_power x 69 4 1 (first_generator_power x hx)
  have k := periodic_power y 277 273 0 (second_generator_power y hy)
  change x^277 = x^1 at h
  change y^(273*277) = y^0 at k
  rw [h, k, Semiring.pow_one, Semiring.pow_zero, Semiring.mul_one]

theorem recover_second_generator {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) :
    (x*y^273)^69 = y := by
  rw [CommSemiring.mul_pow, first_generator_power x hx, Semiring.one_mul, iterated_power]
  have k := periodic_power y 277 68 1 (second_generator_power y hy)
  change y^(273*69) = y^1 at k
  rw [k, Semiring.pow_one]

theorem joint_generator_residue : reduce jointGenerator = 46656 := by
  unfold reduce
  rw [atRoots_jointGenerator]
  decide +kernel

theorem joint_residue_powers :
    (46656 : Fin 114679)^277 = 21767 ∧ (46656 : Fin 114679)^69 = 49063 := by
  decide +kernel

theorem related_of_identity {a b : Term}
    (h : ∀ (R : Type) [CommRing R] (x y : R), value x y a = value x y b) :
    Related a b := by
  refine ⟨.base [], .base [], ?_⟩
  intro R _ x y
  simpa only [value, eval, Semiring.mul_zero, Semiring.add_zero] using h R x y

theorem from69_times (u v : CircularReduction69.ResidueOrder) :
    from69 (CircularReduction69.qmul u v) = times (from69 u) (from69 v) := by
  induction u, v using Quotient.inductionOn₂ with
  | _ p q =>
    apply Quotient.sound (s := ambientSetoid)
    apply related_of_identity
    intro R _ x y
    exact CircularReduction69.eval_mul x p q

theorem signed_units_in_ambient :
    times (from69 (CircularReduction69.signedClass 1))
      (from69 (CircularReduction69.signedClass 276)) = termClass (.base [1]) := by
  rw [← from69_times, CircularReduction69.signed_classes_multiply_one]
  rfl

theorem related_plus {a b c d : Term} (h : Related a b) (k : Related c d) :
    Related (.plus a c) (.plus b d) := by
  obtain ⟨s,t,hs⟩ := h
  obtain ⟨u,v,hu⟩ := k
  refine ⟨.plus s u, .plus t v, ?_⟩
  intro R _ x y
  simp only [value, hs R x y, hu R x y]
  grind only

def plus (u v : Ambient) : Ambient :=
  Quotient.liftOn₂ u v (fun a b => termClass (.plus a b))
    (fun _ _ _ _ h k => Quotient.sound (s := ambientSetoid) (related_plus h k))

theorem atRoots_plus {R : Type} [CommRing R] (x y : R)
    (hx : eval x phi = 0) (hy : geometric y 277 = 0) (u v : Ambient) :
    atRoots x y hx hy (plus u v) = atRoots x y hx hy u + atRoots x y hx hy v :=
  Quotient.inductionOn₂ u v (fun _ _ => rfl)

theorem from69_plus (u v : CircularReduction69.ResidueOrder) :
    from69 (CircularReduction69.qadd u v) = plus (from69 u) (from69 v) := by
  induction u, v using Quotient.inductionOn₂ with
  | _ p q =>
    apply Quotient.sound (s := ambientSetoid)
    apply related_of_identity
    intro R _ x y
    exact eval_add x p q

end Reimann.CircularAmbient69
