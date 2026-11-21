import Reimann.CircularPolynomial69

/-! Evaluation at the auxiliary residue, starting with integer polynomials.
Congruence modulo Φ₆₉ is witnessed by a polynomial multiple in the coefficient
ring, before any root or residue field has been chosen. -/

namespace Reimann.CircularReduction69

open Lean.Grind Reimann.CircularPolynomial69

attribute [local instance] Ring.intCast

def mul : List Int → List Int → List Int
  | [], _ => []
  | c :: p, q => add (q.map (fun b => c * b)) (0 :: mul p q)

theorem eval_mul {R : Type} [CommRing R] (x : R) (p q : List Int) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul, eval, Semiring.zero_mul]
  | cons c p ih =>
    simp only [mul, eval_add, eval_scale, eval, Ring.intCast_zero, ih]
    grind only

/-- The difference is a single multiple of Φ as a polynomial identity. -/
def Congruent (p q : List Int) : Prop :=
  ∃ k : List Int, ∀ (R : Type) [CommRing R] (x : R),
    eval x p = eval x q + eval x phi * eval x k

theorem congruent_of_identity (p q : List Int)
    (h : ∀ (R : Type) [CommRing R] (x : R), eval x p = eval x q) : Congruent p q := by
  refine ⟨[], ?_⟩
  intro R _ x
  rw [h R x]
  simp [eval, Semiring.mul_zero, Semiring.add_zero]

theorem congruent_refl (p : List Int) : Congruent p p :=
  congruent_of_identity p p (fun _ _ _ => rfl)

theorem congruent_symm {p q : List Int} (h : Congruent p q) : Congruent q p := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.map (fun a => (-1 : Int) * a), ?_⟩
  intro R _ x
  rw [eval_scale, Ring.intCast_neg, Ring.intCast_one, hk R x]
  grind only

theorem congruent_trans {p q r : List Int}
    (h : Congruent p q) (h' : Congruent q r) : Congruent p r := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := h'
  refine ⟨add k l, ?_⟩
  intro R _ x
  rw [eval_add, hk R x, hl R x]
  grind only

theorem congruent_add {p p' q q' : List Int}
    (h : Congruent p p') (h' : Congruent q q') : Congruent (add p q) (add p' q') := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := h'
  refine ⟨add k l, ?_⟩
  intro R _ x
  simp only [eval_add, hk R x, hl R x]
  grind only

theorem congruent_mul {p p' q q' : List Int}
    (h : Congruent p p') (h' : Congruent q q') : Congruent (mul p q) (mul p' q') := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := h'
  refine ⟨add (mul k q) (mul p' l), ?_⟩
  intro R _ x
  simp only [eval_add, eval_mul, hk R x, hl R x]
  grind only

def polynomialSetoid : Setoid (List Int) where
  r := Congruent
  iseqv := ⟨congruent_refl, congruent_symm, congruent_trans⟩

abbrev ResidueOrder := Quotient polynomialSetoid

def polyClass (p : List Int) : ResidueOrder := Quotient.mk polynomialSetoid p

theorem phi_class_zero : polyClass phi = polyClass [] := by
  apply Quotient.sound (s := polynomialSetoid)
  refine ⟨[1], ?_⟩
  intro R _ x
  simp only [eval, Ring.intCast_one, Semiring.mul_zero, Semiring.add_zero, Semiring.mul_one]
  grind only

def qadd (u v : ResidueOrder) : ResidueOrder :=
  Quotient.liftOn₂ u v (fun a b => polyClass (add a b))
    (fun _ _ _ _ h k => Quotient.sound (s := polynomialSetoid) (congruent_add h k))

def qmul (u v : ResidueOrder) : ResidueOrder :=
  Quotient.liftOn₂ u v (fun a b => polyClass (mul a b))
    (fun _ _ _ _ h k => Quotient.sound (s := polynomialSetoid) (congruent_mul h k))

def qone : ResidueOrder := polyClass [1]

def qpow (u : ResidueOrder) : Nat → ResidueOrder
  | 0 => qone
  | n + 1 => qmul (qpow u n) u

theorem eval_agrees_at_root {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0)
    {p q : List Int} (h : Congruent p q) : eval x p = eval x q := by
  obtain ⟨k, hk⟩ := h
  simpa only [hx, Semiring.zero_mul, Semiring.add_zero] using hk R x

def atRoot {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) : ResidueOrder → R :=
  Quotient.lift (eval x) (fun _ _ h => eval_agrees_at_root x hx h)

theorem atRoot_polyClass {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) (p : List Int) :
    atRoot x hx (polyClass p) = eval x p := rfl

theorem atRoot_constant {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) (n : Int) :
    atRoot x hx (polyClass [n]) = Int.cast n := by
  simp [atRoot_polyClass, eval, Semiring.mul_zero, Semiring.add_zero]

theorem atRoot_generator {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    atRoot x hx (polyClass [0,1]) = x := by
  simp only [atRoot_polyClass, eval, Ring.intCast_one, Ring.intCast_zero,
    Semiring.mul_zero, Semiring.add_zero, Semiring.mul_one]
  grind only

theorem atRoot_add {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) (u v : ResidueOrder) :
    atRoot x hx (qadd u v) = atRoot x hx u + atRoot x hx v :=
  Quotient.inductionOn₂ u v (fun a b => eval_add x a b)

theorem atRoot_mul {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) (u v : ResidueOrder) :
    atRoot x hx (qmul u v) = atRoot x hx u * atRoot x hx v :=
  Quotient.inductionOn₂ u v (fun a b => eval_mul x a b)

theorem auxiliary_root : eval (21767 : Fin 114679) phi = 0 := by
  decide +kernel

def reduce : ResidueOrder → Fin 114679 := atRoot 21767 auxiliary_root

theorem reduce_generator : reduce (polyClass [0,1]) = 21767 :=
  atRoot_generator 21767 auxiliary_root

theorem reduce_zero : reduce (polyClass []) = 0 := rfl

theorem reduce_one : reduce qone = 1 := by
  change eval (21767 : Fin 114679) [1] = 1
  decide +kernel

theorem reduce_add (u v : ResidueOrder) : reduce (qadd u v) = reduce u + reduce v :=
  atRoot_add 21767 auxiliary_root u v

theorem reduce_mul (u v : ResidueOrder) : reduce (qmul u v) = reduce u * reduce v :=
  atRoot_mul 21767 auxiliary_root u v

theorem reduce_pow (u : ResidueOrder) (n : Nat) : reduce (qpow u n) = (reduce u)^n := by
  induction n with
  | zero => simpa only [qpow, Semiring.pow_zero] using reduce_one
  | succ n ih => rw [qpow, reduce_mul, ih, Semiring.pow_succ]

def signedClass (sign : Nat) : ResidueOrder := polyClass (factors (exponents sign))

theorem atRoot_signedClass {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) (s : Nat) :
    atRoot x hx (signedClass s) = signedProduct x s := eval_factors x (exponents s)

theorem positive_residue_value : signedProduct (21767 : Fin 114679) 1 = 48891 := by
  decide +kernel

theorem negative_residue_value : signedProduct (21767 : Fin 114679) 276 = 65813 := by
  decide +kernel

theorem reduce_positive : reduce (signedClass 1) = 48891 :=
  (atRoot_signedClass 21767 auxiliary_root 1).trans positive_residue_value

theorem reduce_negative : reduce (signedClass 276) = 65813 :=
  (atRoot_signedClass 21767 auxiliary_root 276).trans negative_residue_value

/-- Constant coefficients of the successive cancellations are coefficients of
the polynomial quotient. This also records an exact witness for divisibility. -/
def divisionWitness : Nat → List Int → List Int
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, c :: rest => c :: divisionWitness n (cancel c rest)

theorem cancellation_identity {R : Type} [CommRing R] (x : R) (c : Int) (rest : List Int) :
    eval x (c :: rest) = x * eval x (cancel c rest) + eval x phi * Int.cast c := by
  simp only [cancel, eval_add, eval_scale, phi, eval, Ring.intCast_one, Ring.intCast_neg]
  grind only

theorem division_identity {R : Type} [CommRing R] (x : R) (n : Nat) (p : List Int) :
    eval x p = x^n * eval x (strip n p) + eval x phi * eval x (divisionWitness n p) := by
  induction n generalizing p with
  | zero =>
    simp [strip, divisionWitness, eval, Semiring.pow_zero, Semiring.one_mul,
      Semiring.mul_zero, Semiring.add_zero]
  | succ n ih =>
    cases p with
    | nil => simp [strip, divisionWitness, eval, Semiring.mul_zero, Semiring.add_zero]
    | cons c rest =>
      rw [cancellation_identity x c rest, ih (cancel c rest)]
      simp only [strip, divisionWitness, eval, Semiring.pow_succ]
      grind only

theorem multiple_of_zero_remainder (p : List Int) (n k : Nat)
    (h : strip n p = List.replicate k 0) : Congruent p [] := by
  refine ⟨divisionWitness n p, ?_⟩
  intro R _ x
  have hd := division_identity x n p
  rw [h, eval_zeros, Semiring.mul_zero] at hd
  exact hd

theorem signed_classes_add_25 : qadd (signedClass 1) (signedClass 276) = polyClass [25] := by
  apply Quotient.sound (s := polynomialSetoid)
  obtain ⟨k, hk⟩ := multiple_of_zero_remainder traceDifference _ _ trace_divides
  refine ⟨k, ?_⟩
  intro R _ x
  have h := hk R x
  simp only [traceDifference, eval_add, eval, Ring.intCast_neg,
    Semiring.mul_zero, Semiring.add_zero] at h
  simp only [eval_add, eval, Semiring.mul_zero, Semiring.add_zero]
  grind only

theorem signed_classes_multiply_one : qmul (signedClass 1) (signedClass 276) = qone := by
  apply Quotient.sound (s := polynomialSetoid)
  obtain ⟨k, hk⟩ := multiple_of_zero_remainder normDifference _ _ norm_divides
  refine ⟨k, ?_⟩
  intro R _ x
  have h := hk R x
  simp only [normDifference, eval_add, eval_factors_append, eval, Ring.intCast_neg,
    Ring.intCast_one, Semiring.mul_zero, Semiring.add_zero] at h
  simp only [eval_mul, eval, Ring.intCast_one, Semiring.mul_zero, Semiring.add_zero]
  grind only

end Reimann.CircularReduction69
