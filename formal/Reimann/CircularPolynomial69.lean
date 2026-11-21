import Std

/-!
# Signed products at conductor 69

Coefficient lists are in ascending degree over the integers. The constant
coefficient of the monic cyclotomic polynomial is one. Subtracting a multiple
of that polynomial and removing the constant term permits exact division
without denominators. Evaluation below works in any commutative ring.
-/

namespace Reimann.CircularPolynomial69

open Lean.Grind

attribute [local instance] Ring.intCast

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Evaluate an integer polynomial by Horner's rule. -/
def eval {R : Type} [CommRing R] (x : R) : List Int → R
  | [] => 0
  | c :: p => Int.cast c + x * eval x p

/-- Add coefficient lists, sharing any unpaired tail. -/
def add : List Int → List Int → List Int
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

theorem eval_add {R : Type} [CommRing R] (x : R) (p q : List Int) :
    eval x (add p q) = eval x p + eval x q := by
  induction p generalizing q with
  | nil => simp only [add, eval]; grind only
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval, Semiring.add_zero]
    | cons b q =>
      simp only [add, eval, Ring.intCast_add, ih]
      grind only

theorem eval_scale {R : Type} [CommRing R] (x : R) (c : Int) (p : List Int) :
    eval x (p.map (fun a => c * a)) = Int.cast c * eval x p := by
  induction p with
  | nil => simp [eval, Semiring.mul_zero]
  | cons a p ih =>
    simp only [List.map_cons, eval, Ring.intCast_mul, ih]
    grind only

theorem eval_shift {R : Type} [CommRing R] (x : R) (n : Nat) (p : List Int) :
    eval x (List.replicate n 0 ++ p) = x ^ n * eval x p := by
  induction n with
  | zero => simp [Semiring.pow_zero, Semiring.one_mul]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, eval, Ring.intCast_zero,
      ih, Semiring.pow_succ]
    grind only

/-- The 44 nonconstant coefficients of Φ₆₉, beginning at degree one. -/
def phiTail : List Int :=
  [-1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1,
   -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1, 0, -1, 1]

def phi : List Int := 1 :: phiTail

/-- Integer coefficient certificate for Φ₆₉(X)(1+X+X²)=1+X²³+X⁴⁶. -/
theorem phi_factor_coefficients :
    add phi (add (List.replicate 1 0 ++ phi) (List.replicate 2 0 ++ phi)) =
      add [1] (add (List.replicate 23 0 ++ [1]) (List.replicate 46 0 ++ [1])) := by
  decide +kernel

theorem phi_factorization {R : Type} [CommRing R] (x : R) :
    eval x phi * (1 + x + x ^ 2) = 1 + x ^ 23 + x ^ 46 := by
  have h := congrArg (eval x) phi_factor_coefficients
  simp only [eval_add, eval_shift, eval, Ring.intCast_one, Semiring.mul_zero,
    Semiring.add_zero, Semiring.mul_one] at h
  grind only

/-- Multiply a polynomial by 1-X^a. -/
def factor (a : Nat) (p : List Int) : List Int :=
  add p (List.replicate a 0 ++ p.map (fun c => (-1 : Int) * c))

theorem eval_factor {R : Type} [CommRing R] (x : R) (a : Nat) (p : List Int) :
    eval x (factor a p) = (1 - x ^ a) * eval x p := by
  rw [factor, eval_add, eval_shift, eval_scale, Ring.intCast_neg, Ring.intCast_one]
  grind only

def factors : List Nat → List Int
  | [] => [1]
  | a :: as => factor a (factors as)

theorem eval_factors {R : Type} [CommRing R] (x : R) (as : List Nat) :
    eval x (factors as) = as.foldr (fun a acc => (1 - x ^ a) * acc) 1 := by
  induction as with
  | nil => simp [factors, eval, Ring.intCast_one, Semiring.mul_zero, Semiring.add_zero]
  | cons a as ih => simp [factors, eval_factor, ih]

theorem eval_factors_append {R : Type} [CommRing R] (x : R) (as bs : List Nat) :
    eval x (factors (as ++ bs)) = eval x (factors as) * eval x (factors bs) := by
  induction as with
  | nil => simp [factors, eval, Ring.intCast_one, Semiring.add_zero, Semiring.mul_zero,
      Semiring.one_mul]
  | cons a as ih => simp [factors, eval_factor, ih, Semiring.mul_assoc]

/-- Drop the constant term after subtracting that coefficient times Φ₆₉. -/
def cancel (c : Int) (rest : List Int) : List Int :=
  add rest (phiTail.map (fun a => -c * a))

theorem cancel_at_root {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0)
    (c : Int) (rest : List Int) :
    eval x (c :: rest) = x * eval x (cancel c rest) := by
  change Int.cast (1 : Int) + x * eval x phiTail = 0 at hx
  rw [Ring.intCast_one] at hx
  rw [eval, cancel, eval_add, eval_scale, Ring.intCast_neg]
  grind only

def strip : Nat → List Int → List Int
  | 0, p => p
  | _ + 1, [] => []
  | n + 1, c :: rest => strip n (cancel c rest)

theorem strip_sound {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0)
    (n : Nat) (p : List Int) (h : eval x (strip n p) = 0) : eval x p = 0 := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons c rest =>
      rw [cancel_at_root x hx, ih (cancel c rest) h, Semiring.mul_zero]

theorem eval_zeros {R : Type} [CommRing R] (x : R) (n : Nat) :
    eval x (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, eval, Ring.intCast_zero, ih, Semiring.mul_zero,
      Semiring.add_zero]

/-- The values 1 and 276 represent the signs of the product of the two
quadratic characters at 3 and 23. A nonunit has value zero. -/
def eta (a : Nat) : Nat :=
  let at3 := match a % 3 with | 0 => 0 | 1 => 1 | _ => 276
  let at23 := match (a % 23) ^ 11 % 23 with | 0 => 0 | 1 => 1 | _ => 276
  (at3 * at23) % 277

def exponents (sign : Nat) : List Nat :=
  (List.range 69).filter (fun a => eta a == sign)

theorem signed_exponent_counts : (exponents 1).length = 22 ∧ (exponents 276).length = 22 := by
  decide +kernel

def traceDifference : List Int :=
  add [-25] (add (factors (exponents 1)) (factors (exponents 276)))

def normDifference : List Int :=
  add [-1] (factors (exponents 1 ++ exponents 276))

theorem trace_divides :
    strip (traceDifference.length - 44) traceDifference = List.replicate 44 0 := by
  decide +kernel

theorem norm_divides :
    strip (normDifference.length - 44) normDifference = List.replicate 44 0 := by
  decide +kernel

/-- The sign-1 or sign-276 product evaluated directly in the target ring. -/
def signedProduct {R : Type} [CommRing R] (x : R) (sign : Nat) : R :=
  (exponents sign).foldr (fun a acc => (1 - x ^ a) * acc) 1

theorem norm_products_trace {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    signedProduct x 1 + signedProduct x 276 = 25 := by
  have hz := strip_sound x hx (traceDifference.length - 44) traceDifference
    (by rw [trace_divides, eval_zeros])
  rw [traceDifference, eval_add, eval_add, eval_factors, eval_factors] at hz
  change eval x [-25] + (signedProduct x 1 + signedProduct x 276) = 0 at hz
  simp only [eval, Ring.intCast_neg, Semiring.mul_zero,
    Semiring.add_zero] at hz
  grind only

theorem norm_products_multiply {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    signedProduct x 1 * signedProduct x 276 = 1 := by
  have hz := strip_sound x hx (normDifference.length - 44) normDifference
    (by rw [norm_divides, eval_zeros])
  rw [normDifference, eval_add, eval_factors_append, eval_factors, eval_factors] at hz
  change eval x [-1] + signedProduct x 1 * signedProduct x 276 = 0 at hz
  simp only [eval, Ring.intCast_neg, Ring.intCast_one, Semiring.mul_zero,
    Semiring.add_zero] at hz
  grind only

end Reimann.CircularPolynomial69
