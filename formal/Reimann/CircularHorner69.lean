import Reimann.CircularPrimitive69
import Reimann.CircularConvolution69

/-! Compare the finite monomial sum with the integer Horner evaluation
used to establish the conductor relation. -/
namespace Reimann.CircularHorner69

open Lean.Grind Lean.Grind.Field.NormNum CircularGauss69 CircularPolynomial69
attribute [local instance] Ring.intCast

theorem sum_head {R : Type} [CommRing R] (f : Nat → R) (n : Nat) :
    sumBelow f (n+1) = f 0 + sumBelow (fun i => f (i+1)) n := by
  induction n with
  | zero => change 0 + f 0 = f 0 + 0; grind only
  | succ n ih =>
    change sumBelow f (n+1) + f (n+1) = f 0 + (sumBelow (fun i => f (i+1)) n + f (n+1))
    rw [ih,Semiring.add_assoc]

theorem sum_mul_left {R : Type} [CommRing R] (x : R) (f : Nat → R) (n : Nat) :
    sumBelow (fun i => x*f i) n = x * sumBelow f n := by
  induction n with
  | zero => exact (Semiring.mul_zero x).symm
  | succ n ih => simp only [sumBelow,ih,Semiring.left_distrib]

theorem coeff_cons_zero (c : Int) (p : List Int) : coeff (c :: p) 0 = c := rfl

theorem coeff_cons_succ (c : Int) (p : List Int) (i : Nat) :
    coeff (c :: p) (i+1) = coeff p i := rfl

theorem monomial_sum_cons {R : Type} [CommRing R] (x : R) (c : Int) (p : List Int) (n : Nat) :
    sumBelow (fun i => (Int.cast (coeff (c :: p) i) : R) * x^i) (n+1) =
      Int.cast c + x * sumBelow (fun i => (Int.cast (coeff p i) : R) * x^i) n := by
  rw [sum_head]
  simp only [coeff_cons_zero,coeff_cons_succ,Semiring.pow_zero,Semiring.mul_one]
  rw [← sum_mul_left]
  apply congrArg (fun t : R => Int.cast c + t)
  apply congrArg (fun f : Nat → R => sumBelow f n)
  funext i
  rw [Semiring.pow_succ]
  grind only

theorem horner_eq_sum {R : Type} [CommRing R] (x : R) (p : List Int) :
    sumBelow (fun i => (Int.cast (coeff p i) : R) * x^i) p.length = eval x p := by
  induction p with
  | nil => rfl
  | cons c p ih => rw [List.length_cons,monomial_sum_cons,ih,eval]

theorem phi_length : phi.length = 45 := by decide +kernel

theorem phi_bounded (i : Nat) (hi : 45 ≤ i) : coeff phi i = 0 := by
  have out : phi.length ≤ i := phi_length ▸ hi
  simp [coeff,List.getElem?_eq_none out]

theorem phi_monic : coeff phi 44 = 1 := by decide +kernel

theorem rational_integer_value {R : Type} [Field R] (z : Int) :
    (ofRat (z : Rat) : R) = Int.cast z := by
  simp [ofRat,Rat.num_intCast,Rat.den_intCast,Semiring.natCast_one,
    Field.div_eq_mul_inv,Field.inv_one,Semiring.mul_one]

theorem phi_eval_sum {R : Type} [Field R] (x : R) :
    sumBelow (fun i => (ofRat ((coeff phi i : Int) : Rat) : R) * x^i) 45 = eval x phi := by
  simpa only [rational_integer_value,phi_length] using horner_eq_sum x phi

end Reimann.CircularHorner69
