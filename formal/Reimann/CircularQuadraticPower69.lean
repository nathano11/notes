import Reimann.CircularQuadratic69

/-! Reduction of powers from the quadratic order into the auxiliary residue ring. -/
namespace Reimann.CircularQuadraticPower69

open Lean.Grind Reimann.CircularQuadratic69
attribute [local instance] Ring.intCast

def evaluateAt {R : Type} [CommRing R] (t : R) (u : Element) : R :=
  Int.cast u.1 + Int.cast u.2 * t

theorem evaluateAt_product {R : Type} [CommRing R] (t : R) (ht : t^2 = t + 17)
    (u v : Element) : evaluateAt t (product u v) = evaluateAt t u * evaluateAt t v := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  simp only [evaluateAt, product, Ring.intCast_add, Ring.intCast_mul]
  grind only

def orderPower (u : Element) : Nat → Element
  | 0 => (1, 0)
  | n+1 => product (orderPower u n) u

theorem evaluateAt_power {R : Type} [CommRing R] (t : R) (ht : t^2 = t + 17)
    (u : Element) (n : Nat) : evaluateAt t (orderPower u n) = (evaluateAt t u)^n := by
  induction n with
  | zero => simp [orderPower, evaluateAt, Ring.intCast_one, Ring.intCast_zero,
      Semiring.zero_mul, Semiring.add_zero, Semiring.pow_zero]
  | succ n ih => rw [orderPower, evaluateAt_product t ht, ih, Semiring.pow_succ]

theorem auxiliary_theta : (92746 : Fin 114679)^2 = 92746 + 17 := by decide +kernel

theorem auxiliary_values :
    evaluateAt (92746 : Fin 114679) epsilon = 48891 ∧
    evaluateAt (92746 : Fin 114679) (conjugate epsilon) = 65813 := by decide +kernel

/-- If x*d=1 and a norm calculation gives y^(n+1)=x^n, the inverse d
has an explicit (n+1)-st root. The application uses n = 276. -/
theorem one_more_power_of_inverse {R : Type} [CommSemiring R] (x d y : R) (n : Nat)
    (hinv : x*d = 1) (h : y^(n+1) = x^n) : (y*d)^(n+1) = d := by
  calc
    _ = y^(n+1) * d^(n+1) := CommSemiring.mul_pow _ _ _
    _ = x^n * (d^n * d) := by rw [h, Semiring.pow_succ d n]
    _ = (x*d)^n * d := by rw [CommSemiring.mul_pow, Semiring.mul_assoc]
    _ = d := by rw [hinv, Semiring.one_pow, Semiring.one_mul]

theorem auxiliary_inverse : (48891 : Fin 114679) * 65813 = 1 := by decide +kernel

end Reimann.CircularQuadraticPower69
