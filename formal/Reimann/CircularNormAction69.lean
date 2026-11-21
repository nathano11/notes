import Reimann.CircularFieldNorm69

/-! The quadratic scalar action and multiplication by an arbitrary generated field element. -/
namespace Reimann.CircularNormAction69

open Lean.Grind CircularBasis69 CircularFieldNorm69 CircularFactor69
open CircularPolynomialField69 CircularRelativeBasis69 CircularRationalPeriod69

def constantVector (a : Coeff) : Fin 22 → Coeff :=
  Fin.cases a (fun _ => 0)

theorem constant_value {R : Type} [Field R] (x : R) (a : Coeff) :
    relativeValue x (constantVector a) = evaluate (periodTheta x) a := by
  unfold relativeValue constantVector
  rw [basisSum_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Semiring.pow_zero, Semiring.one_mul]
  change _ + basisSum (fun i : Fin 21 => x^i.succ.val *
    evaluate (periodTheta x) (CircularRational69.scalar 0)) = _
  rw [eval_zero]
  simp only [Semiring.mul_zero, basisSum_zero, Semiring.add_zero]

theorem coefficient_in_generated_field {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (a : Coeff) :
    Generated x (evaluate (periodTheta x) a) := by
  rw [← constant_value x a]
  exact value_in_generated_field x h69 h23 h3 _

theorem relativeValue_add {R : Type} [Field R] [IsCharP R 0] (x : R) (v w : Fin 22 → Coeff) :
    relativeValue x (fun i => v i + w i) = relativeValue x v + relativeValue x w := by
  unfold relativeValue
  rw [← basisSum_add]
  apply congrArg basisSum
  funext i
  change _ * evaluate _ (CircularRational69.plus _ _) = _
  rw [eval_add, Semiring.left_distrib]

theorem relativeValue_scale {R : Type} [Field R] [IsCharP R 0] (x : R)
    (ht : (periodTheta x)^2 = periodTheta x + 17) (a : Coeff) (v : Fin 22 → Coeff) :
    relativeValue x (fun i => a * v i) = evaluate (periodTheta x) a * relativeValue x v := by
  unfold relativeValue
  rw [← basisSum_mul_left]
  apply congrArg basisSum
  funext i
  change _ * evaluate _ (CircularRational69.times _ _) = _
  rw [eval_mul _ ht]
  grind only

def applyColumns (columns : Fin 22 → Fin 22 → Coeff) (v : Fin 22 → Coeff) (i : Fin 22) : Coeff :=
  basisSum (fun j => columns j i * v j)

theorem applyColumns_row {R : Type} [Field R] [IsCharP R 0] (t : R) (ht : t^2 = t+17)
    (columns : Fin 22 → Fin 22 → Coeff) (v : Fin 22 → Coeff) (i : Fin 22) :
    evaluate t (applyColumns columns v i) =
      basisSum (fun j => evaluate t (columns j i) * evaluate t (v j)) := by
  unfold applyColumns
  rw [CircularMultiplication69.evaluate_sum]
  exact congrArg basisSum (funext (fun j => eval_mul t ht (columns j i) (v j)))

theorem applyColumns_value {R : Type} [Field R] [IsCharP R 0] (x : R)
    (ht : (periodTheta x)^2 = periodTheta x+17)
    (columns : Fin 22 → Fin 22 → Coeff) (v : Fin 22 → Coeff) :
    relativeValue x (applyColumns columns v) =
      basisSum (fun j => relativeValue x (columns j) * evaluate (periodTheta x) (v j)) := by
  simp only [relativeValue, applyColumns_row _ ht, basisSum_convolution]

theorem multiplication_action_value {R : Type} [Field R] [IsCharP R 0] (x y : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hy : Generated x y)
    (v : Fin 22 → Coeff) :
    relativeValue x (applyColumns (multiplicationColumn x y h69 h23 h3 hy) v) =
      y * relativeValue x v := by
  have ht := period_theta_quadratic x (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3)
  rw [applyColumns_value x ht]
  simp only [multiplication_column_value, Semiring.mul_assoc, basisSum_mul_left]
  rfl

theorem multiplication_action_coordinates {R : Type} [Field R] [IsCharP R 0] (x y : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hy : Generated x y)
    (v w : Fin 22 → Coeff) :
    relativeValue x w = y * relativeValue x v ↔
      w = applyColumns (multiplicationColumn x y h69 h23 h3 hy) v := by
  constructor
  · intro h
    exact CircularFieldBasis69.relative_value_injective x h69 h23 h3 _ _
      (h.trans (multiplication_action_value x y h69 h23 h3 hy v).symm)
  · rintro rfl
    exact multiplication_action_value x y h69 h23 h3 hy v

theorem quadratic_units_trace {R : Type} [CommRing R] (t : R) :
    (11+3*t) + (14-3*t) = 25 := by grind only

theorem quadratic_units_product {R : Type} [CommRing R] (t : R) (ht : t^2 = t+17) :
    (11+3*t) * (14-3*t) = 1 := by grind only

/-- The field norm of 1 − x and its inverse satisfy the same monic integer polynomial. -/
theorem quadratic_units_monic {R : Type} [CommRing R] (t : R) (ht : t^2 = t+17) :
    (11+3*t)^2 - 25*(11+3*t) + 1 = 0 ∧ (14-3*t)^2 - 25*(14-3*t) + 1 = 0 := by
  have tr := quadratic_units_trace t
  have pr := quadratic_units_product t ht
  constructor <;> grind only

end Reimann.CircularNormAction69
