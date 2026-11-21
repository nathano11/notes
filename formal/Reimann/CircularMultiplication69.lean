import Reimann.CircularFieldBasis69
import Reimann.CircularNorm69

/-! Multiplication by 1 − x in the relative power coordinates at conductor 69. -/
namespace Reimann.CircularMultiplication69

open Lean.Grind CircularRational69 CircularRationalPeriod69
open CircularBasis69 CircularFactor69 CircularNorm69 CircularRelativeBasis69

def entry (i j : Fin 22) : CircularRational69.Element :=
  ofIntegral ((column positiveCoeffs.dropLast j.val)[i.val]?.getD (0,0))

def action (v : Fin 22 → CircularRational69.Element) (i : Fin 22) : CircularRational69.Element :=
  basisSum (fun j => entry i j * v j)

theorem entries_are_companion_rows :
    List.ofFn (fun i => List.ofFn (fun j => entry i j)) =
      (multiplicationMatrix positiveCoeffs.dropLast).map (List.map ofIntegral) := by
  decide +kernel

theorem column_length : ∀ j : Fin 22, (column positiveCoeffs.dropLast j.val).length ≤ 22 := by
  decide +kernel

theorem padded_column_value {R : Type} [CommRing R] (t x : R) (n : Nat)
    (p : List CircularQuadratic69.Element) (h : p.length ≤ n) :
    basisSum (fun i : Fin n => x^i.val * embed t (p[i.val]?.getD (0,0))) = evalPoly t x p := by
  induction n generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (by omega)
    subst p
    rfl
  | succ n ih =>
    cases p with
    | nil =>
      simp only [List.getElem?_nil, Option.getD_none, embed_zero, Semiring.mul_zero, basisSum_zero,
        evalPoly]
    | cons c p =>
      have hlen : p.length ≤ n := by simpa using h
      rw [basisSum_succ, evalPoly, ← ih p hlen]
      simp only [Fin.val_zero, Fin.val_succ, Semiring.pow_zero, Semiring.one_mul,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Semiring.pow_succ]
      rw [← basisSum_mul_left]
      apply congrArg (fun z => embed t c + z)
      apply congrArg basisSum
      funext i
      grind only

theorem column_value {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (j : Fin 22) :
    basisSum (fun i => x^i.val * evaluate (periodTheta x) (entry i j)) = (1-x) * x^j.val := by
  simp only [entry, eval_integral]
  rw [padded_column_value _ _ _ _ (column_length j)]
  exact primitive_companion_columns x h69 h23 h3 j.val j.isLt

theorem evaluate_sum {R : Type} [Field R] [IsCharP R 0] (t : R)
    {n : Nat} (v : Fin n → CircularRational69.Element) :
    evaluate t (basisSum v) = basisSum (fun i => evaluate t (v i)) := by
  induction n with
  | zero => rw [basisSum_empty, basisSum_empty]; exact eval_zero t
  | succ n ih =>
    rw [basisSum_succ, basisSum_succ (fun i => evaluate t (v i))]
    change evaluate t (plus _ _) = _
    rw [eval_add, ih]

theorem evaluated_action_row {R : Type} [Field R] [IsCharP R 0] (t : R) (ht : t^2 = t+17)
    (v : Fin 22 → CircularRational69.Element) (i : Fin 22) :
    evaluate t (action v i) = basisSum (fun j => evaluate t (entry i j) * evaluate t (v j)) := by
  unfold action
  rw [evaluate_sum]
  exact congrArg basisSum (funext (fun j => eval_mul t ht (entry i j) (v j)))

theorem action_value {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (v : Fin 22 → CircularRational69.Element) :
    basisSum (fun i => x^i.val * evaluate (periodTheta x) (action v i)) =
      (1-x) * basisSum (fun i => x^i.val * evaluate (periodTheta x) (v i)) := by
  have ht := period_theta_quadratic x (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3)
  simp only [evaluated_action_row _ ht, basisSum_convolution, column_value x h69 h23 h3,
    Semiring.mul_assoc, basisSum_mul_left]

theorem relativeValue_difference {R : Type} [Field R] [IsCharP R 0] (x : R)
    (v w : Fin 22 → CircularRational69.Element) :
    relativeValue x (fun i => plus (v i) (negative (w i))) = relativeValue x v - relativeValue x w := by
  unfold relativeValue
  calc
    _ = basisSum (fun i => (x^i.val * evaluate (periodTheta x) (v i)) +
        (-1:R) * (x^i.val * evaluate (periodTheta x) (w i))) := by
      apply congrArg basisSum
      funext i
      rw [eval_add, eval_negative]
      grind only
    _ = _ := by rw [basisSum_add, basisSum_mul_left]; grind only

theorem relativeValue_injective {R : Type} [Field R] [IsCharP R 0] (x : R)
    (hi : RelativeIndependent x) {v w : Fin 22 → CircularRational69.Element}
    (h : relativeValue x v = relativeValue x w) : v = w := by
  have hd : relativeValue x (fun i => plus (v i) (negative (w i))) = 0 := by
    rw [relativeValue_difference, h]
    grind only
  have hz := hi _ hd
  funext i
  have he := congrFun hz i
  change v i + -(w i) = 0 at he
  grind only

theorem unique_column {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hi : RelativeIndependent x)
    (j : Fin 22) (v : Fin 22 → CircularRational69.Element) :
    relativeValue x v = (1-x) * x^j.val ↔ v = fun i => entry i j := by
  constructor
  · intro h
    apply relativeValue_injective x hi
    exact h.trans (column_value x h69 h23 h3 j).symm
  · rintro rfl
    exact column_value x h69 h23 h3 j

theorem unique_action {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hi : RelativeIndependent x)
    (v w : Fin 22 → CircularRational69.Element) :
    relativeValue x w = (1-x) * relativeValue x v ↔ w = action v := by
  constructor
  · intro h
    apply relativeValue_injective x hi
    exact h.trans (action_value x h69 h23 h3 v).symm
  · rintro rfl
    exact action_value x h69 h23 h3 v

theorem evaluate_at_theta (a : CircularRational69.Element) : evaluate theta a = a := by
  unfold evaluate
  rw [canonical_scalar, canonical_scalar]
  exact (basis_expansion a).symm

theorem integral_entry_as_embed (a : CircularQuadratic69.Element) :
    ofIntegral a = embed theta a :=
  (evaluate_at_theta _).symm.trans (eval_integral theta a)

theorem entries_as_embedded_rows : List.ofFn (fun i => List.ofFn (fun j => entry i j)) =
    (multiplicationMatrix positiveCoeffs.dropLast).map (List.map (embed theta)) := by
  rw [entries_are_companion_rows, show ofIntegral = embed theta from funext integral_entry_as_embed]

theorem primitive_unique_column {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (j : Fin 22) (v : Fin 22 → CircularRational69.Element) :
    relativeValue x v = (1-x) * x^j.val ↔ v = fun i => entry i j :=
  unique_column x h69 h23 h3 (CircularFieldBasis69.primitive_relative_independent x h69 h23 h3) j v

/-- The coordinate vector of (1 − x)y is the matrix action on the coordinate vector of y. -/
theorem primitive_unique_action {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (v w : Fin 22 → CircularRational69.Element) :
    relativeValue x w = (1-x) * relativeValue x v ↔ w = action v :=
  unique_action x h69 h23 h3 (CircularFieldBasis69.primitive_relative_independent x h69 h23 h3) v w

#print axioms primitive_unique_action

end Reimann.CircularMultiplication69
