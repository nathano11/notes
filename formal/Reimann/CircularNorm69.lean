import Reimann.CircularFactor69
import Reimann.CircularPrimitive69

/-! Multiplication by 1-X in the monomial basis modulo a monic polynomial.
Coefficients use the integral basis 1, θ with θ²=θ+17. The determinant
uses the first-row Laplace expansion, omitting zero summands. -/

namespace Reimann.CircularNorm69

open Lean.Grind CircularQuadratic69 CircularFactor69
attribute [local instance] Ring.intCast

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The coordinates of X^j(1-X) before the last basis vector. -/
def shiftColumn (j : Nat) : List Element := List.replicate j (0, 0) ++ [(1, 0), (-1, 0)]

/-- At X^(n-1) the relation X^n = -Σ q_i X^i adds the lower
coefficients of the defining monic polynomial to the last basis vector. -/
def closingColumn (q : List Element) : List Element :=
  addPoly q (List.replicate (q.length - 1) (0, 0) ++ [(1, 0)])

def column (q : List Element) (j : Nat) : List Element :=
  if j + 1 < q.length then shiftColumn j else closingColumn q

/-- Transpose the columns into square rows, padding omitted high zero entries. -/
def multiplicationMatrix (q : List Element) : List (List Element) :=
  (List.range q.length).map fun i =>
    (List.range q.length).map fun j => (column q j)[i]?.getD (0, 0)

def determinant : Nat → List (List Element) → Element
  | 0, _ => (1, 0)
  | n+1, rows =>
    ((List.range (n+1)).foldl (fun acc j =>
      let a := (rows.headD [])[j]?.getD (0, 0)
      if a = (0, 0) then acc
      else
        let minor := rows.tail.map (fun row => row.eraseIdx j)
        let term := product a (determinant n minor)
        pairAdd acc (if j % 2 = 0 then term else (-term.1, -term.2))) (0, 0))

/-- q lists all the non-leading coefficients in ascending order. -/
def companionNorm (q : List Element) : Element :=
  determinant q.length (multiplicationMatrix q)

theorem monic_decompositions :
    positiveCoeffs = positiveCoeffs.dropLast ++ [(1, 0)] ∧
    negativeCoeffs = negativeCoeffs.dropLast ++ [(1, 0)] ∧
    positiveCoeffs.dropLast.length = 22 ∧ negativeCoeffs.dropLast.length = 22 := by
  decide +kernel

theorem positive_companion_norm : companionNorm positiveCoeffs.dropLast = epsilon := by
  decide +kernel

theorem negative_companion_norm :
    companionNorm negativeCoeffs.dropLast = conjugate epsilon := by
  decide +kernel

theorem evalPoly_zero_prefix {R : Type} [CommRing R] (t x : R) (n : Nat) (q : List Element) :
    evalPoly t x (List.replicate n (0, 0) ++ q) = x^n * evalPoly t x q := by
  induction n with
  | zero => simp [Semiring.pow_zero, Semiring.one_mul]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, evalPoly, embed_zero, ih, Semiring.pow_succ]
    grind only

theorem eval_constant_one {R : Type} [CommRing R] (t x : R) :
    evalPoly t x [(1, 0)] = 1 := by
  simp [evalPoly, embed, Ring.intCast_one, Ring.intCast_zero, Semiring.zero_mul,
    Semiring.mul_zero, Semiring.add_zero]

theorem eval_shiftColumn {R : Type} [CommRing R] (t x : R) (j : Nat) :
    evalPoly t x (shiftColumn j) = (1-x) * x^j := by
  rw [shiftColumn, evalPoly_zero_prefix]
  simp only [evalPoly, embed, Ring.intCast_neg, Ring.intCast_one, Ring.intCast_zero,
    Semiring.zero_mul, Semiring.mul_zero, Semiring.add_zero]
  grind only

theorem eval_closingColumn {R : Type} [CommRing R] (t x : R) (q : List Element) :
    evalPoly t x (closingColumn q) = evalPoly t x q + x^(q.length-1) := by
  rw [closingColumn, evalPoly_add, evalPoly_zero_prefix, eval_constant_one, Semiring.mul_one]

theorem eval_monic_append {R : Type} [CommRing R] (t x : R) (q : List Element) :
    evalPoly t x (q ++ [(1, 0)]) = evalPoly t x q + x^q.length := by
  induction q with
  | nil =>
    rw [List.nil_append, eval_constant_one, evalPoly, List.length_nil, Semiring.pow_zero]
    grind only
  | cons a q ih =>
    rw [List.cons_append, evalPoly, ih, evalPoly, List.length_cons, Semiring.pow_succ]
    grind only

theorem eval_multiplication_column {R : Type} [CommRing R] (t x : R) (q : List Element)
    (hroot : evalPoly t x (q ++ [(1, 0)]) = 0) (j : Nat) (hj : j < q.length) :
    evalPoly t x (column q j) = (1-x) * x^j := by
  unfold column
  split
  · exact eval_shiftColumn t x j
  · rename_i top
    have hlen : q.length = j+1 := by omega
    have heval := eval_monic_append t x q
    rw [hroot, hlen, Semiring.pow_succ] at heval
    rw [eval_closingColumn, hlen, Nat.add_one_sub_one]
    grind only

theorem positive_companion_realization {R : Type} [CommRing R] (t x : R)
    (hroot : evalPoly t x positiveCoeffs = 0) :
    (∀ j < 22, evalPoly t x (column positiveCoeffs.dropLast j) = (1-x) * x^j) ∧
      companionNorm positiveCoeffs.dropLast = epsilon := by
  refine ⟨?_, positive_companion_norm⟩
  intro j hj
  exact eval_multiplication_column t x _ (monic_decompositions.1 ▸ hroot) j
    (by simpa only [monic_decompositions.2.2.1] using hj)

theorem negative_companion_realization {R : Type} [CommRing R] (t x : R)
    (hroot : evalPoly t x negativeCoeffs = 0) :
    (∀ j < 22, evalPoly t x (column negativeCoeffs.dropLast j) = (1-x) * x^j) ∧
      companionNorm negativeCoeffs.dropLast = conjugate epsilon := by
  refine ⟨?_, negative_companion_norm⟩
  intro j hj
  exact eval_multiplication_column t x _ (monic_decompositions.2.1 ▸ hroot) j
    (by simpa only [monic_decompositions.2.2.2] using hj)

theorem primitive_companion_columns {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    ∀ j < 22, evalPoly (periodTheta x) x (column positiveCoeffs.dropLast j) =
      (1-x) * x^j := by
  have hx := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  exact (positive_companion_realization (periodTheta x) x (positive_factor_at_generator x hx)).1

/-- This is the determinant of the displayed 22 columns over the period
order, embedded by θ ↦ periodTheta x. To identify it with a field norm
one still needs the relative power-basis identification. -/
theorem signed_product_eq_embedded_companion_determinant {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    CircularPolynomial69.signedProduct x 1 =
      embed (periodTheta x) (companionNorm positiveCoeffs.dropLast) := by
  have hx := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  rw [← positive_at_one_eq_signed_product x hx, positive_at_one, positive_companion_norm]
  change 11 + 3 * periodTheta x = Int.cast 11 + Int.cast 3 * periodTheta x
  grind only

end Reimann.CircularNorm69
