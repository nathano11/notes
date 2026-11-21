import Reimann.CircularFactor69
import Reimann.CircularPrimitive69
import Reimann.CircularBasisData69

/-! The integral change between the ordinary degree-44 monomial coordinates
and the 22 powers with coefficients in the quadratic period order. -/

namespace Reimann.CircularBasis69

open Lean.Grind CircularBasisData69
attribute [local instance] Ring.intCast

def basisSum {R : Type} [CommRing R] {n : Nat} (f : Fin n → R) : R :=
  (List.ofFn f).sum

theorem basisSum_empty {R : Type} [CommRing R] (f : Fin 0 → R) : basisSum f = 0 := rfl

theorem basisSum_succ {R : Type} [CommRing R] {n : Nat} (f : Fin (n+1) → R) :
    basisSum f = f 0 + basisSum (fun i => f i.succ) := by
  simp [basisSum, List.ofFn_succ]

theorem basisSum_zero {R : Type} [CommRing R] (n : Nat) :
    basisSum (fun _ : Fin n => (0:R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [basisSum_succ, ih]; grind only

theorem basisSum_add {R : Type} [CommRing R] {n : Nat} (f g : Fin n → R) :
    basisSum (fun i => f i + g i) = basisSum f + basisSum g := by
  induction n with
  | zero => rw [basisSum_empty, basisSum_empty, basisSum_empty]; grind only
  | succ n ih =>
    rw [basisSum_succ, basisSum_succ f, basisSum_succ g, ih (fun i => f i.succ) (fun i => g i.succ)]
    grind only

theorem basisSum_mul_left {R : Type} [CommRing R] {n : Nat} (b : R) (f : Fin n → R) :
    basisSum (fun i => b * f i) = b * basisSum f := by
  induction n with
  | zero => rw [basisSum_empty, basisSum_empty]; grind only
  | succ n ih =>
    rw [basisSum_succ, basisSum_succ f, ih (fun i => f i.succ)]
    grind only

theorem basisSum_mul_right {R : Type} [CommRing R] {n : Nat} (f : Fin n → R) (b : R) :
    basisSum (fun i => f i * b) = basisSum f * b := by
  simpa only [CommSemiring.mul_comm] using basisSum_mul_left b f

theorem basisSum_swap {R : Type} [CommRing R] {m n : Nat} (f : Fin m → Fin n → R) :
    basisSum (fun i => basisSum (f i)) = basisSum (fun j => basisSum (fun i => f i j)) := by
  induction m with
  | zero => simp only [basisSum_empty, basisSum_zero]
  | succ m ih =>
    rw [basisSum_succ]
    simp only [basisSum_succ (fun i => f i _), basisSum_add]
    rw [ih (fun i j => f i.succ j)]

theorem basisSum_convolution {R : Type} [CommRing R] {m n : Nat}
    (p : Fin m → R) (a : Fin m → Fin n → R) (v : Fin n → R) :
    basisSum (fun i => p i * basisSum (fun j => a i j * v j)) =
    basisSum (fun j => basisSum (fun i => p i * a i j) * v j) := by
  simp only [← basisSum_mul_left, ← basisSum_mul_right, Semiring.mul_assoc]
  exact basisSum_swap (fun i j => p i * (a i j * v j))

theorem basisSum_cast {R : Type} [CommRing R] {n : Nat} (f : Fin n → Int) :
    basisSum (fun i => (Int.cast (f i) : R)) = Int.cast (basisSum f) := by
  induction n with
  | zero => rw [basisSum_empty, basisSum_empty, Ring.intCast_zero]
  | succ n ih => rw [basisSum_succ, basisSum_succ f, Ring.intCast_add, ih (fun i => f i.succ)]

theorem basisSum_single {R : Type} [CommRing R] {n : Nat} (i : Fin n) (v : Fin n → R) :
    basisSum (fun j => if i = j then v j else 0) = v i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [basisSum_succ]
      have hne (k : Fin n) : (0 : Fin (n+1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
      simp only [ite_true, hne, ite_false, basisSum_zero, Semiring.add_zero]
    · rw [basisSum_succ]
      simp only [Fin.succ_ne_zero, ite_false, Fin.succ_inj]
      rw [ih k (fun j => v j.succ)]
      grind only

theorem eval_ofFn_monomials {R : Type} [CommRing R] (x : R) {n : Nat} (v : Fin n → Int) :
    CircularPolynomial69.eval x (List.ofFn v) = basisSum (fun i => Int.cast (v i) * x^i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, CircularPolynomial69.eval, ih (fun i => v i.succ), basisSum_succ]
    simp only [Fin.val_zero, Fin.val_succ, Semiring.pow_zero, Semiring.mul_one, Semiring.pow_succ]
    rw [← basisSum_mul_left]
    apply congrArg (fun z => Int.cast (v 0) + z)
    apply congrArg basisSum
    funext j
    grind only

def applyMatrix {R : Type} [CommRing R] (a : Fin 44 → Fin 44 → Int)
    (v : Fin 44 → R) (i : Fin 44) : R :=
  basisSum (fun j => Int.cast (a i j) * v j)

theorem cast_matrix_product {R : Type} [CommRing R] (a b : Fin 44 → Fin 44 → Int)
    (i j : Fin 44) :
    basisSum (fun k => (Int.cast (a i k) : R) * Int.cast (b k j)) =
      Int.cast (matrixProduct a b i j) := by
  simp only [← Ring.intCast_mul, basisSum_cast]
  rfl

theorem matrix_action_composition {R : Type} [CommRing R] (a b : Fin 44 → Fin 44 → Int)
    (v : Fin 44 → R) :
    applyMatrix a (applyMatrix b v) = applyMatrix (matrixProduct a b) v := by
  funext i
  unfold applyMatrix
  rw [basisSum_convolution]
  simp only [cast_matrix_product]

theorem matrix_action_identity {R : Type} [CommRing R] (a : Fin 44 → Fin 44 → Int)
    (ha : ∀ i j, a i j = if i = j then 1 else 0) (v : Fin 44 → R) :
    applyMatrix a v = v := by
  funext i
  unfold applyMatrix
  calc
    _ = basisSum (fun j => if i = j then v j else 0) := by
      apply congrArg basisSum
      funext j
      rw [ha]
      by_cases hij : i = j
      · simp only [hij, ite_true, Ring.intCast_one, Semiring.one_mul]
      · simp only [hij, ite_false, Ring.intCast_zero, Semiring.zero_mul]
    _ = _ := basisSum_single i v

theorem ordinary_coordinates_recovered {R : Type} [CommRing R] (v : Fin 44 → R) :
    applyMatrix basisColumns (applyMatrix inverseColumns v) = v := by
  rw [matrix_action_composition]
  exact matrix_action_identity _ basis_inverse v

theorem relative_coordinates_recovered {R : Type} [CommRing R] (v : Fin 44 → R) :
    applyMatrix inverseColumns (applyMatrix basisColumns v) = v := by
  rw [matrix_action_composition]
  exact matrix_action_identity _ inverse_basis v

theorem reduced_column_at_root {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) (j : Fin 44) :
    CircularPolynomial69.eval x (columnPoly j) = CircularPolynomial69.eval x (rawColumn j) := by
  have h := CircularFactor69.eval_of_zero_remainder x hx _ (column_remainders j)
  rw [columnDifference, CircularPolynomial69.eval_add, CircularPolynomial69.eval_scale,
    Ring.intCast_neg, Ring.intCast_one] at h
  grind only

/-- First the 22 powers of x, then the 22 powers multiplied by the period. -/
def mixedPower {R : Type} [CommRing R] (x : R) (j : Fin 44) : R :=
  if j.val < 22 then x^j.val else x^(j.val - 22) * CircularFactor69.periodTheta x

theorem raw_column_value {R : Type} [CommRing R] (x : R) (j : Fin 44) :
    CircularPolynomial69.eval x (rawColumn j) = mixedPower x j := by
  unfold rawColumn mixedPower
  split
  · rw [CircularPolynomial69.eval_shift]
    simp [CircularPolynomial69.eval, Ring.intCast_one, Semiring.mul_zero, Semiring.add_zero,
      Semiring.mul_one]
  · exact CircularPolynomial69.eval_shift x (j.val-22) CircularFactor69.periodPoly

theorem ordinary_column_pairing {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) (j : Fin 44) :
    basisSum (fun i => x^i.val * Int.cast (basisColumns i j)) = mixedPower x j := by
  have h := (reduced_column_at_root x hx j).trans (raw_column_value x j)
  rw [columnPoly, eval_ofFn_monomials] at h
  simpa only [CommSemiring.mul_comm] using h

theorem basis_evaluation {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) (v : Fin 44 → R) :
    basisSum (fun i => x^i.val * applyMatrix basisColumns v i) =
      basisSum (fun j => mixedPower x j * v j) := by
  unfold applyMatrix
  rw [basisSum_convolution]
  simp only [ordinary_column_pairing x hx]

/-- In ordinary monomial coordinates v, the inverse matrix supplies the
unique vector of relative coordinates. Their evaluation agrees at every
primitive 69th root x. This statement allows any scalar specialization. -/
theorem relative_basis_at_primitive {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (v : Fin 44 → R) :
    (∀ w : Fin 44 → R, applyMatrix basisColumns w = v ↔ w = applyMatrix inverseColumns v) ∧
    basisSum (fun j => mixedPower x j * applyMatrix inverseColumns v j) =
      basisSum (fun i => x^i.val * v i) := by
  constructor
  · intro w
    constructor
    · intro h
      rw [← h, relative_coordinates_recovered]
    · intro h
      rw [h, ordinary_coordinates_recovered]
  · have h := basis_evaluation x
      (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3) (applyMatrix inverseColumns v)
    rw [ordinary_coordinates_recovered] at h
    exact h.symm

end Reimann.CircularBasis69
