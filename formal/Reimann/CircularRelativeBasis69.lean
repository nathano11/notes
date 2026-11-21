import Reimann.CircularRationalPeriod69
import Reimann.CircularBasis69

/-! Transfer rational linear independence through the integral change of basis
to 22 powers over the quadratic period field. -/

namespace Reimann.CircularRelativeBasis69

open Lean.Grind Lean.Grind.Field.NormNum CircularBasis69 CircularBasisData69
open CircularRational69 CircularRationalPeriod69

attribute [local instance] Ring.intCast

def flatten (c : Fin 22 → Element) (j : Fin 44) : Rat :=
  Fin.addCases (motive := fun _ => Rat) (fun i => (c i).a) (fun i => (c i).b) j

def pair (q : Fin 44 → Rat) (i : Fin 22) : Element :=
  ⟨q (i.castAdd 22), q (i.natAdd 22)⟩

theorem flatten_left (c : Fin 22 → Element) (i : Fin 22) :
    flatten c (i.castAdd 22) = (c i).a := Fin.addCases_left i

theorem flatten_right (c : Fin 22 → Element) (i : Fin 22) :
    flatten c (i.natAdd 22) = (c i).b := Fin.addCases_right i

theorem pair_flatten (c : Fin 22 → Element) : pair (flatten c) = c := by
  funext i
  apply ext_coordinates
  · exact flatten_left c i
  · exact flatten_right c i

theorem flatten_pair (q : Fin 44 → Rat) : flatten (pair q) = q := by
  funext j
  refine Fin.addCases (m := 22) (n := 22) (fun i => ?_) (fun i => ?_) j
  · exact flatten_left _ i
  · exact flatten_right _ i

theorem list_sum_append {R : Type} [CommRing R] (a b : List R) : (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp only [List.nil_append, List.sum_nil]; grind only
  | cons a as ih => simp only [List.cons_append, List.sum_cons, ih]; grind only

theorem split_sum {R : Type} [CommRing R] {m n : Nat} (f : Fin (m+n) → R) :
    basisSum f = basisSum (fun i => f (i.castAdd n)) + basisSum (fun j => f (j.natAdd m)) := by
  unfold basisSum
  rw [List.ofFn_add (n := m) (m := n), list_sum_append]
  rfl

theorem cast_sum {R : Type} [Field R] [IsCharP R 0] {n : Nat} (v : Fin n → Rat) :
    (ofRat (basisSum v) : R) = basisSum (fun i => ofRat (v i)) := by
  induction n with
  | zero => rw [basisSum_empty, basisSum_empty]; exact (cast_int (R := R) 0).trans Ring.intCast_zero
  | succ n ih => rw [basisSum_succ, basisSum_succ (fun i => (ofRat (v i) : R)), ofRat_add, ih]

theorem cast_matrix {R : Type} [Field R] [IsCharP R 0] (M : Fin 44 → Fin 44 → Int)
    (v : Fin 44 → Rat) (i : Fin 44) :
    (ofRat (applyMatrix M v i) : R) = applyMatrix M (fun j => ofRat (v j)) i := by
  unfold applyMatrix
  rw [cast_sum]
  apply congrArg basisSum
  funext j
  rw [ofRat_mul, cast_int]

theorem matrix_zero (M : Fin 44 → Fin 44 → Int) :
    applyMatrix M (fun _ => (0 : Rat)) = fun _ => 0 := by
  funext i
  simp only [applyMatrix, Rat.mul_zero, basisSum_zero]

def ordinaryValue {R : Type} [Field R] (x : R) (q : Fin 44 → Rat) : R :=
  basisSum (fun i => x^i.val * ofRat (q i))

def relativeValue {R : Type} [Field R] (x : R) (c : Fin 22 → Element) : R :=
  basisSum (fun i => x^i.val * evaluate (CircularFactor69.periodTheta x) (c i))

theorem mixed_left {R : Type} [CommRing R] (x : R) (i : Fin 22) :
    mixedPower x (i.castAdd 22) = x^i.val := by
  unfold mixedPower
  change (if i.val < 22 then _ else _) = _
  split
  · rfl
  · exact False.elim (by omega)

theorem mixed_right {R : Type} [CommRing R] (x : R) (i : Fin 22) :
    mixedPower x (i.natAdd 22) = x^i.val * CircularFactor69.periodTheta x := by
  unfold mixedPower
  change (if 22 + i.val < 22 then _ else _) = _
  split
  · exact False.elim (by omega)
  · change x^(22+i.val-22) * _ = _
    have h : 22 + i.val - 22 = i.val := by omega
    rw [h]

theorem mixed_pairing {R : Type} [Field R] (x : R) (c : Fin 22 → Element) :
    basisSum (fun j : Fin 44 => mixedPower x j * ofRat (flatten c j)) = relativeValue x c := by
  rw [split_sum (m := 22) (n := 22)]
  simp only [mixed_left, mixed_right, flatten_left, flatten_right]
  rw [← basisSum_add]
  apply congrArg basisSum
  funext i
  unfold evaluate
  grind only

theorem change_to_ordinary {R : Type} [Field R] [IsCharP R 0] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) (c : Fin 22 → Element) :
    ordinaryValue x (applyMatrix basisColumns (flatten c)) = relativeValue x c := by
  unfold ordinaryValue
  simp only [cast_matrix, basis_evaluation x hx, mixed_pairing]

theorem change_to_relative {R : Type} [Field R] [IsCharP R 0] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) (q : Fin 44 → Rat) :
    relativeValue x (pair (applyMatrix inverseColumns q)) = ordinaryValue x q := by
  rw [← change_to_ordinary x hx, flatten_pair, ordinary_coordinates_recovered]

theorem pair_zero : pair (fun _ => 0) = fun _ => (0 : Element) := by
  rfl

theorem flatten_zero : flatten (fun _ => (0 : Element)) = fun _ => 0 := by
  rw [← pair_zero, flatten_pair]

def OrdinaryIndependent {R : Type} [Field R] (x : R) : Prop :=
  ∀ q : Fin 44 → Rat, ordinaryValue x q = 0 → q = fun _ => 0

def RelativeIndependent {R : Type} [Field R] (x : R) : Prop :=
  ∀ c : Fin 22 → Element, relativeValue x c = 0 → c = fun _ => 0

theorem relative_of_ordinary {R : Type} [Field R] [IsCharP R 0] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0)
    (h : OrdinaryIndependent x) : RelativeIndependent x := by
  intro c hc
  have hq := h _ ((change_to_ordinary x hx c).trans hc)
  have hh := congrArg (applyMatrix inverseColumns) hq
  rw [relative_coordinates_recovered, matrix_zero] at hh
  rw [← pair_flatten c, hh, pair_zero]

theorem ordinary_of_relative {R : Type} [Field R] [IsCharP R 0] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0)
    (h : RelativeIndependent x) : OrdinaryIndependent x := by
  intro q hq
  have hc := h _ ((change_to_relative x hx q).trans hq)
  have hh := congrArg flatten hc
  rw [flatten_pair, flatten_zero] at hh
  rw [← ordinary_coordinates_recovered q, hh, matrix_zero]

theorem primitive_independence_iff {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    OrdinaryIndependent x ↔ RelativeIndependent x := by
  have hx := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  exact ⟨relative_of_ordinary x hx, ordinary_of_relative x hx⟩

end Reimann.CircularRelativeBasis69
