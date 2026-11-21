import Reimann.DyadicSeriesProjection

/-! Two-sided inversion of dyadic power series with odd constant coefficient,
using the full Cauchy product of coherent dyadic scalars. -/
namespace Reimann.SignedSeriesUnit

open Reimann.DyadicLattice
open Reimann.DyadicSeriesProjection (Series convolution)

/-- The constant series 1. -/
def one : Series
  | 0 => natScalar 1
  | _+1 => natScalar 0

theorem product_zero (f g : Series) : convolution f g 0 = mul (f 0) (g 0) := by
  apply scalar_ext; intro n
  change (f 0).residue n * (g 0).residue n + 0 = _
  simp [mul]

theorem product_succ (f g : Series) (n : Nat) :
    convolution f g (n+1) = add (mul (f 0) (g (n+1))) (convolution (fun k => f (k+1)) g n) := by
  unfold convolution
  rw [List.range_succ_eq_map (n := n+1)]
  simp [List.map_map, Function.comp_def]

/-- Every call in the nth coefficient sum refers to a previously determined
coefficient. The initial scalar v represents the inverse of f(0). -/
def reciprocal (f : Series) (v : Scalar) : (n : Nat) → Scalar
  | 0 => v
  | n+1 => mul (neg v) (((List.range (n+1)).map
      (fun j => mul (f (j+1)) (reciprocal f v (n-j)))).foldr add (natScalar 0))
termination_by n => n
decreasing_by omega

theorem reciprocal_zero (f : Series) (v : Scalar) : reciprocal f v 0 = v := by
  rw [reciprocal]

theorem reciprocal_succ (f : Series) (v : Scalar) (n : Nat) :
    reciprocal f v (n+1) = mul (neg v) (convolution (fun j => f (j+1)) (reciprocal f v) n) := by
  rw [reciprocal]; rfl

theorem right_reciprocal (f : Series) (v : Scalar)
    (inv : ∀ j, (f 0).residue j * v.residue j = 1) :
    convolution f (reciprocal f v) = one := by
  funext n
  cases n with
  | zero =>
    rw [product_zero, reciprocal_zero]
    exact scalar_ext (fun j => inv j)
  | succ n =>
    rw [product_succ, reciprocal_succ]
    apply scalar_ext; intro j
    let x := (convolution (fun i => f (i+1)) (reciprocal f v) n).residue j
    change (f 0).residue j * ((-v.residue j)*x) + x = 0
    have h := inv j
    calc
      _ = -(((f 0).residue j * v.residue j)*x) + x := by grind
      _ = _ := by rw [h]; grind

theorem fold_add_tail (xs : List Scalar) (b : Scalar) :
    xs.foldr add b = add (xs.foldr add (natScalar 0)) b := by
  induction xs with
  | nil => apply scalar_ext; intro p; simp [add, natScalar]
  | cons a xs ih =>
    simp only [List.foldr_cons, ih]
    apply scalar_ext; intro p
    simp only [add]
    grind

theorem product_last (f g : Series) (n : Nat) :
    convolution f g (n+1) = add (convolution f (fun k => g (k+1)) n) (mul (f (n+1)) (g 0)) := by
  unfold convolution
  rw [List.range_succ (n := n+1), List.map_append, List.foldr_append]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.sub_self]
  have rangeEq : (List.range (n+1)).map (fun k => mul (f k) (g (n+1-k))) =
      (List.range (n+1)).map (fun k => mul (f k) (g (n-k+1))) := by
    apply List.map_congr_left
    intro k hk
    have kb := List.mem_range.mp hk
    rw [show n+1-k=n-k+1 by omega]
  rw [rangeEq, fold_add_tail]
  apply scalar_ext; intro p
  simp [add,natScalar]

theorem convolution_comm (f g : Series) : convolution f g = convolution g f := by
  funext n
  induction n generalizing f g with
  | zero =>
    rw [product_zero,product_zero]
    apply scalar_ext; intro p; simp [mul, BitVec.mul_comm]
  | succ n ih =>
    rw [product_succ f g, product_last g f, ih]
    apply scalar_ext; intro p; simp only [add,mul]; grind

/-- Full power-series unit criterion, in both convolution orders. -/
theorem two_sided_inverse (f : Series) (odd : (f 0).residue 0 = 1) :
    ∃ v : Series, convolution f v = one ∧ convolution v f = one := by
  obtain ⟨a,ha⟩ := odd_scalar_inverse (f 0) odd
  have cert := right_reciprocal f a ha
  exact ⟨reciprocal f a, cert, (convolution_comm _ _).trans cert⟩

theorem product_add (f g h : Series) (n : Nat) :
    convolution (fun k => add (f k) (g k)) h n =
      add (convolution f h n) (convolution g h n) := by
  induction n generalizing f g with
  | zero =>
    simp only [product_zero]
    apply scalar_ext; intro p; simp only [mul,add]; grind
  | succ n ih =>
    simp only [product_succ]
    rw [ih (fun k => f (k+1)) (fun k => g (k+1))]
    apply scalar_ext; intro p; simp only [add,mul]; grind

theorem product_scale (a : Scalar) (f g : Series) (n : Nat) :
    convolution (fun k => mul a (f k)) g n = mul a (convolution f g n) := by
  induction n generalizing f with
  | zero =>
    simp only [product_zero]
    apply scalar_ext; intro p; simp only [mul]; grind
  | succ n ih =>
    simp only [product_succ]
    rw [ih (fun k => f (k+1))]
    apply scalar_ext; intro p; simp only [mul,add]; grind

/-- Associativity of the full untruncated Cauchy product. -/
theorem convolution_assoc (f g h : Series) :
    convolution (convolution f g) h = convolution f (convolution g h) := by
  funext n
  induction n generalizing f g h with
  | zero =>
    simp only [product_zero]
    apply scalar_ext; intro p; simp only [mul]; grind
  | succ n ih =>
    rw [product_succ (convolution f g) h, product_zero,
      product_succ f (convolution g h), product_succ g h]
    have split : (fun k => convolution f g (k+1)) =
        fun k => add (mul (f 0) (g (k+1))) (convolution (fun i => f (i+1)) g k) :=
      funext (product_succ f g)
    rw [split, product_add, product_scale, ih]
    apply scalar_ext; intro p; simp only [add,mul]; grind

theorem zero_product (g : Series) (n : Nat) :
    convolution (fun _ => natScalar 0) g n = natScalar 0 := by
  induction n with
  | zero => rw [product_zero]; apply scalar_ext; intro p; simp [mul,natScalar]
  | succ n ih =>
    rw [product_succ,ih]
    apply scalar_ext; intro p; simp [add,mul,natScalar]

theorem one_product (g : Series) : convolution one g = g := by
  funext n
  cases n with
  | zero => rw [product_zero]; apply scalar_ext; intro p; simp [one,mul,natScalar]
  | succ n =>
    rw [product_succ]
    change add (mul (natScalar 1) (g (n+1))) (convolution (fun _ => natScalar 0) g n) = _
    rw [zero_product]
    apply scalar_ext; intro p; simp [add,mul,natScalar]

/-- An odd-constant cofactor leaves the generated principal ideal unchanged
in the full dyadic power-series ring. -/
theorem reverse_factor (phi u q : Series) (odd : (u 0).residue 0=1)
    (h : phi = convolution u q) : ∃ v : Series, q = convolution v phi := by
  obtain ⟨v,_,inv⟩ := two_sided_inverse u odd
  exact ⟨v, by rw [h, ←convolution_assoc, inv, one_product]⟩

end Reimann.SignedSeriesUnit
