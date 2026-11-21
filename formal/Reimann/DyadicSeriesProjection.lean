import Reimann.DyadicStickelberger69

/-!
Projection of a dyadic formal power series to (ℤ/8)[C₂] at T = γ-1.
Coefficients are the coherent dyadic integers. Powers T⁴ and higher vanish
in the target, so multiplication reduces to the first four convolution sums.
-/

namespace Reimann.DyadicSeriesProjection

open Reimann.DyadicLattice Reimann.DyadicStickelberger69

abbrev Series := Nat → Scalar

abbrev Row := BitVec 3 × BitVec 3

/-- Image of T^n in the ordered basis [1], [γ]. -/
def augmentationPower : Nat → Row
  | 0 => (1,0)
  | n+1 => rowMul (-1,1) (augmentationPower n)

theorem square_of_generator_difference : augmentationPower 2 = (2,-2) := by decide

theorem cube_of_generator_difference : augmentationPower 3 = (-4,4) := by decide

theorem fourth_power_zero : augmentationPower 4 = (0,0) := by decide

theorem higher_powers_zero (n : Nat) : augmentationPower (n+4) = (0,0) := by
  induction n with
  | zero => exact fourth_power_zero
  | succ n ih =>
    change rowMul (-1,1) (augmentationPower (n+4)) = (0,0)
    rw [ih]
    decide

/-- Coefficient n of the Cauchy product sums f(j)g(n-j) for 0 ≤ j ≤ n. -/
def convolution (f g : Series) (n : Nat) : Scalar :=
  ((List.range (n+1)).map (fun j => mul (f j) (g (n-j)))).foldr add (natScalar 0)

/-- F(γ-1) is the sum of the first four coefficient rows. -/
def evaluate (f : Series) : Row :=
  let a := (f 0).residue 2
  let b := (f 1).residue 2
  let c := (f 2).residue 2
  let d := (f 3).residue 2
  (a-b+2*c-4*d, b-2*c+4*d)

theorem convolution_zero (f g : Series) :
    (convolution f g 0).residue 2 =
      (f 0).residue 2*(g 0).residue 2 := by
  change (f 0).residue 2*(g 0).residue 2+(0) = _
  simp

theorem convolution_one (f g : Series) :
    (convolution f g 1).residue 2 =
      (f 0).residue 2*(g 1).residue 2+((f 1).residue 2*(g 0).residue 2) := by
  change (f 0).residue 2*(g 1).residue 2+((f 1).residue 2*(g 0).residue 2+(0)) = _
  simp

theorem convolution_two (f g : Series) :
    (convolution f g 2).residue 2 =
      (f 0).residue 2*(g 2).residue 2+((f 1).residue 2*(g 1).residue 2+((f 2).residue 2*(g 0).residue 2)) := by
  change (f 0).residue 2*(g 2).residue 2+((f 1).residue 2*(g 1).residue 2+((f 2).residue 2*(g 0).residue 2+(0))) = _
  simp

theorem convolution_three (f g : Series) :
    (convolution f g 3).residue 2 =
      (f 0).residue 2*(g 3).residue 2+((f 1).residue 2*(g 2).residue 2+((f 2).residue 2*(g 1).residue 2+((f 3).residue 2*(g 0).residue 2))) := by
  change (f 0).residue 2*(g 3).residue 2+((f 1).residue 2*(g 2).residue 2+((f 2).residue 2*(g 1).residue 2+((f 3).residue 2*(g 0).residue 2+(0)))) = _
  simp

/-- The ordinary series product maps to multiplication in (ℤ/8)[C₂]. -/
theorem evaluate_convolution (f g : Series) :
    evaluate (convolution f g) = rowMul (evaluate f) (evaluate g) := by
  simp only [evaluate, rowMul, convolution_zero, convolution_one,
    convolution_two, convolution_three]
  apply Prod.ext <;> grind

/-- Evaluate the truncation containing the coefficients of degrees below n. -/
def partialEvaluation (f : Series) : Nat → Row
  | 0 => (0,0)
  | n+1 =>
    let x := partialEvaluation f n
    let t := augmentationPower n
    let c := (f n).residue 2
    (x.1+c*t.1, x.2+c*t.2)

theorem evaluate_first_four (f : Series) : partialEvaluation f 4 = evaluate f := by
  simp only [partialEvaluation, augmentationPower, rowMul, evaluate]
  apply Prod.ext <;> grind

/-- All longer truncations have exactly the same value in the finite group ring. -/
theorem all_truncations_stabilize (f : Series) (n : Nat) :
    partialEvaluation f (n+4) = evaluate f := by
  induction n with
  | zero => exact evaluate_first_four f
  | succ n ih =>
    change ((partialEvaluation f (n+4)).1+(f (n+4)).residue 2*(augmentationPower (n+4)).1,
      (partialEvaluation f (n+4)).2+(f (n+4)).residue 2*(augmentationPower (n+4)).2) = evaluate f
    rw [ih, higher_powers_zero]
    simp

theorem evaluate_add (f g : Series) :
    evaluate (fun i => add (f i) (g i)) =
      ((evaluate f).1 + (evaluate g).1, (evaluate f).2 + (evaluate g).2) := by
  simp only [evaluate, add]
  apply Prod.ext <;> grind

theorem evaluate_one : evaluate (fun i => natScalar (if i=0 then 1 else 0)) = (1,0) := by
  decide

def quadraticSeries (c0 c1 : Scalar) : Series
  | 0 => c0
  | 1 => c1
  | 2 => natScalar 1
  | _+3 => natScalar 0

theorem evaluate_quadratic (c0 c1 : Scalar) :
    evaluate (quadraticSeries c0 c1) = polynomialRow c0 c1 := by
  rw [polynomial_row_coordinates]
  simp only [evaluate, quadraticSeries, natScalar]
  apply Prod.ext <;> grind

/-- Each unrestricted full-series multiplier maps to a multiplier of the corresponding row. -/
theorem project_mutual_divisibility (p q : Series)
    (h : ∃ u v : Series, p = convolution u q ∧ q = convolution v p) :
    ∃ u v : Row, evaluate p = rowMul u (evaluate q) ∧ evaluate q = rowMul v (evaluate p) := by
  obtain ⟨u,v,hp,hq⟩ := h
  exact ⟨evaluate u, evaluate v, (congrArg evaluate hp).trans (evaluate_convolution _ _),
    (congrArg evaluate hq).trans (evaluate_convolution _ _)⟩

/-- For k = ℚ(√(-69)), an arithmetic construction must supply Φ, the
full-series ideal equality, and the half-normalized Stickelberger row for Φ. -/
theorem projected_ideal_of_full_series (c0 c1 : Scalar) (phi : Series)
    (hideal : ∃ u v : Series, quadraticSeries c0 c1 = convolution u phi ∧
      phi = convolution v (quadraticSeries c0 c1))
    (hrow : evaluate phi = halfRow) : ProjectedIdeal69 c0 c1 := by
  have h := project_mutual_divisibility _ _ hideal
  rw [evaluate_quadratic, hrow] at h
  exact h

end Reimann.DyadicSeriesProjection
