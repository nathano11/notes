import Reimann.DyadicLattice
import Reimann.DyadicInert
import Reimann.DyadicSplitRoot

/-! The completed quadratic orders in coordinates. An element (A,B)
represents A+B*w, with A,B in the quadratic order for q and w²=w−d'.
Evaluation at the two integral roots of the latter equation gives the
two dyadic factors. -/

namespace Reimann.DyadicPlaceAlgebra

open Reimann.DyadicLattice

abbrev Quadratic := Scalar × Scalar

def plus (a b : Quadratic) : Quadratic := (add a.1 b.1, add a.2 b.2)

def minus (a b : Quadratic) : Quadratic := (add a.1 (neg b.1), add a.2 (neg b.2))

def evaluate (r : Scalar) (x : Quadratic × Quadratic) : Quadratic :=
  plus x.1 (scaleVector r x.2)

def evaluations (s t : Scalar) (x : Quadratic × Quadratic) : Quadratic × Quadratic :=
  (evaluate s x, evaluate t x)

def interpolate (s u : Scalar) (values : Quadratic × Quadratic) : Quadratic × Quadratic :=
  let slope := scaleVector u (minus values.2 values.1)
  (minus values.1 (scaleVector s slope), slope)

/-- The slope recovered from two evaluations is the original coefficient
of w. At every precision the denominator t-s is a unit. -/
theorem slope_of_evaluations (s t u : Scalar)
    (hu : ∀ n, ((add t (neg s)).residue n)*u.residue n = 1)
    (x : Quadratic × Quadratic) :
    scaleVector u (minus (evaluate t x) (evaluate s x)) = x.2 := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    have h := hu n <;>
    simp only [evaluate, plus, minus, scaleVector, add, neg, mul] at * <;>
    grind

theorem interpolate_evaluations (s t u : Scalar)
    (hu : ∀ n, ((add t (neg s)).residue n)*u.residue n = 1)
    (x : Quadratic × Quadratic) : interpolate s u (evaluations s t x) = x := by
  unfold interpolate evaluations
  dsimp only
  rw [slope_of_evaluations s t u hu]
  apply Prod.ext
  · apply Prod.ext <;> apply scalar_ext <;> intro n <;>
      simp only [minus,evaluate,plus,scaleVector,add,mul,neg] <;> grind
  · rfl

theorem evaluations_interpolate (s t u : Scalar)
    (hu : ∀ n, ((add t (neg s)).residue n)*u.residue n = 1)
    (values : Quadratic × Quadratic) : evaluations s t (interpolate s u values) = values := by
  apply Prod.ext <;> apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    have h := hu n <;>
    simp only [evaluations,evaluate,interpolate,plus,minus,scaleVector,add,neg,mul] at * <;> grind

def product (cq cd : Scalar) (x y : Quadratic × Quadratic) : Quadratic × Quadratic :=
  let bd := DyadicInert.product cq x.2 y.2
  (minus (DyadicInert.product cq x.1 y.1) (scaleVector cd bd),
   plus (plus (DyadicInert.product cq x.1 y.2) (DyadicInert.product cq x.2 y.1)) bd)

/-- Multiplication reduces w² using its integral equation. Evaluation
therefore preserves products at each of the two chosen roots. -/
theorem evaluate_product (cq cd r : Scalar) (hr : add (mul r r) cd = r)
    (x y : Quadratic × Quadratic) :
    evaluate r (product cq cd x y) = DyadicInert.product cq (evaluate r x) (evaluate r y) := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    have h := congrArg (fun a : Scalar => a.residue n) hr <;>
    simp only [evaluate,product,DyadicInert.product,plus,minus,scaleVector,add,neg,mul] at * <;>
    grind

theorem evaluate_add (r : Scalar) (x y : Quadratic × Quadratic) :
    evaluate r (plus x.1 y.1, plus x.2 y.2) = plus (evaluate r x) (evaluate r y) := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [evaluate,plus,scaleVector,add,mul] <;> grind

theorem evaluate_one (r : Scalar) :
    evaluate r (DyadicInert.one, (natScalar 0,natScalar 0)) = DyadicInert.one := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp [evaluate,plus,scaleVector,add,mul,natScalar,DyadicInert.one]

theorem roots_sum_one (c s t u : Scalar)
    (hs : add (mul s s) c = s) (ht : add (mul t t) c = t)
    (hu : ∀ n, (add t (neg s)).residue n * u.residue n = 1) :
    add s t = natScalar 1 := by
  apply scalar_ext
  intro n
  have h := congrArg (fun x : Scalar => x.residue n) hs
  have k := congrArg (fun x : Scalar => x.residue n) ht
  have inv := hu n
  simp only [add,mul,neg,natScalar] at *
  grind

/-- Acting by w ↦ 1−w fixes the first quadratic order. -/
def conjugateSplit (x : Quadratic × Quadratic) : Quadratic × Quadratic :=
  (plus x.1 x.2, (neg x.2.1,neg x.2.2))

theorem conjugate_exchanges_factors (s t : Scalar) (h : add s t = natScalar 1)
    (x : Quadratic × Quadratic) :
    evaluations s t (conjugateSplit x) = (evaluate t x, evaluate s x) := by
  apply Prod.ext <;> apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    have e := congrArg (fun a : Scalar => a.residue n) h <;>
    simp only [evaluations,evaluate,conjugateSplit,plus,scaleVector,add,mul,neg,natScalar] at * <;>
    grind

/-- Splitting of the integral biquadratic presentation. Coordinates in each
factor use e=(1+√(-q))/2, and w=(1+√(-d))/2 takes the two distinct roots.
The inverse maps, multiplication, addition and identity were checked above. -/
theorem two_dyadic_factors (q d : Nat) (hq : q % 8 = 3) (hd : d % 16 = 7) :
    let cq := natScalar ((q+1)/4)
    let cd := natScalar ((d+1)/4)
    ∃ s t u : Scalar, s.residue 0 = 0 ∧ t.residue 0 = 1 ∧
      (∀ x, interpolate s u (evaluations s t x) = x) ∧
      (∀ y, evaluations s t (interpolate s u y) = y) ∧
      (∀ x y, evaluations s t (product cq cd x y) =
        (DyadicInert.product cq (evaluate s x) (evaluate s y),
         DyadicInert.product cq (evaluate t x) (evaluate t y))) ∧
      (∀ x, evaluations s t (conjugateSplit x) = (evaluate t x, evaluate s x)) ∧
      (∀ z : Quadratic, (∃ v, DyadicInert.product cq z v = DyadicInert.one ∧
        DyadicInert.product cq v z = DyadicInert.one) ↔ DyadicInert.residue z ≠ (0,0)) := by
  obtain ⟨s,t,u,hs,ht,h0,h1,hu⟩ := DyadicSplitRoot.split_roots_of_prime_residue d hd
  exact ⟨s,t,u,h0,h1,interpolate_evaluations s t u hu,evaluations_interpolate s t u hu,
    fun x y => Prod.ext (evaluate_product _ _ s hs x y) (evaluate_product _ _ t ht x y),
    conjugate_exchanges_factors s t (roots_sum_one _ s t u hs ht hu),
    DyadicInert.prime_pair_unit_test q hq⟩

end Reimann.DyadicPlaceAlgebra
