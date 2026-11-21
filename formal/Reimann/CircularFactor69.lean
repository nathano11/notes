import Reimann.CircularPolynomial69
import Reimann.CircularQuadratic69

/-! The two degree-22 factors of Φ₆₉ in the integral basis 1, θ,
where θ² = θ + 17. Coefficients below are in ascending degree. -/

namespace Reimann.CircularFactor69

open Lean.Grind CircularQuadratic69

attribute [local instance] Ring.intCast

def positiveCoeffs : List Element :=
  [(1,0), (-1,1), (9,-1), (-14,3), (20,-5), (-26,6), (32,-5), (-23,6),
   (17,-5), (-18,2), (11,-2), (-5,3), (11,-2), (-18,2), (17,-5), (-23,6),
   (32,-5), (-26,6), (20,-5), (-14,3), (9,-1), (-1,1), (1,0)]

def negativeCoeffs : List Element := positiveCoeffs.map conjugate

theorem degree_and_leading :
    positiveCoeffs.length = 23 ∧ positiveCoeffs.getLast? = some (1, 0) ∧
    negativeCoeffs.length = 23 ∧ negativeCoeffs.getLast? = some (1, 0) := by
  decide +kernel

def embed {R : Type} [CommRing R] (t : R) (u : Element) : R :=
  Int.cast u.1 + Int.cast u.2 * t

def evalPoly {R : Type} [CommRing R] (t x : R) : List Element → R
  | [] => 0
  | c :: cs => embed t c + x * evalPoly t x cs

def pairAdd (u v : Element) : Element := (u.1 + v.1, u.2 + v.2)

def addPoly : List Element → List Element → List Element
  | [], q => q
  | c :: cs, [] => c :: cs
  | c :: cs, d :: ds => pairAdd c d :: addPoly cs ds

def mulPoly : List Element → List Element → List Element
  | [], _ => []
  | c :: cs, q => addPoly (q.map (product c)) ((0, 0) :: mulPoly cs q)

theorem factor_coefficients :
    mulPoly positiveCoeffs negativeCoeffs =
      CircularPolynomial69.phi.map (fun c => (c, 0)) := by
  decide +kernel

theorem embed_zero {R : Type} [CommRing R] (t : R) :
    embed t (0, 0) = 0 := by
  simp [embed, Ring.intCast_zero, Semiring.zero_mul, Semiring.add_zero]

theorem embed_add {R : Type} [CommRing R] (t : R) (u v : Element) :
    embed t (pairAdd u v) = embed t u + embed t v := by
  simp only [embed, pairAdd, Ring.intCast_add]
  grind only

theorem embed_product {R : Type} [CommRing R] (t : R) (ht : t^2 = t+17)
    (u v : Element) : embed t (product u v) = embed t u * embed t v := by
  simp only [embed, product, Ring.intCast_add, Ring.intCast_mul]
  grind only

theorem evalPoly_add {R : Type} [CommRing R] (t x : R) (p q : List Element) :
    evalPoly t x (addPoly p q) = evalPoly t x p + evalPoly t x q := by
  induction p generalizing q with
  | nil => simp only [addPoly, evalPoly]; grind only
  | cons c cs ih =>
    cases q with
    | nil => simp [addPoly, evalPoly, Semiring.add_zero]
    | cons d ds =>
      simp only [addPoly, evalPoly, embed_add, ih]
      grind only

theorem evalPoly_scale {R : Type} [CommRing R] (t x : R) (ht : t^2 = t+17)
    (c : Element) (p : List Element) :
    evalPoly t x (p.map (product c)) = embed t c * evalPoly t x p := by
  induction p with
  | nil => simp [evalPoly, Semiring.mul_zero]
  | cons a as ih =>
    simp only [List.map_cons, evalPoly, embed_product t ht, ih]
    grind only

theorem evalPoly_mul {R : Type} [CommRing R] (t x : R) (ht : t^2 = t+17)
    (p q : List Element) :
    evalPoly t x (mulPoly p q) = evalPoly t x p * evalPoly t x q := by
  induction p with
  | nil => simp [evalPoly, mulPoly, Semiring.zero_mul]
  | cons c cs ih =>
    simp only [mulPoly, evalPoly_add, evalPoly_scale t x ht, evalPoly, embed_zero, ih]
    grind only

theorem evalPoly_integers {R : Type} [CommRing R] (t x : R) (p : List Int) :
    evalPoly t x (p.map (fun c => (c, 0))) = CircularPolynomial69.eval x p := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, evalPoly, CircularPolynomial69.eval, embed, ih,
      Ring.intCast_zero, Semiring.zero_mul, Semiring.add_zero]

theorem factorization {R : Type} [CommRing R] (t x : R) (ht : t^2 = t+17) :
    evalPoly t x positiveCoeffs * evalPoly t x negativeCoeffs = CircularPolynomial69.eval x CircularPolynomial69.phi := by
  rw [← evalPoly_mul t x ht, factor_coefficients, evalPoly_integers]

def sumCoeffs (p : List Element) : Element := p.foldr pairAdd (0, 0)

theorem evalPoly_one {R : Type} [CommRing R] (t : R) (p : List Element) :
    evalPoly t 1 p = embed t (sumCoeffs p) := by
  induction p with
  | nil => exact (embed_zero t).symm
  | cons c cs ih =>
    change embed t c + 1 * evalPoly t 1 cs = embed t (pairAdd c (sumCoeffs cs))
    rw [Semiring.one_mul, ih, embed_add]

theorem signed_coefficient_sums :
    sumCoeffs positiveCoeffs = (11, 3) ∧ sumCoeffs negativeCoeffs = (14, -3) := by
  decide +kernel

theorem positive_at_one {R : Type} [CommRing R] (t : R) :
    evalPoly t 1 positiveCoeffs = 11 + 3*t := by
  rw [evalPoly_one, signed_coefficient_sums.1]
  simp only [embed]
  grind only

theorem negative_at_one {R : Type} [CommRing R] (t : R) :
    evalPoly t 1 negativeCoeffs = 14 - 3*t := by
  rw [evalPoly_one, signed_coefficient_sums.2]
  simp only [embed, Ring.intCast_neg]
  grind only

/-- Add powers of the variable with the supplied exponents. -/
def powerSum : List Nat → List Int
  | [] => []
  | a :: rest => CircularPolynomial69.add (List.replicate a 0 ++ [1]) (powerSum rest)

theorem eval_powerSum {R : Type} [CommRing R] (x : R) (as : List Nat) :
    CircularPolynomial69.eval x (powerSum as) = as.foldr (fun a acc => x^a + acc) 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [powerSum, CircularPolynomial69.eval_add, CircularPolynomial69.eval_shift,
      CircularPolynomial69.eval, Ring.intCast_one, Semiring.mul_zero, Semiring.add_zero,
      Semiring.mul_one, List.foldr_cons, ih]

def periodPoly : List Int :=
  CircularPolynomial69.add [1] ((powerSum (CircularPolynomial69.exponents 1)).map (fun c => (-1 : Int)*c))

def periodTheta {R : Type} [CommRing R] (x : R) : R := CircularPolynomial69.eval x periodPoly

theorem period_theta_formula {R : Type} [CommRing R] (x : R) :
    periodTheta x = 1 - (CircularPolynomial69.exponents 1).foldr (fun a acc => x^a + acc) 0 := by
  rw [periodTheta, periodPoly, CircularPolynomial69.eval_add, CircularPolynomial69.eval_scale, eval_powerSum]
  simp only [CircularPolynomial69.eval, Ring.intCast_one, Ring.intCast_neg, Semiring.mul_zero,
    Semiring.add_zero]
  grind only

/-- Convolve integer coefficients in ascending order. -/
def mulInt : List Int → List Int → List Int
  | [], _ => []
  | c :: cs, q => CircularPolynomial69.add (q.map (fun d => c*d)) (0 :: mulInt cs q)

theorem eval_mulInt {R : Type} [CommRing R] (x : R) (p q : List Int) :
    CircularPolynomial69.eval x (mulInt p q) = CircularPolynomial69.eval x p * CircularPolynomial69.eval x q := by
  induction p with
  | nil => simp [mulInt, CircularPolynomial69.eval, Semiring.zero_mul]
  | cons c cs ih =>
    simp only [mulInt, CircularPolynomial69.eval_add, CircularPolynomial69.eval_scale,
      CircularPolynomial69.eval, Ring.intCast_zero, ih]
    grind only

theorem evalPoly_coordinates {R : Type} [CommRing R] (t x : R) (p : List Element) :
    evalPoly t x p = CircularPolynomial69.eval x (p.map Prod.fst) +
      t * CircularPolynomial69.eval x (p.map Prod.snd) := by
  induction p with
  | nil => simp [evalPoly, CircularPolynomial69.eval, Semiring.mul_zero, Semiring.add_zero]
  | cons c cs ih =>
    simp only [List.map_cons, evalPoly, embed, CircularPolynomial69.eval, ih]
    grind only

/-- The integer polynomial for θ²−θ−17, with θ represented by its period. -/
def periodRelation : List Int :=
  CircularPolynomial69.add (mulInt periodPoly periodPoly)
    (CircularPolynomial69.add (periodPoly.map (fun c => (-1 : Int)*c)) [-17])

def generatorRelation : List Int :=
  CircularPolynomial69.add (positiveCoeffs.map Prod.fst)
    (mulInt periodPoly (positiveCoeffs.map Prod.snd))

def unitRelation : List Int :=
  CircularPolynomial69.add (CircularPolynomial69.factors (CircularPolynomial69.exponents 1))
    (CircularPolynomial69.add [-11] (periodPoly.map (fun c => (-3 : Int)*c)))

/-- A zero remainder at degree 44 proves vanishing at every root of Φ₆₉. -/
theorem eval_of_zero_remainder {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0)
    (p : List Int) (h : CircularPolynomial69.strip (p.length - 44) p = List.replicate 44 0) :
    CircularPolynomial69.eval x p = 0 :=
  CircularPolynomial69.strip_sound x hx _ p (by rw [h, CircularPolynomial69.eval_zeros])

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem period_remainder :
    CircularPolynomial69.strip (periodRelation.length - 44) periodRelation = List.replicate 44 0 := by
  decide +kernel

theorem generator_remainder :
    CircularPolynomial69.strip (generatorRelation.length - 44) generatorRelation = List.replicate 44 0 := by
  decide +kernel

theorem unit_remainder :
    CircularPolynomial69.strip (unitRelation.length - 44) unitRelation = List.replicate 44 0 := by
  decide +kernel

theorem period_theta_quadratic {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) :
    (periodTheta x)^2 = periodTheta x + 17 := by
  have h := eval_of_zero_remainder x hx _ period_remainder
  simp only [periodRelation, CircularPolynomial69.eval_add, eval_mulInt, CircularPolynomial69.eval_scale,
    CircularPolynomial69.eval, Ring.intCast_neg, Semiring.mul_zero, Semiring.add_zero] at h
  unfold periodTheta
  grind only

/-- With the sign fixed by the positive quadratic Gauss period, the original
cyclotomic root belongs to the degree-22 factor whose value at one is 11+3θ. -/
theorem positive_factor_at_generator {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) :
    evalPoly (periodTheta x) x positiveCoeffs = 0 := by
  rw [evalPoly_coordinates, periodTheta]
  have h := eval_of_zero_remainder x hx _ generator_remainder
  simpa only [generatorRelation, CircularPolynomial69.eval_add, eval_mulInt] using h

theorem positive_signed_value {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) :
    CircularPolynomial69.signedProduct x 1 = 11 + 3 * periodTheta x := by
  have h := eval_of_zero_remainder x hx _ unit_remainder
  simp only [unitRelation, CircularPolynomial69.eval_add, CircularPolynomial69.eval_scale,
    CircularPolynomial69.eval, Ring.intCast_neg, Semiring.mul_zero, Semiring.add_zero,
    CircularPolynomial69.eval_factors] at h
  unfold CircularPolynomial69.signedProduct periodTheta
  grind only

theorem positive_at_one_eq_signed_product {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) :
    evalPoly (periodTheta x) 1 positiveCoeffs = CircularPolynomial69.signedProduct x 1 :=
  (positive_at_one (periodTheta x)).trans (positive_signed_value x hx).symm

theorem negative_signed_value {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) :
    CircularPolynomial69.signedProduct x 276 = 14 - 3 * periodTheta x := by
  have ht := CircularPolynomial69.norm_products_trace x hx
  have hp := positive_signed_value x hx
  grind only

theorem negative_at_one_eq_signed_product {R : Type} [CommRing R] (x : R)
    (hx : CircularPolynomial69.eval x CircularPolynomial69.phi = 0) :
    evalPoly (periodTheta x) 1 negativeCoeffs = CircularPolynomial69.signedProduct x 276 :=
  (negative_at_one (periodTheta x)).trans (negative_signed_value x hx).symm

end Reimann.CircularFactor69
