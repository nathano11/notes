import Reimann.CircularRational69
import Reimann.CircularFactor69
import Reimann.CircularPrimitive69

/-! Embed the rational quadratic field by sending θ to a chosen quadratic root,
and specialize to the Gauss period of a primitive 69th root. -/

namespace Reimann.CircularRationalPeriod69

open Lean.Grind Lean.Grind.Field.NormNum CircularRational69

def evaluate {R : Type} [Field R] (t : R) (x : Element) : R :=
  ofRat x.a + ofRat x.b * t

theorem cast_int {R : Type} [Field R] (z : Int) :
    (ofRat (z : Rat) : R) = @Int.cast R Ring.intCast z := by
  simp [ofRat, Rat.num_intCast, Rat.den_intCast, Semiring.natCast_one, Field.div_eq_mul_inv,
    Field.inv_one, Semiring.mul_one]

theorem eval_scalar {R : Type} [Field R] (t : R) (q : Rat) :
    evaluate t (scalar q) = ofRat q := by
  have hz := cast_int (R := R) 0
  change (ofRat 0 : R) = _ at hz
  rw [Ring.intCast_zero] at hz
  simp only [evaluate, scalar, hz, Semiring.zero_mul, Semiring.add_zero]

theorem eval_theta {R : Type} [Field R] (t : R) : evaluate t theta = t := by
  have hz := cast_int (R := R) 0
  have ho := cast_int (R := R) 1
  change (ofRat 0 : R) = _ at hz
  change (ofRat 1 : R) = _ at ho
  rw [Ring.intCast_zero] at hz
  rw [Ring.intCast_one] at ho
  simp only [evaluate, theta, hz, ho, Semiring.one_mul]
  grind only

theorem eval_add {R : Type} [Field R] [IsCharP R 0] (t : R) (x y : Element) :
    evaluate t (plus x y) = evaluate t x + evaluate t y := by
  simp only [evaluate, plus, ofRat_add]
  grind only

theorem eval_negative {R : Type} [Field R] (t : R) (x : Element) :
    evaluate t (negative x) = -evaluate t x := by
  simp only [evaluate, negative, ofRat_neg]
  grind only

theorem eval_mul {R : Type} [Field R] [IsCharP R 0] (t : R) (ht : t^2 = t + 17)
    (x y : Element) : evaluate t (times x y) = evaluate t x * evaluate t y := by
  have h := cast_int (R := R) 17
  change (ofRat 17 : R) = _ at h
  simp only [evaluate, times, ofRat_add, ofRat_mul, h]
  grind only

theorem eval_zero {R : Type} [Field R] (t : R) : evaluate t (scalar 0) = 0 := by
  rw [eval_scalar]
  exact (cast_int (R := R) 0).trans Ring.intCast_zero

theorem eval_one {R : Type} [Field R] (t : R) : evaluate t (scalar 1) = 1 := by
  rw [eval_scalar]
  exact (cast_int (R := R) 1).trans Ring.intCast_one

theorem eval_zero_kernel {R : Type} [Field R] [IsCharP R 0] (t : R) (ht : t^2 = t + 17)
    (x : Element) (h : evaluate t x = 0) : x = scalar 0 := by
  apply Classical.byContradiction
  intro hn
  have hh := eval_mul t ht x (inverse x)
  rw [times_inverse x hn, eval_one, h, Semiring.zero_mul] at hh
  exact Field.zero_ne_one hh.symm

theorem eval_injective {R : Type} [Field R] [IsCharP R 0] (t : R) (ht : t^2 = t + 17)
    {x y : Element} (h : evaluate t x = evaluate t y) : x = y := by
  have hz : evaluate t (plus x (negative y)) = 0 := by rw [eval_add, eval_negative, h]; grind only
  have hh := eval_zero_kernel t ht _ hz
  have ha := congrArg Element.a hh
  have hb := congrArg Element.b hh
  apply ext_coordinates <;> simp only [plus, negative, scalar] at ha hb <;> grind only

theorem primitive_period_injective {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) {v w : Element}
    (h : evaluate (CircularFactor69.periodTheta x) v = evaluate (CircularFactor69.periodTheta x) w) :
    v = w := eval_injective _ (CircularFactor69.period_theta_quadratic x
      (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3)) h

theorem basis_independent {R : Type} [Field R] [IsCharP R 0] (t : R) (ht : t^2 = t + 17)
    (a b : Rat) (h : ofRat a + ofRat b*t = 0) : a = 0 ∧ b = 0 := by
  have hh := eval_zero_kernel t ht ⟨a, b⟩ h
  exact ⟨congrArg Element.a hh, congrArg Element.b hh⟩

def ofIntegral (c : CircularQuadratic69.Element) : Element := ⟨c.1, c.2⟩

theorem eval_integral {R : Type} [Field R] (t : R) (c : CircularQuadratic69.Element) :
    evaluate t (ofIntegral c) = CircularFactor69.embed t c := by
  simp only [evaluate, ofIntegral, cast_int, CircularFactor69.embed]

theorem primitive_epsilon_image {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    evaluate (CircularFactor69.periodTheta x) (ofIntegral CircularQuadratic69.epsilon) =
      CircularPolynomial69.signedProduct x 1 := by
  rw [eval_integral, CircularFactor69.positive_signed_value x
    (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3)]
  unfold CircularFactor69.embed CircularQuadratic69.epsilon
  grind only

theorem eval_inverse {R : Type} [Field R] [IsCharP R 0] (t : R) (ht : t^2 = t + 17)
    (x : Element) : evaluate t (inverse x) = (evaluate t x)⁻¹ := by
  by_cases hx : x = scalar 0
  · rw [hx, inverse_zero, eval_zero, Field.inv_zero]
  · apply Field.eq_inv_of_mul_eq_one
    rw [CommSemiring.mul_comm, ← eval_mul t ht, times_inverse x hx, eval_one]

theorem range_contains_scalars {R : Type} [Field R] (t : R) (q : Rat) :
    ∃ x : Element, evaluate t x = ofRat q := ⟨scalar q, eval_scalar t q⟩

theorem range_contains_root {R : Type} [Field R] (t : R) :
    ∃ x : Element, evaluate t x = t := ⟨theta, eval_theta t⟩

theorem range_minimal {R : Type} [Field R] (t : R) (S : R → Prop)
    (hq : ∀ q : Rat, S (ofRat q)) (ht : S t)
    (ha : ∀ a b, S a → S b → S (a+b)) (hm : ∀ a b, S a → S b → S (a*b)) (x : Element) :
    S (evaluate t x) := ha _ _ (hq x.a) (hm _ _ (hq x.b) ht)

theorem primitive_conjugate_epsilon_image {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    evaluate (CircularFactor69.periodTheta x)
      (ofIntegral (CircularQuadratic69.conjugate CircularQuadratic69.epsilon)) =
        CircularPolynomial69.signedProduct x 276 := by
  rw [eval_integral, CircularFactor69.negative_signed_value x
    (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3), CircularQuadratic69.epsilon_conjugate]
  unfold CircularFactor69.embed
  grind only

theorem primitive_period_basis {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (a b : Rat) :
    ofRat a + ofRat b * CircularFactor69.periodTheta x = (0 : R) ↔ a = 0 ∧ b = 0 := by
  constructor
  · exact basis_independent _ (CircularFactor69.period_theta_quadratic x
      (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3)) a b
  · rintro ⟨rfl, rfl⟩
    exact eval_zero (CircularFactor69.periodTheta x)

end Reimann.CircularRationalPeriod69
