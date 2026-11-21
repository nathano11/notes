import Std

/-! Integral coordinates for θ = (1 + √69)/2 and the two conjugates
of (25 + 3√69)/2. Their products and reductions use θ² = θ + 17. -/

namespace Reimann.CircularQuadratic69

abbrev Element := Int × Int

/-- Product in the ordered basis 1, θ. -/
def product (x y : Element) : Element :=
  (x.1 * y.1 + 17 * x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

def conjugate (x : Element) : Element := (x.1 + x.2, -x.2)

def evaluate (t : Int) (x : Element) : Int := x.1 + x.2 * t

/-- The exact error at an arbitrary integer lift t factors through the defining
polynomial. In particular this formula works for either choice of root. -/
theorem product_evaluation_error (x y : Element) (t : Int) :
    evaluate t x * evaluate t y - evaluate t (product x y) =
      x.2 * y.2 * (t^2 - t - 17) := by
  unfold evaluate product
  grind

theorem reduce_product_at_root (x y : Element) (t m : Int) (h : m ∣ t^2 - t - 17) :
    m ∣ evaluate t x * evaluate t y - evaluate t (product x y) := by
  obtain ⟨k, hk⟩ := h
  rw [product_evaluation_error, hk]
  exact ⟨x.2 * y.2 * k, by grind⟩

theorem evaluate_conjugate (x : Element) (t : Int) :
    evaluate t (conjugate x) = evaluate (1-t) x := by
  unfold evaluate conjugate
  grind

/-- 11 + 3θ = (25 + 3√69)/2 in the integral basis. -/
def epsilon : Element := (11, 3)

theorem epsilon_conjugate : conjugate epsilon = (14, -3) := by decide

theorem epsilon_norm_one : product epsilon (conjugate epsilon) = (1, 0) := by
  rw [epsilon_conjugate]
  decide

theorem sqrt_discriminant_identity (t : Int) :
    (2*t-1)^2 - 69 = 4*(t^2 - t - 17) := by grind

theorem epsilon_sqrt_coordinate (t : Int) :
    2*evaluate t epsilon = 25 + 3*(2*t-1) := by
  unfold evaluate epsilon
  grind

theorem auxiliary_root :
    (114679 : Int) ∣ (92746 : Int)^2 - 92746 - 17 ∧
      (2 * (92746 : Int) - 1) % 114679 = 70812 := by decide

theorem auxiliary_epsilon :
    evaluate 92746 epsilon % 114679 = 48891 ∧
      evaluate 92746 (conjugate epsilon) % 114679 = 65813 := by decide

theorem split_roots :
    (277^2 : Int) ∣ (13420 : Int)^2 - 13420 - 17 ∧
      (277^2 : Int) ∣ (63310 : Int)^2 - 63310 - 17 ∧
      (2 * (13420 : Int) - 1) % 277^2 = 26839 ∧
      (2 * (63310 : Int) - 1) % 277^2 = 49890 := by decide

theorem split_epsilon :
    evaluate 13420 epsilon % 277^2 = 40271 ∧
      evaluate 63310 epsilon % 277^2 = 36483 := by decide

end Reimann.CircularQuadratic69
