import Std

namespace Reimann.TameOrientation

/-- Precomposition by the inverse group element acts on the untwisted
dual by the reciprocal scalar. Here forward and backward act on class representatives. -/
theorem dual_action (m u v : Int) (forward backward : A → A) (f : A → Int)
    (inverse : ∀ x, forward (backward x) = x) (unit : m ∣ u*v-1)
    (equivariant : ∀ x, m ∣ f (forward x)-u*f x) (x : A) :
    m ∣ f (backward x)-v*f x := by
  obtain ⟨a,ha⟩ := equivariant (backward x)
  rw [inverse] at ha
  obtain ⟨b,hb⟩ := unit
  exact ⟨-v*a-b*f (backward x), by grind⟩

/-- If a class belongs to a different eigenline and the difference of
the two eigenvalues is a unit, any equivariant character kills that class. -/
theorem other_line_zero (m u eigen i x fx : Int)
    (target : m ∣ fx-u*x) (source : m ∣ fx-eigen*x)
    (separate : m ∣ i*(eigen-u)-1) : m ∣ x := by
  obtain ⟨a,ha⟩ := target
  obtain ⟨b,hb⟩ := source
  obtain ⟨d,hd⟩ := separate
  exact ⟨i*(a-b)-d*x, by grind⟩

theorem weight_one_inverse : (277 : Int) ∣ 111*5-1 := by decide

/-- For σ₅ at weight one the character evaluates with scalar 111.
The generator acting by pullback on the untwisted dual has scalar 5. -/
theorem weight_one_dual (forward backward : A → A) (f : A → Int)
    (inverse : ∀ x, forward (backward x) = x)
    (equivariant : ∀ x, (277 : Int) ∣ f (forward x)-111*f x) (x : A) :
    (277 : Int) ∣ f (backward x)-5*f x :=
  dual_action 277 111 5 forward backward f inverse weight_one_inverse equivariant x

end Reimann.TameOrientation
