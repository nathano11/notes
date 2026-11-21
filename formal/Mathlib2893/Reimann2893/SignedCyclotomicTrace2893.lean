import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The trace coordinate for the real cyclotomic layer and its forward action. -/
namespace Reimann.SignedCyclotomicTrace2893

variable {F : Type*} [Field F]

def realTrace (z : F) : F := z + z⁻¹

theorem square_trace (z : F) (hz : z ≠ 0) :
    realTrace (z^2) = (realTrace z)^2-2 := by
  unfold realTrace
  field_simp [hz]
  ring

theorem trace_zero (z : F) (hz : z ≠ 0) (h : z^2 = -1) :
    realTrace z = 0 := by
  unfold realTrace
  field_simp [hz]
  simp [h]

/-- The forward generator raises the primitive root to the fifth power. -/
theorem forward_trace (z : F) (hz : z ≠ 0) :
    realTrace (z^5) = (realTrace z)^5 - 5*(realTrace z)^3 + 5*realTrace z := by
  unfold realTrace
  field_simp [hz]
  ring

theorem compatible_traces (z : ℕ → F) (nonzero : ∀ n, z n ≠ 0)
    (square : ∀ n, z (n+1)^2 = z n) (n : ℕ) :
    (realTrace (z (n+1)))^2 = 2 + realTrace (z n) := by
  rw [← square n, square_trace _ (nonzero _)]
  ring

end Reimann.SignedCyclotomicTrace2893
