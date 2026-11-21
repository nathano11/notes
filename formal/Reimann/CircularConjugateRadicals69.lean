import Reimann.CircularRadicals69
import Reimann.CircularRealUnit69

/-! Conjugating the two quadratic Gauss sums in a common cyclotomic field. -/
namespace Reimann.CircularConjugateRadicals69

open Lean.Grind CircularKernel69 CircularRadicals69 CircularRealUnit69

variable {R : Type} [Field R]

theorem inverse_at_conductor (x : R) (h69 : x^69 = 1) : x⁻¹ = x^68 := by
  apply Eq.symm
  apply Field.eq_inv_of_mul_eq_one
  simpa only [Semiring.pow_succ x 68] using h69

theorem map_zero (c : Conjugation R) : c.app 0 = 0 := by
  simpa only [CircularRelationEval69.ofRat_zero] using c.rat 0

theorem map_period_sum (c : Conjugation R) (x : R) (as : List Nat) :
    c.app (periodSum x as) = periodSum (c.app x) as := by
  induction as with
  | nil => exact map_zero c
  | cons a as ih =>
    change c.app (x^a + periodSum x as) = (c.app x)^a + periodSum (c.app x) as
    rw [c.add, map_power, ih]

theorem map_signed_period (c : Conjugation R) (x : R) (p n : List Nat) :
    c.app (signedPeriod x p n) = signedPeriod (c.app x) p n := by
  rw [signedPeriod, c.sub, map_period_sum, map_period_sum, signedPeriod]

theorem map_radical3 (c : Conjugation R) (x : R) :
    c.app (radical3 x) = radical3 (c.app x) :=
  map_signed_period c x [23] [46]

theorem map_radical23 (c : Conjugation R) (x : R) :
    c.app (radical23 x) = radical23 (c.app x) :=
  map_signed_period c x (labels23 1) (labels23 276)

theorem radical3_anti_invariant (x : R) (h69 : x^69 = 1) (c : Conjugation R)
    (hc : c.app x = x⁻¹) : c.app (radical3 x) = -radical3 x := by
  rw [map_radical3, hc, inverse_at_conductor x h69]
  exact (simultaneous_conjugation x h69).1

theorem radical23_anti_invariant (x : R) (h69 : x^69 = 1) (c : Conjugation R)
    (hc : c.app x = x⁻¹) : c.app (radical23 x) = -radical23 x := by
  rw [map_radical23, hc, inverse_at_conductor x h69]
  exact (simultaneous_conjugation x h69).2

theorem compatible_of_root_inverse (x : R) (h69 : x^69 = 1) (c : Conjugation R)
    (hc : c.app x = x⁻¹) (h277 : ∀ z : R, z^277 = 1 → c.app z = z⁻¹) :
    Compatible c (radical3 x) (radical23 x) :=
  ⟨radical3_anti_invariant x h69 c hc, radical23_anti_invariant x h69 c hc, h277⟩

end Reimann.CircularConjugateRadicals69
