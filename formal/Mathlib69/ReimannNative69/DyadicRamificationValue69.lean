import ReimannNative69.DyadicValuationLog69
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

/-! Multiplicative ramification becomes a common additive factor in the orders
of x and 2. Dividing the two orders makes the finite-layer restrictions agree. -/
namespace Reimann.DyadicRamificationValue69

open IsDedekindDomain DyadicValuationLog69

variable {A B K : Type} (L : Type) [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B]
  [Field K] [Field L] [Algebra K L] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [IsScalarTower A K L] [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
  (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

theorem order_liesOver (x : K) :
    order (w.valuation L) (algebraMap K L x) =
      (w.asIdeal.ramificationIdx A : ℤ) * order (v.valuation K) x := by
  simp only [order,← v.valuation_liesOver L w x,WithZero.log_pow,nsmul_eq_mul,mul_neg]

theorem two_order_liesOver : order (w.valuation L) 2 =
    (w.asIdeal.ramificationIdx A : ℤ) * order (v.valuation K) 2 := by
  simpa only [map_ofNat] using order_liesOver L v w (2:K)

/-- The ramification index cancels for every x, including the designated value at zero.
This equality yields stage compatibility without a generation or place-uniqueness hypothesis. -/
theorem normalized_value_liesOver (x : K) :
    scale (w.valuation L) (algebraMap K L x) = scale (v.valuation K) x := by
  have he : (w.asIdeal.ramificationIdx A : ℚ) ≠ 0 := by
    exact_mod_cast (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot).ne'
  simp only [scale,order_liesOver L v w x,two_order_liesOver L v w (K:=K),Int.cast_mul,Int.cast_natCast]
  exact mul_div_mul_left _ _ he

/-- Positivity at two upstairs and agreement of the actual normalized DyadicValue
follow from positivity downstairs and the lying-over prime condition alone. -/
theorem normalized_above_two [CharZero K] [CharZero L] (h : 0 < order (v.valuation K) 2) :
    ∃ h' : 0 < order (w.valuation L) 2, ∀ x : K,
      (normalized (w.valuation L) (by norm_num) h').val (algebraMap K L x) =
        (normalized (v.valuation K) (by norm_num) h).val x := by
  have he : (0:ℤ) < (w.asIdeal.ramificationIdx A : ℤ) := by
    exact_mod_cast (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot)
  refine ⟨(two_order_liesOver L v w (K:=K)).symm ▸ mul_pos he h,?_⟩
  exact normalized_value_liesOver L v w

end Reimann.DyadicRamificationValue69
