import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Field.Rat
import Reimann.DyadicLocalRestriction69

/-! The additive normalization of a discrete multiplicative valuation. -/
namespace Reimann.DyadicValuationLog69

open DyadicDecomposition69 DyadicLocalRestriction69
open scoped WithZero

variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)

/-- The sign converts Arakelov's multiplicative convention into vanishing order.
The core dyadic value assigns zero the dummy order zero. -/
def order (x : K) : ℤ := -WithZero.log (v x)

@[simp] theorem order_zero : order v 0=0 := by simp [order]

theorem order_mul {x y : K} (hx : x≠0) (hy : y≠0) :
    order v (x*y)=order v x+order v y := by
  simp only [order,map_mul,WithZero.log_mul ((map_ne_zero v).mpr hx) ((map_ne_zero v).mpr hy)]
  omega

theorem order_lt_iff {x y : K} (hx : x≠0) (hy : y≠0) :
    order v x < order v y ↔ v y < v x := by
  rw [order,order,neg_lt_neg_iff, WithZero.log_lt_log ((map_ne_zero v).mpr hy) ((map_ne_zero v).mpr hx)]

theorem order_pos_iff {x : K} (hx : x≠0) : 0 < order v x ↔ v x < 1 := by
  have h := order_lt_iff v (x:=1) (y:=x) one_ne_zero hx
  simpa [order] using h

theorem order_nonneg_of_le_one {x : K} (h : v x ≤ 1) : 0 ≤ order v x := by
  by_cases hz : x=0
  · simp [hz]
  · have le := (WithZero.log_le_log ((map_ne_zero v).mpr hz) (one_ne_zero : (1:ℤᵐ⁰)≠0)).mpr h
    simpa [order] using le

def scale (x : K) : ℚ := (order v x : ℚ) / (order v 2 : ℚ)

theorem scale_lt_iff (hd : 0<order v 2) (x y : K) :
    scale v x < scale v y ↔ order v x < order v y := by
  have h : (0:ℚ)<(order v 2 : ℚ) := by exact_mod_cast hd
  simp only [scale,div_lt_div_iff_of_pos_right h,Int.cast_lt]

/-- Normalize the additive order by the actual ramification index v₂(2). -/
def normalized (two_ne : (2:K)≠0) (hd : 0<order v 2) : DyadicValue K where
  val := scale v
  zero := by simp [scale]
  two_ne := two_ne
  two := by exact div_self (by exact_mod_cast (ne_of_gt hd) : (order v 2 : ℚ)≠0)
  mul hx hy := by simp only [scale,order_mul v hx hy,Int.cast_add,add_div]
  smaller {x y} hx hy small := by
    have hv := (order_lt_iff v hx hy).mp ((scale_lt_iff v hd x y).mp small)
    have eq := v.map_add_eq_of_lt_left hv
    refine ⟨fun hz => ((map_ne_zero v).mpr hx) (eq.symm.trans (hz ▸ map_zero v)),?_⟩
    simp only [scale, order, eq]

theorem support_iff (two_ne : (2:K)≠0) (hd : 0<order v 2) (x : K) :
    Supports (normalized v two_ne hd) x ↔ v x<1 := by
  by_cases hx : x=0
  · subst x
    simp [Supports]
  · have h := scale_lt_iff v hd 0 x
    simp only [scale,order_zero,Int.cast_zero,zero_div] at h
    exact (or_iff_right hx).trans (h.trans (order_pos_iff v hx))

end Reimann.DyadicValuationLog69
