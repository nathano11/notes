import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Reimann.TameAdicDomain277

namespace Reimann.TameFiniteRadii277

variable {K : Type*} [Field K] [CharZero K]
variable (v : AbsoluteValue K ℝ) (ha : IsNonarchimedean v)
variable (hb : ∀ z : ℤ, v (z : K) ≤ 1) (hp : v (277 : K) < 1)
include ha hb hp

theorem integer_unit (z : ℤ) (hz : ¬ (277 : ℤ) ∣ z) : v (z : K) = 1 := by
  apply le_antisymm (hb z)
  by_contra! hs
  obtain ⟨a,b,h⟩ := TameAdicDomain277.unit_at_all_depths z hz 1
  have hi : (z : K) * (a : K) + (277:K)*(b : K) = 1 := by
    exact_mod_cast (show z*a+277*b=1 by simpa using h)
  have sm (x : K) (k : ℤ) (hx : v x < 1) : v (x*(k:K)) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_right (v.nonneg x) (hb k)).trans_lt hx
  have hh := ha ((z:K)*(a:K)) ((277:K)*(b:K))
  rw [hi,map_one] at hh
  exact (not_lt_of_ge hh) (max_lt (sm _ _ hs) (sm _ _ hp))

theorem integer_small_iff (z : ℤ) :
    v (z : K) < 1 ↔ (277 : ℤ) ∣ z := by
  constructor
  · intro h; by_contra h'; exact (ne_of_lt h) (integer_unit v ha hb hp z h')
  · rintro ⟨a,rfl⟩
    rw [Int.cast_mul, Int.cast_ofNat, map_mul]
    exact (mul_le_of_le_one_right (v.nonneg _) (hb a)).trans_lt hp

theorem integer_radii (n : ℕ) (z : ℤ) :
    v (z : K) ≤ v (((277 : ℤ)^n : ℤ) : K) ↔ (277 : ℤ)^n ∣ z := by
  induction n generalizing z with
  | zero => simpa using hb z
  | succ n ih =>
    have hpos : 0 < v (277:K) := v.pos (by norm_num)
    have hpow := hb ((277 : ℤ)^n)
    have he : v (((277 : ℤ)^(n+1) : ℤ) : K) =
        v (277:K)*v (((277 : ℤ)^n : ℤ) : K) := by
      rw [pow_succ',Int.cast_mul,Int.cast_ofNat,map_mul]
    rw [he]
    constructor
    · intro h
      have hs := h.trans_lt ((mul_le_of_le_one_right hpos.le hpow).trans_lt hp)
      obtain ⟨a,hh⟩ := (integer_small_iff v ha hb hp z).mp hs
      rw [hh,Int.cast_mul,Int.cast_ofNat,map_mul] at h
      obtain ⟨b,hb'⟩ := (ih a).mp (le_of_mul_le_mul_left h hpos)
      exact ⟨b, by rw [hh,hb',pow_succ']; ac_rfl⟩
    · rintro ⟨a,hh⟩
      rw [hh, ← he, Int.cast_mul, map_mul]
      exact mul_le_of_le_one_right (v.nonneg _) (hb a)

end Reimann.TameFiniteRadii277
