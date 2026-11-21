import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.NormNum
import Reimann277.FiniteRadii

namespace Reimann.TameFiniteAbsolute277

local instance prime277 : Fact (Nat.Prime 277) := ⟨by decide +kernel⟩

theorem norm_prime : ‖(277 : ℚ_[277])‖ = (277 : ℝ)⁻¹ := by
  simpa only [Nat.cast_ofNat] using (Padic.norm_p (p := 277))

variable {K : Type*} [Field K]
variable (v : AbsoluteValue K ℝ) (f : K →+* ℚ_[277])
variable (hc : ∀ x y : K, v x ≤ v y ↔ ‖f x‖ ≤ ‖f y‖)
include hc

theorem strict_comparison (x y : K) : v x < v y ↔ ‖f x‖ < ‖f y‖ := by
  rw [← not_le,← not_le,hc]

theorem normalize_prime (hpow : ∃ k : ℤ, v 277 = (277:ℝ)^k)
    (hstep : ∃ u : K, v u = (277:ℝ)⁻¹) : v 277 = (277:ℝ)⁻¹ := by
  have hs : v (277:K) < v 1 := (strict_comparison v f hc _ _).mpr (by
    rw [map_ofNat,map_one,norm_one]; exact Padic.norm_p_lt_one)
  rw [map_one] at hs
  obtain ⟨k,hk⟩ := hpow
  have hp : 1 < (277:ℝ) := by norm_num
  have hkneg : k < 0 := by
    by_contra! he
    exact (not_lt_of_ge (one_le_zpow₀ hp.le he)) (hk ▸ hs)
  apply le_antisymm
  · rw [hk,← zpow_neg_one]
    exact zpow_le_zpow_right₀ hp.le (by omega)
  · obtain ⟨u,hu⟩ := hstep
    have hsmall : ‖f u‖ < 1 := by
      have h := (strict_comparison v f hc u 1).mp (by rw [map_one,hu]; norm_num)
      simpa only [map_one,norm_one] using h
    have hbound := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (f u) (-1)).mpr
      (by simpa using hsmall)
    have he := (hc u 277).mpr (by
      simpa only [map_ofNat,norm_prime,Nat.cast_ofNat,zpow_neg_one] using hbound)
    rwa [hu] at he

theorem normalized_absolute_value (hprime : v 277 = (277:ℝ)⁻¹) (x : K) :
    v x = ‖f x‖ := by
  by_cases hx : x = 0
  · subst x; simp
  let k : ℤ := (f x).valuation
  let r : K := (277 : K)^k
  have ne : f x ≠ 0 := fun he => hx (f.injective (he.trans (map_zero _).symm))
  have he : ‖f x‖ = ‖f r‖ := by
    dsimp only [r]
    rw [map_zpow₀,map_ofNat,norm_zpow,norm_prime,Padic.norm_eq_zpow_neg_valuation ne,
      inv_zpow,zpow_neg]
    rfl
  have hw := le_antisymm ((hc x r).mpr he.le) ((hc r x).mpr he.ge)
  rw [hw,he]
  dsimp only [r]
  rw [map_zpow₀,hprime,map_zpow₀,map_ofNat,norm_zpow,norm_prime]

end Reimann.TameFiniteAbsolute277
