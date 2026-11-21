import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Reimann277.Biquadratic

namespace Reimann.TameBiquadraticField277

open TameRationalField277

def sqrtNegThree : Biquadratic := ⟨gen3⟩

def sqrtNegTwentyThree : Biquadratic := ⟨gen23⟩

theorem radical_squares :
    sqrtNegThree * sqrtNegThree = algebraMap ℚ Biquadratic (-3) ∧
    sqrtNegTwentyThree * sqrtNegTwentyThree = algebraMap ℚ Biquadratic (-23) := by
  rw [coefficientHom_apply,coefficientHom_apply]
  exact ⟨coord_injective generator_squares.1,coord_injective generator_squares.2⟩

theorem no_real_embedding : ¬Nonempty (Biquadratic →+* ℝ) := by
  rintro ⟨f⟩
  have h := congrArg f radical_squares.1
  have negative : algebraMap ℚ Biquadratic (-3) = -(3 : Biquadratic) := by simp
  rw [map_mul,negative,map_neg,map_ofNat] at h
  have hn := mul_self_nonneg (f sqrtNegThree)
  rw [h] at hn
  norm_num at hn

end Reimann.TameBiquadraticField277
