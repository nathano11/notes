import Reimann277.PadicInteger

namespace Reimann.TameCyclotomicLocal277

open scoped Topology

local instance reductionPrime : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- Reduction modulo 277^k is constant in a neighborhood of every p-adic integer. -/
theorem reduction_near (k : Nat) (x : ℤ_[277]) :
    ∀ᶠ y in 𝓝 x, PadicInt.toZModPow k y = PadicInt.toZModPow k x := by
  have hp : 0 < ((277 : Nat) : ℝ) := Nat.cast_pos.mpr (by decide)
  filter_upwards [Metric.ball_mem_nhds x (zpow_pos hp (-(k : ℤ)))] with y hy
  change dist y x < ((277 : Nat) : ℝ)^(-(k : ℤ)) at hy
  apply sub_eq_zero.mp
  rw [← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa only [dist_eq_norm] using hy.le

/-- In particular reduction is continuous for the discrete topology on the finite target. -/
theorem continuous_reduction (k : Nat) [TopologicalSpace (ZMod (277^k))] :
    Continuous (PadicInt.toZModPow k : ℤ_[277] →+* ZMod (277^k)) :=
  continuous_iff_continuousAt.mpr (fun x => tendsto_nhds_of_eventually_eq (reduction_near k x))

end Reimann.TameCyclotomicLocal277
