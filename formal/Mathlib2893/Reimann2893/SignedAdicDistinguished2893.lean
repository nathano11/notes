import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A two-dimensional representation admitting a coherent tower of cube roots has
distinguished shifted characteristic polynomial at two. This applies to the
dyadic exponent action because three is a unit in the dyadic integers. -/
namespace Reimann.SignedAdicDistinguished2893

open Polynomial
open scoped Matrix Polynomial

theorem descent_three (h : ℕ → ℕ)
    (step : ∀ j, h j ≠ 0 → h j = 3 * h (j+1)) (j : ℕ) : h j = 0 := by
  classical
  by_contra hn
  have ex : ∃ m : ℕ, ∃ i, h i = m ∧ m ≠ 0 := ⟨h j,j,rfl,hn⟩
  obtain ⟨i, hi, hp⟩ := Nat.find_spec ex
  have hs := step i (hi ▸ hp)
  have lt : h (i+1) < Nat.find ex := by omega
  exact (Nat.find_min ex lt) ⟨i+1, rfl, by omega⟩

theorem determinant_norm (d : ℕ → ℚ_[2]) (unit : ∀ j, d j ≠ 0)
    (cube : ∀ j, (d (j+1))^3 = d j) (j : ℕ) : ‖d j‖ = 1 := by
  have v (i : ℕ) : (d i).valuation = 3 * (d (i+1)).valuation := by
    rw [← cube i, Padic.valuation_pow]
    norm_num
  have h := descent_three (fun i => (d i).valuation.natAbs)
    (fun i _ => by simpa [Int.natAbs_mul] using congrArg Int.natAbs (v i)) j
  have hz : (d j).valuation = 0 := Int.natAbs_eq_zero.mp h
  simp [Padic.norm_eq_zpow_neg_valuation (unit j),hz]

theorem trace_norm_cube (x d : ℚ_[2]) (unit : ‖d‖ = 1) (hx : 1 < ‖x‖) :
    ‖x^3 - 3*d*x‖ = ‖x^3‖ := by
  have h3 : ‖(3 : ℚ_[2])‖ = 1 := (Padic.norm_natCast_eq_one_iff (n := 3)).mpr (by decide)
  have hsmall : ‖-(3*d*x)‖ < ‖x^3‖ := by
    rw [norm_neg, norm_mul, norm_mul, h3, unit, one_mul, one_mul, norm_pow]
    nlinarith [mul_pos (sub_pos.mpr hx) (sq_pos_of_pos (lt_trans zero_lt_one hx))]
  rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (ne_of_gt hsmall), max_eq_left (le_of_lt hsmall)]

theorem trace_integral (t d : ℕ → ℚ_[2]) (unit : ∀ j, ‖d j‖ = 1)
    (cube : ∀ j, t j = t (j+1)^3 - 3*d (j+1)*t (j+1)) (j : ℕ) : ‖t j‖ ≤ 1 := by
  let h (i : ℕ) := (-(t i).valuation).toNat
  have step (i : ℕ) (hn : h i ≠ 0) : h i = 3 * h (i+1) := by
    have hv : (t i).valuation < 0 := by dsimp [h] at hn; omega
    have large : 1 < ‖t i‖ := lt_of_not_ge (fun hi => (not_le_of_gt hv) ((Padic.norm_le_one_iff_val_nonneg _).mp hi))
    have h3 : ‖(3 : ℚ_[2])‖ = 1 := (Padic.norm_natCast_eq_one_iff (n := 3)).mpr (by decide)
    have next : 1 < ‖t (i+1)‖ := by
      by_contra! small
      have hlow := Padic.nonarchimedean (t (i+1)^3) (-(3*d (i+1)*t (i+1)))
      rw [← sub_eq_add_neg, ← cube i, norm_pow, norm_neg, norm_mul, norm_mul, h3, unit, one_mul, one_mul] at hlow
      exact (not_le_of_gt large) (hlow.trans (max_le (pow_le_one₀ (norm_nonneg _) small) small))
    have nz : t i ≠ 0 := fun e => by norm_num [e] at large
    have nz' : t (i+1) ≠ 0 := fun e => by norm_num [e] at next
    have he : ‖t i‖ = ‖t (i+1)^3‖ := (congrArg (fun a : ℚ_[2] => ‖a‖) (cube i)).trans
      (trace_norm_cube _ _ (unit _) next)
    rw [Padic.norm_eq_zpow_neg_valuation nz,
      Padic.norm_eq_zpow_neg_valuation (pow_ne_zero 3 nz'), Padic.valuation_pow] at he
    have eq := (zpow_right_inj₀ (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)).mp he
    dsimp [h]
    norm_num at eq
    omega
  have hz := descent_three h step j
  dsimp [h] at hz
  apply (Padic.norm_le_one_iff_val_nonneg _).mpr
  omega

theorem unit_reduction (d : ℤ_[2]) (hd : ‖d‖ = 1) : PadicInt.toZModPow 1 d = 1 := by
  let : Nontrivial (ZMod (2^1)) := (inferInstance : Nontrivial (ZMod 2))
  have hu := ((PadicInt.isUnit_iff.mpr hd).map (PadicInt.toZModPow 1)).ne_zero
  exact (by decide : ∀ a : ZMod (2^1), a ≠ 0 → a=1) _ hu

theorem trace_reduction (t d : ℕ → ℚ_[2]) (unit : ∀ j, ‖d j‖ = 1)
    (cube : ∀ j, t j = t (j+1)^3 - 3*d (j+1)*t (j+1)) (j : ℕ) :
    PadicInt.toZModPow 1 ⟨t j, trace_integral t d unit cube j⟩ = 0 := by
  let T (i : ℕ) : ℤ_[2] := ⟨t i, trace_integral t d unit cube i⟩
  let D (i : ℕ) : ℤ_[2] := ⟨d i, le_of_eq (unit i)⟩
  have tc : T j = T (j+1)^3 - 3*D (j+1)*T (j+1) := Subtype.ext (cube j)
  change PadicInt.toZModPow 1 (T j) = 0
  rw [tc, map_sub, map_pow, map_mul, map_mul, map_ofNat,
    unit_reduction (D (j+1)) (unit (j+1))]
  exact (by decide : ∀ a : ZMod (2^1), a^3 - 3*1*a=0) _

theorem matrix_trace_cube (m : Matrix (Fin 2) (Fin 2) ℚ_[2]) :
    (m^3).trace = m.trace^3 - 3*m.det*m.trace := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem matrix_shift (m : Matrix (Fin 2) (Fin 2) ℚ_[2]) :
    (m-1).charpoly = C (1-m.trace+m.det) + C (2-m.trace)*X + X^2 := by
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two, map_add, map_sub]
  ring

theorem distinguished_of_cube_roots {V : Type*} [AddCommGroup V] [Module ℚ_[2] V]
    [FiniteDimensional ℚ_[2] V] (g : ℕ → Module.End ℚ_[2] V)
    (rank : Module.finrank ℚ_[2] V = 2) (cube : ∀ j, g (j+1)^3 = g j)
    (invertible : ∀ j, IsUnit (g j)) :
    ∃ c0 c1 : ℤ_[2], (g 0 - 1).charpoly = C (c0 : ℚ_[2]) + C (c1 : ℚ_[2])*X + X^2 ∧
      PadicInt.toZModPow 1 c0 = 0 ∧ PadicInt.toZModPow 1 c1 = 0 := by
  classical
  let B := Module.finBasisOfFinrankEq ℚ_[2] V rank
  let M (j : ℕ) := LinearMap.toMatrixAlgEquiv B (g j)
  have mc (j : ℕ) : M (j+1)^3 = M j := by
    dsimp [M]; rw [← map_pow, cube]
  let d (j : ℕ) := (M j).det
  let t (j : ℕ) := (M j).trace
  have nd (j : ℕ) : d j ≠ 0 :=
    (((invertible j).map (LinearMap.toMatrixAlgEquiv B)).map Matrix.detMonoidHom).ne_zero
  have dc (j : ℕ) : d (j+1)^3 = d j := by
    dsimp [d]; rw [← Matrix.det_pow, mc]
  have tc (j : ℕ) : t j = t (j+1)^3 - 3*d (j+1)*t (j+1) := by
    change (M j).trace = _
    rw [← mc j]; exact matrix_trace_cube _
  have du := determinant_norm d nd dc
  let D : ℤ_[2] := ⟨d 0, (du 0).le⟩
  let T : ℤ_[2] := ⟨t 0, trace_integral t d du tc 0⟩
  have rd : PadicInt.toZModPow 1 D = 1 := unit_reduction D (du 0)
  have rt : PadicInt.toZModPow 1 T = 0 := trace_reduction t d du tc 0
  refine ⟨1-T+D,2-T,?_,?_,?_⟩
  · rw [← LinearMap.charpoly_toMatrix (g 0 - 1) B]
    change (LinearMap.toMatrixAlgEquiv B (g 0 - 1)).charpoly = _
    rw [map_sub, map_one]
    exact matrix_shift (M 0)
  · rw [map_add, map_sub, map_one, rd, rt]
    decide
  · rw [map_sub, map_ofNat, rt]
    decide

end Reimann.SignedAdicDistinguished2893

