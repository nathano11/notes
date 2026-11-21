import Reimann.CircularRootOrbit69
import Reimann.CircularConjugateRadicals69

/-! The powers of any nontrivial 277th root exhaust all the 277th roots
in the common characteristic-zero field. -/
namespace Reimann.CommonRootPowers69

open Lean.Grind CircularAmbient69 CircularBasis69 CircularKernel69 CircularRealUnit69
open CircularRootOrbit69 (geometric_eq_basisSum sum_ones swap_power_exponents)

variable {R : Type} [Field R]

theorem power_mod_order (x : R) (n : Nat) (hn : x^n = 1) (e : Nat) :
    x^e = x^(e % n) := by
  calc
    x^e = x^(n*(e/n)+e%n) := congrArg (fun k : Nat => x^k) (Nat.div_add_mod e n).symm
    _ = _ := by rw [Semiring.pow_add, ← power_of_power, hn, Semiring.one_pow, Semiring.one_mul]

theorem inverse_exponents : ∀ a : Fin 277, a.val ≠ 0 → ∃ t : Fin 277,
    (a.val * t.val) % 277 = 1 := by
  set_option maxRecDepth 4096 in decide +kernel

theorem nonzero_frequency (z : R) (hz : z^277 = 1) (hnt : z ≠ 1)
    (a : Fin 277) (ha : a.val ≠ 0) : z^a.val ≠ 1 := by
  intro hp
  obtain ⟨t, ht⟩ := inverse_exponents a ha
  have e := congrArg (fun y : R => y^t.val) hp
  change (z^a.val)^t.val = (1 : R)^t.val at e
  rw [power_of_power, power_mod_order z 277 hz, ht, Semiring.pow_one, Semiring.one_pow] at e
  exact hnt e

theorem power_root (x : R) (n : Nat) (h : x^n = 1) (a : Nat) : (x^a)^n = 1 := by
  rw [power_of_power, Nat.mul_comm, ← power_of_power, h, Semiring.one_pow]

theorem twisted_root (z w : R) (n : Nat) (hz : z^n = 1) (hw : w^n = 1) (a : Nat) :
    (w*z^a)^n = 1 := by
  rw [CommSemiring.mul_pow, hw, power_root z n hz a, Semiring.one_mul]

theorem geometric_vanishes (u : R) (n : Nat) (hu : u^n = 1) (hnt : u ≠ 1) :
    basisSum (fun k : Fin n => u^k.val) = 0 := by
  rw [← geometric_eq_basisSum]
  have he := geometric_identity u n
  rw [hu] at he
  have hp : (u-1) * geometric u n = 0 := by rw [he]; grind only
  exact (Field.of_mul_eq_zero hp).resolve_left (fun h => hnt (by grind only))

theorem complementary_power (z w : R) (hz : z^277 = 1) (a : Fin 277)
    (h : w*z^a.val = 1) : z^((277-a.val)%277) = w := by
  calc
    z^((277-a.val)%277) = z^(277-a.val) := (power_mod_order z 277 hz _).symm
    _ = w * (z^a.val * z^(277-a.val)) := by
      rw [← Semiring.mul_assoc, h, Semiring.one_mul]
    _ = w := by rw [← Semiring.pow_add, show a.val+(277-a.val) = 277 by omega, hz, Semiring.mul_one]

theorem frequency_sum (z w : R) (hz : z^277 = 1) (hnt : z ≠ 1) (k : Fin 277) :
    basisSum (fun a : Fin 277 => (w*z^a.val)^k.val) =
      if (0 : Fin 277) = k then (277 : R) else 0 := by
  by_cases h : k = 0
  · subst k
    simp only [Fin.val_zero, Semiring.pow_zero, ite_true, sum_ones]
    grind only
  · simp only [Ne.symm h, ite_false]
    have hv := geometric_vanishes (z^k.val) 277 (power_root z 277 hz k.val)
      (nonzero_frequency z hz hnt k (fun e => h (Fin.ext e)))
    simp only [swap_power_exponents, basisSum_mul_left, hv, Semiring.mul_zero]

theorem all_frequencies (z w : R) (hz : z^277 = 1) (hnt : z ≠ 1) :
    basisSum (fun k : Fin 277 => basisSum (fun a : Fin 277 => (w*z^a.val)^k.val)) = 277 := by
  simp only [frequency_sum z w hz hnt]
  exact basisSum_single (0 : Fin 277) (fun _ => (277 : R))

theorem root_is_power [IsCharP R 0] {z w : R} (hz : z^277 = 1) (hnt : z ≠ 1) (hw : w^277 = 1) :
    ∃ a : Nat, a < 277 ∧ z^a = w := by
  apply Classical.byContradiction
  intro absent
  have row (a : Fin 277) : basisSum (fun k : Fin 277 => (w*z^a.val)^k.val) = 0 := by
    apply geometric_vanishes _ 277 (twisted_root z w 277 hz hw a.val)
    intro hone
    exact absent ⟨(277-a.val)%277, Nat.mod_lt _ (by decide), complementary_power z w hz a hone⟩
  have swapped := basisSum_swap (fun (a k : Fin 277) => (w*z^a.val)^k.val)
  simp only [row, basisSum_zero, all_frequencies z w hz hnt] at swapped
  have bad := (IsCharP.ofNat_eq_zero_iff 0 277).mp swapped.symm
  exact (by decide : ¬ (277 : Nat) % 0 = 0) bad

theorem inverts_all_roots [IsCharP R 0] (c : Conjugation R) {z : R}
    (hz : z^277 = 1) (hnt : z ≠ 1) (hc : c.app z = z⁻¹) :
    ∀ w : R, w^277 = 1 → c.app w = w⁻¹ := by
  intro w hw
  obtain ⟨a, _, rfl⟩ := root_is_power hz hnt hw
  rw [map_power, hc, Field.inv_pow]

end Reimann.CommonRootPowers69
