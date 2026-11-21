import Reimann.CircularAmbient69
import Reimann.CircularBasis69
import Reimann.CircularKernel69

/-! Finite geometric sums exhaust the 69th roots and recover their
unique power label in a characteristic-zero field. -/
namespace Reimann.CircularRootOrbit69

open Lean.Grind CircularAmbient69 CircularBasis69 CircularKernel69

theorem order_witnesses : ∀ a : Fin 69, a.val ≠ 0 → ∃ t : Fin 69,
    (a.val * t.val) % 69 = 3 ∨ (a.val * t.val) % 69 = 23 := by
  decide +kernel

theorem nonzero_power_ne_one {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (a : Fin 69) (ha : a.val ≠ 0) : x^a.val ≠ 1 := by
  intro hp
  obtain ⟨t, ht⟩ := order_witnesses a ha
  have he := congrArg (fun v : R => v^t.val) hp
  change (x^a.val)^t.val = (1:R)^t.val at he
  rw [power_of_power, power_period x h69, Semiring.one_pow] at he
  rcases ht with h | h
  · exact h3 (h ▸ he)
  · exact h23 (h ▸ he)

theorem power_injective {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (a b : Fin 69) : x^a.val = x^b.val → a = b := by
  have ordered (c d : Fin 69) (hle : c.val ≤ d.val) (he : x^c.val = x^d.val) : c = d := by
    have hprod := congrArg (fun v : R => v*x^(69-c.val)) he
    change x^c.val * x^(69-c.val) = x^d.val * x^(69-c.val) at hprod
    have hr : d.val + (69-c.val) = (d.val-c.val) + 69 := by omega
    have hl : c.val + (69-c.val) = 69 := by omega
    rw [← Semiring.pow_add, ← Semiring.pow_add, hl, hr, Semiring.pow_add, h69,
      Semiring.mul_one] at hprod
    by_cases hcd : c.val = d.val
    · exact Fin.ext hcd
    · exact False.elim (nonzero_power_ne_one x h69 h23 h3 ⟨d.val-c.val, by omega⟩
        (by change d.val-c.val ≠ 0; omega) hprod.symm)
  intro h
  by_cases hab : a.val ≤ b.val
  · exact ordered a b hab h
  · exact (ordered b a (by omega) h.symm).symm

theorem nonunit_power_witness : ∀ a : Fin 69, Nat.gcd a.val 69 ≠ 1 →
    (a.val * 23) % 69 = 0 ∨ (a.val * 3) % 69 = 0 := by decide +kernel

theorem primitive_exponent_is_unit {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (a : Fin 69) (hy23 : (x^a.val)^23 ≠ 1) (hy3 : (x^a.val)^3 ≠ 1) :
    Nat.gcd a.val 69 = 1 := by
  apply Classical.byContradiction
  intro hn
  rcases nonunit_power_witness a hn with h | h
  · apply hy23
    rw [power_of_power, power_period x h69, h, Semiring.pow_zero]
  · apply hy3
    rw [power_of_power, power_period x h69, h, Semiring.pow_zero]

theorem geometric_eq_basisSum {R : Type} [CommRing R] (z : R) (n : Nat) :
    geometric z n = basisSum (fun k : Fin n => z^k.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [geometric, basisSum_succ, ih]
    simp only [Fin.val_zero, Semiring.pow_zero, Fin.val_succ, Semiring.pow_succ]
    rw [basisSum_mul_right]
    grind only

theorem root_geometric_zero {R : Type} [Field R] (z : R) (hz : z^69 = 1) (hne : z ≠ 1) :
    basisSum (fun k : Fin 69 => z^k.val) = 0 := by
  rw [← geometric_eq_basisSum]
  have he := geometric_identity z 69
  rw [hz] at he
  have hp : (z-1) * geometric z 69 = 0 := by rw [he]; grind only
  exact (Field.of_mul_eq_zero hp).resolve_left (fun h => hne (by grind only))

theorem power_root {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1) (a : Nat) :
    (x^a)^69 = 1 := by
  rw [power_of_power, Nat.mul_comm, ← power_of_power, h69, Semiring.one_pow]

theorem product_root {R : Type} [CommRing R] (x y : R) (hx : x^69 = 1) (hy : y^69 = 1)
    (a : Nat) : (y * x^a)^69 = 1 := by
  rw [CommSemiring.mul_pow, hy, power_root x hx a, Semiring.one_mul]

theorem power_of_product_one {R : Type} [CommRing R] (x y : R) (hx : x^69 = 1)
    (a : Fin 69) (h : y*x^a.val = 1) : y = x^((69-a.val)%69) := by
  calc
    y = y * (x^a.val * x^(69-a.val)) := by
      rw [← Semiring.pow_add, show a.val+(69-a.val) = 69 by omega, hx, Semiring.mul_one]
    _ = x^(69-a.val) := by rw [← Semiring.mul_assoc, h, Semiring.one_mul]
    _ = _ := power_period x hx _

theorem sum_ones {R : Type} [CommRing R] (n : Nat) :
    basisSum (fun _ : Fin n => (1:R)) = @Nat.cast R Semiring.natCast n := by
  induction n with
  | zero => exact Semiring.natCast_zero.symm
  | succ n ih => rw [basisSum_succ, ih, Semiring.natCast_succ]; grind only

theorem swap_power_exponents {R : Type} [CommRing R] (x y : R) (a k : Nat) :
    (y*x^a)^k = y^k * (x^k)^a := by
  rw [CommSemiring.mul_pow, power_of_power, power_of_power, Nat.mul_comm a k]

theorem frequency_sum {R : Type} [Field R] (x y : R) (hx : x^69 = 1)
    (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (k : Fin 69) :
    basisSum (fun a : Fin 69 => (y*x^a.val)^k.val) =
      if (0 : Fin 69) = k then (69:R) else 0 := by
  by_cases h : k = 0
  · subst k
    simp only [Fin.val_zero, Semiring.pow_zero, ite_true, sum_ones]
    grind only
  · simp only [Ne.symm h, ite_false]
    have hz := root_geometric_zero (x^k.val) (power_root x hx k.val)
      (nonzero_power_ne_one x hx h23 h3 k (fun e => h (Fin.ext e)))
    simp only [swap_power_exponents, basisSum_mul_left, hz, Semiring.mul_zero]

theorem all_frequency_sum {R : Type} [Field R] (x y : R) (hx : x^69 = 1)
    (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    basisSum (fun k : Fin 69 => basisSum (fun a : Fin 69 => (y*x^a.val)^k.val)) = 69 := by
  simp only [frequency_sum x y hx h23 h3]
  exact basisSum_single (0 : Fin 69) (fun _ => (69:R))

theorem root_exhaustion {R : Type} [Field R] [IsCharP R 0] (x y : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hy : y^69 = 1) :
    ∃ a : Fin 69, y = x^a.val := by
  apply Classical.byContradiction
  intro absent
  have row (a : Fin 69) : basisSum (fun k : Fin 69 => (y*x^a.val)^k.val) = 0 := by
    apply root_geometric_zero _ (product_root x y h69 hy a.val)
    intro hone
    exact absent ⟨⟨(69-a.val)%69, Nat.mod_lt _ (by decide)⟩, power_of_product_one x y h69 a hone⟩
  have swapped := basisSum_swap (fun (a k : Fin 69) => (y*x^a.val)^k.val)
  simp only [row, basisSum_zero, all_frequency_sum x y h69 h23 h3] at swapped
  have bad := (IsCharP.ofNat_eq_zero_iff 0 69).mp swapped.symm
  exact (by decide : ¬ (69 : Nat) % 0 = 0) bad

theorem root_label_unique {R : Type} [Field R] [IsCharP R 0] (x y : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hy : y^69 = 1) :
    ∃ a : Fin 69, y = x^a.val ∧ ∀ b : Fin 69, y = x^b.val → b = a := by
  obtain ⟨a, ha⟩ := root_exhaustion x y h69 h23 h3 hy
  exact ⟨a, ha, fun b hb => power_injective x h69 h23 h3 b a (hb.symm.trans ha)⟩

theorem primitive_root_label {R : Type} [Field R] [IsCharP R 0] (x y : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (hy69 : y^69 = 1) (hy23 : y^23 ≠ 1) (hy3 : y^3 ≠ 1) :
    ∃ a : Fin 69, y = x^a.val ∧ Nat.gcd a.val 69 = 1 ∧
      ∀ b : Fin 69, y = x^b.val → b = a := by
  obtain ⟨a, ha, hu⟩ := root_label_unique x y h69 h23 h3 hy69
  exact ⟨a, ha, primitive_exponent_is_unit x h69 a (ha ▸ hy23) (ha ▸ hy3), hu⟩

end Reimann.CircularRootOrbit69
