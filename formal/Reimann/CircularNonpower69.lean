import Std

/-! A modular Fermat witness for the two conductor-69 residues.  The
Euclidean descent below reduces all 114678 units to a table at the
square-root bound. -/

namespace Reimann.CircularNonpower69

set_option maxRecDepth 8000
set_option maxHeartbeats 1500000

/-- A binary exponent, with the units bit first. -/
def binaryExponent : List Bool → Nat
  | [] => 0
  | b :: bs => binaryExponent bs + binaryExponent bs + (if b then 1 else 0)

def binaryResidue (v : Nat) : List Bool → Nat
  | [] => 1
  | b :: bs =>
    let r := binaryResidue v bs
    if b then ((r * r % 114679) * v) % 114679 else r * r % 114679

theorem binaryResidue_correct (v : Nat) (bits : List Bool) :
    binaryResidue v bits = v ^ binaryExponent bits % 114679 := by
  induction bits with
  | nil => simp [binaryResidue, binaryExponent]
  | cons b bs ih =>
    cases b <;> simp only [binaryExponent, binaryResidue, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero, Nat.pow_succ, Nat.pow_add, ih,
      Nat.mod_mul_mod, Nat.mul_mod_mod]

def fermatBits : List Bool :=
  [false, true, true, false, true, true, true, true, true, true, true,
   true, true, true, false, true, true]

theorem fermat_exponent : binaryExponent fermatBits = 114678 := by decide

theorem small_fermat_table :
    (List.range 339).all (fun i => binaryResidue (i + 1) fermatBits == 1) = true := by
  decide +kernel

theorem small_fermat (v : Nat) (hpos : 0 < v) (hsmall : v ≤ 339) :
    v^114678 % 114679 = 1 := by
  have hmem : v-1 ∈ List.range 339 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp small_fermat_table (v-1) hmem
  have hval : binaryResidue (v-1+1) fermatBits = 1 := beq_iff_eq.mp h
  rw [show v-1+1 = v by omega, binaryResidue_correct, fermat_exponent] at hval
  exact hval

theorem small_nondivisor : ∀ d : Fin 340, 2 ≤ d.val → 114679 % d.val ≠ 0 := by
  decide +kernel

theorem quotient_bound (v : Nat) (large : 339 < v) :
    114679 / v + 1 ≤ 339 := by
  have h : 114679 / v < 339 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  omega

theorem remainder_positive (v : Nat) (large : 339 < v) (below : v < 114679) :
    0 < 114679 % v := by
  have hdiv := Nat.div_add_mod 114679 v
  have hq := quotient_bound v large
  have hp : 0 < 114679 / v := Nat.div_pos (by omega) (by omega)
  apply Nat.pos_of_ne_zero
  intro hz
  have he : v * (114679 / v) = 114679 := by omega
  have htwo : 2 ≤ 114679 / v := by
    by_cases h1 : 114679 / v = 1
    · rw [h1, Nat.mul_one] at he
      omega
    · omega
  have hmod : 114679 % (114679 / v) = 0 := by
    exact Nat.mod_eq_zero_of_dvd ⟨v, by rw [Nat.mul_comm]; exact he.symm⟩
  exact small_nondivisor ⟨114679 / v, by omega⟩ htwo hmod

theorem descent_remainder_bounds (v : Nat) (large : 339 < v) (below : v < 114679) :
    0 < v - 114679 % v ∧ v - 114679 % v < v := by
  have h := remainder_positive v large below
  have hl := Nat.mod_lt 114679 (show v > 0 by omega)
  omega

theorem descent_product (v : Nat) (large : 339 < v) :
    v * (114679 / v + 1) = 114679 + (v - 114679 % v) := by
  have h := Nat.div_add_mod 114679 v
  have hl := Nat.mod_lt 114679 (show v > 0 by omega)
  rw [Nat.mul_succ]
  omega

theorem descend_fermat (v q r n : Nat) (hprod : v * q = 114679 + r)
    (hq : q^n % 114679 = 1) (hr : r^n % 114679 = 1) :
    v^n % 114679 = 1 := by
  calc
    v^n % 114679 = (v^n * (q^n % 114679)) % 114679 := by
      rw [hq, Nat.mul_one]
    _ = (v*q)^n % 114679 := by rw [Nat.mul_mod_mod, Nat.mul_pow]
    _ = r^n % 114679 := by
      rw [hprod, Nat.pow_mod (114679 + r), Nat.add_mod_left, ← Nat.pow_mod]
    _ = 1 := hr

set_option exponentiation.threshold 114678
theorem fermat_for_nonzero (v : Nat) (hpos : 0 < v) (below : v < 114679) :
    v^114678 % 114679 = 1 := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hsmall : v ≤ 339
    · exact small_fermat v hpos hsmall
    · have large : 339 < v := by omega
      have hb := descent_remainder_bounds v large below
      exact descend_fermat v (114679 / v + 1) (v - 114679 % v) 114678
        (descent_product v large)
        (small_fermat (114679 / v + 1) (Nat.succ_pos _) (quotient_bound v large))
        (ih _ hb.2 hb.1 (Nat.lt_trans hb.2 below))

theorem projected_power_is_one (v : Nat) (nonzero : v % 114679 ≠ 0) :
    ((v^277 % 114679)^414) % 114679 = 1 := by
  have h := fermat_for_nonzero (v % 114679) (Nat.pos_of_ne_zero nonzero)
    (Nat.mod_lt _ (by decide))
  calc
    _ = (v^277)^414 % 114679 := (Nat.pow_mod ..).symm
    _ = v^(277*414) % 114679 := by rw [Nat.pow_mul]
    _ = (v % 114679)^114678 % 114679 := Nat.pow_mod v 114678 114679
    _ = 1 := h

theorem signed_projections :
    48891^414 % 114679 = 74194 ∧ 65813^414 % 114679 = 5365 := by
  decide +kernel

theorem signed_nonpowers_nat (v : Nat) :
    v^277 % 114679 ≠ 48891 ∧ v^277 % 114679 ≠ 65813 := by
  by_cases h0 : v % 114679 = 0
  · rw [Nat.pow_mod, h0]
    decide +kernel
  · have h := projected_power_is_one v h0
    constructor
    · intro eqn
      rw [eqn, signed_projections.1] at h
      contradiction
    · intro eqn
      rw [eqn, signed_projections.2] at h
      contradiction

theorem fin_power_residue (y : Fin 114679) (n : Nat) :
    (y^n).val = y.val^n % 114679 := by
  induction n with
  | zero => rw [Lean.Grind.Semiring.pow_zero, Nat.pow_zero]; decide
  | succ n ih =>
    rw [Lean.Grind.Semiring.pow_succ, Fin.val_mul, ih, Nat.mod_mul_mod, Nat.pow_succ]

theorem signed_nonpowers (y : Fin 114679) :
    y^277 ≠ 48891 ∧ y^277 ≠ 65813 := by
  obtain ⟨hp, hn⟩ := signed_nonpowers_nat y.val
  constructor
  · intro h
    apply hp
    rw [← fin_power_residue, h]
    rfl
  · intro h
    apply hn
    rw [← fin_power_residue, h]
    rfl

end Reimann.CircularNonpower69
