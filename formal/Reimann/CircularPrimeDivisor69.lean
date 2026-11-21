import Reimann.CircularEisenstein69

/-! The digits in the expansion in powers of X² + X + 1 over F₂₃. -/
namespace Reimann.CircularPrimeDivisor69

open Lean.Grind Reimann.CircularEisenstein69

abbrev F := Fin 23

/-- The two coordinates at level k in the quadratic-adic expansion. -/
def digit : List F → Nat → F × F
  | [], _ => (0,0)
  | c :: p, 0 => (c - (digit p 0).2, (digit p 0).1 - (digit p 0).2)
  | _ :: p, k+1 => ((digit p k).2 - (digit p (k+1)).2,
      (digit p (k+1)).1 - (digit p (k+1)).2)

theorem digit_zero_index (p : List F) : digit p 0 = omegaEval p := by
  induction p with
  | nil => rfl
  | cons c p ih => simp only [digit, omegaEval, ih]

theorem digit_padd (p q : List F) (k : Nat) : digit (padd p q) k =
    ((digit p k).1 + (digit q k).1, (digit p k).2 + (digit q k).2) := by
  induction p generalizing q k with
  | nil => simp [padd, digit]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, digit]
    | cons b q =>
      cases k <;> apply Prod.ext <;> simp only [padd, digit, ih] <;> grind only

theorem digit_scale (a : F) (p : List F) (k : Nat) :
    digit (p.map (fun c => a*c)) k = (a*(digit p k).1,a*(digit p k).2) := by
  induction p generalizing k with
  | nil => simp [digit] <;> grind only
  | cons c p ih =>
    cases k <;> apply Prod.ext <;> simp only [List.map_cons, digit, ih] <;> grind only

theorem digit_pmul_first (p q : List F) (k : Nat)
    (lower : ∀ j, j < k → digit q j = (0,0)) :
    digit (pmul p q) k = omegaMul (omegaEval p) (digit q k) := by
  induction p generalizing k with
  | nil =>
    apply Prod.ext <;> simp only [pmul, digit, omegaEval, omegaMul] <;> grind only
  | cons a p ih =>
    have same := ih k lower
    cases k with
    | zero =>
      apply Prod.ext <;> simp only [pmul, digit_padd, digit_scale, digit, same,
        omegaEval, omegaMul] <;> grind only
    | succ k =>
      have prev := ih k (fun j hj => lower j (by omega))
      rw [lower k (by omega)] at prev
      apply Prod.ext <;> simp only [pmul, digit_padd, digit_scale, digit, same, prev,
        omegaEval, omegaMul] <;> grind only

theorem digit_quadratic_mul (q : List F) (k : Nat) :
    digit (pmul [1,1,1] q) k = (match k with | 0 => (0,0) | j+1 => digit q j) := by
  cases k with
  | zero =>
    apply Prod.ext <;> simp only [pmul, digit_padd, digit_scale, digit] <;> grind only
  | succ k =>
    cases k <;> apply Prod.ext <;>
      simp only [pmul, digit_padd, digit_scale, digit] <;> grind only

theorem quadratic_power_lower_digits (n k : Nat) (hk : k < n) :
    digit (pPow [1,1,1] n) k = (0,0) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    rw [pPow, digit_quadratic_mul]
    cases k with
    | zero => rfl
    | succ j => exact ih j (by omega)

theorem unit_factor_lower_digits (p q : List F) (n : Nat)
    (hmul : pmul p q = pPow [1,1,1] n) (hp : omegaEval p ≠ (0,0))
    (k : Nat) (hk : k < n) : digit q k = (0,0) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have lower (j : Nat) (hj : j < k) := ih j hj (by omega)
    have prodzero := quadratic_power_lower_digits n k hk
    rw [← hmul, digit_pmul_first p q k lower] at prodzero
    exact (finite_pair_no_zero_divisors _ _ prodzero).resolve_left hp

theorem digit_above_and_at_degree (pre : List F) (a : F) :
    (∀ k, pre.length < 2*k → digit (pre ++ [a]) k = (0,0)) ∧
    (∀ k, pre.length = 2*k → digit (pre ++ [a]) k = (a,0)) ∧
    (∀ k, pre.length = 2*k+1 → (digit (pre ++ [a]) k).2 = a) := by
  induction pre with
  | nil =>
    constructor
    · intro k hk
      cases k with
      | zero => simp at hk
      | succ k => simp [digit] <;> grind only
    constructor
    · intro k hk
      simp only [List.length_nil] at hk
      have : k = 0 := by omega
      subst k
      simp [digit] <;> grind only
    · intro k hk
      simp at hk
  | cons c pre ih =>
    obtain ⟨higher, even, odd⟩ := ih
    simp only [List.length_cons, List.cons_append]
    constructor
    · intro k hk
      cases k with
      | zero => omega
      | succ j =>
        have top := higher (j+1) (by omega)
        have low : (digit (pre ++ [a]) j).2 = 0 := by
          by_cases h : pre.length = 2*j
          · rw [even j h]
          · rw [higher j (by omega)]
        simp only [digit, top, low]
        grind only
    constructor
    · intro k hk
      cases k with
      | zero => omega
      | succ j =>
        have top := higher (j+1) (by omega)
        have low := odd j (by omega)
        have sub_zero (z : F) : z - 0 = z := by grind only
        simp only [digit, top, low, sub_zero]
    · intro k hk
      have top := even k (by omega)
      cases k <;> simp only [digit, top] <;> grind only

theorem monic_top_digit_ne_zero (pre : List F) :
    digit (pre ++ [1]) (pre.length / 2) ≠ (0,0) := by
  obtain ⟨_, even, odd⟩ := digit_above_and_at_degree pre 1
  intro zero
  by_cases h : pre.length = 2*(pre.length / 2)
  · rw [even _ h] at zero
    contradiction
  · have last := odd (pre.length / 2) (by omega)
    rw [zero] at last
    contradiction

theorem positive_factor_vanishes (p qs : List F) (hq : qs.length < 44)
    (hmul : pmul p (qs ++ [1]) = pPow [1,1,1] 22) :
    omegaEval p = (0,0) := by
  apply Classical.byContradiction
  intro nonzero
  exact monic_top_digit_ne_zero qs
    (unit_factor_lower_digits p _ 22 hmul nonzero (qs.length / 2) (by omega))

end Reimann.CircularPrimeDivisor69
