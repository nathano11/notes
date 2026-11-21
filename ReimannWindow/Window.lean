import Std

namespace ReimannWindow

/-- For cyclic factors of orders `p^e`, truncation at `p^k` retains `min k e`
    powers of `p` in the factor of length `e`. -/
def truncatedLength (k : Nat) (exponents : List Nat) : Nat :=
  (exponents.map (fun e => min k e)).sum

theorem truncatedLength_le (k : Nat) (exponents : List Nat) :
    truncatedLength k exponents ≤ exponents.length * k := by
  induction exponents with
  | nil => simp [truncatedLength]
  | cons e es ih =>
    change min k e + truncatedLength k es ≤ (es.length + 1) * k
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (es.length * k) k]
    exact Nat.add_le_add (Nat.min_le_left k e) ih

/-- The integer depth allocated to a positive index `p` from budget `B`. -/
def depth (B p : Nat) : Nat := B / (p * p)

/-- A depth `k` fits exactly when its squared-index cost fits. -/
theorem depth_iff (B p k : Nat) (hp : 0 < p) :
    k ≤ depth B p ↔ k * (p * p) ≤ B :=
  Nat.le_div_iff_mul_le (Nat.mul_pos hp hp)

/-- After multiplying by the index, the allocated depth costs at most `B / p`. -/
theorem depth_cost_le (B p : Nat) : depth B p * p ≤ B / p := by
  unfold depth
  rw [← Nat.div_div_eq_div_mul]
  exact Nat.div_mul_le_self (B / p) p

/-- Sum `f` on the half-open interval `[start, start + len)`. -/
def intervalSum (f : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => intervalSum f start n + f (start + n)

theorem intervalSum_split (f : Nat → Nat) (start left right : Nat) :
    intervalSum f start (left + right) =
      intervalSum f start left + intervalSum f (start + left) right := by
  induction right with
  | zero => simp [intervalSum]
  | succ right ih => simp [intervalSum, ih, Nat.add_assoc]

private theorem intervalSum_le (B : Nat) (f : Nat → Nat)
    (hf : ∀ p, f p ≤ depth B p * p) (start len : Nat) (hs : 0 < start) :
    intervalSum f start len ≤ len * (B / start) := by
  induction len with
  | zero => simp [intervalSum]
  | succ n ih =>
    have h : f (start + n) ≤ B / start :=
      Nat.le_trans (hf (start + n)) (Nat.le_trans (depth_cost_le B (start + n))
        (Nat.div_le_div_left (by omega) hs))
    simpa [intervalSum, Nat.succ_mul] using Nat.add_le_add ih h

/-- Every interval `[s, 2s)` costs at most one budget unit. -/
theorem dyadic_block_le (B : Nat) (f : Nat → Nat) (hf : ∀ p, f p ≤ depth B p * p)
    (s : Nat) (hs : 0 < s) : intervalSum f s s ≤ B := by
  have h := intervalSum_le B f hf s s hs
  exact Nat.le_trans h (by simpa [Nat.mul_comm] using Nat.div_mul_le_self B s)

/-- The total below `2^j` costs at most `j * B`. A prime sum is obtained by
    taking `f` to be zero off the selected primes. -/
theorem window_cost_le (B : Nat) (f : Nat → Nat) (hf : ∀ p, f p ≤ depth B p * p)
    (j : Nat) : intervalSum f 0 (2 ^ j) ≤ j * B := by
  induction j with
  | zero =>
    have h0 := hf 0
    simpa [intervalSum] using h0
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_two, intervalSum_split, Nat.zero_add, Nat.succ_mul]
    exact Nat.add_le_add ih (dyadic_block_le B f hf (2 ^ j) (Nat.pow_pos (by decide)))

end ReimannWindow
