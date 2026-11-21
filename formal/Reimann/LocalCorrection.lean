import Std

/-!
Arithmetic Window Integer, §3. The local formulas in §2 predict exponents
weight by weight. This file sums those exponents at the positive integer
weights 1 through s. Field identifications belong to the arithmetic input.
-/

namespace Reimann.LocalCorrection

/-- On positive n and p greater than one, count successive exact divisions by p. -/
def ord (p n : Nat) : Nat :=
  if h : 1 < p ∧ 0 < n ∧ p ∣ n then ord p (n / p) + 1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self h.2.1 h.1

theorem ord_of_not_dvd {p n : Nat} (hn : ¬ p ∣ n) : ord p n = 0 := by
  rw [ord, dite_eq_right (fun h => hn h.2.2)]

theorem ord_mul_base {p n : Nat} (hp : 1 < p) (hn : 0 < n) :
    ord p (p * n) = ord p n + 1 := by
  have h : 1 < p ∧ 0 < p*n ∧ p ∣ p*n :=
    ⟨hp, Nat.mul_pos (by omega) hn, ⟨n, rfl⟩⟩
  rw [ord, dite_eq_left h, Nat.mul_div_cancel_left _ (by omega)]

/-- Positive n is a power of p times a positive factor indivisible by p. -/
theorem ord_decomposition {p : Nat} (hp : 1 < p) (n : Nat) (hn : 0 < n) :
    ∃ u, 0 < u ∧ ¬ p ∣ u ∧ n = p ^ ord p n * u := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hd : p ∣ n
    · obtain ⟨m, hm⟩ := hd
      have hmpos : 0 < m := by
        cases m with
        | zero => simp_all
        | succ k => omega
      have hlt : m < n := by
        rw [hm]
        have h := Nat.mul_lt_mul_of_pos_right hp hmpos
        simpa using h
      obtain ⟨u, hu, hunit, huEq⟩ := ih m hlt hmpos
      refine ⟨u, hu, hunit, ?_⟩
      rw [hm, ord_mul_base hp hmpos, Nat.pow_succ, Nat.mul_right_comm]
      rw [Nat.mul_comm p m]
      exact congrArg (fun z => z*p) huEq
    · exact ⟨n, hn, hd, by rw [ord_of_not_dvd hd, Nat.pow_zero, Nat.one_mul]⟩

/-- A displayed power with primitive positive cofactor gives the exact valuation. -/
theorem ord_pow_mul {p u : Nat} (hp : 1 < p) (hu : 0 < u) (hunit : ¬ p ∣ u) (j : Nat) :
    ord p (p^j*u) = j := by
  induction j with
  | zero => simpa using ord_of_not_dvd hunit
  | succ j ih =>
    have hpos : 0 < p^j*u := Nat.mul_pos (Nat.pow_pos (by omega)) hu
    rw [Nat.pow_succ, Nat.mul_comm (p^j) p, Nat.mul_assoc, ord_mul_base hp hpos, ih]

/-- The prime divisor property is the only prime-specific input in multiplicativity. -/
theorem ord_mul {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) {x y : Nat} (hx : 0 < x) (hy : 0 < y) :
    ord p (x*y) = ord p x + ord p y := by
  obtain ⟨u, hu, hu', hxu⟩ := ord_decomposition hp x hx
  obtain ⟨v, hv, hv', hyv⟩ := ord_decomposition hp y hy
  have h : x*y = p^(ord p x + ord p y)*(u*v) := by
    rw [Nat.pow_add, Nat.mul_mul_mul_comm (p^ord p x) _ u v, ← hxu, ← hyv]
  have hunit : ¬ p ∣ u*v := fun h => (prime u v h).elim hu' hv'
  rw [h, ord_pow_mul hp (Nat.mul_pos hu hv) hunit]

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem two_prime_divisor (a b : Nat) (h : 2 ∣ a*b) : 2 ∣ a ∨ 2 ∣ b := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod] at h
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  by_cases ha : a % 2 = 0
  · exact Or.inl ha
  · have ha' : a % 2 = 1 := by omega
    rw [ha', Nat.one_mul, Nat.mod_mod] at h
    exact Or.inr h

theorem ord_factorial_succ {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) (n : Nat) :
    ord p (factorial (n+1)) = ord p (n+1) + ord p (factorial n) :=
  ord_mul hp prime (Nat.zero_lt_succ n) (factorial_pos n)

/-- Sum over the positive weights 1,...,s. The empty interval has sum zero. -/
def weightSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => weightSum f n + f (n+1)

theorem sum_add_constant (c s : Nat) (f : Nat → Nat) :
    weightSum (fun r => c + f r) s = c*s + weightSum f s := by
  induction s with
  | zero => simp [weightSum]
  | succ s ih => simp only [weightSum, ih, Nat.mul_succ]; omega

/-- The progression d,2d,... contributes exactly the first floor(s/d) inputs. -/
theorem sum_multiples (d s : Nat) (f : Nat → Nat) :
    weightSum (fun r => if d ∣ r then f (r/d) else 0) s = weightSum f (s/d) := by
  induction s with
  | zero => simp [weightSum]
  | succ s ih =>
    by_cases h : d ∣ s+1
    · rw [weightSum, ih, ite_eq_left h, Nat.succ_div_of_dvd h, weightSum]
    · rw [weightSum, ih, ite_eq_right h, Nat.succ_div_of_not_dvd h, Nat.add_zero]

theorem sum_ord_factorial {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) (s : Nat) :
    weightSum (ord p) s = ord p (factorial s) := by
  induction s with
  | zero =>
    have h : ¬ p ∣ 1 := fun hd => by have := Nat.le_of_dvd (by decide) hd; omega
    simp only [weightSum, factorial, ord_of_not_dvd h]
  | succ s ih =>
    rw [weightSum, ih, ord_factorial_succ hp prime, Nat.add_comm]

theorem weightSum_congr {f g : Nat → Nat} (h : ∀ r, 0 < r → f r = g r) (s : Nat) :
    weightSum f s = weightSum g s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [weightSum, weightSum, ih, h _ (Nat.zero_lt_succ s)]

/-- The exponent of the local correction at 2 specified in §2, with two dyadic places. -/
def dyadicWeight (a r : Nat) : Nat := if 2 ∣ r then a+2+ord 2 r else 1

theorem dyadicWeight_split (a r : Nat) (hr : 0 < r) :
    dyadicWeight a r = 1 + (if 2 ∣ r then a+2+ord 2 (r/2) else 0) := by
  by_cases hd : 2 ∣ r
  · have heq : 2*(r/2) = r := Nat.mul_div_cancel_left' hd
    have hv := ord_mul_base (p := 2) (n := r/2) (by decide) (by omega)
    rw [heq] at hv
    simp only [dyadicWeight, ite_eq_left hd, hv]
    omega
  · simp [dyadicWeight, hd]

/-- Closed dyadic exponent through the last included weight s. -/
theorem dyadic_factorial_correction (a s : Nat) :
    weightSum (dyadicWeight a) s =
      s + (a+2)*(s/2) + ord 2 (factorial (s/2)) := by
  rw [weightSum_congr (dyadicWeight_split a), sum_add_constant,
      sum_multiples 2 s (fun j => a+2+ord 2 j), sum_add_constant,
      sum_ord_factorial (by decide : 1 < 2) two_prime_divisor, Nat.one_mul]
  omega

theorem ord_pred {p : Nat} (hp : 1 < p) : ord p (p-1) = 0 := by
  apply ord_of_not_dvd
  intro hd
  have hle := Nat.le_of_dvd (show 0 < p-1 by omega) hd
  omega

/-- At an unramified odd prime, this exponent precedes multiplication by g_p-1. -/
def tameWeight (p r : Nat) : Nat := if p-1 ∣ r then 1+ord p r else 0

theorem tameWeight_progression {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) (r : Nat) (hr : 0 < r) :
    tameWeight p r = if p-1 ∣ r then 1+ord p (r/(p-1)) else 0 := by
  by_cases hd : p-1 ∣ r
  · have heq : (p-1)*(r/(p-1)) = r := Nat.mul_div_cancel_left' hd
    have hm : 0 < r/(p-1) := by
      by_cases h : r/(p-1) = 0
      · rw [h, Nat.mul_zero] at heq
        omega
      · exact Nat.pos_of_ne_zero h
    have hv := ord_mul hp prime (show 0 < p-1 by omega) hm
    rw [heq, ord_pred hp, Nat.zero_add] at hv
    simp only [tameWeight, ite_eq_left hd, hv]
  · simp [tameWeight, hd]

/-- The complete sum at an unramified odd prime before its place multiplicity. -/
theorem tame_factorial_correction {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) (s : Nat) :
    weightSum (tameWeight p) s = s/(p-1) + ord p (factorial (s/(p-1))) := by
  rw [weightSum_congr (tameWeight_progression hp prime),
      sum_multiples (p-1) s (fun j => 1+ord p j), sum_add_constant,
      sum_ord_factorial hp prime, Nat.one_mul]

theorem sum_scale (k s : Nat) (f : Nat → Nat) :
    weightSum (fun r => k*f r) s = k*weightSum f s := by
  induction s with
  | zero => simp [weightSum]
  | succ s ih => simp only [weightSum, ih, Nat.mul_add]

theorem tame_place_correction {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) (places s : Nat) :
    weightSum (fun r => (places-1)*tameWeight p r) s =
      (places-1)*(s/(p-1) + ord p (factorial (s/(p-1)))) := by
  rw [sum_scale, tame_factorial_correction hp prime]

/-- At a=1, t=4, with g_3=4, the denominator specified by the local rows is 1728. -/
theorem example_denominator :
    2^(weightSum (dyadicWeight 1) 3) *
      3^(weightSum (fun r => (4-1)*tameWeight 3 r) 3) = 1728 := by
  decide +kernel

theorem ord_split_multiples {p n : Nat} (hp : 1 < p) (hn : 0 < n) :
    ord p n = if p ∣ n then 1+ord p (n/p) else 0 := by
  by_cases hd : p ∣ n
  · have heq := Nat.mul_div_cancel_left' hd
    have hm : 0 < n/p := by
      apply Nat.pos_of_ne_zero
      intro h
      rw [h, Nat.mul_zero] at heq
      omega
    have hv := ord_mul_base hp hm
    rw [heq] at hv
    rw [ite_eq_left hd, hv, Nat.add_comm]
  · rw [ite_eq_right hd, ord_of_not_dvd hd]

/-- Legendre's recurrence counts one p from each multiple of p, then recurses. -/
theorem ord_factorial_div {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) (s : Nat) :
    ord p (factorial s) = s/p + ord p (factorial (s/p)) := by
  rw [← sum_ord_factorial hp prime s, weightSum_congr (fun r hr => ord_split_multiples hp hr),
      sum_multiples p s (fun j => 1+ord p j), sum_add_constant, Nat.one_mul,
      sum_ord_factorial hp prime]

/-- The elementary uniform valuation bound used in the size estimate for D(E,t). -/
theorem ord_factorial_bound {p : Nat} (hp : 1 < p)
    (prime : ∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b) (s : Nat) :
    ord p (factorial s) ≤ s/(p-1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < p-1)).mpr
  induction s using Nat.strongRecOn with
  | ind s ih =>
    by_cases h : 0 < s
    · have hi := ih (s/p) (Nat.div_lt_self h hp)
      have hsum : (p-1).succ = p := by omega
      calc
        ord p (factorial s) * (p-1) =
            (s/p)*(p-1) + ord p (factorial (s/p))*(p-1) := by
              rw [ord_factorial_div hp prime s, Nat.add_mul]
        _ ≤ (s/p)*(p-1) + s/p := Nat.add_le_add_left hi _
        _ = (s/p)*p := by rw [← Nat.mul_succ, hsum]
        _ ≤ s := Nat.div_mul_le_self s p
    · have hs : s = 0 := by omega
      have hunit : ¬ p ∣ 1 := fun hd => by have := Nat.le_of_dvd (by decide) hd; omega
      simp [hs, factorial, ord_of_not_dvd hunit]

theorem tame_zero_above_window {p s r : Nat} (hr : 0 < r) (hrs : r ≤ s) (hp : s+1 < p) :
    tameWeight p r = 0 := by
  have hnot : ¬ p-1 ∣ r := by
    intro hd
    have := Nat.le_of_dvd hr hd
    omega
  simp [tameWeight, hnot]

/-- Ramified odd primes with tame index two also disappear if their half-period exceeds s. -/
theorem ramified_half_period_excluded {p s r : Nat}
    (hr : 0 < r) (hrs : r ≤ s) (hp : 2*(s+1)+1 < p) : ¬ (p-1)/2 ∣ r := by
  intro hd
  have := Nat.le_of_dvd hr hd
  omega

end Reimann.LocalCorrection
