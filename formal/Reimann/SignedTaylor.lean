import Reimann.CoinvariantSupport
import Reimann.SignedProjection

/-! Integral Taylor coefficients of the group-polynomial rows of a
compatible measure. All divisibility estimates are uniform in the row. -/
namespace Reimann.SignedTaylor

open Reimann.CoinvariantSupport (binomial binomial_marked binomial_zero_column)
open Reimann.SignedProjection (total total_append)

/-- The odd part of the binomial column index cancels from every 2-power. -/
theorem cancel_odd {k y : Nat} (p : Nat) (hk : k%2=1) (h : 2^p ∣ k*y) : 2^p ∣ y := by
  have cop : Nat.Coprime 2 k := by
    change Nat.gcd 2 k = 1
    rw [Nat.gcd_rec, hk]
    decide
  exact (cop.pow_left p).dvd_of_dvd_mul_left h

/-- Removing an index less than 2^(s+1) loses at most s powers of two. -/
theorem cancel_small_index (s p : Nat) {k y : Nat}
    (hk : 0 < k) (small : k < 2^(s+1)) (h : 2^(s+p) ∣ k*y) : 2^p ∣ y := by
  induction s generalizing k with
  | zero =>
    have one : k = 1 := by change k < 2 at small; omega
    simpa [one] using h
  | succ s ih =>
    by_cases odd : k%2=1
    · apply cancel_odd p odd
      exact Nat.dvd_trans (show 2^p ∣ 2^(s+1+p) from ⟨2^(s+1), by rw [Nat.pow_add, Nat.mul_comm]⟩) h
    · have even : 2*(k/2) = k := by omega
      have bound : k/2 < 2^(s+1) := by rw [Nat.pow_succ] at small; omega
      apply ih (k := k/2) (by omega) bound
      apply Nat.dvd_of_mul_dvd_mul_left (k := 2) (by decide)
      rw [←Nat.mul_assoc, even, show 2*2^(s+p)=2^(s+1+p) by
        rw [show s+1+p=(s+p)+1 by omega, Nat.pow_succ, Nat.mul_comm]]
      exact h

/-- Every nonconstant Pascal coefficient through degree 2^(s+1)-1
of (1+T)^(2^n) vanishes modulo 2^p when n ≥ s+p. -/
theorem power_binomial_dvd (s p n k : Nat) (hn : s+p ≤ n) (hk : 0 < k)
    (small : k < 2^(s+1)) : 2^p ∣ binomial (2^n) k := by
  apply cancel_small_index s p hk small
  cases htop : 2^n with
  | zero => have pos : 0 < 2^n := Nat.pow_pos (by decide); omega
  | succ m =>
    cases k with
    | zero => omega
    | succ j =>
      rw [binomial_marked, ←htop]
      have split : 2^n = 2^(s+p)*2^(n-(s+p)) := by rw [←Nat.pow_add]; congr 1; omega
      exact Nat.dvd_trans ⟨_, split⟩ (Nat.dvd_mul_right ..)

/-- The whole Pascal row is locally constant to precision 2^p in the exponent,
uniformly for k below 2^(s+1). -/
theorem binomial_period_pow (s p n i k : Nat) (hn : s+p ≤ n) (hk : k < 2^(s+1)) :
    binomial (i+2^n) k % 2^p = binomial i k % 2^p := by
  induction i generalizing k with
  | zero =>
    rw [Nat.zero_add]
    cases k with
    | zero => simp [binomial_zero_column]
    | succ k =>
      have hd := power_binomial_dvd s p n (k+1) hn (by omega) hk
      simpa only [binomial, Nat.zero_mod] using Nat.mod_eq_zero_of_dvd hd
  | succ i ih =>
    cases k with
    | zero => simp [binomial_zero_column]
    | succ k =>
      rw [show i+1+2^n = (i+2^n)+1 by omega, binomial, binomial,
        Nat.add_mod, ih k (by omega), ih (k+1) hk, ←Nat.add_mod]

theorem binomial_period (s n i k : Nat) (hn : s+6 ≤ n) (hk : k < 2^(s+1)) :
    binomial (i+2^n) k % 64 = binomial i k % 64 := binomial_period_pow s 6 n i k hn hk

/-- Coefficient of T^k in the level n row after X=1+T, before reducing
the integer coefficient. -/
def taylorAt (w : Nat → Nat → Int) (n k : Nat) : Int :=
  total (fun i : Nat => w n i*(binomial i k : Int)) (2^n)

/-- An integral representative of the stabilized Taylor coefficient mod 64. -/
def canonical (w : Nat → Nat → Int) (k : Nat) : Int := taylorAt w (k+6) k % 64

theorem total_pair_mod (f g h : Nat → Int) (m : Int) (a : Nat)
    (pair : ∀ i, i<a → (f i+g i)%m = h i%m) :
    (total f a + total g a)%m = total h a%m := by
  induction a with
  | zero => simp [total]
  | succ a ih =>
    simp only [total]
    rw [show total f a + f a + (total g a + g a) =
      (total f a + total g a) + (f a+g a) by omega, Int.add_emod,
      ih (fun i hi => pair i (by omega)), pair a (by omega), ←Int.add_emod]

/-- Pushing forward by the binary quotient preserves the Taylor coefficient
once the binomial multiplier is constant modulo 2^p on each fibre. -/
theorem taylorAt_step (w : Nat → Nat → Int)
    (refineRow : ∀ n j, j<2^n → w n j=w (n+1) j + w (n+1) (j+2^n))
    (s p n k : Nat) (hn : s+p ≤ n) (hk : k < 2^(s+1)) :
    taylorAt w (n+1) k % (2:Int)^p = taylorAt w n k % (2:Int)^p := by
  unfold taylorAt
  rw [Nat.pow_succ, Nat.mul_two, total_append]
  apply total_pair_mod
  intro i hi
  have B := congrArg (fun t : Nat => (t:Int)) (binomial_period_pow s p n i k hn hk)
  push_cast at B
  rw [Nat.add_comm (2^n) i, refineRow n i hi, Int.add_mul, Int.add_emod, 
    Int.mul_emod (w (n+1) (i+2^n)), B, ←Int.mul_emod, ←Int.add_emod]

theorem taylorAt_stable (w : Nat → Nat → Int)
    (refineRow : ∀ n j, j<2^n → w n j=w (n+1) j + w (n+1) (j+2^n))
    (s p a b k : Nat) (ha : s+p ≤ a) (hab : a ≤ b) (hk : k < 2^(s+1)) :
    taylorAt w b k % (2:Int)^p = taylorAt w a k % (2:Int)^p := by
  have all (d : Nat) : taylorAt w (a+d) k % (2:Int)^p = taylorAt w a k % (2:Int)^p := by
    induction d with
    | zero => rfl
    | succ d ih => exact (taylorAt_step w refineRow s p (a+d) k (by omega) hk).trans ih
  simpa only [show a+(b-a)=b by omega] using all (b-a)

theorem degree_bound (k : Nat) : k < 2^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem canonical_at_level (w : Nat → Nat → Int)
    (refineRow : ∀ n j, j<2^n → w n j=w (n+1) j + w (n+1) (j+2^n))
    (s n k : Nat) (hn : s+6 ≤ n) (hk : k < 2^(s+1)) :
    canonical w k = taylorAt w n k % 64 := by
  unfold canonical
  let m := max (k+6) n
  have left := taylorAt_stable w refineRow k 6 (k+6) m k (by omega)
    (Nat.le_max_left ..) (degree_bound k)
  have right := taylorAt_stable w refineRow s 6 n m k hn (Nat.le_max_right ..) hk
  exact left.symm.trans right

end Reimann.SignedTaylor
