import Reimann.Dyadic

/-! Exact dyadic spacing of the reciprocal specializations in §8 of Dyadic_Window_Orders.md.
The integral numerator records both signs without introducing division. -/

namespace Reimann.SampleSpacing

open Reimann.Dyadic

theorem cyclotomicSample_pow (j : Nat) : cyclotomicSample j = (5 : Int)^(2^j) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cyclotomicSample, ih, Nat.pow_succ, Nat.mul_two, Int.pow_add]

theorem oddPower_pow (x : Int) (k : Nat) : oddPower x k = x^(2*k+1) := by
  induction k with
  | zero => simpa only [oddPower, Nat.mul_zero, Nat.zero_add] using (Int.pow_one x).symm
  | succ k ih =>
    have he : 2*(k+1)+1 = (2*k+1)+2 := by omega
    rw [oddPower, ih, he, Int.pow_add x (2*k+1) 2]
    rw [Int.pow_succ x 1, Int.pow_one]

theorem power_gap_at_zero (j k : Nat) :
    exactV ((5 : Int)^(2^j*(2*k+1))-1) (j+2) := by
  have h := spacing_odd_multiple j k
  rwa [oddPower_pow, cyclotomicSample_pow, ← Int.pow_mul] at h

theorem five_power_mod_four (n : Nat) : ∃ u : Int, (5 : Int)^n = 1+4*u := by
  induction n with
  | zero => exact ⟨0, by decide⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih
    exact ⟨1+5*u, by rw [Int.pow_succ, hu]; grind⟩

theorem exactV_mul_odd (x : Int) (j : Nat) (v : Int) (hx : exactV x j) :
    exactV ((1+2*v)*x) j := by
  obtain ⟨u, hu⟩ := hx
  exact ⟨u+v+2*u*v, by rw [hu]; grind⟩

theorem power_gap (n j k : Nat) :
    exactV ((5 : Int)^(n+2^j*(2*k+1))-(5 : Int)^n) (j+2) := by
  obtain ⟨v, hv⟩ := five_power_mod_four n
  have h := exactV_mul_odd _ _ (2*v) (power_gap_at_zero j k)
  have he : (5 : Int)^(n+2^j*(2*k+1))-5^n =
      (1+2*(2*v))*(5^(2^j*(2*k+1))-1) := by
    rw [Int.pow_add 5 n, hv]
    grind
  rwa [he]

/-- For t = ε/a−1 and P(t) = t²+c1*t+c0 this is a²P(t). -/
def numerator (c0 c1 ε a : Int) : Int :=
  (ε-a)^2 + c1*a*(ε-a) + c0*a^2

theorem reciprocal_difference_factor (c0 c1 ε a b : Int) :
    b^2*numerator c0 c1 ε a - a^2*numerator c0 c1 ε b =
      (b-a)*(ε^2*(a+b) + ε*(c1-2)*a*b) := by
  unfold numerator
  grind

theorem reciprocal_slope (c1 ε a b : Int) (hcoeff : ∃ z : Int, c1=2+4*z)
    (hsign : ε=1 ∨ ε= -1) (ha : ∃ u : Int, a=1+4*u) (hb : ∃ v : Int, b=1+4*v) :
    ∃ w : Int, ε^2*(a+b) + ε*(c1-2)*a*b = 2*(2*w+1) := by
  obtain ⟨z, hz⟩ := hcoeff
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨u+v+ε*z*a*b, ?_⟩
  rcases hsign with h | h <;> rw [h, hz, hu, hv] <;> grind

theorem exactV_mul_twice_odd (x : Int) (j : Nat) (w : Int) (hx : exactV x j) :
    exactV (x*(2*(2*w+1))) (j+1) := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨u+w+2*u*w, ?_⟩
  rw [hu, twoPower]
  grind

/-- Exact dyadic spacing at weights n and n+2^j(2k+1), for either sign.
The displayed integer is the difference of the reciprocal evaluations with
their common odd denominator a²b² cleared. -/
theorem reciprocal_spacing (c0 c1 ε : Int) (hcoeff : ∃ z : Int, c1=2+4*z)
    (hsign : ε=1 ∨ ε= -1) (n j k : Nat) :
    let a := (5 : Int)^n
    let b := (5 : Int)^(n+2^j*(2*k+1))
    exactV (b^2*numerator c0 c1 ε a-a^2*numerator c0 c1 ε b) (j+3) := by
  dsimp only
  rw [reciprocal_difference_factor]
  obtain ⟨w, hw⟩ := reciprocal_slope c1 ε _ _ hcoeff hsign
    (five_power_mod_four n) (five_power_mod_four (n+2^j*(2*k+1)))
  rw [hw]
  exact exactV_mul_twice_odd _ _ w (power_gap n j k)

theorem common_denominator_odd (n m : Nat) :
    ∃ u : Int, ((5 : Int)^n)^2*((5 : Int)^m)^2 = 2*u+1 := by
  obtain ⟨x, hx⟩ := five_power_mod_four n
  obtain ⟨y, hy⟩ := five_power_mod_four m
  let w := 2*(x+y)+8*x*y
  have h : (5 : Int)^n*5^m = 2*w+1 := by
    rw [hx, hy]
    dsimp [w]
    grind
  refine ⟨2*w*(w+1), ?_⟩
  calc
    _ = ((5 : Int)^n*5^m)^2 := by grind
    _ = _ := by rw [h]; grind

end Reimann.SampleSpacing
