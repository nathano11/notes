import Reimann.PairedOrders

/-! Multiplication of the two signed specializations of a monic quadratic.
All coefficient and product statements below concern ordinary integers. -/

namespace Reimann.SignedProduct

open Reimann.Dyadic Reimann.SampleSpacing Reimann.PairedSigns Reimann.PairedOrders

/-- The conjugate signs yield a difference of squares with no denominators. -/
theorem product_as_difference_of_squares (c0 c1 a : Int) :
    numerator c0 c1 1 a * numerator c0 c1 (-1) a =
      (1 + (1-c1+c0)*a^2)^2 - (a*(c1-2))^2 := by
  unfold numerator
  grind

/-- A Bézout relation between the positive numerator and its argument. -/
theorem numerator_bezout (c0 c1 a : Int) :
    numerator c0 c1 1 a - a*(c1-2 + (1-c1+c0)*a) = 1 := by
  unfold numerator
  grind

/-- This describes every common divisor, including all odd prime powers. -/
theorem common_divisor_iff (c0 c1 a d : Int) :
    (d ∣ numerator c0 c1 1 a ∧ d ∣ numerator c0 c1 (-1) a) ↔
    (d ∣ numerator c0 c1 1 a ∧ d ∣ 2*(c1-2)) := by
  let t := c1-2 + (1-c1+c0)*a
  have bez : numerator c0 c1 1 a - a*t = 1 := numerator_bezout c0 c1 a
  have diff := sign_difference c0 c1 a
  constructor
  · rintro ⟨hp, hm⟩
    have delta := Int.dvd_sub hp hm
    have h := Int.dvd_sub (Int.dvd_mul_of_dvd_left (c := 2*(c1-2)) hp)
      (Int.dvd_mul_of_dvd_left (c := t) delta)
    have id : numerator c0 c1 1 a * (2*(c1-2)) -
        (numerator c0 c1 1 a - numerator c0 c1 (-1) a)*t = 2*(c1-2) := by
      rw [diff]
      calc
        _ = (numerator c0 c1 1 a - a*t)*(2*(c1-2)) := by grind
        _ = _ := by rw [bez]; simp
    exact ⟨hp, id ▸ h⟩
  · rintro ⟨hp, hd⟩
    have delta : d ∣ numerator c0 c1 1 a - numerator c0 c1 (-1) a := by
      rw [diff, show 2*a*(c1-2) = a*(2*(c1-2)) by grind]
      exact Int.dvd_mul_of_dvd_right hd
    exact ⟨hp, by simpa only [show numerator c0 c1 1 a -
      (numerator c0 c1 1 a - numerator c0 c1 (-1) a) = numerator c0 c1 (-1) a by omega]
      using Int.dvd_sub hp delta⟩

/-- The odd parts multiply and the dyadic exponents add. -/
theorem exactV_mul {x y : Int} {i j : Nat} (hx : exactV x i) (hy : exactV y j) :
    exactV (x*y) (i+j) := by
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨c, rfl⟩ := hy
  refine ⟨b+c+2*b*c, ?_⟩
  rw [twoPower_add]
  grind

/-- An exact valuation decides divisibility by every power of two. -/
theorem twoPower_dvd_iff {x : Int} {n : Nat} (hx : exactV x n) (k : Nat) :
    twoPower k ∣ x ↔ k ≤ n := by
  obtain ⟨u, hu⟩ := hx
  constructor
  · rintro ⟨v, hv⟩
    apply Classical.byContradiction
    intro hle
    have hk : k = n + ((k-n-1)+1) := by omega
    rw [hk, twoPower_add, twoPower] at hv
    have nz : twoPower n ≠ 0 := by
      rw [WeightClasses.twoPower_eq_pow]
      exact Int.ne_of_gt (Int.pow_pos (by decide : 0 < (2:Int)))
    have eqn : twoPower n * (2*u+1) = twoPower n * (2*(twoPower (k-n-1)*v)) := by
      calc
        _ = x := hu.symm
        _ = _ := by rw [hv]; grind
    have := Int.eq_of_mul_eq_mul_left nz eqn
    omega
  · intro h
    refine ⟨twoPower (n-k)*(2*u+1), ?_⟩
    have hn : k+(n-k)=n := by omega
    rw [hu, ←Int.mul_assoc, ←twoPower_add, hn]

/-- Exact finite exponents are unique, for integers of either sign. -/
theorem exactV_unique {x : Int} {i j : Nat} (hi : exactV x i) (hj : exactV x j) :
    i = j := by
  have ij := (twoPower_dvd_iff hj i).mp ((twoPower_dvd_iff hi i).mpr (Nat.le_refl i))
  have ji := (twoPower_dvd_iff hi j).mp ((twoPower_dvd_iff hj j).mpr (Nat.le_refl j))
  omega

/-- The product lies exactly at depth eight in the first residue class;
the high class is divisible by 2048, including when one factor vanishes. -/
theorem product_by_weight {c0 c1 : Int} (h : WeightThree c0 c1) {r : Nat} (hr : r%2=1) :
    (r%4=1 ∧ exactV (positiveBranch c0 c1 r * negativeBranch c0 c1 r) 8) ∨
    (r%4=3 ∧ twoPower 11 ∣ positiveBranch c0 c1 r * negativeBranch c0 c1 r) := by
  let x := positiveBranch c0 c1 r
  let y := negativeBranch c0 c1 r
  change (r%4=1 ∧ exactV (x*y) 8) ∨ (r%4=3 ∧ twoPower 11 ∣ x*y)
  have high (v w : Int) (hv : v%64=32) (hw : w%64=0) : twoPower 11 ∣ v*w := by
    change (32:Int)*64 ∣ v*w
    exact Int.mul_dvd_mul (show (32:Int) ∣ v by omega) (show (64:Int) ∣ w by omega)
  rcases all_odd_weights c0 c1 h r hr with ⟨hw, e⟩ | ⟨hw, e⟩ | ⟨hw, e⟩ | ⟨hw, e⟩
  all_goals obtain ⟨hp, hm⟩ := Prod.mk.inj e
  · exact Or.inl ⟨by omega, exactV_mul (exact_four_of_residue (Or.inl hp))
      (exact_four_of_residue (Or.inr hm))⟩
  · exact Or.inr ⟨by omega, high x y hp hm⟩
  · exact Or.inl ⟨by omega, exactV_mul (exact_four_of_residue (Or.inr hp))
      (exact_four_of_residue (Or.inl hm))⟩
  · exact Or.inr ⟨by omega, by rw [Int.mul_comm x y]; exact high y x hm hp⟩

/-- All finite product exponents at positive odd weights, with both directions. -/
theorem product_valuation_spectrum {c0 c1 : Int} (h : WeightThree c0 c1) (n : Nat) :
    (∃ r, r%2=1 ∧ exactV (positiveBranch c0 c1 r * negativeBranch c0 c1 r) n) ↔
      n = 8 ∨ 11 ≤ n := by
  constructor
  · rintro ⟨r, hr, hn⟩
    rcases product_by_weight h hr with ⟨_, low⟩ | ⟨_, high⟩
    · exact Or.inl (exactV_unique hn low)
    · exact Or.inr ((twoPower_dvd_iff hn 11).mp high)
  · rintro (rfl | high)
    · have vals := weight_one_pair h
      exact ⟨1, by decide, exactV_mul vals.1 vals.2⟩
    · obtain ⟨r, hr, vals⟩ := (every_high_pair h (n-11)).1
      have hp := exactV_mul vals.1 vals.2
      exact ⟨r, by omega, (show n-11+6+5=n by omega) ▸ hp⟩

/-- At layers a≥1 the Smith cardinality is determined by the single
product exponent. Its application to a strict group requires the displayed
Smith exponents and cardinality from the arithmetic lattice. -/
theorem order_from_product {c0 c1 : Int} (h : WeightThree c0 c1)
    {r α β a lo hi n order : Nat} (hr : r%2=1) (ha : 1 ≤ a)
    (vals : PairAt c0 c1 r α β)
    (prodVal : exactV (positiveBranch c0 c1 r * negativeBranch c0 c1 r) n)
    (smith : SmithAt a α β lo hi) (card : order = 2^lo * 2^hi) :
    order = 2^(n+2*a-3) := by
  have hn : n=α+β := exactV_unique prodVal (exactV_mul vals.1 vals.2)
  obtain ⟨hlo, hhi⟩ := smith
  rw [card, ← Nat.pow_add]
  apply congrArg (2^·)
  rcases signed_valuations h hr vals with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- The factor two in the common-divisor test drops out for any odd divisor. -/
theorem odd_divides_twice (k x : Int) : (2*k+1) ∣ 2*x ↔ (2*k+1) ∣ x := by
  constructor
  · intro h
    have diff := Int.dvd_sub (Int.dvd_mul_right (2*k+1) x)
      (Int.dvd_mul_of_dvd_left (c := k) h)
    simpa only [show (2*k+1)*x - 2*x*k=x by grind] using diff
  · exact Int.dvd_mul_of_dvd_right

/-- Reducing the linear coefficient to 2 leaves a single quadratic congruence. -/
theorem numerator_at_two (c0 c1 a : Int) :
    numerator c0 c1 1 a - (1+(c0-1)*a^2) = (c1-2)*(a*(1-a)) := by
  unfold numerator
  grind

/-- For each odd prime power (indeed, every odd integer), simultaneous
divisibility is equivalent to two congruences in the coefficients and argument. -/
theorem common_odd_divisor_iff (c0 c1 a k : Int) :
    ((2*k+1) ∣ numerator c0 c1 1 a ∧ (2*k+1) ∣ numerator c0 c1 (-1) a) ↔
    ((2*k+1) ∣ c1-2 ∧ (2*k+1) ∣ 1+(c0-1)*a^2) := by
  rw [common_divisor_iff, odd_divides_twice]
  have difference (h : (2*k+1) ∣ c1-2) :
      (2*k+1) ∣ numerator c0 c1 1 a - (1+(c0-1)*a^2) := by
    rw [numerator_at_two]
    exact Int.dvd_mul_of_dvd_left h
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hc, by simpa only [show numerator c0 c1 1 a -
      (numerator c0 c1 1 a - (1+(c0-1)*a^2)) = 1+(c0-1)*a^2 by omega]
      using Int.dvd_sub hp (difference hc)⟩
  · rintro ⟨hc, hq⟩
    exact ⟨by simpa only [show numerator c0 c1 1 a - (1+(c0-1)*a^2) +
      (1+(c0-1)*a^2) = numerator c0 c1 1 a by omega]
      using Int.dvd_add (difference hc) hq, hc⟩

end Reimann.SignedProduct
