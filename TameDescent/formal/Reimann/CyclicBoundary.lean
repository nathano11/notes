import Reimann.CyclotomicNorm

namespace Reimann.CyclicBoundary

/-- A finite geometric sum inverts a scalar congruent to one modulo the base. -/
theorem unit_bezout_power (p c : Int) (n : Nat) :
    ∃ a b : Int, (1+p*c)*a + p^n*b = 1 := by
  refine ⟨CyclotomicNorm.geom (p*(-c)) n, (-c)^n, ?_⟩
  have h := CyclotomicNorm.geom_identity (p*(-c)) n
  rw [Int.mul_pow] at h
  grind

theorem cancel_unit_factor (p c y : Int) (n : Nat) :
    (p^n ∣ (1+p*c)*y) ↔ (p^n ∣ y) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨a,b,hab⟩ := unit_bezout_power p c n
    refine ⟨a*z+b*y, ?_⟩
    calc
      y = ((1+p*c)*a+p^n*b)*y := by rw [hab, Int.one_mul]
      _ = a*((1+p*c)*y)+p^n*(b*y) := by grind
      _ = p^n*(a*z+b*y) := by rw [hz]; grind
  · rintro ⟨z, rfl⟩
    exact ⟨(1+p*c)*z, by grind⟩

/-- With coefficient depth k+d and a group of order p^k, a generator value
is norm-admissible exactly when it is divisible by p^d. -/
theorem norm_kernel_gap (p q k d : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (hp0 : (p : Int) ≠ 0) (t y : Int) :
    ((p : Int)^(k+d) ∣ CyclotomicNorm.geom (1+(p : Int)*t) (p^k)*y) ↔
      ((p : Int)^d ∣ y) := by
  obtain ⟨c,hc⟩ := CyclotomicNorm.norm_over_power p q hp t k
  rw [hc, Int.pow_add, Int.mul_assoc, Int.mul_dvd_mul_iff_left (Int.pow_ne_zero hp0)]
  exact cancel_unit_factor (p : Int) c y d

/-- At arbitrary depths, the loss is exactly the truncated difference n-k. -/
theorem norm_kernel_at_depth (p q k n : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (hp0 : (p : Int) ≠ 0) (t y : Int) :
    ((p : Int)^n ∣ CyclotomicNorm.geom (1+(p : Int)*t) (p^k)*y) ↔
      ((p : Int)^(n-k) ∣ y) := by
  by_cases h : k ≤ n
  · have hn : k+(n-k) = n := by omega
    simpa only [hn] using norm_kernel_gap p q k (n-k) hp hp0 t y
  · have hn : n+(k-n) = k := by omega
    obtain ⟨c,hc⟩ := CyclotomicNorm.norm_over_power p q hp t k
    rw [Nat.sub_eq_zero_of_le (by omega : n ≤ k), Int.pow_zero]
    constructor
    · intro _
      exact Int.one_dvd y
    · intro _
      refine ⟨(p : Int)^(k-n)*((1+(p : Int)*c)*y), ?_⟩
      rw [hc, ← hn, Int.pow_add]
      grind

/-- A lift of the generator at denominator p^(w+1) has numerator 1 mod p. -/
theorem primitive_lift_form (p a : Int) (w : Nat)
    (hlift : p^(w+1) ∣ a-1) : ∃ c : Int, a = 1+p*c := by
  obtain ⟨z,hz⟩ := hlift
  refine ⟨p^w*z, ?_⟩
  rw [Int.pow_succ] at hz
  grind

/-- Fixing any lift of a lower generator forces the scalar to fix every
residue at the upper denominator. This also applies to inverse twists. -/
theorem primitive_lift_fixed (p a u : Int) (w N : Nat) (hlift : p^(w+1) ∣ a-1) :
    (p^N ∣ u*a-a) ↔ (p^N ∣ u-1) := by
  obtain ⟨c,hc⟩ := primitive_lift_form p a w hlift
  have h : u*a-a = (1+p*c)*(u-1) := by rw [hc]; grind
  rw [h]
  exact cancel_unit_factor p c (u-1) N

/-- A subgroup has a simultaneous fixed lift of the lower generator precisely
when every one of its scalars acts trivially at the upper denominator. -/
theorem subgroup_fixes_lift_iff (p : Int) (w n : Nat) (scalar : G → Int) :
    (∃ a : Int, (p^(w+1) ∣ a-1) ∧ ∀ g, p^(n+(w+1)) ∣ scalar g*a-a) ↔
      (∀ g, p^(n+(w+1)) ∣ scalar g-1) := by
  constructor
  · rintro ⟨a,ha,hfix⟩ g
    exact (primitive_lift_fixed p a (scalar g) w _ ha).mp (hfix g)
  · intro h
    refine ⟨1, by simp, fun g => ?_⟩
    simpa using h g

end Reimann.CyclicBoundary
