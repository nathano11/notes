import Std

namespace Reimann.CyclotomicNorm

/-- The norm operator for a cyclic scalar action, written as an integer sum. -/
def geom (u : Int) : Nat → Int
  | 0 => 0
  | n+1 => geom u n + u^n

theorem geom_identity (u : Int) (n : Nat) :
    (u-1)*geom u n = u^n-1 := by
  induction n with
  | zero => simp [geom]
  | succ n ih =>
    rw [geom, Int.pow_succ]
    grind

/-- Linear part of a power; the remainder is explicitly divisible by p². -/
theorem power_linear (p t : Int) (n : Nat) :
    ∃ c : Int, (1+p*t)^n = 1 + (n : Int)*p*t + p^2*c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih
    refine ⟨c + (n : Int)*t^2 + p*t*c, ?_⟩
    rw [Int.pow_succ, hc, Int.natCast_succ]
    grind

def triangular : Nat → Int
  | 0 => 0
  | n+1 => triangular n + (n : Int)

theorem triangular_twice (n : Nat) :
    2*triangular n = (n : Int)*((n : Int)-1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [triangular, Int.natCast_succ]
    grind

theorem geom_linear (p t : Int) (n : Nat) :
    ∃ c : Int, geom (1+p*t) n =
        (n : Int) + p*t*triangular n + p^2*c := by
  induction n with
  | zero => exact ⟨0, by simp [geom, triangular]⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := ih
    obtain ⟨b,hb⟩ := power_linear p t n
    refine ⟨a+b, ?_⟩
    rw [geom, ha, hb, triangular, Int.natCast_succ]
    grind

theorem triangular_at_odd (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1) :
    triangular p = (p : Int)*(q : Int) := by
  have ht := triangular_twice p
  rw [hp] at ht ⊢
  grind

theorem one_layer (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1) (t : Int) :
    ∃ c : Int, geom (1+(p : Int)*t) p = (p : Int)*(1+(p : Int)*c) := by
  obtain ⟨c,hc⟩ := geom_linear (p : Int) t p
  rw [triangular_at_odd p q hp] at hc
  exact ⟨t*(q : Int)+c, by grind⟩

theorem geom_add (u : Int) (a b : Nat) :
    geom u (a+b) = geom u a + u^a * geom u b := by
  induction b with
  | zero => simp [geom]
  | succ b ih =>
    change geom u (a+b) + u^(a+b) = geom u a + u^a * (geom u b + u^b)
    rw [ih, Int.pow_add]
    grind

theorem geom_blocks (u : Int) (a b : Nat) :
    geom u (a*b) = geom u a * geom (u^a) b := by
  induction b with
  | zero => simp [geom]
  | succ b ih =>
    rw [Nat.mul_succ, geom_add, ih, Int.pow_mul, geom]
    grind

/-- Each block has one factor p and an integral factor congruent to 1 modulo p. -/
theorem norm_over_power (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t : Int) (n : Nat) :
    ∃ c : Int, geom (1+(p : Int)*t) (p^n) = (p : Int)^n * (1+(p : Int)*c) := by
  induction n with
  | zero => exact ⟨0, by simp [geom]⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := ih
    obtain ⟨b,hb⟩ := power_linear (p : Int) t (p^n)
    let w : Int := ((p^n : Nat) : Int)*t + (p : Int)*b
    have hw : (1+(p : Int)*t)^(p^n : Nat) = 1+(p : Int)*w := by
      dsimp [w]
      grind
    obtain ⟨c,hc⟩ := one_layer p q hp w
    refine ⟨a+c+(p : Int)*a*c, ?_⟩
    rw [Nat.pow_succ, geom_blocks, ha, hw, hc, Int.pow_succ]
    grind

theorem lifted_power_difference (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t : Int) (n : Nat) :
    ∃ c : Int, (1+(p : Int)*t)^(p^n : Nat) - 1 =
       (p : Int)^(n+1)*t*(1+(p : Int)*c) := by
  obtain ⟨c,hc⟩ := norm_over_power p q hp t n
  have hg := geom_identity (1+(p : Int)*t) (p^n)
  rw [hc] at hg
  refine ⟨c, ?_⟩
  rw [Int.pow_succ]
  grind

/-- Exact divisibility, including the nondivisibility needed for the cyclic norm. -/
theorem norm_exact_depth (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (hp1 : (1 : Int) < (p : Int)) (t : Int) (n : Nat) :
    ((p : Int)^n ∣ geom (1+(p : Int)*t) (p^n)) ∧
    ¬ ((p : Int)^(n+1) ∣ geom (1+(p : Int)*t) (p^n)) := by
  obtain ⟨c,hc⟩ := norm_over_power p q hp t n
  constructor
  · exact ⟨1+(p : Int)*c, hc⟩
  · intro h
    obtain ⟨b,hb⟩ := h
    rw [hc, Int.pow_succ, Int.mul_assoc] at hb
    have hz : (p : Int)^n ≠ 0 := Int.pow_ne_zero (by omega)
    have he := Int.eq_of_mul_eq_mul_left hz hb
    have hd : (p : Int) ∣ 1+(p : Int)*c := ⟨b,he⟩
    have hr := Int.emod_eq_zero_of_dvd hd
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by decide) hp1] at hr
    contradiction

/-- The concrete norm endomorphism on Z/p^n vanishes on every residue class. -/
theorem norm_action_zero (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t z : Int) (n : Nat) :
    (geom (1+(p : Int)*t) (p^n)*z) % ((p : Int)^n) = 0 := by
  obtain ⟨c,hc⟩ := norm_over_power p q hp t n
  apply Int.emod_eq_zero_of_dvd
  refine ⟨(1+(p : Int)*c)*z, ?_⟩
  rw [hc, Int.mul_assoc]

end Reimann.CyclotomicNorm
