import Reimann.CyclotomicNorm

namespace Reimann.WeightDepth

/-- The coefficient of p in a weight-k power is k*t modulo p. -/
theorem weight_linear (p t : Int) (k : Nat) :
    ∃ c : Int, (1+p*t)^k = 1+p*((k : Int)*t+p*c) := by
  obtain ⟨c,hc⟩ := CyclotomicNorm.power_linear p t k
  exact ⟨c, by grind⟩

/-- After removing p^(s+1), the scalar difference at weight p^s*k
    has residue k*t. The identity also holds for zero weights. -/
theorem normalized_difference (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t : Int) (s k : Nat) :
    ∃ c : Int, (1+(p : Int)*t)^(p^s*k)-1 =
      (p : Int)^(s+1)*((k : Int)*t+(p : Int)*c) := by
  obtain ⟨a,ha⟩ := weight_linear (p : Int) t k
  obtain ⟨b,hb⟩ := CyclotomicNorm.lifted_power_difference p q hp ((k : Int)*t+(p : Int)*a) s
  refine ⟨a + (k : Int)*t*b + (p : Int)*a*b, ?_⟩
  rw [Nat.mul_comm, Int.pow_mul, ha, hb]
  grind

/-- Cancelling the known power leaves a single divisibility test. -/
theorem next_power_iff (p a c : Int) (s : Nat) (hp : p ≠ 0) :
    (p^(s+1) ∣ p^s*(a+p*c)) ↔ p ∣ a := by
  constructor
  · rintro ⟨b,hb⟩
    rw [Int.pow_succ, Int.mul_assoc] at hb
    have hc := Int.eq_of_mul_eq_mul_left (Int.pow_ne_zero hp) hb
    exact ⟨b-c, by grind⟩
  · rintro ⟨b,hb⟩
    exact ⟨b+c, by rw [Int.pow_succ, hb]; grind⟩

/-- The next power divides exactly when p divides the residual weight times t. -/
theorem weight_depth_test (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t : Int) (s k : Nat) :
    ((p : Int)^(s+1) ∣ (1+(p : Int)*t)^(p^s*k)-1) ∧
    (((p : Int)^(s+2) ∣ (1+(p : Int)*t)^(p^s*k)-1) ↔ (p : Int) ∣ (k : Int)*t) := by
  obtain ⟨c,hc⟩ := normalized_difference p q hp t s k
  rw [hc]
  exact ⟨⟨(k : Int)*t+(p : Int)*c, rfl⟩, next_power_iff _ _ _ _ (by omega)⟩

/-- Every multiple of p^s acts as 1 modulo p^(s+1). -/
theorem weight_dvd_lower (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t : Int) (s r : Nat) (hr : p^s ∣ r) :
    (p : Int)^(s+1) ∣ (1+(p : Int)*t)^r-1 := by
  obtain ⟨k,rfl⟩ := hr
  exact (weight_depth_test p q hp t s k).1

/-- For every weight including zero, congruence to the identity at level s+1
    is equivalent to divisibility of the weight by p^s. -/
theorem generator_divisibility (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (s r : Nat) :
    ((p : Int)^(s+1) ∣ (1+(p : Int))^r-1) ↔ p^s ∣ r := by
  constructor
  · induction s with
    | zero => intro _; simp
    | succ s ih =>
      intro hh
      have hlow : (p : Int)^(s+1) ∣ (1+(p : Int))^r-1 :=
        Int.dvd_trans ⟨(p : Int), Int.pow_succ _ _⟩ hh
      obtain ⟨k,rfl⟩ := ih hlow
      have htest := (weight_depth_test p q hp 1 s k).2
      simp only [Int.mul_one] at htest
      obtain ⟨b,hb⟩ := Int.ofNat_dvd.mp (htest.mp hh)
      exact ⟨b, by rw [hb, Nat.pow_succ, Nat.mul_assoc]⟩
  · intro h
    simpa using weight_dvd_lower p q hp 1 s r h

/-- Congruence of actual residue representatives, including the modulus-one case. -/
theorem generator_period (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (s r : Nat) :
    (1+(p : Int))^r % (p : Int)^(s+1) = 1 % (p : Int)^(s+1) ↔ p^s ∣ r := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
  exact generator_divisibility p q hp s r

/-- The least positive weight acting trivially modulo p^(s+1) is p^s. -/
theorem generator_least_period (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (s : Nat) :
    0 < p^s ∧ (1+(p : Int))^(p^s) % (p : Int)^(s+1) = 1 % (p : Int)^(s+1) ∧
    ∀ r : Nat, 0 < r → (1+(p : Int))^r % (p : Int)^(s+1) = 1 % (p : Int)^(s+1) → p^s ≤ r := by
  refine ⟨Nat.pow_pos (by omega), (generator_period p q hp s _).mpr (Nat.dvd_refl _), ?_⟩
  intro r hr heq
  exact Nat.le_of_dvd hr ((generator_period p q hp s r).mp heq)

/-- An element and any inverse representative are simultaneously 1 modulo m. -/
theorem inverse_trivial_iff (m a b : Int) (hinv : m ∣ a*b-1) :
    (m ∣ b-1) ↔ m ∣ a-1 := by
  obtain ⟨z,hz⟩ := hinv
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨z-a*j, by grind⟩
  · rintro ⟨j,hj⟩
    exact ⟨z-b*j, by grind⟩

/-- A concrete representative of the negative weight at every finite level. -/
theorem inverse_weight_representative (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (s r : Nat) :
    (p : Int)^(s+1) ∣ (1+(p : Int))^r*(1+(p : Int))^((p^s-1)*r)-1 := by
  have hs : 0 < p^s := Nat.pow_pos (by omega)
  have he : r+(p^s-1)*r = p^s*r := by
    have ht : p^s - 1 + 1 = p^s := by omega
    rw [← ht, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
    omega
  rw [← Int.pow_add, he]
  exact (generator_divisibility p q hp s _).mpr ⟨r,rfl⟩

/-- The same period criterion applies to the negative cyclotomic twist, with
    an explicit integer representative at the chosen coefficient level. -/
theorem inverse_weight_period (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (s r : Nat) :
    ((p : Int)^(s+1) ∣ (1+(p : Int))^((p^s-1)*r)-1) ↔ p^s ∣ r := by
  exact (inverse_trivial_iff _ _ _ (inverse_weight_representative p q hp s r)).trans
    (generator_divisibility p q hp s r)

/-- At one extra digit an inverse negates the normalized first digit. -/
theorem inverse_first_digit (p d k c y : Int)
    (hinv : (d*p)*p ∣ (1+(d*p)*(k+p*c))*y-1) :
    ∃ b : Int, y-1 = (d*p)*(-k+p*b) := by
  obtain ⟨z,hz⟩ := hinv
  let w := p*z-(k+p*c)*y
  have hw : y-1 = (d*p)*w := by dsimp [w]; grind
  refine ⟨z-c*y-k*d*w, ?_⟩
  have hw' : w = -k+p*(z-c*y-k*d*w) := by
    calc
      w = -k+p*(z-c*y)-k*(y-1) := by dsimp [w]; grind
      _ = -k+p*(z-c*y-k*d*w) := by rw [hw]; grind
  calc
    y-1 = (d*p)*w := hw
    _ = (d*p)*(-k+p*(z-c*y-k*d*w)) := by conv => lhs; rw [hw']

/-- For every inverse representative at level s+2 the normalized digit at
    weight p^s*k is -k*t modulo p. -/
theorem inverse_normalized_difference (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t y : Int) (s k : Nat)
    (hinv : (p : Int)^(s+2) ∣ (1+(p : Int)*t)^(p^s*k)*y-1) :
    ∃ b : Int, y-1 = (p : Int)^(s+1)*(-((k : Int)*t)+(p : Int)*b) := by
  obtain ⟨c,hc⟩ := normalized_difference p q hp t s k
  have ha : (1+(p : Int)*t)^(p^s*k) =
      1+((p : Int)^s*(p : Int))*((k : Int)*t+(p : Int)*c) := by
    rw [Int.pow_succ] at hc
    omega
  rw [ha, Int.pow_succ, Int.pow_succ] at hinv
  rw [Int.pow_succ]
  exact inverse_first_digit _ _ _ _ _ hinv

/-- An unconditional finite representative of the negative twist realizes the
    signed digit. Use precision s+2 so the digit after division is determined. -/
theorem negative_weight_digit (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (s k : Nat) :
    ∃ b : Int, (1+(p : Int))^((p^(s+1)-1)*(p^s*k))-1 =
      (p : Int)^(s+1)*(-(k : Int)+(p : Int)*b) := by
  have hi := inverse_weight_representative p q hp (s+1) (p^s*k)
  simpa using inverse_normalized_difference p q hp 1 _ s k (by simpa using hi)

end Reimann.WeightDepth
