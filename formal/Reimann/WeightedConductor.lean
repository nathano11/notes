import Reimann.WeightDepth

namespace Reimann.WeightedConductor

/-- A factor coprime to the base preserves divisibility at every depth. -/
theorem weight_unit_cancel (p b d e : Nat) (cop : Nat.Coprime p b) :
    p^d ∣ b*e ↔ p^d ∣ e := by
  exact ⟨(cop.pow_left d).dvd_of_dvd_mul_left, fun h => Nat.dvd_mul_left_of_dvd h b⟩

/-- Strip the prescribed depth of the weight, including when s ≤ j. -/
theorem power_divides_weighted_exponent (p j b s e : Nat) (hp : 0 < p)
    (cop : Nat.Coprime p b) :
    (p^s ∣ (p^j*b)*e) ↔ (p^(s-j) ∣ e) := by
  rw [Nat.mul_assoc]
  by_cases hj : j ≤ s
  · have split : j+(s-j) = s := by omega
    have power : p^s = p^j*p^(s-j) := by
      calc
        p^s = p^(j+(s-j)) := congrArg (fun k => p^k) split.symm
        _ = _ := Nat.pow_add _ _ _
    rw [power, Nat.mul_dvd_mul_iff_left (Nat.pow_pos hp)]
    exact weight_unit_cancel p b (s-j) e cop
  · have split : s+(j-s) = j := by omega
    have power : p^j = p^s*p^(j-s) := by
      calc
        p^j = p^(s+(j-s)) := congrArg (fun k => p^k) split.symm
        _ = _ := Nat.pow_add _ _ _
    rw [power, Nat.mul_assoc, Nat.sub_eq_zero_of_le (by omega : s ≤ j), Nat.pow_zero]
    exact ⟨fun _ => Nat.one_dvd _, fun _ => Nat.dvd_mul_right _ _⟩

/-- The kernel of the weighted scalar action on residues modulo p^(s+1). -/
theorem weighted_period (p q r j b s e : Nat)
    (odd : (p : Int) = 2*(q : Int)+1) (weight : r = p^j*b) (cop : Nat.Coprime p b) :
    ((1+(p : Int))^(r*e) % (p : Int)^(s+1) = 1 % (p : Int)^(s+1)) ↔ p^(s-j) ∣ e := by
  rw [WeightDepth.generator_period p q odd, weight]
  exact power_divides_weighted_exponent p j b s e (by omega) cop

/-- Raising the coefficient depth from j+1 to j+n+1 gives precisely p^n
as the period of the weight, for every n including zero. -/
theorem weighted_lift_period (p q r j b n e : Nat)
    (odd : (p : Int) = 2*(q : Int)+1) (weight : r = p^j*b) (cop : Nat.Coprime p b) :
    ((1+(p : Int))^(r*e) % (p : Int)^(j+n+1) = 1 % (p : Int)^(j+n+1)) ↔ p^n ∣ e := by
  simpa only [Nat.add_sub_cancel_left] using weighted_period p q r j b (j+n) e odd weight cop

/-- Any inverse representative of the weighted cyclotomic scalar has exactly
the same kernel of exponents. -/
theorem inverse_weighted_period (p q r j b s e : Nat) (u : Int)
    (odd : (p : Int) = 2*(q : Int)+1) (weight : r = p^j*b) (cop : Nat.Coprime p b)
    (inv : (p : Int)^(s+1) ∣ (1+(p : Int))^(r*e)*u-1) :
    ((p : Int)^(s+1) ∣ u-1) ↔ p^(s-j) ∣ e := by
  rw [WeightDepth.inverse_trivial_iff _ _ _ inv, WeightDepth.generator_divisibility p q odd,
    weight]
  exact power_divides_weighted_exponent p j b s e (by omega) cop

/-- A character of a cyclic group of order m, raised to weight r, has a
kernel described by m/gcd(m,r). No factorization of either input is required. -/
theorem cyclic_kernel_divisor (m r e : Nat) (hm : 0 < m) :
    (m ∣ r*e) ↔ m / Nat.gcd m r ∣ e := by
  let g := Nat.gcd m r
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hm
  have hmg : g*(m/g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m r)
  calc
    (m ∣ r*e) ↔ (m ∣ g*e) := Nat.dvd_gcd_mul_iff_dvd_mul.symm
    _ ↔ (g*(m/g) ∣ g*e) := by rw [hmg]
    _ ↔ (m/g ∣ e) := Nat.mul_dvd_mul_iff_left hg

/-- At any odd base, the exact wild period can be computed from a single gcd,
including for the trivial weight and for bases with several prime factors. -/
theorem weighted_period_without_factorization (p q r s e : Nat)
    (odd : (p : Int) = 2*(q : Int)+1) :
    ((1+(p : Int))^(r*e) % (p : Int)^(s+1) = 1 % (p : Int)^(s+1)) ↔
      (p^s / Nat.gcd (p^s) r) ∣ e := by
  rw [WeightDepth.generator_period p q odd]
  exact cyclic_kernel_divisor (p^s) r e (Nat.pow_pos (by omega))

/-- The order of the combined scalar read from tame and wild generators.
The tame generator has order h and the two periods are relatively prime. -/
theorem tame_wild_period (p q h r j b s e : Nat) (odd : (p : Int) = 2*(q : Int)+1)
    (hh : 0 < h) (separate : Nat.Coprime h p) (weight : r = p^j*b)
    (cop : Nat.Coprime p b) :
    ((h ∣ r*e) ∧ (1+(p : Int))^(r*e) % (p : Int)^(s+1) = 1 % (p : Int)^(s+1)) ↔
      (h / Nat.gcd h r)*p^(s-j) ∣ e := by
  rw [cyclic_kernel_divisor h r e hh, weighted_period p q r j b s e odd weight cop]
  have hd : h / Nat.gcd h r ∣ h :=
    ⟨Nat.gcd h r, (Nat.div_mul_cancel (Nat.gcd_dvd_left h r)).symm⟩
  have relativelyPrime : Nat.Coprime (h / Nat.gcd h r) (p^(s-j)) :=
    (separate.pow_right (s-j)).coprime_dvd_left hd
  constructor
  · rintro ⟨ht,hw⟩
    exact relativelyPrime.mul_dvd_of_dvd_of_dvd ht hw
  · intro both
    exact ⟨Nat.dvd_trans (Nat.dvd_mul_right _ _) both,
      Nat.dvd_trans (Nat.dvd_mul_left _ _) both⟩

/-- An explicit integer representative for the inverse twist, constructed
from the unweighted period. This gives the inverse at every finite depth. -/
theorem weighted_inverse_witness (p q s r e : Nat) (odd : (p : Int) = 2*(q : Int)+1) :
    (p : Int)^(s+1) ∣
      (1+(p : Int))^(r*e) * (1+(p : Int))^((r*e)*(p^s-1)) - 1 := by
  rw [← Int.pow_add, WeightDepth.generator_divisibility p q odd]
  have pos : 0 < p^s := Nat.pow_pos (by omega)
  have full : (r*e)+(r*e)*(p^s-1) = (r*e)*(p^s) := by
    calc
      (r*e)+(r*e)*(p^s-1) = (r*e)*((p^s-1)+1) := by rw [Nat.mul_add]; omega
      _ = (r*e)*(p^s) := by congr 1; omega
  rw [full]
  exact Nat.dvd_mul_left _ _

/-- At lift depth j+n+1 the explicitly represented inverse twist first
returns to the identity at exponent p^n. -/
theorem inverse_lift_period (p q r j b n e : Nat)
    (odd : (p : Int) = 2*(q : Int)+1) (weight : r = p^j*b) (cop : Nat.Coprime p b) :
    ((p : Int)^(j+n+1) ∣ (1+(p : Int))^((r*e)*(p^(j+n)-1))-1) ↔ p^n ∣ e := by
  simpa only [Nat.add_sub_cancel_left] using
    inverse_weighted_period p q r j b (j+n) e _ odd weight cop
      (weighted_inverse_witness p q (j+n) r e odd)

end Reimann.WeightedConductor
