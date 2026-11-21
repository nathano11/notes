import Reimann.SampleSpacing

/-! The even-weight dyadic local obstruction in lattice coordinates.
The model uses integer numerators for dyadic fractions modulo one. The
comparison of a global restriction with this coordinate model is arithmetic.
-/

namespace Reimann.DyadicEven

open Reimann.Dyadic

/-- Equivariance for inversion on the lattice and the identity on coefficients
forces a canonical numerator at denominator 2*d to represent zero or one half. -/
theorem involution_forces_half (d z : Int) (hd : 0 < d)
    (lo : 0 ≤ z) (hi : z < 2*d) :
    (2*d ∣ -z-z) ↔ z=0 ∨ z=d := by
  constructor
  · rintro ⟨t,ht⟩
    have he : z = d*(-t) := by grind
    have hn : 0 ≤ -t := by
      by_cases h : 0 ≤ -t
      · exact h
      · have := Int.mul_neg_of_pos_of_neg hd (show -t < 0 by omega)
        omega
    have hu : -t < 2 := by
      by_cases h : -t < 2
      · exact h
      · have := Int.mul_le_mul_of_nonneg_left (show 2 ≤ -t by omega) (Int.le_of_lt hd)
        omega
    have : -t=0 ∨ -t=1 := by omega
    rcases this with h | h
    · exact Or.inl (by rw [he,h,Int.mul_zero])
    · exact Or.inr (by rw [he,h,Int.mul_one])
  · rintro (rfl|rfl)
    · simp
    · exact ⟨-1, by grind⟩

/-- Iteration on the ambient basis (b,c), with C₀=2h and C₁=2k. -/
def orbit (h k x y : Int) : Nat → Int × Int
  | 0 => (x,y)
  | n+1 =>
    let p := orbit h k x y n
    (p.1-2*h*p.2, p.1+(1-2*k)*p.2)

/-- In the ambient lattice the second coordinate changes by n*x modulo two. -/
theorem orbit_parity (h k x y : Int) (n : Nat) :
    ∃ i j : Int, (orbit h k x y n).1 = x+2*i ∧
      (orbit h k x y n).2 = y+(n : Int)*x+2*j := by
  induction n with
  | zero => exact ⟨0,0,by simp [orbit],by simp [orbit]⟩
  | succ n ih =>
    obtain ⟨i,j,hi,hj⟩ := ih
    refine ⟨i-h*(orbit h k x y n).2, j+i-k*(orbit h k x y n).2, ?_, ?_⟩
    · simp only [orbit]; grind
    · simp only [orbit, Int.natCast_succ]; grind

/-- For f(2b)=0 and f(c)=t/2, every power of γ fixes f on X. Every
odd cyclotomic scalar acts identically on its values. -/
theorem surviving_character_equivariant (h k x y t w : Int) (n : Nat) :
    2 ∣ t*(orbit h k (2*x) y n).2 - (1+2*w)*(t*y) := by
  obtain ⟨i,j,_,hj⟩ := orbit_parity h k (2*x) y n
  exact ⟨t*((n : Int)*x+j-w*y), by rw [hj]; grind⟩

/-- On the prime-switching b, the discrepancy f((1−γⁿ)b) of a surviving
character has numerator n*t modulo two. -/
theorem discrepancy_at_power (h k t : Int) (n : Nat) :
    2 ∣ -t*(orbit h k 1 0 n).2 - (n : Int)*t := by
  obtain ⟨i,j,_,hj⟩ := orbit_parity h k 1 0 n
  exact ⟨-t*((n : Int)+j), by rw [hj]; grind⟩

/-- For discrepancies p/2,z/2 on σ,g, a single primitive y/(2*2^m)
is tested at the same denominator. The action of σ is +1. Multiplying
the g equation by the odd unit u clears its scalar u⁻¹. -/
def CommonPrimitive (u p z : Int) : Prop :=
  ∃ m : Nat, ∃ y : Int,
    2*twoPower m ∣ twoPower m*p ∧
    2*twoPower m ∣ (u-1)*y-u*twoPower m*z

theorem twoPower_pos (m : Nat) : 0 < twoPower m := by
  induction m with
  | zero => decide
  | succ m ih => unfold twoPower; omega

/-- The σ equation detects the class p/2 at every denominator. -/
theorem sigma_obstruction {u p z : Int} (hc : CommonPrimitive u p z) : 2 ∣ p := by
  obtain ⟨m,y,⟨t,ht⟩,_⟩ := hc
  exact ⟨t, Int.eq_of_mul_eq_mul_left (show twoPower m ≠ 0 by have := twoPower_pos m; omega)
    (show twoPower m*p = twoPower m*(2*t) by grind)⟩

/-- If v₂(u−1)=m, the explicit numerator u*z at denominator 2^(m+1)
solves the procyclic equation for any half-integral discrepancy. -/
theorem procyclic_primitive (u z : Int) (m : Nat) (hu : exactV (u-1) m) :
    2*twoPower m ∣ (u-1)*(u*z)-u*twoPower m*z := by
  obtain ⟨v,hv⟩ := hu
  exact ⟨v*u*z, by rw [hv]; grind⟩

/-- The two simultaneous equations discard exactly the nonzero value on 2b. -/
theorem common_primitive_iff (u p z : Int) (m : Nat) (hu : exactV (u-1) m) :
    CommonPrimitive u p z ↔ 2 ∣ p := by
  refine ⟨sigma_obstruction, ?_⟩
  rintro ⟨t,ht⟩
  exact ⟨m,u*z,⟨t,by rw [ht]; grind⟩, procyclic_primitive u z m hu⟩

theorem positive_weight_factorization (r : Nat) (hr : 0 < r) :
    ∃ j k : Nat, r = 2^j*(2*k+1) := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases h : r%2=1
    · exact ⟨0,r/2,by simp; omega⟩
    · obtain ⟨j,k,hk⟩ := ih (r/2) (by omega) (by omega)
      refine ⟨j+1,k,?_⟩
      calc
        r = 2*(r/2) := by omega
        _ = 2*(2^j*(2*k+1)) := by rw [hk]
        _ = 2^(j+1)*(2*k+1) := by rw [Nat.pow_succ]; grind

/-- At layer a and positive weight r, the multiplier on coefficients is
the inverse of the odd integer 5^(r*2^a). -/
theorem cyclotomic_common_primitive (a r : Nat) (hr : 0 < r) (p z : Int) :
    CommonPrimitive ((5 : Int)^(r*2^a)) p z ↔ 2 ∣ p := by
  have hn : 0 < r*2^a := Nat.mul_pos hr (Nat.pow_pos (by decide))
  obtain ⟨j,k,hk⟩ := positive_weight_factorization _ hn
  rw [hk]
  exact common_primitive_iff _ _ _ (j+2) (SampleSpacing.power_gap_at_zero j k)

/-- Coordinates in X of the difference b−γⁿb, in the basis (2b,c). -/
def switchCoordinates (h k : Int) (n : Nat) : Int × Int :=
  let image := orbit h k 1 0 n
  ((1-image.1)/2,-image.2)

theorem switch_coordinates_exact (h k : Int) (n : Nat) :
    2*(switchCoordinates h k n).1 = 1-(orbit h k 1 0 n).1 ∧
    (switchCoordinates h k n).2 = -(orbit h k 1 0 n).2 := by
  obtain ⟨i,j,hi,_⟩ := orbit_parity h k 1 0 n
  unfold switchCoordinates
  exact ⟨by dsimp; omega,rfl⟩

/-- Every power preserves X, so dividing its first coordinate by two gives
the coefficient of 2b. -/
theorem orbit_preserves_X (h k x y : Int) (n : Nat) :
    2*((orbit h k (2*x) y n).1/2) = (orbit h k (2*x) y n).1 := by
  obtain ⟨i,j,hi,_⟩ := orbit_parity h k (2*x) y n
  omega

/-- After imposing σ-equivariance, p and t are the half-numerators of
f(2b) and f(c). The first conjunct imposes g-equivariance on X. The second
tests one primitive for the two local discrepancy values. An odd unit and
its inverse both act as the identity on half-integral classes. -/
def LocalConditions (h k : Int) (a r : Nat) (p t : Fin 2) : Prop :=
  let n := 2^a
  let u : Int := 5^(r*n)
  let eval (x y : Int) := (p.val : Int)*x+(t.val : Int)*y
  (∀ x y : Int, let image := orbit h k (2*x) y n
    2 ∣ eval (image.1/2) image.2 - eval x y) ∧
  CommonPrimitive u (p.val : Int)
    (eval (switchCoordinates h k n).1 (switchCoordinates h k n).2)

/-- In the even-weight action model the strict coordinate pairs are exactly
(0,t). Positivity gives the nontrivial procyclic scalar; the parity of the
weight has already selected the identity action of σ in CommonPrimitive. -/
theorem even_local_conditions_iff (h k : Int) (a r : Nat) (hr : 0 < r) (p t : Fin 2) :
    LocalConditions h k a r p t ↔ p=0 := by
  constructor
  · intro hloc
    have hp := sigma_obstruction hloc.2
    have hir := p.isLt
    apply Fin.ext
    change p.val = 0
    obtain ⟨z,hz⟩ := hp
    omega
  · intro hp
    subst p
    refine ⟨?_, ?_⟩
    · intro x y
      simpa using surviving_character_equivariant h k x y (t.val : Int) 0 (2^a)
    · apply (cyclotomic_common_primitive a r hr _ _).mpr
      exact ⟨0,rfl⟩

/-- Projection to f(c) and t ↦ (0,t) are inverse on the coordinate solutions. -/
theorem even_solution_bijection (h k : Int) (a r : Nat) (hr : 0 < r) :
    let solutions := {pt : Fin 2 × Fin 2 // LocalConditions h k a r pt.1 pt.2}
    ∃ encode : solutions → Fin 2, ∃ decode : Fin 2 → solutions,
      (∀ pt, decode (encode pt) = pt) ∧ (∀ t, encode (decode t) = t) := by
  dsimp only
  refine ⟨fun pt => pt.val.2,
    fun t => ⟨(0,t),(even_local_conditions_iff h k a r hr 0 t).mpr rfl⟩, ?_, fun _ => rfl⟩
  rintro ⟨⟨p,t⟩,hp⟩
  have hz := (even_local_conditions_iff h k a r hr p t).mp hp
  subst p
  rfl

/-- In the bottom layer the surviving c-character can have a nonzero
g-discrepancy. From the first layer up that discrepancy already vanishes. -/
theorem discrepancy_by_layer (h k t : Int) :
    (2 ∣ t*(switchCoordinates h k 1).2-t) ∧
    (∀ a : Nat, 2 ∣ t*(switchCoordinates h k (2^(a+1))).2) := by
  constructor
  · simpa [switchCoordinates,Int.neg_mul,Int.mul_neg] using discrepancy_at_power h k t 1
  · intro a
    obtain ⟨v,hv⟩ := discrepancy_at_power h k t (2^(a+1))
    refine ⟨v+(2 : Int)^a*t, ?_⟩
    simp only [switchCoordinates, Nat.pow_succ, Int.natCast_mul, Int.natCast_pow] at *
    grind

end Reimann.DyadicEven
