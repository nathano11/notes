import Reimann.CircularMonomial69

/-! A least monic relation divides every vanishing polynomial. The proof
keeps the quotient monic and exposes its degree for the factor obstruction. -/

namespace Reimann.CircularLeastRelation69

open CircularMonomial69 CircularGauss69

def MonicRelation (V : (Nat → Rat) → Prop) (n : Nat) : Prop :=
  ∃ p, Bounded p (n+1) ∧ p n = 1 ∧ V p

theorem least_remainder_zero (V : (Nat → Rat) → Prop) (d : Nat)
    (least : ∀ i < d, ¬ MonicRelation V i)
    (normalize : ∀ p m, Bounded p m → V p → (∃ k, p k ≠ 0) →
      ∃ i < m, MonicRelation V i)
    (r : Nat → Rat) (hr : Bounded r d) (hv : V r) : ∀ k, r k = 0 := by
  intro k
  apply Classical.byContradiction
  intro h
  obtain ⟨i,hi,hm⟩ := normalize r d hr hv ⟨k,h⟩
  exact least i hi hm

theorem least_relation_factor (P D : Nat → Rat) (N d : Nat) (hd : d ≤ N)
    (hP : Bounded P (N+1)) (hPm : P N = 1) (hD : Bounded D (d+1)) (hDm : D d = 1)
    (V : (Nat → Rat) → Prop) (hPV : V P)
    (closed : ∀ f s a, V f → V (fun k => f k - shift s a D k))
    (least : ∀ i < d, ¬ MonicRelation V i)
    (normalize : ∀ p m, Bounded p m → V p → (∃ k, p k ≠ 0) →
      ∃ i < m, MonicRelation V i) :
    ∃ q, Bounded q ((N-d)+1) ∧ q (N-d) = 1 ∧ ∀ k, convolution q D k = P k := by
  obtain ⟨q,r,hq,hr,hrv,he⟩ := division_preserving D d hD hDm V closed (N+1) P hP hPV
  have hq' : Bounded q ((N-d)+1) := by rwa [show (N-d)+1 = N+1-d by omega]
  have hz := least_remainder_zero V d least normalize r hr hrv
  have hprod : ∀ k, convolution q D k = P k := by
    intro k; have h := he k; rw [hz k, Rat.add_zero] at h; exact h.symm
  refine ⟨q,hq',?_,hprod⟩
  have htop := top_convolution q D (N-d) d hq' hD
  rw [show N-d+d=N by omega, hprod N, hPm, hDm, Rat.mul_one] at htop
  exact htop.symm

/-- A polynomial with no proper monic split admits no shorter monic
relation, provided constants are faithful and vanishing survives division. -/
theorem no_shorter_than_irreducible (P : Nat → Rat) (N : Nat)
    (hP : Bounded P (N+1)) (hPm : P N = 1) (V : (Nat → Rat) → Prop) (hPV : V P)
    (constant : ¬ MonicRelation V 0)
    (closed : ∀ f D s a, V f → V D → V (fun k => f k - shift s a D k))
    (normalize : ∀ p m, Bounded p m → V p → (∃ k, p k ≠ 0) →
      ∃ i < m, MonicRelation V i)
    (noSplit : ∀ d e, 0 < d → 0 < e → d+e = N → ∀ q D,
      Bounded q (e+1) → Bounded D (d+1) → q e = 1 → D d = 1 →
      (∀ k, convolution q D k = P k) → False)
    (i : Nat) (hi : i < N) : ¬ MonicRelation V i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro h
    obtain ⟨D,hD,hDm,hDV⟩ := h
    have pos : 0 < i := by
      by_cases hz : i = 0
      · subst i; exact False.elim (constant ⟨D,hD,hDm,hDV⟩)
      · omega
    have least : ∀ j < i, ¬ MonicRelation V j := by
      intro j hj; exact ih j hj (by omega)
    obtain ⟨q,hq,hqm,hprod⟩ := least_relation_factor P D N i (by omega) hP hPm hD hDm
      V hPV (fun f s a hv => closed f D s a hv hDV) least normalize
    exact noSplit i (N-i) pos (by omega) (by omega) q D hq hD hqm hDm hprod

end Reimann.CircularLeastRelation69
