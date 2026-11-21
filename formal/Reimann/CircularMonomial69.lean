import Reimann.CircularConvolution69

/-! Coefficient division by a monic rational polynomial, retaining strict degree bounds. -/

namespace Reimann.CircularMonomial69

open Reimann.CircularGauss69

def Bounded (p : Nat → Rat) (m : Nat) : Prop := ∀ i, m ≤ i → p i = 0

def atom (s : Nat) (a : Rat) (i : Nat) : Rat := if i = s then a else 0

def shift (s : Nat) (a : Rat) (p : Nat → Rat) (k : Nat) : Rat :=
  if s ≤ k then a * p (k - s) else 0

theorem sum_congr (f g : Nat → Rat) (m : Nat) (h : ∀ i, i < m → f i = g i) :
    sumBelow f m = sumBelow g m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [sumBelow, sumBelow, ih (by intro i hi; exact h i (by omega)), h m (by omega)]

theorem sum_zero (m : Nat) : sumBelow (fun _ => (0 : Rat)) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [sumBelow, ih, Rat.zero_add]

theorem sum_add (f g : Nat → Rat) (m : Nat) :
    sumBelow (fun i => f i + g i) m = sumBelow f m + sumBelow g m := by
  induction m with
  | zero => exact (Rat.zero_add 0).symm
  | succ m ih => simp only [sumBelow, ih]; grind

theorem sum_single (s : Nat) (a : Rat) (m : Nat) :
    sumBelow (atom s a) m = if s < m then a else 0 := by
  induction m with
  | zero => simp [sumBelow]
  | succ m ih =>
    simp only [sumBelow, ih, atom]
    split <;> split <;> split <;> grind

theorem convolution_zero (p : Nat → Rat) (k : Nat) :
    convolution (fun _ => 0) p k = 0 := by
  simpa only [convolution, Rat.zero_mul] using sum_zero (k+1)

theorem convolution_add (u v p : Nat → Rat) (k : Nat) :
    convolution (fun i => u i + v i) p k = convolution u p k + convolution v p k := by
  simp only [convolution, Rat.add_mul, sum_add]

theorem convolution_atom (s : Nat) (a : Rat) (p : Nat → Rat) (k : Nat) :
    convolution (atom s a) p k = shift s a p k := by
  unfold convolution
  calc
    _ = sumBelow (atom s (a * p (k-s))) (k+1) := by
      apply sum_congr
      intro i _
      by_cases h : i = s
      · subst i; simp [atom]
      · simp [atom, h, Rat.zero_mul]
    _ = _ := by rw [sum_single]; simp [shift, Nat.lt_succ_iff]

theorem eliminate_top (p D : Nat → Rat) (n d : Nat)
    (hd : d ≤ n) (hp : Bounded p (n+1)) (hD : Bounded D (d+1)) (hm : D d = 1) :
    Bounded (fun k => p k - shift (n-d) (p n) D k) n := by
  intro k hk
  have hsk : n-d ≤ k := by omega
  simp only [shift, hsk, ite_true]
  by_cases he : k = n
  · subst k; rw [show n - (n-d) = d by omega, hm, Rat.mul_one, Rat.sub_self]
  · rw [hp k (by omega), hD _ (by omega), Rat.mul_zero, Rat.sub_self]

/-- Long division preserves any property stable under subtracting a shifted
multiple of the divisor. Both the quotient and remainder have degree bounds. -/
theorem division_preserving (D : Nat → Rat) (d : Nat) (hD : Bounded D (d+1)) (hm : D d = 1)
    (V : (Nat → Rat) → Prop) (closed : ∀ f s a, V f → V (fun k => f k - shift s a D k))
    (m : Nat) (p : Nat → Rat) (hp : Bounded p m) (hv : V p) :
    ∃ q r : Nat → Rat, Bounded q (m-d) ∧ Bounded r d ∧ V r ∧
      ∀ k, p k = convolution q D k + r k := by
  induction m generalizing p with
  | zero =>
    refine ⟨fun _ => 0, p, fun _ _ => rfl, fun i _ => hp i (by omega), hv, ?_⟩
    intro k; rw [convolution_zero, Rat.zero_add]
  | succ n ih =>
    by_cases hd : d ≤ n
    · let rem := fun k => p k - shift (n-d) (p n) D k
      obtain ⟨q,r,hq,hr,hrv,he⟩ := ih rem (eliminate_top p D n d hd hp hD hm) (closed p _ _ hv)
      refine ⟨fun k => q k + atom (n-d) (p n) k, r, ?_, hr, hrv, ?_⟩
      · intro k hk; have hne : k ≠ n-d := by omega
        change q k + atom (n-d) (p n) k = 0
        rw [hq k (by omega)]; simp [atom, hne, Rat.zero_add]
      · intro k; rw [convolution_add, convolution_atom]
        have h := he k
        unfold rem at h
        grind
    · refine ⟨fun _ => 0, p, fun _ _ => rfl, fun i hi => hp i (by omega), hv, ?_⟩
      intro k; rw [convolution_zero, Rat.zero_add]

theorem top_convolution (q D : Nat → Rat) (e d : Nat) (hq : Bounded q (e+1))
    (hD : Bounded D (d+1)) : convolution q D (e+d) = q e * D d := by
  unfold convolution
  calc
    _ = sumBelow (atom e (q e * D d)) (e+d+1) := by
      apply sum_congr
      intro i _
      by_cases he : i = e
      · subst i; simp [atom]
      · simp only [atom, he, ite_false]
        by_cases hi : i < e
        · rw [hD _ (by omega), Rat.mul_zero]
        · rw [hq _ (by omega), Rat.zero_mul]
    _ = _ := by simp [sum_single, show e < e+d+1 by omega]

end Reimann.CircularMonomial69
