import Reimann.SignedProjection

/-! Integral comparison of the negative first moment and the cleared literal
Bernoulli coefficient on an opposite pair and on an entire character fibre. -/
namespace Reimann.SignedBernoulliPairing

open Reimann.SignedProjection

/-- The summand of the negative weighted first moment. -/
def rawTerm (g : Nat → Int) (a : Nat) : Int := -(a:Int)*g a

/-- The numerator of the literal coefficient -B₁(a/M), cleared by 2M. -/
def literalTerm (g : Nat → Int) (M a : Nat) : Int := ((M:Int)-2*(a:Int))*g a

def rawPair (g : Nat → Int) (M a : Nat) : Int := rawTerm g a + rawTerm g (M-a)

def literalPair (g : Nat → Int) (M a : Nat) : Int :=
  literalTerm g M a + literalTerm g M (M-a)

theorem raw_pair (g : Nat → Int) (M a : Nat) (bound : a ≤ M)
    (opposite : g (M-a) = -g a) : rawPair g M a = ((M:Int)-2*(a:Int))*g a := by
  simp only [rawPair, rawTerm, opposite, Int.natCast_sub bound]
  grind

theorem literal_pair (g : Nat → Int) (M a : Nat) (bound : a ≤ M)
    (opposite : g (M-a) = -g a) : literalPair g M a = 2*rawPair g M a := by
  rw [raw_pair g M a bound opposite]
  simp only [literalPair, literalTerm, opposite, Int.natCast_sub bound]
  grind

def rawFibre (g : Nat → Int) (t D m : Nat) : Int :=
  total (fun k => rawPair g (D*m) (t+D*k)) m

def literalFibre (g : Nat → Int) (t D m : Nat) : Int :=
  total (fun k => literalPair g (D*m) (t+D*k)) m

theorem total_congr (f h : Nat → Int) (m : Nat)
    (same : ∀ k, k < m → f k = h k) : total f m = total h m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [total]
    rw [ih (fun k hk => same k (by omega)), same m (by omega)]

theorem raw_fibre_normalization (g f : Nat → Int) (t D m : Nat) (c : Int)
    (bound : ∀ k, k < m → t+D*k ≤ D*m)
    (onFibre : ∀ k, k < m → g (t+D*k) = f k)
    (opposite : ∀ k, k < m → g (D*m-(t+D*k)) = -g (t+D*k))
    (zeroSum : total f m = 0) (momentEq : -moment f m = (m:Int)*c) :
    rawFibre g t D m = 2*((D*m:Nat):Int)*c := by
  have eqn := paired_normalization f m (t:Int) (D:Int) c zeroSum momentEq
  rw [Int.natCast_mul]
  refine Eq.trans (total_congr _ _ m ?_) eqn
  intro k hk
  rw [raw_pair _ _ _ (bound k hk) (opposite k hk), onFibre k hk]
  simp only [Int.natCast_mul, Int.natCast_add]
  grind

theorem literal_fibre (g : Nat → Int) (t D m : Nat)
    (bound : ∀ k, k < m → t+D*k ≤ D*m)
    (opposite : ∀ k, k < m → g (D*m-(t+D*k)) = -g (t+D*k)) :
    literalFibre g t D m = 2*rawFibre g t D m := by
  let p := fun k => rawPair g (D*m) (t+D*k)
  have eqn := total_affine p p 2 0 m
  calc
    literalFibre g t D m = total (fun k => 2*p k + 0*p k) m := by
      apply total_congr
      intro k hk
      rw [literal_pair _ _ _ (bound k hk) (opposite k hk)]
      simp [p]
    _ = 2*rawFibre g t D m := by simpa [p, rawFibre] using eqn

/-- For a zero-sum block, both normalization factors hold integrally. -/
theorem fibre_normalization (g f : Nat → Int) (t D m : Nat) (c : Int)
    (bound : ∀ k, k < m → t+D*k ≤ D*m)
    (onFibre : ∀ k, k < m → g (t+D*k) = f k)
    (opposite : ∀ k, k < m → g (D*m-(t+D*k)) = -g (t+D*k))
    (zeroSum : total f m = 0) (momentEq : -moment f m = (m:Int)*c) :
    rawFibre g t D m = 2*((D*m:Nat):Int)*c ∧
      literalFibre g t D m = 4*((D*m:Nat):Int)*c := by
  have h := raw_fibre_normalization g f t D m c bound onFibre opposite zeroSum momentEq
  refine ⟨h, ?_⟩
  rw [literal_fibre g t D m bound opposite, h]
  grind

end Reimann.SignedBernoulliPairing
