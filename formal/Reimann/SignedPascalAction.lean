import Reimann.CoinvariantSupport
import Reimann.SignedSeriesMap
import Reimann.SignedCyclicAction

/-! Taylor expansion of every cyclic group basis element at X=1. -/
namespace Reimann.SignedPascalAction

open Reimann.CoinvariantSupport (binomial binomial_zero_column)
open Reimann.SignedSeriesMap (partialAction delay Coeffs Row)

/-- Binomial coefficients reduced to the six-bit coefficient ring. -/
def weights (j : Nat) : Coeffs := fun k => BitVec.ofNat 6 (binomial j k)

theorem weights_succ (j : Nat) : weights (j+1) = fun k => weights j k + delay (weights j) k := by
  funext k
  cases k with
  | zero => simp [weights, delay, binomial_zero_column]
  | succ k =>
    change BitVec.ofNat 6 (binomial j k + binomial j (k+1)) = _
    rw [BitVec.ofNat_add, BitVec.add_comm]
    rfl

theorem constant_action (p : Nat → Row) (n : Nat) (i : Fin 64) :
    partialAction (weights 0) p (n+1) i = p 0 i := by
  induction n with
  | zero => simp [partialAction, weights, binomial]
  | succ n ih =>
    change partialAction (weights 0) p (n+1) i + 0 * p (n+1) i = _
    rw [ih]; simp

/-- The Pascal recurrence shifts the row by one X after rarefying the
endpoint with the vanishing of power 224. -/
theorem successor_action (p : Nat → Row) (hz : ∀ i, p 224 i = 0)
    (hs : ∀ k j, p (k+1) j = p k (j-1) - p k j) (n : Nat) (i : Fin 64) :
    partialAction (weights (n+1)) p 224 i = partialAction (weights n) p 224 (i-1) := by
  rw [weights_succ, SignedSeriesMap.partial_add, SignedSeriesMap.truncated_delay (weights n) p hz hs]
  grind

theorem index_wrap (j : Nat) (i : Fin 64) : j%64 = (i-1).val ↔ (j+1)%64 = i.val := by
  rw [Fin.val_sub]
  change j%64 = (63+i.val)%64 ↔ (j+1)%64 = i.val
  omega

/-- The truncated Taylor expansion of Xʲ is the individual group basis
row indexed by j modulo 64. -/
theorem binomial_action_of_powers (p : Nat → Row)
    (h0 : ∀ i, p 0 i = if i.val=0 then 1 else 0) (hz : ∀ i, p 224 i=0)
    (hs : ∀ k j, p (k+1) j = p k (j-1) - p k j) (j : Nat) (i : Fin 64) :
    partialAction (weights j) p 224 i = if j%64=i.val then 1 else 0 := by
  induction j generalizing i with
  | zero =>
    change partialAction (weights 0) p (223+1) i = if 0=i.val then 1 else 0
    rw [constant_action, h0]
    simp only [eq_comm (a := i.val)]
  | succ j ih =>
    rw [successor_action p hz hs, ih]
    simp only [index_wrap]

/-- Reconstruction of each Xʲ in the actual cyclic coefficient ring. -/
theorem binomial_action (j : Nat) (i : Fin 64) :
    partialAction (fun k => BitVec.ofNat 6 (binomial j k))
      (fun k => SignedCyclicAction.iterate k SignedCyclicAction.delta) 224 i =
      if j%64=i.val then 1 else 0 := by
  apply binomial_action_of_powers
  · intro a
    change (if a=0 then (1 : BitVec 6) else 0) = if a.val=0 then 1 else 0
    by_cases h : a=0
    · subst a; decide
    · have hval : a.val ≠ 0 := fun ha => h (Fin.ext ha)
      simp [h, hval]
  · exact congrFun (SignedCyclicAction.iterate_224 SignedCyclicAction.delta)
  · intro k a
    rfl

end Reimann.SignedPascalAction
