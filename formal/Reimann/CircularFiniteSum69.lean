import Reimann.CircularRelationEval69
import Reimann.CircularBasis69

/-! The same power combination as a finite basis sum and as evaluation of
its rational coefficient sequence extended by zero. -/
namespace Reimann.CircularFiniteSum69

open Lean.Grind Lean.Grind.Field.NormNum CircularGauss69 CircularMonomial69
open CircularBasis69 CircularRelationEval69

def extendCoeffs {n : Nat} (v : Fin n → Rat) (k : Nat) : Rat :=
  if hk : k < n then v ⟨k, hk⟩ else 0

theorem extend_at {n : Nat} (v : Fin n → Rat) (j : Fin n) :
    extendCoeffs v j.val = v j := by simp [extendCoeffs, j.isLt]

theorem extend_bounded {n : Nat} (v : Fin n → Rat) : Bounded (extendCoeffs v) n := by
  intro k hk
  simp [extendCoeffs, Nat.not_lt.mpr hk]

theorem sumBelow_first {R : Type} [CommRing R] (f : Nat → R) (m : Nat) :
    sumBelow f (m+1) = f 0 + sumBelow (fun j => f (j+1)) m := by
  induction m with
  | zero => change 0 + f 0 = f 0 + 0; grind only
  | succ m ih =>
    change sumBelow f (m+1) + f (m+1) =
      f 0 + (sumBelow (fun j => f (j+1)) m + f (m+1))
    rw [ih]
    grind only

theorem sumBelow_eq_basisSum {R : Type} [CommRing R] (f : Nat → R) (n : Nat) :
    sumBelow f n = basisSum (fun i : Fin n => f i.val) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_first, basisSum_succ, ih (fun j => f (j+1))]
    rfl

theorem evalAt_extendCoeffs {R : Type} [Field R] (x : R) {n : Nat} (v : Fin n → Rat) :
    evalAt x (extendCoeffs v) n = basisSum (fun j : Fin n => ofRat (v j) * x^j.val) := by
  unfold evalAt
  rw [sumBelow_eq_basisSum]
  simp only [extend_at]

theorem evalAt_extendCoeffs_right {R : Type} [Field R] (x : R) {n : Nat} (v : Fin n → Rat) :
    evalAt x (extendCoeffs v) n = basisSum (fun j : Fin n => x^j.val * ofRat (v j)) := by
  simpa only [CommSemiring.mul_comm] using evalAt_extendCoeffs x v

theorem vanishes_extend_iff {R : Type} [Field R] (x : R) {n : Nat} (v : Fin n → Rat) :
    Vanishes x (extendCoeffs v) ↔ basisSum (fun j : Fin n => x^j.val * ofRat (v j)) = 0 := by
  constructor
  · intro hv
    rw [← evalAt_extendCoeffs_right]
    exact eval_of_vanishes x _ _ (extend_bounded v) hv
  · intro hv
    exact ⟨n, extend_bounded v, (evalAt_extendCoeffs_right x v).trans hv⟩

end Reimann.CircularFiniteSum69
