import Reimann.TameSplitting277
import Reimann.TameOrderReduction277

namespace Reimann.TameArithmetic277

open Reimann.TameSplitting277

/-- The basis 1, X, Y, XY of the order Z[X,Y]/(X²+3,Y²+23).
Coordinates are grouped as (a+bX)+(c+dX)Y. -/
abbrev OrderCoordinates := (Int × Int) × (Int × Int)

def evalAt (x y : Int) (v : OrderCoordinates) : Int :=
  (v.1.1+v.1.2*x)+(v.2.1+v.2.2*x)*y

theorem eval_congr (m x x' y y' : Int) (v : OrderCoordinates)
    (hx : m ∣ x'-x) (hy : m ∣ y'-y) :
    m ∣ evalAt x' y' v-evalAt x y v := by
  obtain ⟨dx,hx⟩ := hx
  obtain ⟨dy,hy⟩ := hy
  refine ⟨dx*(v.1.2+v.2.2*y')+dy*(v.2.1+v.2.2*x), ?_⟩
  unfold evalAt
  grind

def rootAt (negative : Bool) (a x d : Int) (n : Nat) : Int :=
  if negative then -(liftPair a x d n).1 else (liftPair a x d n).1

theorem rootAt_compatible (negative : Bool) (a x d : Int) (n : Nat)
    (h : SignedLevel a x d n) :
    (277 : Int)^(n+1) ∣ rootAt negative a x d (n+1)-rootAt negative a x d n := by
  cases negative with
  | false => exact h.positiveCompatible
  | true => exact h.negativeCompatible

def branchEval (sx sy : Bool) (n : Nat) (v : OrderCoordinates) : Int :=
  evalAt (rootAt sx (-3) 44 85 n) (rootAt sy (-23) 114 130 n) v

theorem branchEval_compatible (sx sy : Bool) (n : Nat) (v : OrderCoordinates) :
    (277 : Int)^(n+1) ∣ branchEval sx sy (n+1) v-branchEval sx sy n v :=
  eval_congr _ _ _ _ _ v
    (rootAt_compatible sx _ _ _ n (split_both_277 n).1)
    (rootAt_compatible sy _ _ _ n (split_both_277 n).2)

def integerCoordinates (z : Int) : OrderCoordinates := ((z,0),(0,0))

theorem branchEval_integer (sx sy : Bool) (n : Nat) (z : Int) :
    branchEval sx sy n (integerCoordinates z) = z := by
  simp [branchEval,evalAt,integerCoordinates]

theorem all_depths_first_residue (sx sy : Bool) (n : Nat) (v : OrderCoordinates) :
    (277 : Int) ∣ branchEval sx sy n v-branchEval sx sy 0 v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : (277 : Int) ∣ (277 : Int)^(n+1) :=
      ⟨277^n, by rw [Int.pow_succ, Int.mul_comm]⟩
    obtain ⟨k,hk⟩ := Int.dvd_trans hd (branchEval_compatible sx sy n v)
    obtain ⟨j,hj⟩ := ih
    exact ⟨k+j, by grind⟩

def coordinate (sx sy : Bool) (v : (R × R) × (R × R)) : R :=
  let xs := if sx then v.2 else v.1
  if sy then xs.2 else xs.1

theorem first_roots (sx sy : Bool) :
    branchEval sx sy 0 ((0,1),(0,0)) = (if sx then -44 else 44) ∧
    branchEval sx sy 0 ((0,0),(1,0)) = (if sy then -114 else 114) := by
  cases sx <;> cases sy <;> decide

/-- Two linear polynomials already distinguish the four kernels modulo 277. -/
theorem kernel_detects_signs (sx sy : Bool) :
    ((277 : Int) ∣ branchEval sx sy 0 ((-44,1),(0,0)) ↔ sx = false) ∧
    ((277 : Int) ∣ branchEval sx sy 0 ((-114,0),(1,0)) ↔ sy = false) := by
  cases sx <;> cases sy <;> decide +kernel

open Reimann.TameBiquadratic277 Reimann.TameOrderReduction277 Fin.IntCast Lean.Grind

theorem bridge (sx sy : Bool) (n : Nat) (v : OrderCoordinates) :
    coordinate sx sy ((finite_splitting277 n).evaluate (reduce n v)) =
      ((branchEval sx sy n v : Int) : Residue n) := by
  cases sx <;> cases sy <;>
    simp only [coordinate,finite_splitting277,splittingOfRoots,fourEval,pairEval,
      reduce,branchEval,evalAt,rootAt,liftedRoot,Bool.false_eq_true,if_false,if_true,
      Ring.intCast_add,Ring.intCast_mul,Ring.intCast_neg] <;> grind

theorem finite_multiple_test (n : Nat) (a : Int) :
    (∃ k : Residue n, (a : Residue n) = 277*k) ↔ (277 : Int) ∣ a := by
  constructor
  · rintro ⟨k,h⟩
    have hk : (a : Residue n) = ((277*(k.val : Int) : Int) : Residue n) := by
      rw [Ring.intCast_mul, cast_val]
      exact h
    obtain ⟨w,hw⟩ := (cast_eq_iff n _ _).mp hk
    refine ⟨(k.val : Int)+277^n*w, ?_⟩
    rw [Int.pow_succ] at hw
    grind
  · rintro ⟨k,rfl⟩
    exact ⟨(k : Residue n), by rw [Ring.intCast_mul]; rfl⟩

theorem same_prime_every_depth (sx sy : Bool) (n : Nat) (v : OrderCoordinates) :
    (∃ k : Residue n, coordinate sx sy ((finite_splitting277 n).evaluate (reduce n v)) = 277*k)
      ↔ (277 : Int) ∣ branchEval sx sy 0 v := by
  rw [bridge, finite_multiple_test]
  obtain ⟨e,he⟩ := all_depths_first_residue sx sy n v
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a-e, by grind⟩
  · rintro ⟨a,ha⟩
    exact ⟨a+e, by grind⟩

end Reimann.TameArithmetic277
