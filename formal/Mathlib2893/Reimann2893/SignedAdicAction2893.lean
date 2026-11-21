import Reimann2893.SignedNormLimit2893
import Reimann.DyadicLattice
import Mathlib.Algebra.Group.End

/-! A coherent dyadic exponent acts on a norm limit whenever its level-n
generator has period dividing 2^n. This is the algebraic action. -/
namespace Reimann.SignedAdicAction2893

open DyadicLattice (Scalar)

def exponent (z : Scalar) : ℕ → ℕ
  | 0 => 0
  | n+1 => (z.residue n).toNat

theorem exponent_step (z : Scalar) (n : ℕ) : exponent z (n+1) % 2^n = exponent z n := by
  cases n with
  | zero => exact Nat.mod_one _
  | succ n =>
    have h := congrArg BitVec.toNat (z.reduce (i:=n) (j:=n+1) (by omega))
    simpa only [BitVec.toNat_setWidth, exponent] using h

theorem exponent_nat (k n : ℕ) : exponent (DyadicLattice.natScalar k) n = k % 2^n := by
  cases n with
  | zero => exact (Nat.mod_one k).symm
  | succ n => simp [exponent, DyadicLattice.natScalar, BitVec.toNat_ofNat]

theorem exponent_add (x y : Scalar) (n : ℕ) :
    exponent (DyadicLattice.add x y) n = (exponent x n + exponent y n) % 2^n := by
  cases n <;> simp [exponent, DyadicLattice.add, BitVec.toNat_add]

universe u v
variable {A : Type u} [Group A] {B : Type v} [Group B]

def iterate (g : A ≃* A) : ℕ → A ≃* A
  | 0 => MulEquiv.refl A
  | n+1 => (iterate g n).trans g

theorem iterate_eq_pow_apply (g : A ≃* A) (n : ℕ) (x : A) : iterate g n x = (g ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    exact congrArg g ih

theorem iterate_add (g : A ≃* A) (a b : ℕ) (x : A) :
    iterate g (a+b) x = iterate g b (iterate g a x) := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg g ih

theorem iterate_multiple (g : A ≃* A) (m : ℕ) (p : ∀ x, iterate g m x = x)
    (t : ℕ) (x : A) : iterate g (m*t) x = x := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Nat.mul_succ, iterate_add, p, ih]

theorem iterate_mod (g : A ≃* A) (m : ℕ) (p : ∀ x, iterate g m x = x)
    (k : ℕ) (x : A) : iterate g k x = iterate g (k%m) x := by
  calc
    iterate g k x = iterate g (k%m+m*(k/m)) x := congrArg (fun i => iterate g i x) (Nat.mod_add_div k m).symm
    _ = _ := by rw [iterate_add, iterate_multiple g m p]

theorem iterate_natural (f : A →* B) (g : A ≃* A) (h : B ≃* B)
    (c : ∀ x, f (g x) = h (f x)) (k : ℕ) (x : A) :
    f (iterate g k x) = iterate h k (f x) := by
  induction k with
  | zero => rfl
  | succ k ih => exact (c _).trans (congrArg h ih)

variable {G : ℕ → Type u} [∀ n, Group (G n)]
variable (N : ∀ n, G (n+1) →* G n) (γ : ∀ n, G n ≃* G n)
  (comm : ∀ n x, N n (γ (n+1) x) = γ n (N n x))
  (period : ∀ n x, iterate (γ n) (2^n) x = x)

include comm period in
theorem exponent_compatible (z : Scalar) (n : ℕ) (x : G (n+1)) :
    N n (iterate (γ (n+1)) (exponent z (n+1)) x) = iterate (γ n) (exponent z n) (N n x) := by
  rw [iterate_natural (N n) (γ (n+1)) (γ n) (comm n), iterate_mod (γ n) (2^n) (period n)
    (exponent z (n+1)), exponent_step]

def act (z : Scalar) : SignedNormLimit2893.coherent N ≃* SignedNormLimit2893.coherent N :=
  SignedNormLimit2893.forward N (fun n => iterate (γ n) (exponent z n))
    (exponent_compatible N γ comm period z)

theorem act_nat (k : ℕ) (x : SignedNormLimit2893.coherent N) (n : ℕ) :
    (act N γ comm period (DyadicLattice.natScalar k) x).val n = iterate (γ n) k (x.val n) := by
  change iterate (γ n) (exponent _ n) _ = _
  rw [exponent_nat, ← iterate_mod (γ n) (2^n) (period n) k]

theorem act_one (x : SignedNormLimit2893.coherent N) :
    act N γ comm period (DyadicLattice.natScalar 1) x = SignedNormLimit2893.forward N γ comm x :=
  Subtype.ext (funext fun n => act_nat N γ comm period 1 x n)

theorem act_add (z w : Scalar) (x : SignedNormLimit2893.coherent N) :
    act N γ comm period (DyadicLattice.add z w) x = act N γ comm period w (act N γ comm period z x) := by
  apply Subtype.ext
  funext n
  change iterate (γ n) (exponent _ n) (x.val n) =
    iterate (γ n) (exponent w n) (iterate (γ n) (exponent z n) (x.val n))
  rw [exponent_add, ← iterate_mod (γ n) (2^n) (period n) (exponent z n + exponent w n), iterate_add]

end Reimann.SignedAdicAction2893
