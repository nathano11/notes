import Reimann.DyadicLattice

/-! Coordinates in the inverse limit of the cyclic group rings of order
2^n over the coherent 2-adic integers. X rotates a coefficient row. -/
namespace Reimann.SignedCompletedAction

open Reimann.DyadicLattice

/-- The lower-index lift of a group element to the next cyclic level. -/
def low {n : Nat} (i : Fin (2^n)) : Fin (2^(n+1)) :=
  ⟨i.val, by have h := i.isLt; rw [Nat.pow_succ]; omega⟩

def high {n : Nat} (i : Fin (2^n)) : Fin (2^(n+1)) :=
  ⟨i.val+2^n, by have h := i.isLt; rw [Nat.pow_succ]; omega⟩

/-- The input coordinate that contributes to this coordinate after multiplication by X. -/
def prev {m : Nat} (i : Fin m) : Fin m :=
  ⟨if i.val=0 then m-1 else i.val-1, by have h := i.isLt; split <;> omega⟩

/-- Away from index zero, rotation preserves the two lifts. At index zero it interchanges them. -/
theorem prev_children {n : Nat} (i : Fin (2^n)) :
    (prev (low i) = low (prev i) ∧ prev (high i) = high (prev i)) ∨
    (prev (low i) = high (prev i) ∧ prev (high i) = low (prev i)) := by
  have p : 0 < 2^n := Nat.pow_pos (by decide)
  have hi := i.isLt
  by_cases hz : i.val=0
  · right
    constructor <;> apply Fin.ext <;> simp [low, high, prev, hz, Nat.pow_succ] <;> omega
  · left
    constructor <;> apply Fin.ext <;> simp [low, high, prev, hz, Nat.pow_succ] <;> omega

/-- A distribution with 2-adic coefficients in inverse-generator coordinates. -/
structure Tower where
  coeff (n : Nat) : Fin (2^n) → Scalar
  compatible {n : Nat} (i : Fin (2^n)) :
    coeff n i = add (coeff (n+1) (low i)) (coeff (n+1) (high i))

def rotate (u : Tower) : Tower where
  coeff n i := u.coeff n (prev i)
  compatible i := by
    rw [u.compatible (prev i)]
    rcases prev_children i with ⟨h,k⟩ | ⟨h,k⟩
    · rw [h,k]
    · rw [h,k]
      apply scalar_ext
      intro j
      apply BitVec.add_comm

def plus (u v : Tower) : Tower where
  coeff n i := add (u.coeff n i) (v.coeff n i)
  compatible i := by
    rw [u.compatible i, v.compatible i]
    apply scalar_ext
    intro j
    simp only [add]
    grind

def scale (a : Scalar) (u : Tower) : Tower where
  coeff n i := mul a (u.coeff n i)
  compatible i := by
    rw [u.compatible i]
    apply scalar_ext
    intro j
    exact BitVec.mul_add ..

/-- The same integer reduced compatibly at every coefficient precision. -/
def integer (a : Int) : Scalar where
  residue n := BitVec.ofInt (n+1) a
  reduce h := by
    cases a with
    | ofNat v => exact BitVec.setWidth_ofNat_of_le (by omega) v
    | negSucc v =>
      have eqNeg (n : Nat) : BitVec.ofInt n (.negSucc v) = -(BitVec.ofNat n (v+1)) := by
        change BitVec.ofInt n (-((v+1 : Nat) : Int)) = _
        rw [BitVec.ofInt_neg]
        rfl
      rw [eqNeg, eqNeg, BitVec.setWidth_neg_of_le (by omega), BitVec.setWidth_ofNat_of_le (by omega)]

theorem integer_add (a b : Int) : integer (a+b) = add (integer a) (integer b) := by
  apply scalar_ext
  intro n
  exact BitVec.ofInt_add a b

/-- Multiplication by Q(X−1) for the monic quadratic Q(T)=T²+c1·T+c0. -/
def quadraticAction (c0 c1 : Scalar) (u : Tower) : Tower :=
  plus (plus (scale (add (add (integer 1) c0) (neg c1)) u)
      (scale (add c1 (integer (-2))) (rotate u))) (rotate (rotate u))

/-- Coefficient precision 64 at the quotient of cyclic order 64. -/
def coordinate (u : Tower) (i : Fin 64) : BitVec 6 := (u.coeff 6 i).residue 5

theorem prev_six : ∀ i : Fin 64, prev i = i-1 ∧ prev (prev i) = i-2 := by decide

theorem project_quadratic (c0 c1 : Scalar) (u : Tower) (i : Fin 64) :
    coordinate (quadraticAction c0 c1 u) i =
      (1+c0.residue 5-c1.residue 5)*coordinate u i +
      (c1.residue 5-2)*coordinate u (i-1) + coordinate u (i-2) := by
  obtain ⟨hi, hj⟩ := prev_six i
  change (1+c0.residue 5 + -c1.residue 5) * (u.coeff 6 i).residue 5 +
      (c1.residue 5 + -2)*(u.coeff 6 (prev i)).residue 5 +
      (u.coeff 6 (prev (prev i))).residue 5 = _
  rw [hi, show prev (i-1) = i-2 by rw [← hi]; exact hj]
  unfold coordinate
  grind

end Reimann.SignedCompletedAction
