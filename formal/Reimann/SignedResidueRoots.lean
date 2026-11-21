import Reimann.SignedAdicRoots
import Reimann.DyadicBottom

/-! From the two six-bit coefficient residues directly to the simultaneous
factorization for all signed inputs in the inverse limit. -/
namespace Reimann.SignedResidueRoots

open Reimann.DyadicLattice
open Reimann.DyadicBottom (halfShift double_halfShift)

theorem linear_half (c1 : Scalar) (h1 : c1.residue 5=18) :
    add (halfShift c1) (halfShift c1) = c1 ∧ (halfShift c1).residue 1=1 := by
  have hb : c1.residue 0=0 := by
    rw [←c1.reduce (i:=0) (j:=5) (by decide), h1]
    decide
  refine ⟨double_halfShift _ hb, ?_⟩
  change (c1.residue 2).extractLsb' 1 2 = 1
  rw [←c1.reduce (i:=2) (j:=5) (by decide), h1]
  decide

theorem constant_quarter (c0 : Scalar) (h0 : c0.residue 5=40) :
    let c := halfShift (halfShift c0)
    add (add c c) (add c c) = c0 ∧ c.residue 1=2 := by
  have even : c0.residue 0=0 := by
    rw [←c0.reduce (i:=0) (j:=5) (by decide), h0]
    decide
  have twiceEven : (halfShift c0).residue 0=0 := by
    change (c0.residue 1).extractLsb' 1 1 = 0
    rw [←c0.reduce (i:=1) (j:=5) (by decide), h0]
    decide
  constructor
  · rw [double_halfShift _ twiceEven, double_halfShift _ even]
  · change ((c0.residue 3).extractLsb' 1 3).extractLsb' 1 2 = 2
    rw [←c0.reduce (i:=3) (j:=5) (by decide), h0]
    decide

/-- The same two labelled coherent roots factor every specialization of the
homogeneous polynomial belonging to these actual coefficients. -/
theorem factorization_of_six_bits (c0 c1 : Scalar) (h0 : c0.residue 5=40) (h1 : c1.residue 5=18) :
    ∃ R S : Scalar, R.residue 2=4 ∧ S.residue 2=2 ∧ ∀ s a : Scalar,
      let x := add s (neg a)
      add (add (mul x x) (mul (mul c1 a) x)) (mul (mul c0 a) a) =
        mul (add x (neg (mul a R))) (add x (neg (mul a S))) := by
  obtain ⟨hc0, hc⟩ := constant_quarter c0 h0
  obtain ⟨hc1, hb⟩ := linear_half c1 h1
  obtain ⟨R,S,hR,hS,eqn⟩ := SignedAdicRoots.labelled_scalar_factorization _ _ hb hc
  exact ⟨R,S,hR,hS,by simpa only [hc0, hc1] using eqn⟩

def quadraticValue (c0 c1 x : Scalar) : Scalar := add (add (mul x x) (mul c1 x)) c0

theorem ordinary_factorization (c0 c1 : Scalar) (h0 : c0.residue 5=40) (h1 : c1.residue 5=18) :
    ∃ R S : Scalar, R.residue 2=4 ∧ S.residue 2=2 ∧ ∀ x : Scalar,
      quadraticValue c0 c1 x = mul (add x (neg R)) (add x (neg S)) := by
  obtain ⟨R,S,hR,hS,eqn⟩ := factorization_of_six_bits c0 c1 h0 h1
  refine ⟨R,S,hR,hS,fun x => scalar_ext (fun n => ?_)⟩
  have e := congrArg (fun z : Scalar => z.residue n) (eqn (add x (natScalar 1)) (natScalar 1))
  simp [quadraticValue, add, mul, neg, natScalar] at e ⊢
  grind

theorem labelled_zeros (c0 c1 : Scalar) (h0 : c0.residue 5=40) (h1 : c1.residue 5=18) :
    ∃ R S : Scalar, R.residue 2=4 ∧ S.residue 2=2 ∧ R≠S ∧
      quadraticValue c0 c1 R=natScalar 0 ∧ quadraticValue c0 c1 S=natScalar 0 := by
  obtain ⟨R,S,hR,hS,F⟩ := ordinary_factorization c0 c1 h0 h1
  refine ⟨R,S,hR,hS,fun e => ?_, ?_, ?_⟩
  · have h := congrArg (fun x : Scalar => x.residue 2) e
    rw [hR,hS] at h
    exact (by decide : (4:BitVec 3) ≠ 2) h
  · rw [F]
    apply scalar_ext
    intro n
    simp [add,mul,neg,natScalar]
    grind
  · rw [F]
    apply scalar_ext
    intro n
    simp [add,mul,neg,natScalar]
    grind

end Reimann.SignedResidueRoots
