import Reimann.DyadicLocalizedPrimes69

/-! Sign changes of √−3 and √−23 on the two dyadic residue maps of E₀. -/

namespace Reimann.DyadicPlaceAction69

open Lean.Grind
open Reimann.Dyadic (Matrix)
open Reimann.DyadicFieldTrace69 (embed conjugate twice_half)
open Reimann.DyadicLocalizedPrimes69 (fiber Represents reduce reduce_of_rep represents_self)
open Reimann.DyadicFiberPrimes (F4 project kernel)
open Reimann.TameRationalField277 (Biquad)

def flipE (x : Matrix) : Matrix := ⟨x.a+x.b,-x.b,x.c+x.d,-x.d⟩

def flipW (x : Matrix) : Matrix := ⟨x.a+x.c,x.b+x.d,-x.c,-x.d⟩

def integerAction (s t : Bool) (x : Matrix) : Matrix :=
  let y := if s then flipE x else x
  if t then flipW y else y

def sign (flipped : Bool) : Rat := if flipped then -1 else 1

def fieldAction (s t : Bool) (z : Biquad) : Biquad := conjugate (sign s) (sign t) z

/-- The half-basis substitutions implement the actual radical automorphisms. -/
theorem embed_action (s t : Bool) (x : Matrix) :
    embed (integerAction s t x) = fieldAction s t (embed x) := by
  have hh := twice_half
  cases s <;> cases t <;> apply Prod.ext <;> apply Prod.ext <;>
    simp only [integerAction,flipE,flipW,fieldAction,conjugate,sign,embed,
      DyadicBasisComparison.fromIntegral,Bool.false_eq_true,ite_false,ite_true,
      Rat.intCast_add,Rat.intCast_neg] <;> grind

def frobenius (v : F4) : F4 := DyadicInert.residueProduct v v

theorem frobenius_coordinates (a b : BitVec 1) : frobenius (a,b) = (a+b,b) := by
  revert a b
  decide

theorem fiber_flipE (x : Matrix) :
    fiber (flipE x) = (frobenius (fiber x).1,frobenius (fiber x).2) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [fiber,flipE,frobenius_coordinates,BitVec.ofInt_add,BitVec.ofInt_neg] <;> grind

theorem fiber_flipW (x : Matrix) : fiber (flipW x) = ((fiber x).2,(fiber x).1) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [fiber,flipW,BitVec.ofInt_add,BitVec.ofInt_neg] <;> grind

/-- A sign on √−3 squares the residue. A sign on √−23 exchanges the two projections. -/
theorem sign_action_residue (s t i : Bool) (x : Matrix) :
    project i (fiber (integerAction s t x)) =
      let v := project (if t then !i else i) (fiber x)
      if s then frobenius v else v := by
  cases s <;> cases t <;> cases i <;>
    simp [integerAction,project,fiber_flipE,fiber_flipW]

theorem frobenius_zero_iff (v : F4) : frobenius v = (0,0) ↔ v = (0,0) := by
  simpa [frobenius] using DyadicFiberPrimes.field_zero_product v v

theorem kernel_action (s t i : Bool) (x : Matrix) :
    kernel i (fiber (integerAction s t x)) ↔ kernel (if t then !i else i) (fiber x) := by
  unfold kernel
  rw [sign_action_residue]
  cases s with
  | false => rfl
  | true => exact frobenius_zero_iff _

/-- Among all four sign choices exactly the two fixing √−23 preserve a given kernel. -/
theorem prime_stabilizer (s t i : Bool) :
    (∀ x, kernel i (fiber (integerAction s t x)) ↔ kernel i (fiber x)) ↔ t = false := by
  constructor
  · intro h
    cases t with
    | false => rfl
    | true =>
      have e := (kernel_action s true i ⟨0,0,1,0⟩).symm.trans (h ⟨0,0,1,0⟩)
      have bad : kernel true (fiber ⟨0,0,1,0⟩) := by
        cases i with
        | false => exact e.mpr rfl
        | true => exact e.mp rfl
      exact False.elim ((by decide : ¬ ((1,0) : F4) = (0,0)) bad)
  · rintro rfl x
    exact kernel_action s false i x

theorem fieldAction_scalar (s t : Bool) (a : Rat) :
    fieldAction s t (TameRationalField277.scalar a) = TameRationalField277.scalar a := by
  simp [fieldAction,conjugate,TameRationalField277.scalar]

theorem fieldAction_mul (s t : Bool) (x y : Biquad) :
    fieldAction s t (TameRationalField277.bm x y) =
      TameRationalField277.bm (fieldAction s t x) (fieldAction s t y) := by
  have hs (b : Bool) : sign b * sign b = 1 := by cases b <;> simp [sign] <;> grind
  exact DyadicFieldTrace69.conjugate_multiply (sign s) (sign t) (hs s) (hs t) x y

theorem represents_action {z : Biquad} {k : Int} {p : Matrix} (s t : Bool)
    (hp : Represents z k p) : Represents (fieldAction s t z) k (integerAction s t p) := by
  unfold Represents at hp ⊢
  rw [embed_action,hp,fieldAction_mul,fieldAction_scalar]

def HasOddDenominator (z : Biquad) : Prop := ∃ p : Matrix, ∃ k : Int, Represents z k p

theorem action_odd_denominator (s t : Bool) {z : Biquad} (hz : HasOddDenominator z) :
    HasOddDenominator (fieldAction s t z) := by
  obtain ⟨p,k,hp⟩ := hz
  exact ⟨_,k,represents_action s t hp⟩

theorem odd_denominator_action (s t i : Bool) {z : Biquad} (hz : HasOddDenominator z) :
    project i (reduce (fieldAction s t z) (action_odd_denominator s t hz)) =
      let v := project (if t then !i else i) (reduce z hz)
      if s then frobenius v else v := by
  have H : ∃ p : Matrix, ∃ k : Int, Represents z k p := hz
  obtain ⟨p,k,hp⟩ := H
  rw [reduce_of_rep (action_odd_denominator s t hz) (represents_action s t hp),reduce_of_rep hz hp]
  exact sign_action_residue s t i p

theorem odd_denominator_kernel (s t i : Bool) {z : Biquad} (hz : HasOddDenominator z) :
    kernel i (reduce (fieldAction s t z) (action_odd_denominator s t hz)) ↔
      kernel (if t then !i else i) (reduce z hz) := by
  unfold kernel
  rw [odd_denominator_action]
  cases s with
  | false => rfl
  | true => exact frobenius_zero_iff _

theorem odd_denominator_stabilizer (s t i : Bool) :
    (∀ z (hz : HasOddDenominator z),
      kernel i (reduce (fieldAction s t z) (action_odd_denominator s t hz)) ↔
        kernel i (reduce z hz)) ↔ t = false := by
  constructor
  · intro h
    apply (prime_stabilizer s t i).mp
    intro x
    have hz : HasOddDenominator (embed x) := ⟨x,0,represents_self x⟩
    have e := h (embed x) hz
    rw [reduce_of_rep (action_odd_denominator s t hz) (represents_action s t (represents_self x)),
        reduce_of_rep hz (represents_self x)] at e
    exact e
  · rintro rfl z hz
    exact odd_denominator_kernel s false i hz

/-- The nonidentity sign in the stabilizer acts nontrivially on the residue of e. -/
theorem frobenius_on_e (i : Bool) :
    project i (fiber (integerAction true false ⟨0,1,0,0⟩)) = (1,1) ∧
    project i (fiber ⟨0,1,0,0⟩) = (0,1) := by
  cases i <;> exact ⟨rfl,rfl⟩

end Reimann.DyadicPlaceAction69
