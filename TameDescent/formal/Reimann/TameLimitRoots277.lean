import Reimann.TameLimit277
import Reimann.TameRootExhaustion277

namespace Reimann.TameLimitRoots277

open Reimann.TameSplitting277 Reimann.TameLimit277 Reimann.TameRootExhaustion277

def chooseRoot (b : Bool) (x : Integer277) : Integer277 :=
  if b then neg x else x

theorem chooseRoot_square (x : Integer277) (b : Bool) :
    mul (chooseRoot b x) (chooseRoot b x) = mul x x := by
  cases b with
  | false => rfl
  | true => exact negative_squares x

theorem square_congruence (z : Integer277) (a : Int) (h : mul z z = ofInt a)
    (n : Nat) : modulus n ∣ (z.residue n)^2-a := by
  have e := congrArg (fun v : Integer277 => v.residue n) h
  change (z.residue n*z.residue n)%modulus n = a%modulus n at e
  rw [Int.pow_succ, Int.pow_one]
  exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp e)

theorem signed_lift_residue (a x d : Int) (hx : 277 ∣ x^2-a)
    (hd : 277 ∣ 2*x*d-1) (b : Bool) (n : Nat) :
    (chooseRoot b (liftedRoot a x d hx hd)).residue n =
      (signed b (liftPair a x d n).1) % modulus n := by
  cases b with
  | false => rfl
  | true =>
    change (-((liftPair a x d n).1 % modulus n)) % modulus n =
      (-(liftPair a x d n).1) % modulus n
    simp [Int.neg_emod, Int.dvd_iff_emod_eq_zero]

theorem eq_signed_lift (a x d : Int) (hx : 277 ∣ x^2-a)
    (hd : 277 ∣ 2*x*d-1) (z : Integer277) (b : Bool) (h : Matches a x d z.residue b) :
    z = chooseRoot b (liftedRoot a x d hx hd) := by
  apply equal_of_residues
  intro n
  rw [signed_lift_residue]
  exact (z.canonical n).symm.trans
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd (h n)))

/-- Actual solutions of both equations in the inverse-limit ring. -/
def RootPair := {z : Integer277 × Integer277 //
  mul z.1 z.1 = ofInt (-3) ∧ mul z.2 z.2 = ofInt (-23)}

def ofSigns (s : Bool × Bool) : RootPair :=
  ⟨(chooseRoot s.1 rootThree,chooseRoot s.2 rootTwentyThree),
    (chooseRoot_square rootThree s.1).trans rootThree_square,
    (chooseRoot_square rootTwentyThree s.2).trans rootTwentyThree_square⟩

/-- The inverse needs only the residues modulo 277. -/
def readSigns (z : RootPair) : Bool × Bool :=
  (decide (z.val.1.residue 0 ≠ 44), decide (z.val.2.residue 0 ≠ 114))

theorem readSigns_ofSigns (s : Bool × Bool) : readSigns (ofSigns s) = s := by
  obtain ⟨b,c⟩ := s
  cases b <;> cases c <;> decide +kernel

theorem all_pairs_ofSigns (z : RootPair) : ∃ s, z = ofSigns s := by
  obtain ⟨s,hs,ht,_⟩ := (four_signs_iff z.val.1.residue z.val.2.residue
    (step_difference z.val.1) (step_difference z.val.2)).mp
      (fun n => ⟨square_congruence _ _ z.property.1 n,square_congruence _ _ z.property.2 n⟩)
  refine ⟨s,Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact eq_signed_lift _ _ _ simple_seeds.1 simple_seeds.2.1 z.val.1 s.1 hs
  · exact eq_signed_lift _ _ _ simple_seeds.2.2.1 simple_seeds.2.2.2.1 z.val.2 s.2 ht

theorem ofSigns_readSigns (z : RootPair) : ofSigns (readSigns z) = z := by
  obtain ⟨s,rfl⟩ := all_pairs_ofSigns z
  rw [readSigns_ofSigns]

/-- Evaluation on the two signed lifts and first-digit decoding are
mutual inverses between four labels and the ring's actual solution pairs. -/
theorem four_root_pairs :
    (∀ s : Bool × Bool, readSigns (ofSigns s) = s) ∧
    (∀ z : RootPair, ofSigns (readSigns z) = z) :=
  ⟨readSigns_ofSigns, ofSigns_readSigns⟩

end Reimann.TameLimitRoots277
