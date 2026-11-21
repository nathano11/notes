import Mathlib.NumberTheory.Padics.RingHoms
import Reimann.DyadicLattice

/-! Coherent binary words and the standard ring of 2-adic integers. -/
namespace Reimann.SignedNativeScalar2893

open DyadicLattice

theorem appr_mod (z : ℤ_[2]) (a b : Nat) (hab : a≤b) :
    z.appr b % 2^a = z.appr a := by
  obtain ⟨q,hq⟩ := PadicInt.dvd_appr_sub_appr z a b hab
  have hle := PadicInt.appr_mono z hab
  have he : z.appr b = z.appr a + (2^a)*q := by omega
  rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (z.appr_lt a)]

noncomputable def read (z : ℤ_[2]) : Scalar where
  residue n := BitVec.ofNat (n+1) (z.appr (n+1))
  reduce {i j} hij := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (z.appr_lt _)]
    exact appr_mod z (i+1) (j+1) (by omega)

theorem read_reduction (z : ℤ_[2]) (n : Nat) :
    (((read z).residue n).toNat : ZMod (2^(n+1))) = PadicInt.toZModPow (n+1) z := by
  change ((BitVec.ofNat (n+1) (z.appr (n+1))).toNat : ZMod (2^(n+1))) = _
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (z.appr_lt _)]
  rfl

theorem word_ext {p : Nat} {x y : BitVec p}
    (h : (x.toNat : ZMod (2^p)) = (y.toNat : ZMod (2^p))) : x=y := by
  apply BitVec.eq_of_toNat_eq
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt y.isLt] using
    congrArg ZMod.val h

theorem word_add {p : Nat} (x y : BitVec p) :
    ((x+y).toNat : ZMod (2^p)) = x.toNat + y.toNat := by
  rw [BitVec.toNat_add,ZMod.natCast_mod,Nat.cast_add]

theorem word_mul {p : Nat} (x y : BitVec p) :
    ((x*y).toNat : ZMod (2^p)) = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul,ZMod.natCast_mod,Nat.cast_mul]

theorem read_add (x y : ℤ_[2]) : read (x+y) = add (read x) (read y) := by
  apply scalar_ext
  intro n
  apply word_ext
  change _ = (((read x).residue n + (read y).residue n).toNat : ZMod (2^(n+1)))
  rw [word_add, read_reduction, read_reduction, read_reduction, map_add]

theorem read_mul (x y : ℤ_[2]) : read (x*y) = mul (read x) (read y) := by
  apply scalar_ext
  intro n
  apply word_ext
  change _ = (((read x).residue n * (read y).residue n).toNat : ZMod (2^(n+1)))
  rw [word_mul, read_reduction, read_reduction, read_reduction, map_mul]

theorem read_nat (k : Nat) : read (k : ℤ_[2]) = natScalar k := by
  apply scalar_ext
  intro n
  apply word_ext
  change _ = ((BitVec.ofNat (n+1) k).toNat : ZMod (2^(n+1)))
  rw [read_reduction, map_natCast, BitVec.toNat_ofNat,ZMod.natCast_mod]

def liftDigit (x : Scalar) : Nat → Int
  | 0 => 0
  | n+1 => (x.residue n).toNat

theorem liftDigit_step (x : Scalar) (n : Nat) :
    (2:Int)^n ∣ liftDigit x (n+1) - liftDigit x n := by
  cases n with
  | zero => simp [liftDigit]
  | succ n =>
    have hr := congrArg BitVec.toNat (x.reduce (i:=n) (j:=n+1) (Nat.le_succ n))
    rw [BitVec.toNat_setWidth] at hr
    have h := Int.emod_add_mul_ediv (((x.residue (n+1)).toNat:Nat):Int) ((2:Int)^(n+1))
    have hm : (((x.residue (n+1)).toNat:Nat):Int)%(2:Int)^(n+1) = (x.residue n).toNat := by
      exact_mod_cast hr
    rw [hm] at h
    refine ⟨((x.residue (n+1)).toNat:Int) / ((2:Int)^(n+1)), ?_⟩
    change ((x.residue (n+1)).toNat:Int) - (x.residue n).toNat = _
    omega

noncomputable def realize (x : Scalar) : ℤ_[2] :=
  PadicInt.ofIntSeq (liftDigit x)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ 2 (liftDigit_step x))

theorem realize_reduction (x : Scalar) (n : Nat) :
    PadicInt.toZModPow (n+1) (realize x) = ((x.residue n).toNat : ZMod (2^(n+1))) := by
  simpa only [realize, liftDigit, Int.cast_natCast] using
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (liftDigit x) 2 (liftDigit_step x) (n+1)

theorem read_realize (x : Scalar) : read (realize x) = x := by
  apply scalar_ext
  intro n
  apply word_ext
  rw [read_reduction,realize_reduction]

theorem realize_read (z : ℤ_[2]) : realize (read z) = z := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    have : Subsingleton (ZMod (2^0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n => rw [realize_reduction,read_reduction]

end Reimann.SignedNativeScalar2893
