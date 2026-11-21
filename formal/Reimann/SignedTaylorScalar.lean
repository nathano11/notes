import Reimann.SignedTaylor
import Reimann.DyadicLattice

/-! The compatible integer measure has a single coherent dyadic series of
Taylor coefficients. This module constructs the coefficient at every precision. -/
namespace Reimann.SignedTaylorScalar

open Reimann.SignedTaylor
open Reimann.DyadicLattice (Scalar)

/-- Reducing an integral representative in two stages agrees with direct reduction. -/
theorem narrow_int (a b : Nat) (hab : a ≤ b) (z : Int) :
    (BitVec.ofInt b z).setWidth a = BitVec.ofInt a z := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have dvd : (↑(2^a : Nat) : Int) ∣ ↑(2^b : Nat) := by
    exact_mod_cast Nat.pow_dvd_pow 2 hab
  have natred := Int.toNat_emod (x := z % (↑(2^b : Nat) : Int)) (y := ↑(2^a : Nat))
    (Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt (Nat.pow_pos (n:=b) (by decide : 0<2))))
    (Int.natCast_nonneg _)
  rw [Int.emod_emod_of_dvd z dvd] at natred
  simpa only [Int.toNat_natCast] using natred.symm

theorem ofInt_at_level (w : Nat → Nat → Int)
    (compat : ∀ n j, j<2^n → w n j=w (n+1) j + w (n+1) (j+2^n))
    (s p n k : Nat) (hn : s+p ≤ n) (hk : k < 2^(s+1)) :
    BitVec.ofInt p (taylorAt w (k+p) k) = BitVec.ofInt p (taylorAt w n k) := by
  let b := max (k+p) n
  have l := taylorAt_stable w compat k p (k+p) b k (by omega) (Nat.le_max_left ..) (degree_bound k)
  have r := taylorAt_stable w compat s p n b k hn (Nat.le_max_right ..) hk
  have eqn := l.symm.trans r
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, Int.natCast_pow]
  exact congrArg Int.toNat eqn

/-- The compatible system of residues of the kth Taylor moment. -/
def coefficient (w : Nat → Nat → Int)
    (compat : ∀ n j, j<2^n → w n j=w (n+1) j + w (n+1) (j+2^n))
    (k : Nat) : Scalar where
  residue i := BitVec.ofInt (i+1) (taylorAt w (k+(i+1)) k)
  reduce {i j} hij := by
    rw [narrow_int _ _ (by omega)]
    exact (ofInt_at_level w compat k (i+1) (k+(j+1)) k (by omega) (degree_bound k)).symm

theorem coefficient_at_level (w : Nat → Nat → Int)
    (compat : ∀ n j, j<2^n → w n j=w (n+1) j + w (n+1) (j+2^n))
    (s i n k : Nat) (hn : s+(i+1) ≤ n) (hk : k < 2^(s+1)) :
    (coefficient w compat k).residue i = BitVec.ofInt (i+1) (taylorAt w n k) :=
  ofInt_at_level w compat s (i+1) n k hn hk

/-- One finite group row simultaneously determines the first 224 coefficients
of the canonical power series at six-bit precision. -/
theorem jet_at_thirteen (w : Nat → Nat → Int)
    (compat : ∀ n j, j<2^n → w n j=w (n+1) j + w (n+1) (j+2^n))
    (k : Nat) (hk : k < 224) :
    (coefficient w compat k).residue 5 = BitVec.ofInt 6 (taylorAt w 13 k) :=
  coefficient_at_level w compat 7 5 13 k (by decide) (by change k<256; omega)

end Reimann.SignedTaylorScalar
