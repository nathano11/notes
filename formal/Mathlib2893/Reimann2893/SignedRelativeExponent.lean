import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Reimann.SignedCommonNormalization

/-! Compatible exponents of the full cyclotomic field which act trivially on
the conductor of the imaginary quadratic character and as five on the dyadic part. -/
namespace Reimann.SignedRelativeExponent

theorem odd_coprime_dyadic (m n : Nat) (hm : Odd m) : m.Coprime (2^(n+2)) :=
  (Nat.coprime_two_right.mpr hm).pow_right _

def relativeExponent (m n : Nat) (hm : Odd m) : Nat :=
  (Nat.chineseRemainder (odd_coprime_dyadic m n hm) 1 5).val

theorem exponent_congruences (m n : Nat) (hm : Odd m) :
    relativeExponent m n hm ≡ 1 [MOD m] ∧ relativeExponent m n hm ≡ 5 [MOD 2^(n+2)] :=
  (Nat.chineseRemainder (odd_coprime_dyadic m n hm) 1 5).property

theorem exponent_bound (m n : Nat) (hm : Odd m) : relativeExponent m n hm < m*2^(n+2) := by
  exact Nat.chineseRemainder_lt_mul _ _ _ (by obtain ⟨u,hu⟩ := hm; omega)
    (Nat.ne_of_gt (Nat.pow_pos (by decide)))

theorem fixes_conductor (m n : Nat) (hm : Odd m) : relativeExponent m n hm ≡ 1 [MOD 4*m] := by
  obtain ⟨oddPart,dyadic⟩ := exponent_congruences m n hm
  apply (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 4 m from
    ((Nat.coprime_two_right.mpr hm).pow_right 2).symm)).mp
  exact ⟨(dyadic.of_dvd (SignedGammaTower.four_dvd_modulus n)).trans (by decide), oddPart⟩

theorem exponent_is_unit (m n : Nat) (hm : Odd m) : (relativeExponent m n hm).Coprime (m*2^(n+2)) := by
  obtain ⟨oddPart,dyadic⟩ := exponent_congruences m n hm
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · change (relativeExponent m n hm).gcd m = 1
    rw [oddPart.gcd_eq]
    simp
  · change (relativeExponent m n hm).gcd (2^(n+2)) = 1
    rw [dyadic.gcd_eq]
    exact (show Nat.Coprime 5 2 by decide).pow_right _

theorem exponent_unique (m n e : Nat) (hm : Odd m) (bound : e < m*2^(n+2))
    (hodd : e ≡ 1 [MOD m]) (hdyadic : e ≡ 5 [MOD 2^(n+2)]) :
    relativeExponent m n hm = e := by
  have h := Nat.chineseRemainder_modEq_unique (odd_coprime_dyadic m n hm) hodd hdyadic
  change e % (m*2^(n+2)) = relativeExponent m n hm % (m*2^(n+2)) at h
  rwa [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (exponent_bound m n hm), eq_comm] at h

theorem exponent_restricts (m n : Nat) (hm : Odd m) :
    relativeExponent m (n+1) hm % (m*2^(n+2)) = relativeExponent m n hm := by
  obtain ⟨oddPart,dyadic⟩ := exponent_congruences m (n+1) hm
  have smaller := dyadic.of_dvd (Nat.pow_dvd_pow 2 (show n+2≤(n+1)+2 by omega))
  have h := Nat.chineseRemainder_modEq_unique (odd_coprime_dyadic m n hm) oddPart smaller
  change _ = relativeExponent m n hm % (m*2^(n+2)) at h
  rwa [Nat.mod_eq_of_lt (exponent_bound m n hm)] at h

/-- The full cyclotomic exponent 5 has negative imaginary quadratic character. -/
theorem character_at_five : SignedCommonNormalization.character2893 5 = -1 := by decide +kernel

theorem character69_at_five : DyadicZeroValues.chi276 5 = 1 := by decide +kernel

/-- A CRT lift fixing the conductor part has positive imaginary quadratic character. -/
theorem relative_lift_character (e : Nat) (he : e%11572=1) :
    SignedCommonNormalization.character2893 e = 1 := by
  have h11 := congrArg (fun b : Nat => b%11) he
  have h263 := congrArg (fun b : Nat => b%263) he
  have h4 := congrArg (fun b : Nat => b%4) he
  simp only [Nat.mod_mod_of_dvd _ (by decide : 11 ∣ 11572)] at h11
  simp only [Nat.mod_mod_of_dvd _ (by decide : 263 ∣ 11572)] at h263
  simp only [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 11572)] at h4
  change e%11=1 at h11
  change e%263=1 at h263
  change e%4=1 at h4
  simp [SignedCommonNormalization.character2893, SignedMeasure256.character, Dyadic.quadSymbol,
    SignedStickelberger.signFour, h11, h263, h4]

/-- At D=256 a single ambient exponent realizes the relative forward-five action. -/
theorem relative_lift_256 :
    57861%256=5 ∧ 57861%11572=1 ∧ SignedCommonNormalization.character2893 57861=1 :=
  ⟨by decide, by decide, relative_lift_character _ (by decide)⟩

theorem conductor_examples_256 :
    relativeExponent 2893 6 (by decide) = 57861 ∧ relativeExponent 69 6 (by decide) = 3589 := by
  constructor <;> apply exponent_unique <;> decide

end Reimann.SignedRelativeExponent
