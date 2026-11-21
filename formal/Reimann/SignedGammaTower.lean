import Reimann.DyadicCyclotomicImage
import Reimann.SignedMeasure256

/-! Finite inverse-generator indices for the dyadic Stickelberger rows.
Level n has conductor at 2 equal to 2^(n+2), and 2^n positive angular classes. -/
namespace Reimann.SignedGammaTower

/-- Least nonnegative exponent representing -j modulo the group order. -/
def exponent (n j : Nat) : Nat := ((-(j:Int)) % ((2^n : Nat) : Int)).toNat

theorem exponent_cast (n j : Nat) : (exponent n j : Int) = (-(j:Int)) % ((2^n : Nat) : Int) := by
  unfold exponent
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt (Nat.pow_pos (by decide : 0<2)))

/-- Least positive angular residue representing the inverse power of 5. -/
def representative (n j : Nat) : Nat := 5^(exponent n j) % 2^(n+2)

theorem residue_iff_dvd (m a b : Nat) :
    a%m = b%m ↔ (m:Int) ∣ (a:Int)-(b:Int) := by
  rw [← Int.ofNat_inj, Int.natCast_emod, Int.natCast_emod, Int.dvd_iff_emod_eq_zero,
    Int.emod_eq_emod_iff_emod_sub_eq_zero]

theorem exponent_lt (n j : Nat) : exponent n j < 2^n := by
  have pos : (0:Int) < ((2^n:Nat):Int) := by exact_mod_cast Nat.pow_pos (a:=2) (n:=n) (by decide)
  have h := Int.emod_lt_of_pos (-(j:Int)) pos
  have e := exponent_cast n j
  omega

theorem neg_residues (a b m : Int) : (-a)%m = (-b)%m ↔ a%m=b%m := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_eq_emod_iff_emod_sub_eq_zero,
    show -a - -b = -(a-b) by omega, ← Int.dvd_iff_emod_eq_zero, Int.dvd_neg,
    Int.dvd_iff_emod_eq_zero]

theorem exponent_injective_mod (n i j : Nat) : exponent n i = exponent n j ↔ i%2^n=j%2^n := by
  rw [← Int.ofNat_inj, exponent_cast, exponent_cast, neg_residues, ←Int.natCast_emod,
    ←Int.natCast_emod, Int.ofNat_inj]

theorem forward_power_iff (n i j : Nat) :
    5^i % 2^(n+2) = 5^j % 2^(n+2) ↔ i%2^n=j%2^n := by
  obtain ⟨u,hu⟩ := SampleSpacing.five_power_mod_four j
  obtain ⟨t, ht⟩ := DyadicCyclotomicImage.principal_unit_class ((5:Int)^j) ⟨-u, by omega⟩ n
  have hj := (ht j).mp (by simp)
  rw [residue_iff_dvd, Int.natCast_pow, Int.natCast_pow, Int.natCast_pow]
  change (2:Int)^(n+2) ∣ 5^i - 5^j ↔ i%2^n=j%2^n
  rw [ht, hj]

theorem representative_lt (n j : Nat) : representative n j < 2^(n+2) :=
  Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem representative_injective_mod (n i j : Nat) :
    representative n i = representative n j ↔ i%2^n=j%2^n := by
  unfold representative
  rw [forward_power_iff, Nat.mod_eq_of_lt (exponent_lt n i), Nat.mod_eq_of_lt (exponent_lt n j),
    exponent_injective_mod]

theorem exponent_reduce (n j : Nat) : exponent (n+1) j % 2^n = exponent n j := by
  rw [← Int.ofNat_inj, Int.natCast_emod, exponent_cast, exponent_cast]
  apply Int.emod_emod_of_dvd
  exact ⟨2, by rw [Nat.pow_succ, Int.natCast_mul]; rfl⟩

theorem representative_reduce (n j : Nat) :
    representative (n+1) j % 2^(n+2) = representative n j := by
  have hd : 2^(n+2) ∣ 2^(n+1+2) := ⟨2, Nat.pow_succ ..⟩
  unfold representative
  rw [Nat.mod_mod_of_dvd _ hd, forward_power_iff, exponent_reduce, Nat.mod_eq_of_lt (exponent_lt n j)]

theorem half_turn_distinct (n j : Nat) :
    representative (n+1) j ≠ representative (n+1) (j+2^n) := by
  intro e
  have hd := (residue_iff_dvd _ _ _).mp ((representative_injective_mod _ _ _).mp e)
  rw [Int.natCast_add, show (j:Int) - (j + ((2^n:Nat):Int)) = -((2^n:Nat):Int) by omega,
      Int.dvd_neg] at hd
  have pos : 0 < (2^n:Nat) := Nat.pow_pos (by decide)
  have bad := Int.le_of_dvd (by exact_mod_cast pos) hd
  rw [Nat.pow_succ, Int.natCast_mul] at bad
  omega

/-- The two child exponents give the two different lifts of the parent residue. -/
theorem sibling_fibres (n j : Nat) :
    let t := representative n j
    let a := representative (n+1) j
    let b := representative (n+1) (j+2^n)
    (a=t ∧ b=t+2^(n+2)) ∨ (a=t+2^(n+2) ∧ b=t) := by
  dsimp only
  have right := representative_reduce n (j+2^n)
  have ep : representative n (j+2^n) = representative n j :=
    (representative_injective_mod _ _ _).mpr (by simp)
  rw [ep] at right
  have bound (i : Nat) : representative (n+1) i < 2 * 2^(n+2) := by
    have h := representative_lt (n+1) i
    rwa [show n+1+2 = (n+2)+1 by omega, Nat.pow_succ, Nat.mul_comm] at h
  have leftPair := WeightClasses.binary_fiber (bound j) (representative_reduce n j)
  have rightPair := WeightClasses.binary_fiber (bound (j+2^n)) right
  have ne := half_turn_distinct n j
  omega

theorem level256_representative (j : Fin 64) :
    representative 6 j.val = SignedMeasure256.inverseResidue j.val := by
  revert j
  decide

theorem exponent_inverse (n j : Nat) : (j+exponent n j)%2^n = 0 := by
  rw [Nat.add_comm, ← Int.ofNat_inj, Int.natCast_emod, Int.natCast_add, exponent_cast,
    Int.emod_add_emod, show -(j:Int)+j=0 by omega]
  simp

/-- The angular coordinate has the required inverse orientation at every level. -/
theorem representative_is_inverse (n j : Nat) :
    (5^j * representative n j) % 2^(n+2) = 1 := by
  have hp : 1 < 2^(n+2) := Nat.one_lt_pow (by omega) (by decide)
  unfold representative
  rw [Nat.mul_mod_mod, ←Nat.pow_add]
  have h := (forward_power_iff n (j+exponent n j) 0).mpr (by simpa using exponent_inverse n j)
  simpa [Nat.mod_eq_of_lt hp] using h

theorem exponent_involutive (n j : Nat) : exponent n (exponent n j) = j % 2^n := by
  rw [←Int.ofNat_inj, exponent_cast, Int.natCast_emod]
  have h : ((exponent n j:Int) % ((2^n:Nat):Int)) = (-(j:Int)) % ((2^n:Nat):Int) := by
    rw [exponent_cast]; simp
  simpa using (neg_residues _ _ _).mpr h

theorem four_dvd_modulus (n : Nat) : 4 ∣ 2^(n+2) := by
  refine ⟨2^n, ?_⟩
  rw [Nat.pow_add, Nat.mul_comm]

theorem positive_residue (n j : Nat) : representative n j % 4 = 1 := by
  unfold representative
  rw [Nat.mod_mod_of_dvd _ (four_dvd_modulus n), ←Int.ofNat_inj, Int.natCast_emod, Int.natCast_pow]
  obtain ⟨u,hu⟩ := SampleSpacing.five_power_mod_four (exponent n j)
  change (5:Int)^exponent n j % 4 = 1
  omega

/-- Every positive principal residue has precisely one inverse-generator index. -/
theorem positive_class (n x : Nat) (hx : x%4=1) :
    ∃ t : Fin (2^n), ∀ j : Nat, representative n j = x%2^(n+2) ↔ j%2^n=t.val := by
  have hd : (4:Int) ∣ 1-(x:Int) := by omega
  obtain ⟨k, hk⟩ := DyadicCyclotomicImage.principal_unit_class x hd n
  let t : Fin (2^n) := ⟨exponent n k.val, exponent_lt n k.val⟩
  have image : representative n t.val = x%2^(n+2) := by
    unfold representative
    change 5^(exponent n (exponent n k.val)) % _ = _
    rw [exponent_involutive, Nat.mod_eq_of_lt k.isLt, residue_iff_dvd, Int.natCast_pow, Int.natCast_pow]
    exact (hk k.val).mpr (Nat.mod_eq_of_lt k.isLt)
  refine ⟨t, fun j => ?_⟩
  rw [←image, representative_injective_mod, Nat.mod_eq_of_lt t.isLt]

/-- True chooses the reflected class in the full odd unit group. -/
def signedRepresentative (n : Nat) (minus : Bool) (j : Nat) : Nat :=
  if minus then 2^(n+2) - representative n j else representative n j

/-- Every odd residue in the full interval fixes both its sign and its inverse-generator index. -/
theorem signed_unique_class (n x : Nat) (hx : x < 2^(n+2)) (ho : x%2=1) :
    ∃ sign : Bool, ∃ t : Fin (2^n), ∀ b j,
      signedRepresentative n b j = x ↔ b=sign ∧ j%2^n=t.val := by
  have hd := Nat.mod_eq_zero_of_dvd (four_dvd_modulus n)
  by_cases hp : x%4=1
  · obtain ⟨t,ht⟩ := positive_class n x hp
    refine ⟨false,t,fun b j => ?_⟩
    have hval := positive_residue n j
    have hlt := representative_lt n j
    cases b
    · simpa [signedRepresentative, Nat.mod_eq_of_lt hx] using ht j
    · simp [signedRepresentative]
      omega
  · have hp' : (2^(n+2)-x)%4=1 := by omega
    have hlt' : 2^(n+2)-x < 2^(n+2) := by omega
    obtain ⟨t,ht⟩ := positive_class n (2^(n+2)-x) hp'
    refine ⟨true,t,fun b j => ?_⟩
    have hval := positive_residue n j
    have hlt := representative_lt n j
    cases b
    · simp [signedRepresentative]
      omega
    · have h := ht j
      rw [Nat.mod_eq_of_lt hlt'] at h
      simp [signedRepresentative]
      omega

end Reimann.SignedGammaTower
