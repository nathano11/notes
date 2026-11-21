import Reimann.PairedSigns
import Reimann.SignedPreparation
import Reimann.SignedMeasure256

/-! Conversion between finite coefficient residues and the signed weight-three
numerators for the conductor 2893 calculation. -/
namespace Reimann.SignedCoefficients

/-- Six bits of each monic coefficient give the earlier signed input. -/
theorem weight_three_from_coefficients {c0 c1 : Int}
    (h0 : c0 % 64 = 40) (h1 : c1 % 64 = 18) : PairedSigns.WeightThree c0 c1 := by
  obtain ⟨hp, hm⟩ := PairedSigns.linear_at_three c0 c1
  constructor <;> simp only [hp, hm] <;> omega

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- Every monic distinguished quadratic at precision 64 is represented by
one of 32 times 32 pairs. Reduction uses the entire level-256 row. -/
theorem finite_quadratic_test : ∀ i j : Fin 32,
    SignedPreparation.remainder (2 * (i.val : Int)) (2 * (j.val : Int))
      SignedMeasure256.row = (0, 0) ↔ i.val = 20 ∧ j.val = 9 := by
  decide +kernel

theorem remainder_at_residues (c0 c1 : Int) (row : List Int) :
    SignedPreparation.remainder (c0%64) (c1%64) row = SignedPreparation.remainder c0 c1 row := by
  have castMod (c : Int) : BitVec.ofInt 6 (c%64) = BitVec.ofInt 6 c := by
    apply BitVec.eq_of_toNat_eq
    change ((c%64)%64).toNat = (c%64).toNat
    simp
  unfold SignedPreparation.remainder
  rw [castMod, castMod]

/-- Exhaustion applies to any integer lifts of the two even coefficients. -/
theorem coefficients_of_remainder {c0 c1 : Int} (h0 : c0%2=0) (h1 : c1%2=0)
    (divides : SignedPreparation.remainder c0 c1 SignedMeasure256.row = (0,0)) :
    c0%64=40 ∧ c1%64=18 := by
  let i : Fin 32 := ⟨(c0%64).toNat/2, by omega⟩
  let j : Fin 32 := ⟨(c1%64).toNat/2, by omega⟩
  have hi : 2*(i.val:Int) = c0%64 := by dsimp [i]; omega
  have hj : 2*(j.val:Int) = c1%64 := by dsimp [j]; omega
  have pair := (finite_quadratic_test i j).mp (by rw [hi, hj, remainder_at_residues]; exact divides)
  omega

/-- One finite ideal-membership statement for the field polynomial gives both
coefficient residues, including the sixth bit of the linear coefficient. -/
theorem coefficients_of_cyclic_factor {c0 c1 : Int} (h0 : c0%2=0) (h1 : c1%2=0)
    (h : SignedPreparation.CyclicFactor c0 c1 SignedMeasure256.row) :
    c0%64=40 ∧ c1%64=18 :=
  coefficients_of_remainder h0 h1 (SignedPreparation.cyclic_factor_remainder _ _ _ h0 h1 h)

theorem weight_three_of_cyclic_factor {c0 c1 : Int} (h0 : c0%2=0) (h1 : c1%2=0)
    (h : SignedPreparation.CyclicFactor c0 c1 SignedMeasure256.row) : PairedSigns.WeightThree c0 c1 := by
  obtain ⟨hc0, hc1⟩ := coefficients_of_cyclic_factor h0 h1 h
  exact weight_three_from_coefficients hc0 hc1

/-- The sixth bit of c1 determines the signed difference to seven bits,
one bit beyond the valuation-five statement. -/
theorem signed_difference_mod128 (c0 c1 : Int) (h1 : c1%64=18) (r : Nat) :
    (PairedSigns.positiveBranch c0 c1 r - PairedSigns.negativeBranch c0 c1 r)%128 = 32 := by
  unfold PairedSigns.positiveBranch PairedSigns.negativeBranch
  rw [PairedSigns.sign_difference]
  obtain ⟨u, hu⟩ := SampleSpacing.five_power_mod_four r
  have hc : c1 = 18 + 64*(c1/64) := by omega
  have he : 2*(5:Int)^r*(c1-2) = 32 + 128*(u + c1/64 + 4*u*(c1/64)) := by
    rw [hu]
    grind
  rw [he, Int.add_mul_emod_self_left]
  decide

end Reimann.SignedCoefficients
