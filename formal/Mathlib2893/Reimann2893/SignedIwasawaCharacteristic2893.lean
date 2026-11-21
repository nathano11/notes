import Reimann2893.SignedArithmeticTower2893
import Reimann2893.SignedClassScalars2893
import Reimann2893.SignedRationalCharacteristic2893
import Reimann2893.SignedCyclicCriterion2893
import Reimann2893.SignedFiniteAnnihilation2893
import Reimann2893.SignedAdicDistinguished2893
import Reimann2893.SignedLinearGammaPowers2893

/-! The forward characteristic polynomial of the norm limit of actual 2-class
groups. Finite rank, distinguishedness and the main-conjecture inclusion are
explicit arithmetic inputs at the points where they are required. -/
namespace Reimann.SignedIwasawaCharacteristic2893

open scoped Polynomial
open Reimann.SignedArithmeticTower2893 (X)

noncomputable instance scalarModule : Module ℤ_[2] (Additive X) :=
  SignedClassScalars2893.limitModule SignedLayerClasses2893.layerClass
    SignedArithmeticTower2893.norm

noncomputable def gamma : Additive X ≃ₗ[ℤ_[2]] Additive X :=
  SignedClassScalars2893.limitForwardLinear SignedLayerClasses2893.layerClass
    SignedArithmeticTower2893.norm SignedLayerClasses2893.primaryForward
    SignedArithmeticTower2893.norm_forward

abbrev V := SignedRationalCharacteristic2893.Space (Additive X)

noncomputable def gammaQ : Module.End ℚ_[2] V :=
  SignedRationalCharacteristic2893.forward (Additive X) gamma

theorem finite_of_rank_two (rank : Module.finrank ℚ_[2] V = 2) : FiniteDimensional ℚ_[2] V :=
  Module.finite_of_finrank_pos (by rw [rank]; decide)

noncomputable def coordinatePrecision (b : Additive X) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (SignedClassScalars2893.primary_killed (SignedLayerClasses2893.layerClass n) (b.toMul.val n))

theorem coordinate_order (b : Additive X) (n : ℕ) :
    (b.toMul.val n)^(2^coordinatePrecision b n) = 1 := by
  classical
  exact Nat.find_spec (SignedClassScalars2893.primary_killed (SignedLayerClasses2893.layerClass n) (b.toMul.val n))

-- Finite dimension for this particular arithmetic module is the rank input.
set_option linter.concreteInstances false
variable [FiniteDimensional ℚ_[2] V]

noncomputable def P : ℚ_[2][X] :=
  SignedRationalCharacteristic2893.characteristic (Additive X) gamma

theorem eval_P (t : ℚ_[2]) :
    P.eval t = (algebraMap ℚ_[2] (Module.End ℚ_[2] V) (1+t) - gammaQ).det :=
  SignedRationalCharacteristic2893.determinant_convention (Additive X) gamma t

/-- In rank two the dyadic action itself forces the actual characteristic
polynomial to have integral even lower coefficients. -/
theorem distinguished_of_rank_two (rank : Module.finrank ℚ_[2] V = 2) :
    ∃ c0 c1 : ℤ_[2],
      P = Polynomial.C (c0 : ℚ_[2]) + Polynomial.C (c1 : ℚ_[2]) * Polynomial.X + Polynomial.X^2 ∧
      PadicInt.toZModPow 1 c0 = 0 ∧ PadicInt.toZModPow 1 c1 = 0 := by
  obtain ⟨G,hzero,hcube,hunit⟩ := SignedLinearGammaPowers2893.exists_cube_tower
    SignedLayerClasses2893.layerClass SignedArithmeticTower2893.norm SignedLayerClasses2893.primaryForward
    SignedArithmeticTower2893.norm_forward SignedArithmeticTower2893.primary_period
  have h := SignedAdicDistinguished2893.distinguished_of_cube_roots G rank hcube hunit
  rw [hzero] at h
  exact h

noncomputable def distinguishedCoefficients (rank : Module.finrank ℚ_[2] V = 2) :
    {c : ℤ_[2] × ℤ_[2] // P = Polynomial.C (c.1 : ℚ_[2]) +
      Polynomial.C (c.2 : ℚ_[2]) * Polynomial.X + Polynomial.X^2 ∧
      PadicInt.toZModPow 1 c.1 = 0 ∧ PadicInt.toZModPow 1 c.2 = 0} :=
  Classical.choice (by
    obtain ⟨c0,c1,h⟩ := distinguished_of_rank_two rank
    exact ⟨⟨(c0,c1),h⟩⟩)

/-- The only arithmetic inputs are the actual rank and the actual ideal inclusion.
The coefficients are selected from the native forward determinant. -/
theorem actual_characteristic_bits (rank : Module.finrank ℚ_[2] V = 2)
    (ideal : let c := (distinguishedCoefficients rank).val
             SignedNativeSeries2893.candidate ∈ Ideal.span {SignedNativeSeries2893.quadratic c.1 c.2}) :
    let c := (distinguishedCoefficients rank).val
    P = Polynomial.C (c.1 : ℚ_[2]) + Polynomial.C (c.2 : ℚ_[2]) * Polynomial.X + Polynomial.X^2 ∧
      PadicInt.toZModPow 6 c.1 = 40 ∧ PadicInt.toZModPow 6 c.2 = 18 := by
  obtain ⟨shape,h0,h1⟩ := (distinguishedCoefficients rank).property
  exact ⟨shape,SignedNativeSeries2893.characteristic_bits_of_principal_inclusion _ _ h0 h1 ideal⟩

/-- With a cyclic basis of the actual rationalized class module, one arithmetic
relation on its first vector identifies the whole polynomial and gives the inclusion. -/
theorem ideal_of_actual_generator (B : Module.Basis (Fin 2) ℚ_[2] V)
    (first : SignedRationalCharacteristic2893.augmentation (Additive X) gamma (B 0) = B 1)
    (ann : let f := SignedRationalCharacteristic2893.augmentation (Additive X) gamma
           f (f (B 0)) + (SignedCyclicCriterion2893.linear : ℚ_[2]) • f (B 0) +
             (SignedCyclicCriterion2893.constant : ℚ_[2]) • B 0 = 0) :
    ∃ c0 c1 : ℤ_[2],
      P = Polynomial.C (c0 : ℚ_[2]) + Polynomial.C (c1 : ℚ_[2]) * Polynomial.X + Polynomial.X^2 ∧
      SignedNativeSeries2893.candidate ∈ Ideal.span {SignedNativeSeries2893.quadratic c0 c1} :=
  SignedCyclicCriterion2893.ideal_from_generator
    (SignedRationalCharacteristic2893.augmentation (Additive X) gamma) B first ann

/-- The remaining annihilation can be tested on integral ideal classes.
One exponent must work at every level, while the coefficient precision
automatically follows the order of the particular class in that level. -/
theorem ideal_of_class_relations (b : Additive X) (B : Module.Basis (Fin 2) ℚ_[2] V)
    (base : B 0 = SignedFiniteAnnihilation2893.oneTensor b)
    (first : SignedRationalCharacteristic2893.augmentation (Additive X) gamma (B 0) = B 1)
    (s : ℕ) (kill : ∀ n, (SignedFiniteAnnihilation2893.localResidual
        (SignedLayerClasses2893.primaryForward n) (b.toMul.val n)
        (SignedCyclicCriterion2893.constant.appr (coordinatePrecision b n))
        (SignedCyclicCriterion2893.linear.appr (coordinatePrecision b n)))^(2^s) = 1) :
    ∃ c0 c1 : ℤ_[2],
      P = Polynomial.C (c0 : ℚ_[2]) + Polynomial.C (c1 : ℚ_[2]) * Polynomial.X + Polynomial.X^2 ∧
      SignedNativeSeries2893.candidate ∈ Ideal.span {SignedNativeSeries2893.quadratic c0 c1} :=
  SignedFiniteAnnihilation2893.ideal_from_local_powers SignedLayerClasses2893.layerClass
    SignedArithmeticTower2893.norm SignedLayerClasses2893.primaryForward SignedArithmeticTower2893.norm_forward
    b B base first (coordinatePrecision b) (coordinate_order b) s kill

noncomputable def characteristicSeries (h0 : ‖P.coeff 0‖ ≤ 1) (h1 : ‖P.coeff 1‖ ≤ 1) :
    PowerSeries ℤ_[2] :=
  SignedNativeSeries2893.quadratic (SignedRationalCharacteristic2893.integralCoeff P 0 h0)
    (SignedRationalCharacteristic2893.integralCoeff P 1 h1)

theorem coefficient_comparison (rank : Module.finrank ℚ_[2] V = 2)
    (h0 : ‖P.coeff 0‖ ≤ 1) (h1 : ‖P.coeff 1‖ ≤ 1)
    (even0 : PadicInt.toZModPow 1 (SignedRationalCharacteristic2893.integralCoeff P 0 h0)=0)
    (even1 : PadicInt.toZModPow 1 (SignedRationalCharacteristic2893.integralCoeff P 1 h1)=0)
    (ideal : SignedNativeSeries2893.candidate ∈ Ideal.span {characteristicSeries h0 h1}) :
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1)*Polynomial.X + Polynomial.X^2 ∧
    PadicInt.toZModPow 6 (SignedRationalCharacteristic2893.integralCoeff P 0 h0)=40 ∧
    PadicInt.toZModPow 6 (SignedRationalCharacteristic2893.integralCoeff P 1 h1)=18 :=
  ⟨SignedRationalCharacteristic2893.characteristic_quadratic (Additive X) gamma rank,
    SignedNativeSeries2893.characteristic_bits_of_principal_inclusion _ _ even0 even1 ideal⟩

end Reimann.SignedIwasawaCharacteristic2893
