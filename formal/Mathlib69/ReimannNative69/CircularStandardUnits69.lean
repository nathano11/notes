import ReimannNative69.CommonIntegralUnits69
import ReimannNative69.CircularCommonField69

/-! Transport into any ring representing the integral closure of ℤ in the
concrete real field. Only the inclusion of conductor 69 is used. -/
namespace Reimann.CircularStandardUnits69

open CircularCommonField69 CircularSubgroup69 CommonIntegralUnits69 CircularPolynomial69

variable (O : Type*) [CommRing O] [Algebra O realField] [IsIntegralClosure O ℤ realField]

noncomputable def numbersAt (f : Nat) : Subgroup Kˣ :=
  CircularOrbitFamily69.circularNumbers (fun n => n ∣ f) (fun y => y ∈ realField)

theorem numbers_at_19113 : numbersAt 19113 = numberGroup := rfl

theorem generators_at_level (f : Nat) (hf : 69 ∣ f) :
    normGenerators x CommonAmbient69.x_primitive (CircularRealUnit69.RealPart c u v) ⊆ numbersAt f := by
  unfold numbersAt
  rw [real_predicate]
  rintro w ⟨a, ha, hw⟩
  exact CircularOrbitFamily69.norm_factor_mem hf x CommonAmbient69.x_primitive
    (CircularRealUnit69.RealPart c u v) a ha w hw

theorem signed_units_at_level (f : Nat) (hf : 69 ∣ f) :
    ∃ w : Oˣ, integerEmbedding realField O w.val = signedProduct x 1 ∧
      integerEmbedding realField O (w⁻¹).val = signedProduct x 276 ∧
      w ∈ standardCircularUnits realField O (numbersAt f) ∧
      w⁻¹ ∈ standardCircularUnits realField O (numbersAt f) := by
  obtain ⟨w, he, hi, hw, hinv⟩ := CommonIntegralUnits69.positive_and_inverse x u v
    CommonAmbient69.x_primitive radical_values.1 radical_values.2.1 c CommonConjugation69.compatible
    realField real_membership O (numbersAt f) (generators_at_level f hf)
  exact ⟨w, he, hi.trans signed_inverse_value, hw, hinv⟩

theorem standard_integral_closure_units :
    ∃ w : Oˣ, integerEmbedding realField O w.val = signedProduct x 1 ∧
      integerEmbedding realField O (w⁻¹).val = signedProduct x 276 ∧
      w ∈ standardCircularUnits realField O numberGroup ∧
      w⁻¹ ∈ standardCircularUnits realField O numberGroup :=
  signed_units_at_level O 19113 CircularOrbitFamily69.conductor_divisor

end Reimann.CircularStandardUnits69
