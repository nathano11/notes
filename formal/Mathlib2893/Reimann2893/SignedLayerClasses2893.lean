import Reimann2893.SignedClassAction2893
import Reimann2893.SignedFieldLayers2893
import Reimann2893.SignedForwardPeriod2893

/-! The ordinary and two-primary ideal class groups of the explicit cyclotomic layers
over the imaginary quadratic field of conductor 2893 in the even-character convention. -/
namespace Reimann.SignedLayerClasses2893

open NumberField SignedFieldLayers2893
open scoped nonZeroDivisors

instance layerNumberField (n : ℕ) : NumberField (Layer n) where
  to_charZero := inferInstance
  to_finiteDimensional := finiteOverRat n

abbrev layerClass (n : ℕ) := ClassGroup (𝓞 (Layer n))

abbrev layerTwoClass (n : ℕ) := SignedClassAction2893.twoClasses (Layer n)

noncomputable def classForward (n : ℕ) : layerClass n ≃* layerClass n :=
  SignedClassAction2893.forward (forward n)

noncomputable def primaryForward (n : ℕ) : layerTwoClass n ≃* layerTwoClass n :=
  SignedClassAction2893.primaryForward (forward n)

/-- The forward field automorphism takes the class of a nonzero integral ideal to
the class of its image in the same layer's integer ring. -/
theorem forward_on_integral_ideal (n : ℕ) (I : (Ideal (𝓞 (Layer n)))⁰) :
    classForward n (ClassGroup.mk0 I) = ClassGroup.mk0
      ⟨I.val.map (RingOfIntegers.mapRingEquiv (forward n)), mem_nonZeroDivisors_iff_ne_zero.mpr <|
        (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv (forward n)).injective).not.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mp I.property)⟩ :=
  SignedClassAction2893.transport_mk0 (forward n) I

theorem forward_on_classes (n : ℕ) (x : layerTwoClass n) :
    (primaryForward n x).val = classForward n x.val :=
  SignedClassAction2893.forward_on_classes (forward n) x

theorem primaryForward_period (n : ℕ) : primaryForward n ^ (2^n) = 1 :=
  SignedClassAction2893.primaryForward_period (forward n) (2^n)
    (SignedForwardPeriod2893.forward_period n)

end Reimann.SignedLayerClasses2893
