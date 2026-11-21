import Reimann2893.SignedLayerClasses2893
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs

/-! Finiteness of the ideal class groups in the tower over ℚ(√-2893).
The admissible absolute value on ℤ supplies the class-number finiteness theorem. -/
namespace Reimann.SignedFiniteClasses2893

open NumberField SignedFieldLayers2893 SignedLayerClasses2893

theorem finite_layer_classes (n : ℕ) : Finite (layerClass n) := by
  letI : Fintype (layerClass n) :=
    ClassGroup.fintypeOfAdmissibleOfFinite ℚ (Layer n) AbsoluteValue.absIsAdmissible
  infer_instance

theorem finite_two_classes (n : ℕ) : Finite (layerTwoClass n) := by
  letI := finite_layer_classes n
  exact Finite.of_injective Subtype.val Subtype.val_injective

end Reimann.SignedFiniteClasses2893
