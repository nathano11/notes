import Reimann.CircularNonpower69
import Reimann.CircularQuadraticPower69
import Reimann.CircularReduction69

/-! A power in either integral presentation would remain a power at the
auxiliary residue. A norm transfer explains the later degree-276 input. -/
namespace Reimann.CircularPowerDescent69

open Reimann.CircularQuadratic69 Reimann.CircularQuadraticPower69
open Reimann.CircularReduction69 Reimann.CircularNonpower69

theorem nonpower_of_specialization {A B : Type} (f : A → B) (pa : A → A) (pb : B → B)
    (commutes : ∀ y, f (pa y) = pb (f y)) (u : A)
    (nonpower : ∀ b, pb b ≠ f u) (y : A) : pa y ≠ u := by
  intro h
  exact nonpower (f y) ((commutes y).symm.trans (congrArg f h))

theorem quadratic_units_not_powers (y : Element) :
    orderPower y 277 ≠ epsilon ∧ orderPower y 277 ≠ conjugate epsilon := by
  let f := evaluateAt (92746 : Fin 114679)
  have commutes (w : Element) : f (orderPower w 277) = (f w)^277 :=
    evaluateAt_power 92746 auxiliary_theta w 277
  constructor
  · apply nonpower_of_specialization f (fun w => orderPower w 277) (fun b => b^277) commutes
    intro b
    change b^277 ≠ evaluateAt (92746 : Fin 114679) epsilon
    rw [auxiliary_values.1]
    exact (signed_nonpowers b).1
  · apply nonpower_of_specialization f (fun w => orderPower w 277) (fun b => b^277) commutes
    intro b
    change b^277 ≠ evaluateAt (92746 : Fin 114679) (conjugate epsilon)
    rw [auxiliary_values.2]
    exact (signed_nonpowers b).2

theorem signed_classes_not_powers (y : ResidueOrder) :
    qpow y 277 ≠ signedClass 1 ∧ qpow y 277 ≠ signedClass 276 := by
  have commutes (w : ResidueOrder) : reduce (qpow w 277) = (reduce w)^277 := reduce_pow w 277
  constructor
  · apply nonpower_of_specialization reduce (fun w => qpow w 277) (fun b => b^277) commutes
    intro b
    rw [reduce_positive]
    exact (signed_nonpowers b).1
  · apply nonpower_of_specialization reduce (fun w => qpow w 277) (fun b => b^277) commutes
    intro b
    rw [reduce_negative]
    exact (signed_nonpowers b).2

theorem degree276_residue_not_power (b : Fin 114679) : b^277 ≠ 48891^276 := by
  intro h
  have hr := one_more_power_of_inverse (48891 : Fin 114679) 65813 b 276 auxiliary_inverse h
  exact (signed_nonpowers (b*65813)).2 hr

/-- The specialization on an overfield must be constructed as norm followed
by reduction. Its two required identities are explicit here. -/
theorem degree276_norm_obstruction {A : Type} (normRed : A → Fin 114679)
    (power277 : A → A) (u : A) (map_power : ∀ w, normRed (power277 w) = (normRed w)^277)
    (norm_u : normRed u = (48891 : Fin 114679)^276) (y : A) : power277 y ≠ u := by
  apply nonpower_of_specialization normRed power277 (fun b => b^277) map_power
  intro b
  rw [norm_u]
  exact degree276_residue_not_power b

end Reimann.CircularPowerDescent69
