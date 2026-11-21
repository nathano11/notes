import Reimann2893.SignedClassTower2893
import Reimann2893.SignedLayerClasses2893
import Reimann2893.SignedIdealNormEquivariance2893
import Reimann2893.SignedAdicAction2893

/-! The inverse limit of the ideal 2-class groups of the actual quadratic
number-field layers, with norm as transition and the fifth-power forward action. -/
namespace Reimann.SignedArithmeticTower2893

open NumberField
open SignedFieldLayers2893 (Layer)
open scoped nonZeroDivisors

abbrev integers (n : ℕ) := 𝓞 (Layer n)

noncomputable def norm (n : ℕ) :
    SignedLayerClasses2893.layerTwoClass (n+1) →* SignedLayerClasses2893.layerTwoClass n :=
  SignedClassTower2893.twoClassNorm (integers n) (S := integers (n+1))

/-- Along each of the actual quadratic steps, relative norm after extension squares every class. -/
theorem norm_after_extension (n : ℕ) (c : SignedLayerClasses2893.layerClass n) :
    SignedClassTower2893.classNorm (integers n)
      (ClassGroup.extendedHom (integers n) (integers (n+1)) c) = c^2 := by
  rw [SignedClassTower2893.classNorm_extended,
    ← IsFractionRing.finrank_eq (integers n) (Layer n) (integers (n+1)) (Layer (n+1)),
    SignedFieldLayers2893.step_degree_two]

theorem field_square (n : ℕ) (x : Layer n) :
    SignedFieldLayers2893.forward (n+1) (algebraMap (Layer n) (Layer (n+1)) x) =
      algebraMap (Layer n) (Layer (n+1)) (SignedFieldLayers2893.forward n x) :=
  SignedFieldLayers2893.forward_include n x

theorem norm_forward (n : ℕ) (x : SignedLayerClasses2893.layerTwoClass (n+1)) :
    norm n (SignedLayerClasses2893.primaryForward (n+1) x) =
      SignedLayerClasses2893.primaryForward n (norm n x) := by
  apply Subtype.ext
  exact SignedClassTower2893.classNorm_equivariant (integers n)
    (RingOfIntegers.mapRingEquiv (SignedFieldLayers2893.forward n))
    (RingOfIntegers.mapRingEquiv (SignedFieldLayers2893.forward (n+1)))
    (fun I => (SignedIdealNormEquivariance2893.map_relNorm
      (SignedFieldLayers2893.forward n) (SignedFieldLayers2893.forward (n+1)) (field_square n) I).symm)
    x.val

/-- The inverse limit definition of the unramified 2-class Iwasawa module, in multiplicative notation. -/
noncomputable abbrev X := SignedNormLimit2893.coherent norm

noncomputable def gamma : X ≃* X :=
  SignedNormLimit2893.forward norm SignedLayerClasses2893.primaryForward norm_forward

theorem gamma_at_level (x : X) (n : ℕ) :
    (gamma x).val n = SignedLayerClasses2893.primaryForward n (x.val n) := rfl

/-- On an integral representative of a coherent class, the forward generator takes the image ideal. -/
theorem gamma_on_ideal (x : X) (n : ℕ) (I : (Ideal (integers n))⁰)
    (h : (x.val n).val = ClassGroup.mk0 I) :
    ((gamma x).val n).val = ClassGroup.mk0
      ⟨I.val.map (RingOfIntegers.mapRingEquiv (SignedFieldLayers2893.forward n)),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective
            (RingOfIntegers.mapRingEquiv (SignedFieldLayers2893.forward n)).injective).not.mpr
              (mem_nonZeroDivisors_iff_ne_zero.mp I.property)⟩ := by
  rw [gamma_at_level, SignedLayerClasses2893.forward_on_classes, h,
    SignedLayerClasses2893.forward_on_integral_ideal]

theorem primary_period (n : ℕ) (x : SignedLayerClasses2893.layerTwoClass n) :
    SignedAdicAction2893.iterate (SignedLayerClasses2893.primaryForward n) (2^n) x = x := by
  exact (SignedAdicAction2893.iterate_eq_pow_apply _ _ x).trans
    (congrArg (fun g : MulAut _ => g x) (SignedLayerClasses2893.primaryForward_period n))

/-- The full algebraic action of coherent dyadic exponents on the norm limit. -/
noncomputable def gammaPower (z : DyadicLattice.Scalar) : X ≃* X :=
  SignedAdicAction2893.act norm SignedLayerClasses2893.primaryForward norm_forward primary_period z

theorem gammaPower_one (x : X) : gammaPower (DyadicLattice.natScalar 1) x = gamma x :=
  SignedAdicAction2893.act_one norm SignedLayerClasses2893.primaryForward norm_forward primary_period x

theorem gammaPower_add (z w : DyadicLattice.Scalar) (x : X) :
    gammaPower (DyadicLattice.add z w) x = gammaPower w (gammaPower z x) :=
  SignedAdicAction2893.act_add norm SignedLayerClasses2893.primaryForward norm_forward primary_period z w x

end Reimann.SignedArithmeticTower2893
