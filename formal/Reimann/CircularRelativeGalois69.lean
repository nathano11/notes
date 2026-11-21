import Reimann.CircularGalois69
import Reimann.CircularPowerSubstitution69
import Reimann.CircularRootOrbit69

/-! All and only the positive exponents act by relative field automorphisms. -/

namespace Reimann.CircularRelativeGalois69

open Lean.Grind CircularGalois69 CircularFieldReduction69 CircularPowerSubstitution69
  CircularRootOrbit69 CircularSubstitution69 CircularPolynomial69

variable {R : Type} [Field R] [IsCharP R 0]

theorem label_exists {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) :
    ∃ a : Fin 69, generatorImage e = x^a.val ∧ Nat.Coprime a.val 69 ∧
      ∀ b : Fin 69, generatorImage e = x^b.val → b = a := by
  have hy := generator_image_primitive e
  exact primitive_root_label x _ hx.order69 hx.not23 hx.not3 hy.order69 hy.not23 hy.not3

noncomputable def label {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) : Fin 69 :=
  Classical.choose (label_exists e)

theorem label_spec {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) :
    generatorImage e = x^(label e).val ∧ Nat.Coprime (label e).val 69 ∧
      ∀ b : Fin 69, generatorImage e = x^b.val → b = label e :=
  Classical.choose_spec (label_exists e)

theorem fixes_iff_label {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) :
    FixesQuadratic e ↔ eta (label e).val = 1 := by
  obtain ⟨h,hu,_⟩ := label_spec e
  rw [fixes_quadratic_iff, h]
  exact period_fixed_iff_positive x hx (label e) hu (primitive_unit_power x hx _ hu)

abbrev PositiveLabel := {a : Fin 69 // eta a.val = 1}

abbrev RelativeAuto (x : R) (hx : Primitive69 x) := {e : FieldIso x x hx hx // FixesQuadratic e}

noncomputable def toLabel {x : R} {hx : Primitive69 x} (e : RelativeAuto x hx) : PositiveLabel :=
  ⟨label e.val,(fixes_iff_label e.val).mp e.property⟩

theorem positive_unit (a : PositiveLabel) : Nat.Coprime a.val.val 69 :=
  (CircularKernel69.unit_partition a.val).mpr (Or.inl a.property)

theorem power_generator (x : R) (hx : Primitive69 x) (a : Fin 69) (hu : Nat.Coprime a.val 69) :
    generatorImage (power_automorphism x hx a hu) = x^a.val :=
  congrArg Subtype.val (power_automorphism_generator x hx a hu)

theorem power_label (x : R) (hx : Primitive69 x) (a : Fin 69) (hu : Nat.Coprime a.val 69) :
    label (power_automorphism x hx a hu) = a :=
  ((label_spec _).2.2 a (power_generator x hx a hu)).symm

noncomputable def fromLabel (x : R) (hx : Primitive69 x) (a : PositiveLabel) : RelativeAuto x hx :=
  ⟨power_automorphism x hx a.val (positive_unit a), (fixes_iff_label _).mpr
    (by rw [power_label]; exact a.property)⟩

theorem from_generator (x : R) (hx : Primitive69 x) (a : PositiveLabel) :
    generatorImage (fromLabel x hx a).val = x^a.val.val := power_generator x hx a.val (positive_unit a)

theorem to_from (x : R) (hx : Primitive69 x) (a : PositiveLabel) : toLabel (fromLabel x hx a) = a :=
  Subtype.ext (power_label x hx a.val (positive_unit a))

theorem from_to (x : R) (hx : Primitive69 x) (e : RelativeAuto x hx) : fromLabel x hx (toLabel e) = e := by
  apply Subtype.ext
  apply iso_ext_generator
  exact Subtype.ext ((from_generator x hx (toLabel e)).trans (label_spec e.val).1.symm)

end Reimann.CircularRelativeGalois69
