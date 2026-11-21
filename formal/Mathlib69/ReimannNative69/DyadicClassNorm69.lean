import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.Basic

/-! The ideal-class norm descends directly from the relative ideal norm
on nonzero integral ideals, without using an Artin isomorphism. -/
namespace Reimann.DyadicClassNorm69

open scoped nonZeroDivisors NumberField

variable (R : Type*) {S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

noncomputable def idealNorm : (Ideal S)⁰ →* (Ideal R)⁰ where
  toFun I := ⟨Ideal.relNorm R I.val,mem_nonZeroDivisors_iff_ne_zero.mpr
    (Ideal.relNorm_eq_bot_iff.not.mpr (mem_nonZeroDivisors_iff_ne_zero.mp I.property))⟩
  map_one' := Subtype.ext (map_one (Ideal.relNorm R))
  map_mul' I J := Subtype.ext (map_mul (Ideal.relNorm R) I.val J.val)

/-- Apply the relative ideal norm to xI=yJ. The scalars become their integral norms. -/
theorem norm_preserves_class {I J : (Ideal S)⁰} (h : ClassGroup.mk0 I=ClassGroup.mk0 J) :
    ClassGroup.mk0 (idealNorm R I)=ClassGroup.mk0 (idealNorm R J) := by
  obtain ⟨x,y,hx,hy,eq⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨Algebra.intNorm R S x,Algebra.intNorm R S y,
    Algebra.intNorm_ne_zero.mpr hx,Algebra.intNorm_ne_zero.mpr hy,?_⟩
  change Ideal.span {Algebra.intNorm R S x} * Ideal.relNorm R I.val =
    Ideal.span {Algebra.intNorm R S y} * Ideal.relNorm R J.val
  simpa only [map_mul,Ideal.relNorm_singleton] using congrArg (Ideal.relNorm R) eq

noncomputable def onClass (c : ClassGroup S) : ClassGroup R :=
  ClassGroup.mk0 (idealNorm R (ClassGroup.mk0_surjective c).choose)

theorem onClass_mk0 (I : (Ideal S)⁰) :
    onClass R (ClassGroup.mk0 I)=ClassGroup.mk0 (idealNorm R I) :=
  norm_preserves_class R (ClassGroup.mk0_surjective (ClassGroup.mk0 I)).choose_spec

noncomputable def classNorm : ClassGroup S →* ClassGroup R where
  toFun := onClass R
  map_one' := by
    have h := onClass_mk0 R (1 : (Ideal S)⁰)
    simpa only [map_one] using h
  map_mul' x y := by
    obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective x
    obtain ⟨J,rfl⟩ := ClassGroup.mk0_surjective y
    rw [← map_mul,onClass_mk0,onClass_mk0,onClass_mk0,map_mul,map_mul]

theorem classNorm_mk0 (I : (Ideal S)⁰) :
    classNorm R (ClassGroup.mk0 I)=ClassGroup.mk0 (idealNorm R I) := onClass_mk0 R I

theorem classNorm_tower (T : Type*) [CommRing T] [IsDedekindDomain T]
    [Algebra R T] [Algebra T S] [IsScalarTower R T S] [Module.Finite R T] [Module.Finite T S]
    [Module.IsTorsionFree R T] [Module.IsTorsionFree T S] (c : ClassGroup S) :
    classNorm R (classNorm T c)=classNorm R c := by
  obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective c
  simp only [classNorm_mk0]
  exact congrArg ClassGroup.mk0 (Subtype.ext (Ideal.relNorm_relNorm R T I.val))

/-- The descending class norm on the actual rings of integers in a finite
extension of number fields, expressed as a group homomorphism. -/
noncomputable def numberField_norm (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : ClassGroup (𝓞 L) →* ClassGroup (𝓞 K) :=
  classNorm (𝓞 K)

theorem numberField_norm_mk0 (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (I : (Ideal (𝓞 L))⁰) :
    numberField_norm K L (ClassGroup.mk0 I)=ClassGroup.mk0 (idealNorm (𝓞 K) I) :=
  classNorm_mk0 _ I

theorem numberField_norm_tower (K M L : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
    [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    (c : ClassGroup (𝓞 L)) : numberField_norm K M (numberField_norm M L c)=numberField_norm K L c :=
  classNorm_tower (𝓞 K) (𝓞 M) c

attribute [local instance] FractionRing.liftAlgebra

/-- On an actual prime ideal the class norm raises its contraction's class to
the actual residue degree. -/
theorem classNorm_prime [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : (Ideal S)⁰) (p : (Ideal R)⁰) [P.val.IsMaximal] [p.val.IsMaximal] [P.val.LiesOver p.val] :
    classNorm R (ClassGroup.mk0 P)=(ClassGroup.mk0 p)^(P.val.inertiaDeg R) := by
  rw [classNorm_mk0,←map_pow]
  exact congrArg ClassGroup.mk0 (Subtype.ext (Ideal.relNorm_eq_pow_of_isMaximal P.val p.val))

theorem numberField_norm_prime (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (P : (Ideal (𝓞 L))⁰) (p : (Ideal (𝓞 K))⁰)
    [P.val.IsMaximal] [p.val.IsMaximal] [P.val.LiesOver p.val] :
    numberField_norm K L (ClassGroup.mk0 P)=(ClassGroup.mk0 p)^(P.val.inertiaDeg (𝓞 K)) :=
  classNorm_prime (𝓞 K) P p

end Reimann.DyadicClassNorm69
