import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.GroupTheory.Torsion
import Reimann2893.SignedNormLimit2893

/-! Norm maps on ideal classes and the coherent 2-primary class tower. -/
namespace Reimann.SignedClassTower2893

open scoped nonZeroDivisors
open Module

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]

/-- The arithmetic relative ideal norm carries a nonzero integral ideal to a nonzero ideal. -/
noncomputable def nonzeroNorm (I : (Ideal S)⁰) : (Ideal R)⁰ :=
  ⟨Ideal.relNorm R I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
    (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp I.2) (Ideal.relNorm_eq_bot_iff.mp h))⟩

theorem norm_respects_classes {I J : (Ideal S)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (nonzeroNorm R I) = ClassGroup.mk0 (nonzeroNorm R J) := by
  obtain ⟨x,y,hx,hy,hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  have nz (z : S) (hz : z ≠ 0) : Algebra.intNorm R S z ≠ 0 := by
    intro he
    have hbot : Ideal.relNorm R (Ideal.span ({z} : Set S)) = ⊥ := by
      rw [Ideal.relNorm_singleton, he, Ideal.span_singleton_zero]
    exact hz (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp hbot))
  refine ClassGroup.mk0_eq_mk0_iff.mpr
    ⟨Algebra.intNorm R S x, Algebra.intNorm R S y, nz x hx, nz y hy, ?_⟩
  simpa only [map_mul, Ideal.relNorm_singleton, nonzeroNorm] using congrArg (Ideal.relNorm R) hxy

/-- Choose an integral representative of a class. Independence of this choice is proved above. -/
noncomputable def representative (x : ClassGroup S) : (Ideal S)⁰ :=
  (ClassGroup.mk0_surjective x).choose

theorem representative_class (x : ClassGroup S) : ClassGroup.mk0 (representative x) = x :=
  (ClassGroup.mk0_surjective x).choose_spec

noncomputable def normValue (x : ClassGroup S) : ClassGroup R :=
  ClassGroup.mk0 (nonzeroNorm R (representative x))

theorem normValue_mk0 (I : (Ideal S)⁰) :
    normValue R (ClassGroup.mk0 I) = ClassGroup.mk0 (nonzeroNorm R I) :=
  norm_respects_classes R (representative_class (ClassGroup.mk0 I))

/-- Relative norm on the actual ideal class groups, determined on nonzero integral ideals. -/
noncomputable def classNorm : ClassGroup S →* ClassGroup R where
  toFun := normValue R
  map_one' := by
    rw [← (ClassGroup.mk0 : (Ideal S)⁰ →* ClassGroup S).map_one, normValue_mk0]
    have h : nonzeroNorm R (1 : (Ideal S)⁰) = 1 := Subtype.ext (map_one _)
    rw [h, map_one]
  map_mul' a b := by
    obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J,rfl⟩ := ClassGroup.mk0_surjective b
    rw [← map_mul, normValue_mk0, normValue_mk0, normValue_mk0, ← map_mul]
    apply congrArg ClassGroup.mk0
    exact Subtype.ext (map_mul (Ideal.relNorm R) _ _)

theorem classNorm_mk0 (I : (Ideal S)⁰) :
    classNorm R (ClassGroup.mk0 I) = ClassGroup.mk0 (nonzeroNorm R I) :=
  normValue_mk0 R I

/-- Extending an ideal class and taking its relative norm raises it to the extension rank. -/
theorem classNorm_extended (x : ClassGroup R) :
    classNorm R (ClassGroup.extendedHom R S x) = x ^ Module.finrank R S := by
  obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective x
  rw [ClassGroup.extendedHom_mk0, classNorm_mk0, ← map_pow]
  apply congrArg ClassGroup.mk0
  exact Subtype.ext (Ideal.relNorm_algebraMap S I.val)

/-- Norm compatibility across an intermediate field is inherited from the transitivity of ideal norms. -/
theorem classNorm_trans (T : Type*) [CommRing T] [IsDedekindDomain T]
    [Algebra R T] [Algebra T S] [IsScalarTower R T S] [Module.Finite R T] [Module.Finite T S]
    [IsTorsionFree R T] [IsTorsionFree T S] (x : ClassGroup S) :
    classNorm R (classNorm T x) = classNorm R x := by
  obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective x
  rw [classNorm_mk0, classNorm_mk0, classNorm_mk0]
  apply congrArg ClassGroup.mk0
  exact Subtype.ext (Ideal.relNorm_relNorm R T I.val)

/-- Equivariance of the relative ideal norm descends to equality on ideal classes. -/
theorem classNorm_equivariant (e : R ≃+* R) (f : S ≃+* S)
    (square : ∀ I : Ideal S, Ideal.relNorm R (I.map f) = (Ideal.relNorm R I).map e)
    (x : ClassGroup S) :
    classNorm R (ClassGroup.mulEquiv f x) = ClassGroup.mulEquiv e (classNorm R x) := by
  obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective x
  rw [ClassGroup.mulEquiv_mk0, classNorm_mk0, classNorm_mk0, ClassGroup.mulEquiv_mk0]
  apply congrArg ClassGroup.mk0
  exact Subtype.ext (square I.val)

/-- Restrict the actual norm to the classes annihilated by a power of two. -/
noncomputable def twoClassNorm :
    CommGroup.primaryComponent (ClassGroup S) 2 →*
      CommGroup.primaryComponent (ClassGroup R) 2 :=
  ((classNorm R (S := S)).comp (CommGroup.primaryComponent (ClassGroup S) 2).subtype).codRestrict _
    (fun x => by
      obtain ⟨k,hk⟩ := CommGroup.mem_primaryComponent.mp x.2
      refine ⟨k, ?_⟩
      change (classNorm R (x : ClassGroup S)) ^ 2 ^ k = 1
      rw [← map_pow, hk, map_one])

section Tower

universe u
variable (A : ℕ → Type u) [∀ n, CommRing (A n)] [∀ n, IsDedekindDomain (A n)]
  [∀ n, Algebra (A n) (A (n+1))] [∀ n, Module.Finite (A n) (A (n+1))]
  [∀ n, IsTorsionFree (A n) (A (n+1))]

/-- The inverse limit in multiplicative coordinates: the transition maps are ideal class norms. -/
noncomputable def coherentClasses : Subgroup (∀ n, CommGroup.primaryComponent (ClassGroup (A n)) 2) :=
  SignedNormLimit2893.coherent (G := fun n => ↥(CommGroup.primaryComponent (ClassGroup (A n)) 2))
    (fun n => twoClassNorm (A n) (S := A (n+1)))

/-- A norm-equivariant forward automorphism on the tower acts on its inverse limit. -/
noncomputable def forward_on_limit
    (γ : ∀ n, (CommGroup.primaryComponent (ClassGroup (A n)) 2) ≃*
      (CommGroup.primaryComponent (ClassGroup (A n)) 2))
    (comm : ∀ n x, twoClassNorm (A n) (γ (n+1) x) = γ n (twoClassNorm (A n) x)) :
    coherentClasses A ≃* coherentClasses A :=
  SignedNormLimit2893.forward (G := fun n => ↥(CommGroup.primaryComponent (ClassGroup (A n)) 2))
    (fun n => twoClassNorm (A n) (S := A (n+1))) γ comm

end Tower

end Reimann.SignedClassTower2893
