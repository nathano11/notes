import Reimann277.CyclotomicInertia
import Reimann277.BiquadraticNumberField
import Reimann277.SplitQuotient
import Reimann277.Inertia
import Reimann277.IdealArtin
import Reimann277.LocalClassGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Localization.Away.Basic

namespace Reimann.TameArtin277

open TameBiquadraticField277 TameCyclotomicLocal277

/-- Algebraic closure of the actual biquadratic base field. -/
abbrev Closure := AlgebraicClosure Biquadratic

theorem mem_cutField (r n : ℕ) (x : Closure) :
    x ∈ cutField r n ↔ ∀ g ∈ globalKernel r n, asAut g x = x :=
  IntermediateField.mem_fixedField_iff _ _

theorem no_real_place (r n : ℕ) : ¬Nonempty (cutField r n →+* ℝ) := by
  rintro ⟨f⟩
  exact no_real_embedding ⟨f.comp (algebraMap Biquadratic (cutField r n))⟩

instance cutNumberField (r n : ℕ) : NumberField (cutField r n) := by
  letI := (cutField_finite_galois r n).1
  exact NumberField.of_module_finite Biquadratic _

abbrev CutIntegers (r n : ℕ) := NumberField.RingOfIntegers (cutField r n)

abbrev SIntegers (r n : ℕ) := Localization.Away (277 : CutIntegers r n)

instance sIntegersDomain (r n : ℕ) : IsDomain (SIntegers r n) :=
  Localization.Away.isDomain (by norm_num : (277 : CutIntegers r n) ≠ 0)

abbrev SClassGroup (r n : ℕ) := ClassGroup (SIntegers r n)

instance sClass_finite (r n : ℕ) : Finite (SClassGroup r n) :=
  TameLocalClass277.class_finite_away_277 (cutField r n) (SIntegers r n)

/-- Kill the actual inertia elements over all finite primes away from 277
and all conjugates of the four local restriction images on the upstairs kernel. -/
noncomputable def localRelations (r n : ℕ) : Set (globalKernel r n) :=
  TameInertia277.away (globalKernel r n) ∪ atPlaces r n

abbrev UnramifiedSplitQuotient (r n : ℕ) :=
  TameSplitQuotient277.SplitQuotient (localRelations r n)

noncomputable def project (r n : ℕ) : globalKernel r n →ₜ* UnramifiedSplitQuotient r n :=
  TameSplitQuotient277.project _

theorem project_surjective (r n : ℕ) : Function.Surjective (project r n) :=
  TameSplitQuotient277.project_surjective _

theorem unramified_away (r n : ℕ) (P : Ideal (TameInertia277.Integers Closure))
    (hm : P.IsMaximal) (hp : (277 : TameInertia277.Integers Closure) ∉ P)
    (g : globalKernel r n) (hg : g.val ∈ TameInertia277.inertia P) : project r n g = 1 :=
  TameSplitQuotient277.project_local _ (Or.inl ⟨P,hm,hp,hg⟩)

theorem split_at_277 (r n : ℕ) (g : globalKernel r n) (hg : g ∈ atPlaces r n) :
    project r n g = 1 := TameSplitQuotient277.project_local _ (Or.inr hg)

theorem quotient_commutes (r n : ℕ) (u v : UnramifiedSplitQuotient r n) : u*v=v*u :=
  TameSplitQuotient277.project_commutes _ u v

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [T2Space A]

theorem continuous_split_characters (r n : ℕ) (χ : globalKernel r n →ₜ* A) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), χ x = 1) ∧
     (∀ x ∈ atPlaces r n, χ x = 1)) ↔
     ∃! φ : UnramifiedSplitQuotient r n →ₜ* A, ∀ x, φ (project r n x) = χ x := by
  unfold project
  rw [← TameSplitQuotient277.continuous_characters (localRelations r n) χ]
  exact ⟨fun H x hx => hx.elim (H.1 x) (H.2 x),
    fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩⟩

/-- The missing global reciprocity identification, oriented from Galois to ideal classes. -/
abbrev ClassReciprocity (r n : ℕ) := UnramifiedSplitQuotient r n ≃* SClassGroup r n

noncomputable def fromIdealSymbol {r n : ℕ}
    (a : TameIdealArtin277.IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n)) :
    ClassReciprocity r n := (TameIdealArtin277.classToGalois a).symm

theorem ideal_symbol_orientation {r n : ℕ}
    (a : TameIdealArtin277.IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n))
    (I : TameIdealArtin277.InvertibleIdeals (SIntegers r n)) :
    fromIdealSymbol a (a.symbol I) = ClassGroup.mk (FractionRing (SIntegers r n)) I :=
  TameIdealArtin277.galoisToClass_symbol a I

noncomputable def toClassGroup {r n : ℕ} (e : ClassReciprocity r n) : globalKernel r n →* SClassGroup r n :=
  e.toMonoidHom.comp (project r n).toMonoidHom

theorem toClassGroup_surjective {r n : ℕ} (e : ClassReciprocity r n) :
    Function.Surjective (toClassGroup e) := e.surjective.comp (project_surjective r n)

/-- The inverse Artin projection is continuous for the discrete topology on
the finite localized class group. This formulation tests all preimages. -/
theorem class_projection_open_preimage {r n : ℕ}
    (e : ClassReciprocity r n) (U : Set (SClassGroup r n)) :
    IsOpen ((toClassGroup e) ⁻¹' U) := by
  letI : IsClosed (TameSplitQuotient277.kernel (localRelations r n) : Set (globalKernel r n)) :=
    Subgroup.isClosed_topologicalClosure _
  letI : Finite (UnramifiedSplitQuotient r n) := Finite.of_injective e e.injective
  exact (isOpen_discrete (e ⁻¹' U)).preimage (project r n).continuous

theorem class_character_descent {r n : ℕ} (e : ClassReciprocity r n)
    (χ : globalKernel r n →ₜ* A) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), χ x = 1) ∧
     (∀ x ∈ atPlaces r n, χ x = 1)) ↔
      ∃! ψ : SClassGroup r n →* A, ∀ x, ψ (toClassGroup e x) = χ x := by
  constructor
  · intro h
    obtain ⟨φ,hφ,_⟩ := (continuous_split_characters r n χ).mp h
    let ψ := φ.toMonoidHom.comp e.symm.toMonoidHom
    have he (x : globalKernel r n) : ψ (toClassGroup e x) = χ x := by
      change φ (e.symm (e (project r n x))) = χ x
      rw [e.symm_apply_apply,hφ]
    refine ⟨ψ,he,?_⟩
    intro θ hθ
    ext c
    obtain ⟨x,rfl⟩ := toClassGroup_surjective e c
    exact (hθ x).trans (he x).symm
  · rintro ⟨ψ,hψ,_⟩
    have one (x : globalKernel r n) (hx : x ∈ localRelations r n) : χ x = 1 := by
      rw [← hψ]
      change ψ (e (project r n x)) = 1
      rw [show project r n x = 1 from TameSplitQuotient277.project_local _ hx, map_one, map_one]
    exact ⟨fun x hx => one x (Or.inl hx), fun x hx => one x (Or.inr hx)⟩

end Reimann.TameArtin277
