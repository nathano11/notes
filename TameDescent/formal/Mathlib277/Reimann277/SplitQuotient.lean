import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.Commutator.Basic

namespace Reimann.TameSplitQuotient277

open scoped commutatorElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Elements selected at places, together with commutators in the upstairs group. -/
def relations (atPlaces : Set G) : Set G :=
  {x | x ∈ atPlaces ∨ ∃ a b : G, x = ⁅a,b⁆}

def kernel (atPlaces : Set G) : Subgroup G :=
  (Subgroup.normalClosure (relations atPlaces)).topologicalClosure

instance kernelNormal (atPlaces : Set G) : (kernel atPlaces).Normal := by
  unfold kernel
  exact Subgroup.is_normal_topologicalClosure _

abbrev SplitQuotient (atPlaces : Set G) := G ⧸ kernel atPlaces

def project (atPlaces : Set G) : G →ₜ* SplitQuotient atPlaces :=
  { QuotientGroup.mk' (kernel atPlaces) with continuous_toFun := QuotientGroup.continuous_mk }

theorem project_surjective (atPlaces : Set G) : Function.Surjective (project atPlaces) :=
  QuotientGroup.mk'_surjective (kernel atPlaces)

theorem project_one (atPlaces : Set G) {x : G} (hx : x ∈ relations atPlaces) :
    project atPlaces x = 1 :=
  (QuotientGroup.eq_one_iff (N := kernel atPlaces) x).mpr
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hx))

theorem project_local (atPlaces : Set G) {x : G} (hx : x ∈ atPlaces) :
    project atPlaces x = 1 := project_one atPlaces (Or.inl hx)

theorem project_commutes (atPlaces : Set G) (x y : SplitQuotient atPlaces) : x*y = y*x := by
  obtain ⟨a,rfl⟩ := project_surjective atPlaces x
  obtain ⟨b,rfl⟩ := project_surjective atPlaces y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact project_one atPlaces (Or.inr ⟨a,b,rfl⟩)

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [T2Space A]

theorem kills_kernel (atPlaces : Set G) (χ : G →ₜ* A)
    (h : ∀ x ∈ atPlaces, χ x = 1) : kernel atPlaces ≤ χ.toMonoidHom.ker := by
  apply Subgroup.topologicalClosure_minimal
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases hx with hl | ⟨a,b,rfl⟩
    · exact h _ hl
    · change χ ⁅a,b⁆ = 1
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm,mul_comm]
  · exact isClosed_eq χ.continuous continuous_const

def descend (atPlaces : Set G) (χ : G →ₜ* A) (h : ∀ x ∈ atPlaces, χ x = 1) :
    SplitQuotient atPlaces →ₜ* A where
  toMonoidHom := QuotientGroup.lift _ χ.toMonoidHom (kills_kernel atPlaces χ h)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (kernel atPlaces)).continuous_iff.mpr χ.continuous

theorem descend_project (atPlaces : Set G) (χ : G →ₜ* A) (h : ∀ x ∈ atPlaces, χ x = 1) (x : G) :
    descend atPlaces χ h (project atPlaces x) = χ x := rfl

theorem descend_unique (atPlaces : Set G) (f g : SplitQuotient atPlaces →ₜ* A)
    (h : ∀ x : G, f (project atPlaces x) = g (project atPlaces x)) : f = g := by
  ext q
  obtain ⟨x,rfl⟩ := project_surjective atPlaces q
  exact h x

theorem continuous_characters (atPlaces : Set G) (χ : G →ₜ* A) :
    (∀ x ∈ atPlaces, χ x = 1) ↔
      ∃! φ : SplitQuotient atPlaces →ₜ* A, ∀ x, φ (project atPlaces x) = χ x := by
  constructor
  · intro h
    exact ⟨descend atPlaces χ h,descend_project atPlaces χ h,
      fun f hf => descend_unique atPlaces f _ (fun x => (hf x).trans (descend_project atPlaces χ h x).symm)⟩
  · rintro ⟨φ,hφ,_⟩ x hx
    rw [← hφ,project_local atPlaces hx,map_one]

end Reimann.TameSplitQuotient277
