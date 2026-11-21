import Reimann277.Inertia
import Reimann277.SplitQuotient

namespace Reimann.TameQuotientTransport277

open TameInertia277 TameSplitQuotient277
open scoped commutatorElement

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem inertia_conjugate (P : Ideal (Integers L)) (g h : L ≃ₐ[K] L) (hh : h ∈ inertia P) :
    g*h*g⁻¹ ∈ inertia (conjugateIdeal g P) := by
  apply (inertia_iff_residue _ _).mpr
  have h₁ : FrobeniusResidue P 1 h := by
    simpa only [FrobeniusResidue, pow_one] using (inertia_iff_residue P h).mp hh
  simpa only [FrobeniusResidue, pow_one] using frobenius_conjugate P 1 g h h₁

theorem maximal_conjugate (P : Ideal (Integers L)) (g : L ≃ₐ[K] L) (hp : P.IsMaximal) :
    (conjugateIdeal g P).IsMaximal :=
  (Ideal.isMaximal_comap_iff_of_bijective (integralEquiv g⁻¹).toRingHom
    (integralEquiv g⁻¹).bijective).mpr hp

theorem nonmem_conjugate (P : Ideal (Integers L)) (g : L ≃ₐ[K] L) (p : ℕ)
    (hp : (p : Integers L) ∉ P) : (p : Integers L) ∉ conjugateIdeal g P := by
  change (integralEquiv g⁻¹) (p : Integers L) ∉ P
  rwa [map_natCast]

theorem away_conjugate {N : Subgroup (L ≃ₐ[K] L)} (g : L ≃ₐ[K] L) (x : N)
    (hx : x ∈ away N) (hmem : g*x.val*g⁻¹ ∈ N) : (⟨_,hmem⟩ : N) ∈ away N := by
  obtain ⟨P,hm,hp,hi⟩ := hx
  exact ⟨conjugateIdeal g P, maximal_conjugate P g hm, nonmem_conjugate P g 277 hp,
    inertia_conjugate P g x.val hi⟩

section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem kernel_preserved (S : Set G) (f : G →* G) (hf : Continuous f)
    (hs : ∀ x ∈ S, f x ∈ S) : kernel S ≤ (kernel S).comap f := by
  apply Subgroup.topologicalClosure_minimal
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    change f x ∈ kernel S
    apply Subgroup.le_topologicalClosure _
    apply Subgroup.subset_normalClosure
    rcases hx with h | ⟨a,b,rfl⟩
    · exact Or.inl (hs _ h)
    · exact Or.inr ⟨f a,f b,map_commutatorElement f a b⟩
  · exact (Subgroup.isClosed_topologicalClosure _).preimage hf

theorem kernel_map_eq (S : Set G) (e : G ≃* G) (he : Continuous e) (hi : Continuous e.symm)
    (hs : ∀ x, x ∈ S ↔ e x ∈ S) : (kernel S).map e.toMonoidHom = kernel S := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (kernel_preserved S e.toMonoidHom he (fun x hx => (hs x).mp hx))
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply kernel_preserved S e.symm.toMonoidHom hi _ hx
    intro y hy
    exact (hs _).mpr (by simpa using hy)

noncomputable def descendEquiv (S : Set G) (e : G ≃* G) (he : Continuous e)
    (hi : Continuous e.symm) (hs : ∀ x, x ∈ S ↔ e x ∈ S) :
    SplitQuotient S ≃* SplitQuotient S :=
  QuotientGroup.congr _ _ e (kernel_map_eq S e he hi hs)

theorem descendEquiv_project (S : Set G) (e : G ≃* G) (he : Continuous e)
    (hi : Continuous e.symm) (hs : ∀ x, x ∈ S ↔ e x ∈ S) (x : G) :
    descendEquiv S e he hi hs (project S x) = project S (e x) := rfl

theorem descendEquiv_continuous (S : Set G) (e : G ≃* G) (he : Continuous e)
    (hi : Continuous e.symm) (hs : ∀ x, x ∈ S ↔ e x ∈ S) :
    Continuous (descendEquiv S e he hi hs) :=
  (QuotientGroup.isQuotientMap_mk (kernel S)).continuous_iff.mpr ((project S).continuous.comp he)

end Transport

end Reimann.TameQuotientTransport277
