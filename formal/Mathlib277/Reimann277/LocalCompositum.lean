import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite

namespace Reimann.TameLocalCompositum277

open IntermediateField

variable {F V : Type*} [Field F] [Field V]

/-- The field generated over the completed base by the image of the cut field. -/
noncomputable def localCompositum (j : AlgebraicClosure F →+* AlgebraicClosure V)
    (K : IntermediateField F (AlgebraicClosure F)) :
    IntermediateField V (AlgebraicClosure V) :=
  adjoin V (j '' (K : Set (AlgebraicClosure F)))

theorem mem_fixing_localCompositum_iff (j : AlgebraicClosure F →+* AlgebraicClosure V)
    (K : IntermediateField F (AlgebraicClosure F)) (g : Gal(AlgebraicClosure V/V)) :
    g ∈ (localCompositum j K).fixingSubgroup ↔ ∀ z ∈ K, g (j z) = j z := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z hz
    exact h _ (subset_adjoin _ _ ⟨z,hz,rfl⟩)
  · intro h z hz
    apply adjoin_induction V (motive := fun x _ => g x = x) _ _ _ _ _ hz
    · rintro _ ⟨x,hx,rfl⟩
      exact h x hx
    · exact g.commutes
    · intro x y _ _ hx hy
      rw [map_add,hx,hy]
    · intro x _ hx
      rw [map_inv₀,hx]
    · intro x y _ _ hx hy
      rw [map_mul,hx,hy]

theorem fixing_localCompositum (j : AlgebraicClosure F →+* AlgebraicClosure V)
    (D : Gal(AlgebraicClosure V/V) →* Gal(AlgebraicClosure F/F))
    (commutes : ∀ g z, j (D g z) = g (j z))
    (K : IntermediateField F (AlgebraicClosure F)) :
    (localCompositum j K).fixingSubgroup = K.fixingSubgroup.comap D := by
  ext g
  rw [mem_fixing_localCompositum_iff,Subgroup.mem_comap,IntermediateField.mem_fixingSubgroup_iff]
  simp only [← commutes,j.injective.eq_iff]

theorem fixedField_comap (j : AlgebraicClosure F →+* AlgebraicClosure V)
    (D : Gal(AlgebraicClosure V/V) →* Gal(AlgebraicClosure F/F))
    (commutes : ∀ g z, j (D g z) = g (j z))
    (K : IntermediateField F (AlgebraicClosure F)) [IsGalois V (AlgebraicClosure V)] :
    fixedField (K.fixingSubgroup.comap D) = localCompositum j K := by
  rw [← fixing_localCompositum j D commutes K,InfiniteGalois.fixedField_fixingSubgroup]

end Reimann.TameLocalCompositum277
