import Reimann277.ArtinBasic
import Reimann277.LocalClassGroup

namespace Reimann.TameArtin277

open TameCyclotomicLocal277

instance sClass_finite (r n : ℕ) : Finite (SClassGroup r n) :=
  TameLocalClass277.class_finite_away_277 (cutField r n) (SIntegers r n)

/-- The inverse Artin projection is continuous for the discrete topology on
the finite localized class group. This formulation tests all preimages. -/
theorem class_projection_open_preimage {r n : ℕ}
    (e : ClassReciprocity r n) (U : Set (SClassGroup r n)) :
    IsOpen ((toClassGroup e) ⁻¹' U) := by
  letI : IsClosed (TameSplitQuotient277.kernel (localRelations r n) : Set (globalKernel r n)) :=
    Subgroup.isClosed_topologicalClosure _
  letI : Finite (UnramifiedSplitQuotient r n) := Finite.of_injective e e.injective
  exact (isOpen_discrete (e ⁻¹' U)).preimage (project r n).continuous

end Reimann.TameArtin277
