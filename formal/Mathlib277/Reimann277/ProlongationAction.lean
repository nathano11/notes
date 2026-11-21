import Reimann277.AbsoluteFrobenius
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.MulAction
import Mathlib.RingTheory.Invariant.Defs

namespace Reimann.TameProlongationAction277

open NumberField TameInertia277
open scoped Pointwise

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem integers_invariant [IsGalois K L] : Algebra.IsInvariant (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) := by
  constructor
  intro x hx
  obtain ⟨a,ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (x : L)).mpr
    (fun g => congrArg (fun y : 𝓞 L => (y : L)) (hx g))
  have ia : IsIntegral ℤ a := (isIntegral_algebraMap_iff (B := L)).mp (ha ▸ x.isIntegral_coe)
  exact ⟨⟨a,ia⟩,RingOfIntegers.ext ha⟩

theorem integers_commute : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := by
  constructor
  intro g a x
  apply RingOfIntegers.ext
  change g (algebraMap K L (a : K) * (x : L)) = algebraMap K L (a : K) * g (x : L)
  rw [map_mul, g.commutes]

theorem integers_continuous [IsGalois K L] [TopologicalSpace (𝓞 L)] [DiscreteTopology (𝓞 L)] :
    ContinuousSMul (L ≃ₐ[K] L) (𝓞 L) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  exact TameAbsoluteFrobenius277.one_test_open x (fun y => y = x)

theorem smul_is_conjugate (g : L ≃ₐ[K] L) (P : Ideal (𝓞 L)) :
    g • P = conjugateIdeal g P := by
  rw [Ideal.pointwise_smul_eq_comap]
  rfl

end Reimann.TameProlongationAction277
