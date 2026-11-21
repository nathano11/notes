import ReimannNative69.DyadicHilbertTransition69
import ReimannNative69.DyadicClassPrimeExt69
import Mathlib.Topology.Algebra.Group.Basic

/-! Arithmetic Artin on the norm-coherent 2-primary ideal classes with the
subspace topology from the product of the discrete finite ideal class groups. -/
namespace Reimann.DyadicClassArtinLimit69

open Reimann.DyadicHilbertStage69 Reimann.DyadicHilbertTransition69 Reimann.DyadicClassNorm69
open Reimann.DyadicNativeFrob69 Reimann.DyadicNativeClass69 IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

variable (K L K' L' : Type) [Field K] [Field L] [Field K'] [Field L']
  [NumberField K] [NumberField L] [NumberField K'] [NumberField L']
  [Algebra K L] [Algebra K K'] [Algebra K L'] [Algebra L L'] [Algebra K' L']
  [IsScalarTower K L L'] [IsScalarTower K K' L']
  [FiniteDimensional K L] [FiniteDimensional K' L'] [IsGalois K L] [IsGalois K' L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem classArtin_at_integral
    (principal : ∀ x : Kˣ, numberFieldSymbol K L (toPrincipalIdeal (𝓞 K) K x)=1)
    (I : (Ideal (𝓞 K))⁰) :
    numberFieldClassArtin K L principal (ClassGroup.mk0 I) =
      numberFieldSymbol K L (FractionalIdeal.mk0 K I) := by
  rw [← ClassGroup.mk_mk0 K]
  exact classArtin_at_ideal K L principal _

end Reimann.DyadicClassArtinLimit69
