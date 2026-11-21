import Reimann277.FrobeniusFiniteTests
import Mathlib.FieldTheory.Galois.Profinite

namespace Reimann.TameAbsoluteFrobenius277

open NumberField TameInertia277 TameFrobeniusFiniteTests277

/-- In any Galois extension of a number field, even an infinite extension,
one lift of arithmetic Frobenius acts by the residue cardinality on every
algebraic integer modulo the chosen prime. -/
theorem exists_frobenius {K L : Type} [Field K] [Field L] [Algebra K L]
    [NumberField K] [IsGalois K L] (P : Ideal (𝓞 L)) (hp : P.IsPrime)
    (h : P.under (𝓞 K) ≠ 0) :
    ∃ g : L ≃ₐ[K] L, FrobeniusResidue P (Nat.card (𝓞 K ⧸ P.under (𝓞 K))) g :=
  exists_of_finite_tests P _ (finite_tests P hp h)

end Reimann.TameAbsoluteFrobenius277
