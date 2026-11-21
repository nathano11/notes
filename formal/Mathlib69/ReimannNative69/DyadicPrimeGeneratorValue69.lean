import ReimannNative69.DyadicCyclotomicModel69
import Mathlib.Tactic.NormNum

/-! The two integral bottom generators at the labeled dyadic primes. -/
namespace Reimann.DyadicPrimeGeneratorValue69

open DyadicNativeEmbedding69 DyadicCyclotomicModel69

theorem root_generator_value {F : Type} [Field F] [CharZero F] (x y : F)
    (hx : x^2= -3) (hy : y^2= -23) (v : Bool) :
    (root_embedding x y hx hy).app (DyadicArithmetic69.primeGenerator v).val =
      if v then 1-(1+y)/2 else (1+y)/2 := by
  cases v <;>
    norm_num [root_embedding,value,quadValue,DyadicArithmetic69.primeGenerator,
      DyadicFieldTrace69.embed,DyadicBasisComparison.fromIntegral,DyadicFieldTrace69.half] <;> ring

/-- In the ambient field the false label is the root (1+y)/2 and the true
label is its conjugate. -/
theorem prime_generator_value (Ω : Type) [Field Ω] [CharZero Ω] (x y : Ω)
    (ζ : ℕ → Ω) (a : ℕ) (hx : x^2= -3) (hy : y^2= -23) (v : Bool) :
    ((bottom Ω x y ζ a hx hy).app (DyadicArithmetic69.primeGenerator v).val : Ω) =
      if v then 1-(1+y)/2 else (1+y)/2 := by
  have e := root_generator_value (lowerX Ω x y ζ a) (lowerY Ω x y ζ a)
    (lower_squares Ω x y ζ a hx hy).1 (lower_squares Ω x y ζ a hx hy).2 v
  change (bottom Ω x y ζ a hx hy).app _ = _ at e
  cases v <;> exact congrArg Subtype.val e

end Reimann.DyadicPrimeGeneratorValue69
