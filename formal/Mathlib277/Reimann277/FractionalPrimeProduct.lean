import Reimann277.IdealArtin
import Mathlib.RingTheory.DedekindDomain.Factorization

namespace Reimann.TameFractionalPrimeProduct277

open scoped nonZeroDivisors BigOperators
open IsDedekindDomain TameIdealArtin277

variable {R H : Type*} [CommRing R] [IsDedekindDomain R] [CommGroup H]

/-- An invertible fractional ideal has nonzero exponent at only finitely many primes. -/
theorem finite_prime_support (f : HeightOneSpectrum R → H) (I : InvertibleIdeals R) :
    (Function.mulSupport (fun v => f v ^ FractionalIdeal.count (FractionRing R) v I.val)).Finite := by
  apply (FractionalIdeal.finite_factors I.val).subset
  intro v hv h
  change FractionalIdeal.count (FractionRing R) v I.val = 0 at h
  exact hv (by simp only [h,zpow_zero])

/-- The exponent of each prime in a product is the sum of its two exponents. -/
theorem prime_power_mul (f : HeightOneSpectrum R → H) (I J : InvertibleIdeals R)
    (v : HeightOneSpectrum R) :
    f v ^ FractionalIdeal.count (FractionRing R) v (I*J).val =
      f v ^ FractionalIdeal.count (FractionRing R) v I.val *
        f v ^ FractionalIdeal.count (FractionRing R) v J.val := by
  rw [Units.val_mul,FractionalIdeal.count_mul _ _ I.ne_zero J.ne_zero,zpow_add]

noncomputable def product (f : HeightOneSpectrum R → H) (I : InvertibleIdeals R) : H :=
  ∏ᶠ v, f v ^ FractionalIdeal.count (FractionRing R) v I.val

theorem product_one (f : HeightOneSpectrum R → H) : product f 1 = 1 := by
  simp only [product,Units.val_one,FractionalIdeal.count_one,zpow_zero,finprod_one]

theorem product_mul (f : HeightOneSpectrum R → H) (I J : InvertibleIdeals R) :
    product f (I*J) = product f I * product f J := by
  unfold product
  rw [← finprod_mul_distrib (finite_prime_support f I) (finite_prime_support f J)]
  exact finprod_congr (prime_power_mul f I J)

noncomputable def symbol (f : HeightOneSpectrum R → H) : InvertibleIdeals R →* H where
  toFun := product f
  map_one' := product_one f
  map_mul' := product_mul f

def integralPrime (v : HeightOneSpectrum R) : (Ideal R)⁰ :=
  ⟨v.asIdeal,mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

/-- Evaluation at one prime has exponent one there and exponent zero elsewhere. -/
theorem symbol_prime (f : HeightOneSpectrum R → H) (v : HeightOneSpectrum R) :
    symbol f (FractionalIdeal.mk0 (FractionRing R) (integralPrime v)) = f v := by
  change (∏ᶠ w, f w ^ FractionalIdeal.count (FractionRing R) w
    (v.asIdeal : FractionalIdeal R⁰ (FractionRing R))) = f v
  rw [finprod_eq_single _ v, FractionalIdeal.count_self, zpow_one]
  intro w h
  rw [FractionalIdeal.count_maximal_coprime _ w h.symm, zpow_zero]

end Reimann.TameFractionalPrimeProduct277
