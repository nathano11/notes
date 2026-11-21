import Reimann277.FractionalPrimeProduct
import Reimann277.FrobeniusNormalization
import Reimann277.ProlongationIndependence

namespace Reimann.TameFractionalFrobenius277

open scoped nonZeroDivisors
open IsDedekindDomain TameArtin277 TameArithmeticSymbol277 TameArithmeticNaturality277
open TameFrobeniusNormalization277 TameCyclotomicLocal277 TameIdealArtin277
open TameFractionalPrimeProduct277 (integralPrime)

attribute [local instance] TameArithmeticSymbol277.localizedDedekind

noncomputable local instance quotientCommGroup (r n : ℕ) : CommGroup (UnramifiedSplitQuotient r n) :=
  { (inferInstance : Group (UnramifiedSplitQuotient r n)) with mul_comm := quotient_commutes r n }

theorem exists_prime_lift {r n : ℕ} (v : HeightOneSpectrum (SIntegers r n)) :
    ∃ x : globalKernel r n, ∃ P, Prolongs (integralPrime v) P ∧ FrobeniusAt (integralPrime v) P x := by
  obtain ⟨P,hP⟩ := exists_prolongation (integralPrime v) v.isMaximal
  obtain ⟨x,hx⟩ := exists_frobeniusAt (integralPrime v) v.isMaximal P hP
  exact ⟨x,P,hP,hx⟩

noncomputable def primeValue {r n : ℕ} (v : HeightOneSpectrum (SIntegers r n)) :
    UnramifiedSplitQuotient r n :=
  project r n (exists_prime_lift v).choose

theorem primeValue_at {r n : ℕ} (v : HeightOneSpectrum (SIntegers r n))
    {P : Ideal ClosureIntegers} (hP : Prolongs (integralPrime v) P) (x : globalKernel r n)
    (hx : FrobeniusAt (integralPrime v) P x) : primeValue v = project r n x := by
  obtain ⟨Q,hQ,hy⟩ := (exists_prime_lift v).choose_spec
  exact project_independent_prolongations hQ hP _ x hy hx

/-- The arithmetic Frobenius homomorphism on all invertible fractional S-ideals.
Its prime factors use the actual quotient and integral residue maps. -/
noncomputable def symbol (r n : ℕ) :
    InvertibleIdeals (SIntegers r n) →* UnramifiedSplitQuotient r n :=
  TameFractionalPrimeProduct277.symbol primeValue

theorem symbol_at_prime {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal)
    (P : Ideal ClosureIntegers) (hP : Prolongs J P) (x : globalKernel r n)
    (hx : FrobeniusAt J P x) :
    symbol r n (FractionalIdeal.mk0 (FractionRing (SIntegers r n)) J) = project r n x := by
  let v : HeightOneSpectrum (SIntegers r n) :=
    ⟨J.val,hJ.isPrime,mem_nonZeroDivisors_iff_ne_zero.mp J.property⟩
  exact (TameFractionalPrimeProduct277.symbol_prime primeValue v).trans (primeValue_at v hP x hx)

/-- The remaining global class-field statements for the constructed homomorphism. -/
structure GlobalLaws (r n : ℕ) : Prop where
  onto : Function.Surjective (symbol r n)
  principal_kernel : (symbol r n).ker =
    (toPrincipalIdeal (SIntegers r n) (FractionRing (SIntegers r n))).range

noncomputable def idealSymbol {r n : ℕ} (h : GlobalLaws r n) :
    IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n) where
  symbol := symbol r n
  onto := h.onto
  principal_kernel := h.principal_kernel

theorem forward_normalization {r n : ℕ} (h : GlobalLaws r n) :
    ForwardNormalization (idealSymbol h) :=
  symbol_at_prime

noncomputable def primeSymbol {r n : ℕ} (h : GlobalLaws r n) : PrimeSymbol r n :=
  primeSymbol_of_normalization (idealSymbol h) (forward_normalization h)

end Reimann.TameFractionalFrobenius277
