import Reimann277.ArithmeticNaturality
import Reimann277.FrobeniusAtPrime

namespace Reimann.TameFrobeniusNormalization277

open TameArithmeticSymbol277 TameArithmeticNaturality277 TameArtin277 TameIdealArtin277
open TameIdealAction277 TameCyclotomicLocal277

attribute [local instance] TameArithmeticSymbol277.localizedDedekind

/-- The remaining prime normalization for a proposed global Artin homomorphism.
The exponent in `FrobeniusAt` is the cardinality of the actual finite residue field. -/
def ForwardNormalization {r n : ℕ}
    (a : IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n)) : Prop :=
  ∀ (J : IntegralIdeals r n), J.val.IsMaximal → ∀ P, Prolongs J P →
    ∀ x : globalKernel r n, FrobeniusAt J P x →
      a.symbol (FractionalIdeal.mk0 (FractionRing (SIntegers r n)) J) = project r n x

/-- The local existence theorem provides the lift at every prolongation. -/
def primeSymbol_of_normalization {r n : ℕ}
    (a : IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n))
    (h : ForwardNormalization a) : PrimeSymbol r n where
  ideals := a
  at_prime J hJ P hP := by
    obtain ⟨x,hx⟩ := exists_frobeniusAt J hJ P hP
    exact ⟨x,hx,h J hJ P hP x hx⟩

theorem normalization_of_primeSymbol {r n : ℕ} (s : PrimeSymbol r n) :
    ForwardNormalization s.ideals :=
  all_frobenius_lifts s

theorem equivariance_of_normalization {r n : ℕ}
    (a : IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n))
    (h : ForwardNormalization a) : ArtinEquivariant (fromIdealSymbol a) :=
  arithmetic_equivariance (primeSymbol_of_normalization a h)

end Reimann.TameFrobeniusNormalization277
