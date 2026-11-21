import Reimann277.PrimeStrict
import Reimann277.FractionalFrobenius

namespace Reimann.TameStrictArtin277

open TameArtin277 TameCyclotomicLocal277 TameStrictLocal277
open TameArithmeticSymbol277 TameArithmeticNaturality277 TameRestriction
open TameCanonicalDecomposition277 TameFinitePlaces277 TameBiquadraticField277
open TameStrictReciprocity277 TameStrictCohomology277 TameFractionalFrobenius277

/-- The two global ideal-theoretic laws specialize the strict cohomology
comparison to the particular Frobenius product on fractional ideals. -/
noncomputable def strict_H1_of_global_laws {r n : ℕ} (hr : ¬276 ∣ r) (h : GlobalLaws r n) :
    StrictH1 r n ≃+ characters r n :=
  TamePrimeStrict277.strict_cohomology_equiv hr (primeSymbol h)

theorem strict_H1_at_frobenius {r n : ℕ} (hr : ¬276 ∣ r) (h : GlobalLaws r n)
    (c : cocycles r n) (J : IntegralIdeals r n) (hJ : J.val.IsMaximal)
    (P : Ideal ClosureIntegers) (hP : Prolongs J P)
    (x : globalKernel r n) (hx : FrobeniusAt J P x) :
    (strict_H1_of_global_laws hr h (QuotientAddGroup.mk c)).val (Additive.ofMul (ClassGroup.mk0 J)) =
      c.val x.val :=
  TamePrimeStrict277.evaluate_at_prime hr (primeSymbol h) c J hJ P hP x hx

theorem strict_class_character_of_global_laws {r n : ℕ} (hr : ¬276 ∣ r) (h : GlobalLaws r n)
    {c : Global → ℤ} (hc : Crossed (data (tameWitness r n hr)) c)
    (hcont : Continuous (fun g : Global => (c g : Coeff n))) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), modulus n ∣ c x.val) ∧
      ∀ (v : Above Biquadratic) (g : Global) (y : completionKernel r n v),
        modulus n ∣ c (conjugatedAt r n v g y).val) ↔
      ∃! η : SClassGroup r n →* Target n, Twisted η ∧
        ∀ x : globalKernel r n, η (toClassGroup (fromIdealSymbol (idealSymbol h)) x) =
          kernelCharacter hc hcont x :=
  TamePrimeStrict277.strict_class_character hr (primeSymbol h) hc hcont

end Reimann.TameStrictArtin277
