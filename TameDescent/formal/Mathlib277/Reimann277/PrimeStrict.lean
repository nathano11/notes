import Reimann277.ArithmeticNaturality
import Reimann277.CanonicalStrict
import Reimann277.StrictCohomology

namespace Reimann.TamePrimeStrict277

open TameArtin277 TameCyclotomicLocal277 TameStrictLocal277 TameStrictArtin277
open TameArithmeticSymbol277 TameArithmeticNaturality277 TameRestriction
open TameCanonicalDecomposition277 TameFinitePlaces277 TameBiquadraticField277
open TameStrictReciprocity277 TameStrictCohomology277

/-- A surjective ideal symbol with principal kernel, normalized on arithmetic
Frobenius at every finite prime of the localized integer ring, suffices. -/
noncomputable def strict_cohomology_equiv {r n : ℕ} (hr : ¬276 ∣ r) (s : PrimeSymbol r n) :
    StrictH1 r n ≃+ characters r n :=
  strict_class_group_equiv hr (toInput s)

theorem evaluate_at_prime {r n : ℕ} (hr : ¬276 ∣ r) (s : PrimeSymbol r n)
    (c : cocycles r n) (J : IntegralIdeals r n) (hJ : J.val.IsMaximal)
    (P : Ideal ClosureIntegers) (hP : Prolongs J P)
    (x : globalKernel r n) (hx : FrobeniusAt J P x) :
    (strict_cohomology_equiv hr s (QuotientAddGroup.mk c)).val
      (Additive.ofMul (ClassGroup.mk0 J)) = c.val x.val := by
  rw [← inverse_frobenius (toInput s) J hJ P hP x hx]
  exact strict_class_group_equiv_apply hr (toInput s) c x

theorem strict_class_character {r n : ℕ} (hr : ¬276 ∣ r) (s : PrimeSymbol r n)
    {c : Global → ℤ} (hc : Crossed (data (tameWitness r n hr)) c)
    (hcont : Continuous (fun g : Global => (c g : Coeff n))) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), modulus n ∣ c x.val) ∧
      ∀ (v : Above Biquadratic) (g : Global) (y : completionKernel r n v),
        modulus n ∣ c (conjugatedAt r n v g y).val) ↔
      ∃! η : SClassGroup r n →* Target n, Twisted η ∧
        ∀ x : globalKernel r n, η (toClassGroup (reciprocity (toInput s)) x) = kernelCharacter hc hcont x :=
  canonical_strict_class_character r n hr (toInput s) hc hcont

end Reimann.TamePrimeStrict277
