import Reimann277.ProlongationAction
import Reimann277.ArithmeticSymbol
import Reimann277.QuotientConjugation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite

namespace Reimann.TameArithmeticSymbol277

open NumberField TameInertia277 TameArtin277 TameCyclotomicLocal277
open TameProlongationAction277 TameIdealAction277 TameQuotientConjugation277
open scoped Pointwise

theorem absolute_primes_conjugate {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (P Q : Ideal (𝓞 L)) (hp : P.IsPrime) (hq : Q.IsPrime) (hc : P.under (𝓞 K) = Q.under (𝓞 K)) :
    ∃ g : L ≃ₐ[K] L, conjugateIdeal g P = Q := by
  let G := L ≃ₐ[K] L
  letI : TopologicalSpace (𝓞 L) := ⊥
  letI : DiscreteTopology (𝓞 L) := ⟨rfl⟩
  letI : ContinuousSMul G (𝓞 L) := integers_continuous
  letI : SMulCommClass G (𝓞 K) (𝓞 L) := integers_commute
  letI : Algebra.IsInvariant (𝓞 K) (𝓞 L) G := integers_invariant
  letI := hp
  letI := hq
  obtain ⟨g,hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 K)
    (B := 𝓞 L) (G := G) P Q hc
  exact ⟨g,(smul_is_conjugate g P).symm.trans hg.symm⟩

/-- Absolute primes over the same finite prime are conjugate by an element
over the cut field. -/
theorem prolongations_conjugate {r n : ℕ} {J : IntegralIdeals r n} {P Q : Ideal ClosureIntegers}
    (hp : Prolongs J P) (hq : Prolongs J Q) :
    ∃ g : globalKernel r n, conjugateIdeal (asAut g.val) P = Q := by
  obtain ⟨σ,hσ⟩ := absolute_primes_conjugate (K := cutField r n) (L := Closure)
    P Q hp.maximal.isPrime hq.maximal.isPrime (hp.contraction.trans hq.contraction.symm)
  obtain ⟨g,rfl⟩ := (kernelAutEquiv r n).surjective σ
  refine ⟨g,?_⟩
  exact hσ

/-- Inertia gives equality for two lifts at one prime; conjugacy and
abelianization give equality for lifts at any two prolongations. -/
theorem project_independent_prolongations {r n : ℕ} {J : IntegralIdeals r n}
    {P Q : Ideal ClosureIntegers} (hp : Prolongs J P) (hq : Prolongs J Q) (x y : globalKernel r n)
    (hx : FrobeniusAt J P x) (hy : FrobeniusAt J Q y) : project r n x = project r n y := by
  obtain ⟨g,rfl⟩ := prolongations_conjugate hp hq
  have hc : FrobeniusAt J (conjugateIdeal (asAut g.val) P) (conjugateKernel g.val x) :=
    frobenius_conjugate P (residueSize J) (asAut g.val) (asAut x.val) hx
  calc
    project r n x = onQuotient r n g.val (project r n x) := (onQuotient_kernel r n g _).symm
    _ = project r n (conjugateKernel g.val x) := onQuotient_project r n g.val x
    _ = project r n y := project_frobenius_independent hq _ y hc hy

end Reimann.TameArithmeticSymbol277
