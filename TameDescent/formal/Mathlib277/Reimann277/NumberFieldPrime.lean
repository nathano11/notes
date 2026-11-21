import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.NormNum
import Reimann277.FiniteResidue
import Reimann277.PadicPlaces
import Reimann277.BiquadraticNumberField

namespace Reimann.TameFinitePlaces277

open NumberField IsDedekindDomain
open scoped NumberField

local instance primeForIntegers : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

variable {K : Type*} [Field K] [NumberField K]

theorem integral_image_bounded (f : K →ₐ[ℚ] ℚ_[277]) (x : 𝓞 K) :
    ‖f (x : K)‖ ≤ 1 := by
  have hz : IsIntegral ℤ (f (x : K)) := IsIntegral.map (A := ℚ) f x.isIntegral_coe
  have hi : IsIntegral ℤ_[277] (f (x : K)) := hz.tower_top
  obtain ⟨u,hu⟩ := (isIntegrallyClosed_iff ℚ_[277]).mp
    (inferInstance : IsIntegrallyClosed ℤ_[277]) hi
  rw [← hu]
  exact u.2

/-- The center of a p-adic embedding on the actual ring of integers. -/
def embeddingIdeal (f : K →ₐ[ℚ] ℚ_[277]) : Ideal (𝓞 K) :=
  TameFiniteResidue277.embeddingIdeal f (integral_image_bounded f)

theorem mem_embeddingIdeal_iff (f : K →ₐ[ℚ] ℚ_[277]) (x : 𝓞 K) :
    x ∈ embeddingIdeal f ↔ ‖f (x : K)‖ < 1 := Iff.rfl

theorem embeddingIdeal_prime (f : K →ₐ[ℚ] ℚ_[277]) : (embeddingIdeal f).IsPrime :=
  TameFiniteResidue277.embeddingIdeal_prime f (integral_image_bounded f)

theorem prime_mem_embeddingIdeal (f : K →ₐ[ℚ] ℚ_[277]) :
    (277 : 𝓞 K) ∈ embeddingIdeal f :=
  TameFiniteResidue277.prime_mem_embeddingIdeal f (integral_image_bounded f)

def embeddingPrime (f : K →ₐ[ℚ] ℚ_[277]) : HeightOneSpectrum (𝓞 K) where
  asIdeal := embeddingIdeal f
  isPrime := embeddingIdeal_prime f
  ne_bot := by
    intro h
    have e := prime_mem_embeddingIdeal f
    rw [h,Submodule.mem_bot] at e
    exact (by norm_num : (277 : 𝓞 K) ≠ 0) e

noncomputable def residue_equiv (f : K →ₐ[ℚ] ℚ_[277]) :
    ((𝓞 K) ⧸ (embeddingPrime f).asIdeal) ≃+* ZMod 277 :=
  TameFiniteResidue277.residue_equiv f (integral_image_bounded f)

theorem residue_cardinality (f : K →ₐ[ℚ] ℚ_[277]) :
    Nat.card ((𝓞 K) ⧸ (embeddingPrime f).asIdeal) = 277 :=
  TameFiniteResidue277.residue_card f (integral_image_bounded f)

open TameBiquadraticField277 TameRationalField277 TamePlaceRestriction277
open TameArithmetic277 TameOrderFaithful277 TamePadicEmbeddings277

theorem scalar_int (a : ℤ) : (Biquadratic.mk (scalar (a : ℚ))) = (a : Biquadratic) := by
  rw [← coefficientHom_apply,map_intCast]

theorem integral_scalar (a : ℤ) :
    IsIntegral ℤ (Biquadratic.mk (scalar (a : ℚ))) := by
  rw [scalar_int]
  exact isIntegral_intCast a

theorem integral_radicals :
    IsIntegral ℤ (Biquadratic.mk gen3) ∧ IsIntegral ℤ (Biquadratic.mk gen23) := by
  constructor
  · apply IsIntegral.of_pow (n := 2) (by decide)
    rw [pow_two,show Biquadratic.mk gen3 * Biquadratic.mk gen3 =
      Biquadratic.mk (scalar ((-3 : ℤ) : ℚ)) from coord_injective generator_squares.1]
    exact integral_scalar (-3)
  · apply IsIntegral.of_pow (n := 2) (by decide)
    rw [pow_two,show Biquadratic.mk gen23 * Biquadratic.mk gen23 =
      Biquadratic.mk (scalar ((-23 : ℤ) : ℚ)) from coord_injective generator_squares.2]
    exact integral_scalar (-23)

theorem integral_on_order (x : OrderCoordinates) :
    IsIntegral ℤ (Biquadratic.mk (rationalize x)) := by
  obtain ⟨hi,hj⟩ := integral_radicals
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change IsIntegral ℤ (Biquadratic.mk (((a : ℚ),(b : ℚ)),((c : ℚ),(d : ℚ))))
  rw [← basis_expansion]
  exact ((integral_scalar a).add ((integral_scalar b).mul hi)).add
    (((integral_scalar c).mul hj).add ((integral_scalar d).mul (hi.mul hj)))

/-- Distinct choices of the two lifted roots have distinct centers even in the
full ring of integers. The radical order already detects the distinction. -/
theorem signed_primes_injective :
    Function.Injective (fun s => embeddingPrime (embedding s)) := by
  intro s t h
  apply TamePadicPlaces277.equiv.injective
  change TamePadicPlaces277.order s = TamePadicPlaces277.order t
  apply place_order_ext
  rw [TamePadicPlaces277.center_eq,TamePadicPlaces277.center_eq]
  funext a
  apply propext
  rw [← norm_lt_one_iff_prime s a, ← norm_lt_one_iff_prime t a]
  let x : 𝓞 Biquadratic := ⟨_, integral_on_order a⟩
  change x ∈ (embeddingPrime (embedding s)).asIdeal ↔ x ∈ (embeddingPrime (embedding t)).asIdeal
  change embeddingPrime (embedding s) = embeddingPrime (embedding t) at h
  rw [h]

end Reimann.TameFinitePlaces277
