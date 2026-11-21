import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import ReimannNative69.DyadicValuationLog69

/-! The normalized valuation at an actual height-one prime of a Dedekind
domain and the comparison of such primes on a dyadic cyclotomic layer. -/
namespace Reimann.DyadicNativeValue69

open IsDedekindDomain DyadicDecomposition69 DyadicLocalRestriction69
open DyadicValuationLog69

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K]

theorem dyadic_ramification_positive (P : HeightOneSpectrum R) (hP : (2:R)∈P.asIdeal) :
    0 < order (P.valuation K) 2 := by
  apply (order_pos_iff _ (by norm_num : (2:K)≠0)).mpr
  simpa only [map_ofNat] using (P.valuation_lt_one_iff_mem (K:=K) (2:R)).mpr hP

/-- The height-one prime above two gives a normalized rational additive
valuation on the fraction field. -/
noncomputable def normalized_prime_value (P : HeightOneSpectrum R) (hP : (2:R)∈P.asIdeal) :
    DyadicValue K :=
  normalized (P.valuation K) (by norm_num) (dyadic_ramification_positive P hP)

theorem integer_nonneg (P : HeightOneSpectrum R) (hp : (2:R)∈P.asIdeal) (x : R) :
    0 ≤ (normalized_prime_value (K:=K) P hp).val (algebraMap R K x) := by
  apply div_nonneg
  · exact_mod_cast order_nonneg_of_le_one (P.valuation K) (P.valuation_le_one (K:=K) x)
  · exact_mod_cast (dyadic_ramification_positive (K:=K) P hp).le

theorem integer_support (P : HeightOneSpectrum R) (hp : (2:R)∈P.asIdeal) (x : R) :
    Supports (normalized_prime_value (K:=K) P hp) (algebraMap R K x) ↔ x∈P.asIdeal :=
  (support_iff _ _ (dyadic_ramification_positive P hp) _).trans (P.valuation_lt_one_iff_mem (K:=K) x)

/-- In an actual finite cyclotomic compositum, two height-one primes giving
the same labeled center on the bottom localized order are equal. -/
theorem finite_prime_unique (P Q : HeightOneSpectrum R) (hp : (2:R)∈P.asIdeal) (hq : (2:R)∈Q.asIdeal)
    (f : DyadicBottomValue69.Embedding K) (i : Bool)
    (cp : DyadicBottomValue69.Centered f (normalized_prime_value P hp) i)
    (cq : DyadicBottomValue69.Centered f (normalized_prime_value Q hq) i)
    (n : ℕ) (z : K) (hz : z^(2^n : ℕ)= -1)
    (gen : ∀ x : K, DyadicCyclotomicSpan69.Generated (DyadicEmbeddedBase69.baseImage f) z x) :
    P=Q := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← integer_support (K:=K) P hp,← integer_support (K:=K) Q hq]
  unfold Supports
  rw [finite_layer_place_unique f i _ _ cp cq n hz (gen (algebraMap R K x))]

theorem valuation_of_odd (P : HeightOneSpectrum R) (hp : (2:R)∈P.asIdeal) (k : ℤ) :
    P.valuation K ((1+2*k : ℤ) : K) = 1 := by
  have h : ((1+2*k : ℤ) : R) ∉ P.asIdeal := by
    intro hm
    have ha := P.asIdeal.sub_mem hm (P.asIdeal.mul_mem_right (k:R) hp)
    exact P.isPrime.one_notMem (by simpa using ha)
  simpa only [map_intCast] using (P.valuation_eq_one_iff_notMem (K:=K)).mpr h

open DyadicArithmetic69 DyadicBottomValue69 DyadicFiberDescent
open DyadicLocalizedPrimes69 (fiber Represents)
open DyadicFieldTrace69 (embed)

/-- Clearing an odd denominator preserves the canonical multiplicative value. -/
theorem numerator_value (P : HeightOneSpectrum R) (hp : (2:R)∈P.asIdeal)
    (f : Embedding K) {z : TameRationalField277.Biquad} {p : Dyadic.Matrix} {k : ℤ}
    (rep : Represents z k p) :
    P.valuation K (f.app (embed p)) = P.valuation K (f.app z) := by
  rw [rep,f.mul,f.scalar_int,map_mul,valuation_of_odd P hp,one_mul]

/-- The global order's numerator membership test gives the center on all
localized integers of the explicit lower field, including odd fractions. -/
theorem centered_of_integer_order (P : HeightOneSpectrum R) (hp : (2:R)∈P.asIdeal)
    (f : Embedding K) (i : Bool) (num : Dyadic.Matrix → R)
    (maps : ∀ p, algebraMap R K (num p) = f.app (embed p))
    (label : ∀ p, num p ∈ P.asIdeal ↔ DyadicFiberPrimes.kernel i (fiber p)) :
    Centered f (normalized_prime_value P hp) i := by
  have entry (x : LocalIntegers) :
      ∃ p : Dyadic.Matrix, P.valuation K (algebraMap R K (num p)) = P.valuation K (f.app x.val) ∧
        residueMap.red x = fiber p := by
    obtain ⟨p,k,rep⟩ := (integers_localized_at_two _).mp x.property
    exact ⟨p,(congrArg (P.valuation K) (maps p)).trans (numerator_value P hp f rep),
      DyadicLocalizedPrimes69.reduce_of_rep _ rep⟩
  constructor
  · intro x
    obtain ⟨p,eq,_⟩ := entry x
    apply div_nonneg
    · exact_mod_cast order_nonneg_of_le_one (P.valuation K) (eq ▸ P.valuation_le_one (K:=K) (num p))
    · exact_mod_cast (dyadic_ramification_positive (K:=K) P hp).le
  · intro x
    obtain ⟨p,eq,red⟩ := entry x
    change DyadicFiberPrimes.kernel i (residueMap.red x) ↔ Supports (normalized_prime_value P hp) (f.app x.val)
    rw [red,← label,normalized_prime_value,support_iff,← eq]
    exact (P.valuation_lt_one_iff_mem (K:=K) (num p)).symm


end Reimann.DyadicNativeValue69
