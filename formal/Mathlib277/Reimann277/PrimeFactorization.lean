import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.BigOperators.Associated
import Reimann277.NumberFieldPrime

namespace Reimann.TamePrimeFactorization277

open NumberField IsDedekindDomain TameBiquadraticField277 TamePadicEmbeddings277 TameFinitePlaces277
open scoped NumberField BigOperators

abbrev Sign := Bool × Bool
abbrev O := 𝓞 Biquadratic
noncomputable abbrev signedPrime (s : Sign) : HeightOneSpectrum O := embeddingPrime (embedding s)
noncomputable abbrev signedIdeal (s : Sign) : Ideal O := (signedPrime s).asIdeal
abbrev principal : Ideal O := Ideal.span {(277 : O)}

theorem signed_norm (s : Sign) : (signedIdeal s).absNorm = 277 := by
  letI : Infinite O := Infinite.of_injective (fun n : ℕ => (n : O)) Nat.cast_injective
  rw [Ideal.absNorm_eq_natCard]
  exact residue_cardinality (embedding s)

theorem principal_norm : principal.absNorm = 277^4 := by
  change (Ideal.span {((277 : ℕ) : O)}).absNorm = _
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank Biquadratic, biquadratic_degree]

theorem product_norm : (∏ s : Sign, signedIdeal s).absNorm = 277^4 := by
  rw [map_prod]
  simp [signed_norm]

theorem pairwise_coprime {s t : Sign} (h : s ≠ t) : IsCoprime (signedIdeal s) (signedIdeal t) :=
  (signedPrime s).isCoprime_of_ne _ (signed_primes_injective.ne h)

theorem product_is_intersection : (∏ s : Sign, signedIdeal s) = ⨅ s : Sign, signedIdeal s := by
  classical
  simpa only [Finset.mem_univ, iInf_pos] using
    (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) (J := signedIdeal)
      (fun s _ t _ h => pairwise_coprime h))

theorem principal_le_product : principal ≤ ∏ s : Sign, signedIdeal s := by
  rw [product_is_intersection]
  exact le_iInf (fun s => (Ideal.span_singleton_le_iff_mem _).mpr (prime_mem_embeddingIdeal (embedding s)))

/-- The four distinct prime ideals occur in the factorization of (277) in the
full integer ring. The norm of their product equals the norm of (277), so the
remaining ideal factor has norm one. -/
theorem prime_factorization_277 : principal = ∏ s : Sign, signedIdeal s := by
  obtain ⟨rest, he⟩ := Ideal.dvd_iff_le.mpr principal_le_product
  have hn := congrArg Ideal.absNorm he
  rw [principal_norm,map_mul,product_norm] at hn
  have h1 : rest.absNorm = 1 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 277^4)
    (hn.symm.trans (Nat.mul_one _).symm)
  rw [he, Ideal.absNorm_eq_one_iff.mp h1, Ideal.mul_top]

theorem signed_dvd_iff (s t : Sign) : signedIdeal s ∣ signedIdeal t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => h ▸ dvd_refl _⟩
  have hEq := (signedPrime t).isMaximal.eq_of_le (signedPrime s).isPrime.ne_top (Ideal.dvd_iff_le.mp h)
  exact signed_primes_injective (HeightOneSpectrum.asIdeal_injective hEq.symm)

theorem multiplicity_one (s : Sign) :
    signedIdeal s ∣ principal ∧ ¬ (signedIdeal s)^2 ∣ principal := by
  classical
  rw [prime_factorization_277]
  have hprod := Finset.mul_prod_erase (Finset.univ : Finset Sign) signedIdeal (Finset.mem_univ s)
  rw [← hprod]
  refine ⟨dvd_mul_right _ _,?_⟩
  rw [pow_two,mul_dvd_mul_iff_left (signedPrime s).ne_bot]
  apply (signedPrime s).prime.not_dvd_finsetProd
  intro t ht hd
  exact (Finset.mem_erase.mp ht).1 ((signed_dvd_iff s t).mp hd).symm

/-- Exhaust all height-one primes of the full ring of integers which contain 277. -/
theorem prime_over_277 (P : HeightOneSpectrum O) (hp : (277 : O) ∈ P.asIdeal) :
    ∃! s : Sign, signedPrime s = P := by
  have h : P.asIdeal ∣ principal := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hp)
  rw [prime_factorization_277] at h
  obtain ⟨s,_,hs⟩ := (P.prime.dvd_finsetProd_iff signedIdeal).mp h
  have he : signedPrime s = P := HeightOneSpectrum.asIdeal_injective
    ((signedPrime s).isMaximal.eq_of_le P.isPrime.ne_top (Ideal.dvd_iff_le.mp hs))
  exact ⟨s,he,fun t ht => signed_primes_injective (ht.trans he.symm)⟩

end Reimann.TamePrimeFactorization277
