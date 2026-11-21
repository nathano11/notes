import ReimannNative69.DyadicHilbertStage69

/-! Norm and restriction in the Hilbert class tower of number fields. -/
namespace Reimann.DyadicHilbertTransition69

open Reimann.DyadicHilbertStage69 Reimann.DyadicArtinLimit69 Reimann.DyadicNativeClass69
open Reimann.DyadicNativeFrob69 IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

variable (K L K' L' : Type) [Field K] [Field L] [Field K'] [Field L']
  [NumberField K] [NumberField L] [NumberField K'] [NumberField L']
  [Algebra K L] [Algebra K K'] [Algebra K L'] [Algebra L L'] [Algebra K' L']
  [IsScalarTower K L L'] [IsScalarTower K K' L']
  [FiniteDimensional K L] [FiniteDimensional K' L'] [IsGalois K L] [IsGalois K' L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K'] L')]

/-- The native relative norm of an upper prime, as an invertible fractional ideal. -/
noncomputable def normedPrime (p : HeightOneSpectrum (𝓞 K')) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (Ideal.relNorm (𝓞 K) p.asIdeal : FractionalIdeal (𝓞 K)⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.relNorm_eq_bot_iff.not.mpr p.ne_bot))

theorem unramified_prime_symbol
    (h : ∀ (P : Ideal (𝓞 L)) [P.IsMaximal], Algebra.IsUnramifiedAt (𝓞 K) P)
    (h' : ∀ (P : Ideal (𝓞 L')) [P.IsMaximal], Algebra.IsUnramifiedAt (𝓞 K') P)
    (p' : HeightOneSpectrum (𝓞 K')) :
    numberFieldSymbol K L (normedPrime K K' p') =
      numberFieldRestriction K L K' L' (numberFieldFrobenius K' L' p') := by
  obtain ⟨p,_,normEq,frobEq⟩ := numberField_prime_norm_of_unramified K L K' L' h h' p'
  have eq : normedPrime K K' p' = (primeUnit (K:=K) p) ^ p'.asIdeal.inertiaDeg (𝓞 K) := by
    apply Units.ext
    change ((Ideal.relNorm (𝓞 K) p'.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ((p.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ _)
    rw [normEq,FractionalIdeal.coeIdeal_pow]
  rw [eq,map_pow,symbol_at_prime,frobEq]

/-- The relative ideal norm extended to signed fractional-ideal exponents. -/
noncomputable def fractional_norm :
    (FractionalIdeal (𝓞 K')⁰ K')ˣ →* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  idealSymbol (normedPrime K K')

theorem fractional_norm_at_prime (p' : HeightOneSpectrum (𝓞 K')) :
    ((fractional_norm K K' (primeUnit (K:=K') p') : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.relNorm (𝓞 K) p'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [fractional_norm,idealSymbol_primeUnit]; rfl

/-- For the two full Hilbert fields in a tower, only finite global reciprocity
and everywhere finite-place unramifiedness enter. No norm law is assumed. -/
noncomputable def native_transition
    (onto : Function.Surjective (numberFieldSymbol K L))
    (kernel : ∀ I, numberFieldSymbol K L I = 1 ↔ (I : Submodule (𝓞 K) K).IsPrincipal)
    (onto' : Function.Surjective (numberFieldSymbol K' L'))
    (kernel' : ∀ I, numberFieldSymbol K' L' I = 1 ↔ (I : Submodule (𝓞 K') K').IsPrincipal)
    (h : ∀ (P : Ideal (𝓞 L)) [P.IsMaximal], Algebra.IsUnramifiedAt (𝓞 K) P)
    (h' : ∀ (P : Ideal (𝓞 L')) [P.IsMaximal], Algebra.IsUnramifiedAt (𝓞 K') P) :
    Transition (hilbert_stage K' L' onto' kernel') (hilbert_stage K L onto kernel) where
  norm := lawHom (A:=(FractionalIdeal (𝓞 K')⁰ K')ˣ) (B:=(FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (fractional_norm K K')
  restriction := lawHom (A:=(L' ≃ₐ[K'] L')) (B:=(L ≃ₐ[K] L)) (numberFieldRestriction K L K' L')
  frobenius_norm := by
    intro I
    change numberFieldSymbol K L (fractional_norm K K' I) =
      numberFieldRestriction K L K' L' (numberFieldSymbol K' L' I)
    exact fractional_norm_restriction (K:=K) (L:=K') (numberFieldFrobenius K L)
      (numberFieldFrobenius K' L') (numberFieldRestriction K L K' L') (normedPrime K K')
      (unramified_prime_symbol K L K' L' h h') I

end Reimann.DyadicHilbertTransition69
