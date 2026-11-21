import ReimannNative69.DyadicNativeClass69
import ReimannNative69.DyadicNativeFrob69
import Reimann.DyadicArtinLimit69

/-! Full Hilbert reciprocity on the actual fractional ideals, ideal classes,
and finite abelian Galois groups of number fields. -/
namespace Reimann.DyadicHilbertStage69

open Reimann.Transfer Reimann.DyadicArtinLimit69 Reimann.DyadicNativeClass69
open Reimann.DyadicNativeFrob69 IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

def groupLaw (G : Type*) [Group G] : GroupLaw G where
  zero := 1
  add := (· * ·)
  neg := Inv.inv
  assoc := mul_assoc
  zero_add := one_mul
  add_zero := mul_one
  add_neg := mul_inv_cancel
  neg_add := inv_mul_cancel

def lawHom {A B : Type*} [Group A] [Group B] (h : A →* B) : Hom (groupLaw A) (groupLaw B) where
  app := h
  preserves_zero := h.map_one
  preserves_add := h.map_mul
  preserves_neg := map_inv h

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

/-- The divisor product of arithmetic Frobenii for a named abelian extension. -/
noncomputable def numberFieldSymbol : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (L ≃ₐ[K] L) :=
  idealSymbol (numberFieldFrobenius K L)

theorem symbol_at_prime (p : HeightOneSpectrum (𝓞 K)) :
    numberFieldSymbol K L (primeUnit (K:=K) p) = numberFieldFrobenius K L p :=
  idealSymbol_primeUnit _ _

/-- Sending principal ideals to the identity suffices for a map out of the full class group. -/
noncomputable def numberFieldClassArtin
    (principal : ∀ x : Kˣ, numberFieldSymbol K L (toPrincipalIdeal (𝓞 K) K x)=1) :
    ClassGroup (𝓞 K) →* (L ≃ₐ[K] L) :=
  class_artin (numberFieldFrobenius K L) principal

theorem classArtin_at_ideal
    (principal : ∀ x : Kˣ, numberFieldSymbol K L (toPrincipalIdeal (𝓞 K) K x)=1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    numberFieldClassArtin K L principal (ClassGroup.mk K I) = numberFieldSymbol K L I :=
  class_artin_mk _ principal I

/-- Finite Hilbert reciprocity is reduced precisely to the arithmetic symbol's
surjectivity and principal kernel. The class projection is the native class map. -/
noncomputable def hilbert_stage (onto : Function.Surjective (numberFieldSymbol K L))
    (kernel : ∀ I, numberFieldSymbol K L I = 1 ↔ (I : Submodule (𝓞 K) K).IsPrincipal) : Stage where
  Ideal := (FractionalIdeal (𝓞 K)⁰ K)ˣ
  Class := ClassGroup (𝓞 K)
  Gal := L ≃ₐ[K] L
  ideals := groupLaw _
  classes := groupLaw _
  galois := groupLaw _
  idealClass := ⟨lawHom (ClassGroup.mk K), fun c => ClassGroup.induction K (fun I => ⟨I,rfl⟩) c⟩
  symbol := lawHom (numberFieldSymbol K L)
  onto := onto
  kernel I := (kernel I).trans ClassGroup.mk_eq_one_iff.symm
  abelian := mul_comm

theorem hilbert_stage_at_prime (onto : Function.Surjective (numberFieldSymbol K L))
    (kernel : ∀ I, numberFieldSymbol K L I = 1 ↔ (I : Submodule (𝓞 K) K).IsPrincipal)
    (p : HeightOneSpectrum (𝓞 K)) :
    (finiteArtin (hilbert_stage K L onto kernel)).app (ClassGroup.mk K (primeUnit (K:=K) p)) =
      numberFieldFrobenius K L p :=
  (artin_of_ideal (hilbert_stage K L onto kernel) (primeUnit (K:=K) p)).trans (symbol_at_prime K L p)

end Reimann.DyadicHilbertStage69
