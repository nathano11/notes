import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic

/-! Finite arithmetic Artin symbols on the fractional ideals of a Dedekind
domain. For a number field the domain is its ring of integers. -/
namespace Reimann.DyadicNativeClass69

open scoped nonZeroDivisors
open IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Valuations of the actual invertible fractional ideal, as its finite divisor. -/
noncomputable def divisor (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count K v (I : FractionalIdeal R⁰ K))
    (by simpa only [Filter.eventually_cofinite, Function.support, not_not] using
      FractionalIdeal.finite_factors (K:=K) (I : FractionalIdeal R⁰ K))

theorem divisor_at (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    divisor I v = FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := rfl

theorem divisor_one : divisor (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
  ext v
  exact FractionalIdeal.count_one K v

theorem divisor_mul (I J : (FractionalIdeal R⁰ K)ˣ) :
    divisor (I*J)=divisor I+divisor J := by
  ext v
  exact FractionalIdeal.count_mul K v I.ne_zero J.ne_zero

/-- Products of arithmetic Frobenii, with signed fractional-ideal exponents. -/
noncomputable def idealSymbol {G : Type*} [CommGroup G] (Frob : HeightOneSpectrum R → G) :
    (FractionalIdeal R⁰ K)ˣ →* G where
  toFun I := (divisor I).prod (fun p e => Frob p ^ e)
  map_one' := by rw [divisor_one]; exact Finsupp.prod_zero_index
  map_mul' I J := by
    rw [divisor_mul]
    exact Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ x y => zpow_add _ x y)

theorem divisor_prime (p : HeightOneSpectrum R) (I : (FractionalIdeal R⁰ K)ˣ)
    (rep : (I : FractionalIdeal R⁰ K) = (p.asIdeal : FractionalIdeal R⁰ K)) :
    divisor I = Finsupp.single p 1 := by
  classical
  ext v
  rw [divisor_at,rep,FractionalIdeal.count_maximal]
  simp [Finsupp.single_apply]

theorem idealSymbol_prime {G : Type*} [CommGroup G] (Frob : HeightOneSpectrum R → G)
    (p : HeightOneSpectrum R) (I : (FractionalIdeal R⁰ K)ˣ)
    (rep : (I : FractionalIdeal R⁰ K)=(p.asIdeal : FractionalIdeal R⁰ K)) :
    idealSymbol Frob I=Frob p := by
  change (divisor I).prod _ = _
  rw [divisor_prime p I rep,Finsupp.prod_single_index (zpow_zero _),zpow_one]

/-- Only the principal-ideal product formula is needed for descent; odd
ideal classes may still lie in the kernel of the 2-Hilbert quotient. -/
noncomputable def class_artin {G : Type*} [CommGroup G] (Frob : HeightOneSpectrum R → G)
    (principal : ∀ x : Kˣ, idealSymbol Frob (toPrincipalIdeal R K x)=1) :
    ClassGroup R →* G :=
  (QuotientGroup.lift (toPrincipalIdeal R K).range (idealSymbol Frob)
    (by rintro I ⟨x,rfl⟩; exact principal x)).comp (ClassGroup.equiv K).toMonoidHom

theorem class_artin_mk {G : Type*} [CommGroup G] (Frob : HeightOneSpectrum R → G)
    (principal : ∀ x : Kˣ, idealSymbol Frob (toPrincipalIdeal R K x)=1)
    (I : (FractionalIdeal R⁰ K)ˣ) :
    class_artin Frob principal (ClassGroup.mk K I) = idealSymbol Frob I := by
  simp only [class_artin,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,ClassGroup.equiv_mk,
    FractionalIdeal.canonicalEquiv_self,RingEquiv.coe_mulEquiv_refl]
  rfl

noncomputable def primeUnit (p : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (p.asIdeal : FractionalIdeal R⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)

theorem idealSymbol_primeUnit {G : Type*} [CommGroup G] (Frob : HeightOneSpectrum R → G)
    (p : HeightOneSpectrum R) : idealSymbol Frob (primeUnit (K:=K) p) = Frob p :=
  idealSymbol_prime Frob p _ rfl

/-- Frobenius functoriality on every fractional ideal follows from its
values on prime generators, including all negative valuations. -/
theorem symbol_natural {A B : Type*} [CommGroup A] [CommGroup B]
    (a : HeightOneSpectrum R → A) (h : A →* B) (I : (FractionalIdeal R⁰ K)ˣ) :
    h (idealSymbol a I) = idealSymbol (fun p => h (a p)) I := by
  change h ((divisor I).prod _) = (divisor I).prod _
  rw [map_finsuppProd]
  apply Finsupp.prod_congr
  intro v hv
  exact map_zpow h _ _

/-- Use the ideal norm of each native prime as a factor of the
fractional-ideal norm. An equality of arithmetic prime Frobenii suffices. -/
theorem fractional_norm_restriction {S L U G : Type*} [CommRing S] [IsDedekindDomain S]
    [Field L] [Algebra S L] [IsFractionRing S L] [CommGroup U] [CommGroup G]
    (lower : HeightOneSpectrum R → G) (upper : HeightOneSpectrum S → U)
    (res : U →* G) (normPrime : HeightOneSpectrum S → (FractionalIdeal R⁰ K)ˣ)
    (norm_frob : ∀ p, idealSymbol lower (normPrime p)=res (upper p)) (I : (FractionalIdeal S⁰ L)ˣ) :
    idealSymbol lower (idealSymbol normPrime I)=res (idealSymbol upper I) := by
  rw [symbol_natural,symbol_natural]
  exact congrArg (fun f => idealSymbol f I) (funext norm_frob)

end Reimann.DyadicNativeClass69
