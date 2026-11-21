import Reimann277.ArithmeticSymbol
import Reimann277.QuotientConjugation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

namespace Reimann.TameArithmeticNaturality277

set_option maxRecDepth 4096

open scoped nonZeroDivisors
open TameArithmeticSymbol277 TameArtin277 TameIdealArtin277 TameIdealAction277
open TameCyclotomicLocal277 TameQuotientConjugation277

attribute [local instance] TameArithmeticSymbol277.localizedDedekind

/-- A homomorphism from the ideal class group of a Dedekind domain is determined
by its values on classes of nonzero maximal ideals. -/
theorem class_hom_ext_on_primes {R H : Type*} [CommRing R] [IsDedekindDomain R] [Group H]
    (f g : ClassGroup R →* H)
    (hp : ∀ J : (Ideal R)⁰, J.val.IsMaximal → f (ClassGroup.mk0 J) = g (ClassGroup.mk0 J)) :
    f = g := by
  have each (I : Ideal R) : ∀ hI : I ∈ (Ideal R)⁰,
      f (ClassGroup.mk0 ⟨I,hI⟩) = g (ClassGroup.mk0 ⟨I,hI⟩) := by
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro hI
      exact False.elim ((mem_nonZeroDivisors_iff_ne_zero.mp hI) rfl)
    | h₂ I hI =>
      intro h
      have he : (⟨I,h⟩ : (Ideal R)⁰) = 1 :=
        Subtype.ext ((Ideal.isUnit_iff.mp hI).trans Ideal.one_eq_top.symm)
      rw [he,map_one,map_one,map_one]
    | h₃ I p hI hprime ih =>
      intro h
      let i : (Ideal R)⁰ := ⟨I,mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
      let j : (Ideal R)⁰ := ⟨p,mem_nonZeroDivisors_iff_ne_zero.mpr hprime.ne_zero⟩
      letI : p.IsPrime := Ideal.isPrime_of_prime hprime
      have hm : j.val.IsMaximal := ((inferInstance : p.IsPrime).isMaximal hprime.ne_zero)
      change f (ClassGroup.mk0 (j*i)) = g (ClassGroup.mk0 (j*i))
      rw [map_mul,map_mul,map_mul,hp j hm,ih i.property]
  apply MonoidHom.ext
  intro c
  obtain ⟨J,rfl⟩ := ClassGroup.mk0_surjective c
  exact each J.val J.property

/-- A commuting square of ring automorphisms transports ideal contractions. -/
theorem transport_contraction {A B : Type*} [CommRing A] [CommRing B] (i : A →+* B)
    (u : A ≃+* A) (v : B ≃+* B) (square : ∀ a, v (i a) = i (u a)) (P : Ideal B) :
    (P.map v).comap i = (P.comap i).map u := by
  rw [← Ideal.comap_symm v, ← Ideal.comap_symm u]
  ext a
  change v.symm (i a) ∈ P ↔ i (u.symm a) ∈ P
  have hinv : v.symm (i a) = i (u.symm a) := by
    apply v.injective
    rw [v.apply_symm_apply,square,u.apply_symm_apply]
  rw [hinv]

theorem quotient_card_transport {A : Type*} [CommRing A] (u : A ≃+* A) (J : Ideal A) :
    Nat.card (A ⧸ J.map u) = Nat.card (A ⧸ J) :=
  Nat.card_congr (Ideal.quotientEquiv J (J.map u) u rfl).symm.toEquiv

noncomputable def primeTransport (r n : ℕ) (g : Global) (J : IntegralIdeals r n) :
    IntegralIdeals r n :=
  ⟨J.val.map (onSIntegers r n g),
    mem_nonZeroDivisors_iff_ne_zero.mpr
      ((Ideal.map_eq_bot_iff_of_injective (onSIntegers r n g).injective).not.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp J.property))⟩

theorem transported_maximal {r n : ℕ} (g : Global) (J : IntegralIdeals r n) (hJ : J.val.IsMaximal) :
    (primeTransport r n g J).val.IsMaximal :=
  (Ideal.isMaximal_map_iff_of_bijective (f := onSIntegers r n g)
    (onSIntegers r n g).bijective).mpr hJ

theorem transported_residueSize {r n : ℕ} (g : Global) (J : IntegralIdeals r n) :
    residueSize (primeTransport r n g J) = residueSize J :=
  quotient_card_transport (onSIntegers r n g) J.val

theorem integral_square (r n : ℕ) (g : Global) (z : CutIntegers r n) :
    TameInertia277.integralEquiv (asAut g) (integralInclusion r n z) =
      integralInclusion r n (onIntegers r n g z) := by
  apply Subtype.ext
  letI := (cutField_finite_galois r n).2
  exact ((asAut g).restrictNormal_commutes (cutField r n) z.val).symm

theorem localization_square (r n : ℕ) (g : Global) (z : CutIntegers r n) :
    onSIntegers r n g (algebraMap (CutIntegers r n) (SIntegers r n) z) =
      algebraMap (CutIntegers r n) (SIntegers r n) (onIntegers r n g z) :=
  IsLocalization.ringEquivOfRingEquiv_eq (denominators_fixed r n g) z

theorem transported_prolongs {r n : ℕ} (g : Global) {J : IntegralIdeals r n}
    {P : Ideal ClosureIntegers} (h : Prolongs J P) :
    Prolongs (primeTransport r n g J) (TameInertia277.conjugateIdeal (asAut g) P) := by
  let k := TameInertia277.integralEquiv (asAut g)
  have ideal_transport : TameInertia277.conjugateIdeal (asAut g) P = P.map k := by
    rw [← Ideal.comap_symm k]
    ext z
    rfl
  refine ⟨?_,?_,?_⟩
  · rw [ideal_transport]
    exact (Ideal.isMaximal_map_iff_of_bijective (f := k) k.bijective).mpr h.maximal
  · change k.symm (277 : ClosureIntegers) ∉ P
    simpa only [map_ofNat] using h.away
  · rw [ideal_transport,transport_contraction _ _ k (integral_square r n g),h.contraction]
    exact (transport_contraction (algebraMap (CutIntegers r n) (SIntegers r n))
      (onIntegers r n g) (onSIntegers r n g) (localization_square r n g) J.val).symm

theorem conjugated_frobenius {r n : ℕ} (g : Global) (J : IntegralIdeals r n)
    (P : Ideal ClosureIntegers) (x : globalKernel r n) (hx : FrobeniusAt J P x) :
    FrobeniusAt (primeTransport r n g J) (TameInertia277.conjugateIdeal (asAut g) P)
      (conjugateKernel g x) := by
  unfold FrobeniusAt
  rw [transported_residueSize]
  exact TameInertia277.frobenius_conjugate P (residueSize J) (asAut g) (asAut x.val) hx

/-- Global reciprocity at the prime level. Conjugation is derived below. -/
structure PrimeSymbol (r n : ℕ) where
  ideals : IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n)
  at_prime : ∀ (J : IntegralIdeals r n), J.val.IsMaximal → ∀ P, Prolongs J P →
    ∃ x : globalKernel r n, FrobeniusAt J P x ∧
      ideals.symbol (FractionalIdeal.mk0 (FractionRing (SIntegers r n)) J) = project r n x

theorem all_frobenius_lifts {r n : ℕ} (s : PrimeSymbol r n) (J : IntegralIdeals r n)
    (hJ : J.val.IsMaximal) (P : Ideal ClosureIntegers) (hP : Prolongs J P)
    (x : globalKernel r n) (hx : FrobeniusAt J P x) :
    s.ideals.symbol (FractionalIdeal.mk0 (FractionRing (SIntegers r n)) J) = project r n x := by
  obtain ⟨y,hy,h⟩ := s.at_prime J hJ P hP
  exact h.trans (project_frobenius_independent hP y x hy hx)

theorem classToGalois_mk0 {r n : ℕ} (s : PrimeSymbol r n) (J : IntegralIdeals r n) :
    classToGalois s.ideals (ClassGroup.mk0 J) =
      s.ideals.symbol (FractionalIdeal.mk0 (FractionRing (SIntegers r n)) J) := by
  rw [← ClassGroup.mk_mk0 (FractionRing (SIntegers r n)) J, classToGalois_mk]

theorem class_prime_action {r n : ℕ} (g : Global) (J : IntegralIdeals r n) :
    onClass r n g (ClassGroup.mk0 J) = ClassGroup.mk0 (primeTransport r n g J) :=
  ClassGroup.mulEquiv_mk0 (onSIntegers r n g) J

theorem natural_on_prime {r n : ℕ} (s : PrimeSymbol r n) (g : Global) (J : IntegralIdeals r n)
    (hJ : J.val.IsMaximal) :
    classToGalois s.ideals (onClass r n g (ClassGroup.mk0 J)) =
      onQuotient r n g (classToGalois s.ideals (ClassGroup.mk0 J)) := by
  obtain ⟨P,hP⟩ := exists_prolongation J hJ
  obtain ⟨x,hx,hs⟩ := s.at_prime J hJ P hP
  rw [class_prime_action,classToGalois_mk0,classToGalois_mk0,hs,onQuotient_project]
  exact all_frobenius_lifts s _ (transported_maximal g J hJ) _ (transported_prolongs g hP)
    _ (conjugated_frobenius g J P x hx)

theorem natural_on_class {r n : ℕ} (s : PrimeSymbol r n) (g : Global) (c : SClassGroup r n) :
    classToGalois s.ideals (onClass r n g c) = onQuotient r n g (classToGalois s.ideals c) := by
  let f := (classToGalois s.ideals).toMonoidHom.comp (onClass r n g).toMonoidHom
  let k := (onQuotient r n g).toMonoidHom.comp (classToGalois s.ideals).toMonoidHom
  have h : f = k := class_hom_ext_on_primes f k (natural_on_prime s g)
  exact DFunLike.congr_fun h c

theorem natural_on_representatives {r n : ℕ} (s : PrimeSymbol r n) (g : Global)
    (x : globalKernel r n) (I : InvertibleIdeals (SIntegers r n))
    (hI : s.ideals.symbol I = project r n x) :
    s.ideals.symbol (transport r n g I) = project r n (conjugateKernel g x) := by
  have h := natural_on_class s g (ClassGroup.mk (FractionRing (SIntegers r n)) I)
  rw [transport_class,classToGalois_mk,classToGalois_mk,hI,onQuotient_project] at h
  exact h

def toInput {r n : ℕ} (s : PrimeSymbol r n) : Input r n where
  ideals := s.ideals
  frobenius := s.at_prime
  conjugation := natural_on_representatives s

theorem arithmetic_equivariance {r n : ℕ} (s : PrimeSymbol r n) :
    ArtinEquivariant (reciprocity (toInput s)) :=
  reciprocity_equivariant (toInput s)

end Reimann.TameArithmeticNaturality277
