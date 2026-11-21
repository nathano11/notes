import ReimannNative69.DyadicNativeClass69
import ReimannNative69.DyadicClassNorm69

/-! Height-one prime classes determine homomorphisms on a Dedekind class group. -/
namespace Reimann.DyadicClassPrimeExt69

open IsDedekindDomain DyadicNativeClass69 DyadicClassNorm69
open scoped nonZeroDivisors NumberField

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {G : Type*} [Monoid G]

def primeIdeal (p : HeightOneSpectrum R) : (Ideal R)⁰ :=
  ⟨p.asIdeal,mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩

theorem integral_hom_ext_on_primes (f g : (Ideal R)⁰ →* G)
    (primes : ∀ p : HeightOneSpectrum R, f (primeIdeal p)=g (primeIdeal p)) : f=g := by
  apply MonoidHom.ext
  rintro ⟨I,hI⟩
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact ((mem_nonZeroDivisors_iff_ne_zero.mp hI) rfl).elim
  | h₂ J hu =>
    obtain rfl : J=1 := (Ideal.isUnit_iff.mp hu).trans Ideal.one_eq_top.symm
    change f 1 = g 1
    simp
  | h₃ J P hJ hP ih =>
    let q : HeightOneSpectrum R := ⟨P,Ideal.isPrime_of_prime hP,hP.ne_zero⟩
    let a : (Ideal R)⁰ := ⟨J,mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩
    have ha : f a=g a := ih a.property
    change f (primeIdeal q * a)=g (primeIdeal q * a)
    rw [map_mul,map_mul,primes,ha]

theorem class_hom_ext_on_primes (f g : ClassGroup R →* G)
    (primes : ∀ p : HeightOneSpectrum R,
      f (ClassGroup.mk0 (primeIdeal p))=g (ClassGroup.mk0 (primeIdeal p))) : f=g := by
  have h := integral_hom_ext_on_primes (f.comp ClassGroup.mk0) (g.comp ClassGroup.mk0) primes
  apply MonoidHom.ext
  intro x
  obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective x
  exact DFunLike.congr_fun h I

theorem prime_class_mk (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) :
    ClassGroup.mk K (primeUnit (K:=K) p) = ClassGroup.mk0 (primeIdeal p) :=
  ClassGroup.mk_mk0 K (primeIdeal p)

theorem class_hom_ext_on_primeUnit (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (f g : ClassGroup R →* G)
    (primes : ∀ p : HeightOneSpectrum R,
      f (ClassGroup.mk K (primeUnit (K:=K) p))=g (ClassGroup.mk K (primeUnit (K:=K) p))) : f=g := by
  apply class_hom_ext_on_primes
  simpa only [prime_class_mk] using primes

/-- An upper class-group transition equals the canonical norm once its value
on each prime class is the class of that prime's relative ideal norm. -/
theorem eq_numberField_norm_on_primes (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (F : ClassGroup (𝓞 L) →* ClassGroup (𝓞 K))
    (primes : ∀ p : HeightOneSpectrum (𝓞 L), F (ClassGroup.mk L (primeUnit (K:=L) p)) =
      ClassGroup.mk0 (idealNorm (𝓞 K) (primeIdeal p))) : F=numberField_norm K L := by
  apply class_hom_ext_on_primeUnit L
  intro p
  rw [primes,prime_class_mk,numberField_norm_mk0]

end Reimann.DyadicClassPrimeExt69
