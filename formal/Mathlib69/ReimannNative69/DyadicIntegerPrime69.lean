import ReimannNative69.DyadicNativePrime69
import Reimann.DyadicPrimeConjugacy69
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-! Maximal prolongations in the actual integral closures of ℤ, and their finite contractions. -/
namespace Reimann.DyadicIntegerPrime69

open DyadicNativePrime69

variable {R S : Type*} [CommRing R] [CommRing S]

theorem contraction_eq_comap (f : R →+* S) (P : Ideal S) :
    contraction f P=P.comap f := by ext x; rfl

/-- The actual subring cut out by monic integer polynomial equations. -/
abbrev integerRing (A : Type*) [CommRing A] : Subring A :=
  (integralClosure ℤ A).toSubring

def integersMap (f : R →+* S) : integerRing R →+* integerRing S where
  toFun x := ⟨f x.val,map_isIntegral_int f x.property⟩
  map_zero' := Subtype.ext f.map_zero
  map_one' := Subtype.ext f.map_one
  map_add' x y := Subtype.ext (f.map_add x y)
  map_mul' x y := Subtype.ext (f.map_mul x y)

/-- The intrinsic ring of integers at the layer is exactly its intersection with upper integers. -/
theorem integers_reflect (f : R →+* S) (hf : Function.Injective f) (x : R) :
    f x ∈ integerRing S ↔ x ∈ integerRing R := isIntegral_algHom_iff f.toIntAlgHom hf

def integerStageEquiv (layer : Subring R) :
    integerRing layer ≃+* stageOrder (integerRing R) layer where
  toFun x := ⟨x.val.val,(integers_reflect layer.subtype Subtype.val_injective x.val).mpr x.property,x.val.property⟩
  invFun y := ⟨⟨y.val,y.property.2⟩,(integers_reflect layer.subtype Subtype.val_injective _).mp y.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- When the field orbit product lies in the lower field, its integral value lies in the
lower integer ring. Apply this with x the product of the integral conjugates. -/
theorem integral_norm_descends (f : R →+* S) (hf : Function.Injective f)
    (x : integerRing S) (inField : ∃ a : R, f a = x.val) :
    ∃ y : integerRing R, integersMap f y=x := by
  obtain ⟨a,ha⟩ := inField
  have h : f a ∈ integerRing S := ha ▸ x.property
  exact ⟨⟨a,(integers_reflect f hf a).mp h⟩,Subtype.ext ha⟩

/-- At the finite level this is the prime of the intrinsic integer ring of the subfield. -/
theorem stage_ring_prime (layer : Subring R) (P : Ideal (integerRing R)) (hP : P.IsPrime) :
    (contraction (integersMap layer.subtype) P).IsPrime := prime_contraction _ P hP

/-- Each integral element of the upper prime occurs in the prime of the full intrinsic
integer ring of a finite layer. No chosen list of integral representatives is needed. -/
theorem contracted_integer_tower (layer : ℕ → Subring R) (exhaustive : ∀ x : R, ∃ n, x ∈ layer n)
    (P : Ideal (integerRing R)) (x : integerRing R) :
    x ∈ P ↔ ∃ n, ∃ y : integerRing (layer n), y ∈ contraction (integersMap (layer n).subtype) P ∧
      integersMap (layer n).subtype y=x := by
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := exhaustive x.val
    let z : layer n := ⟨x.val,hn⟩
    have hz := (integers_reflect (layer n).subtype Subtype.val_injective z).mp x.property
    exact ⟨n,⟨z,hz⟩,hx,rfl⟩
  · rintro ⟨n,y,hy,rfl⟩
    exact hy

/-- For every field embedding, the entire target integer ring is integral over the source
integer ring, with no finiteness condition on the upper extension. -/
theorem integersMap_integral (f : R →+* S) : (integersMap f).IsIntegral := by
  intro x
  have hx : IsIntegral ℤ x :=
    (isIntegral_algHom_iff (integerRing S).subtype.toIntAlgHom Subtype.val_injective).mp x.property
  letI := (integersMap f).toAlgebra
  exact hx.tower_top (A := integerRing R)

theorem maximal_integer_contraction (f : R →+* S) (P : Ideal (integerRing S)) (hP : P.IsMaximal) :
    (contraction (integersMap f) P).IsMaximal := by
  letI := hP
  rw [contraction_eq_comap]
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (integersMap_integral f) P

/-- An actual maximal ideal of the lower ring of integers has a maximal prolongation,
including in an infinite algebraic upper field. -/
theorem prolong_integer_prime (f : R →+* S) (hf : Function.Injective f)
    (p : Ideal (integerRing R)) (hp : p.IsMaximal) :
    ∃ P : Ideal (integerRing S), P.IsMaximal ∧ contraction (integersMap f) P=p := by
  let φ := integersMap f
  letI := φ.toAlgebra
  letI : Algebra.IsIntegral (integerRing R) (integerRing S) := ⟨integersMap_integral f⟩
  letI := hp
  have hi : Function.Injective φ := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
  have hk : RingHom.ker (algebraMap (integerRing R) (integerRing S))≤p := by
    change RingHom.ker φ ≤ p
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hi]
    exact bot_le
  obtain ⟨P,hP,e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral p hk
  exact ⟨P,hP,(contraction_eq_comap φ P).trans e⟩

/-- Turn the native maximal ideal into the residue-field hypothesis of the finite
prime-correction proof. -/
theorem residueMaximal_of_maximal {A : Type} [CommRing A] (P : Ideal A) (hp : P.IsMaximal) :
    DyadicPrimeConjugacy69.ResidueMaximal (fun x : A => x∈P) where
  zero := P.zero_mem
  proper := hp.isPrime.one_notMem
  plus _ _ := P.add_mem
  absorb _ y := P.mul_mem_right y
  inverse x hx := by
    obtain ⟨y,z,hz,he⟩ := hp.exists_inv hx
    refine ⟨y,?_⟩
    rwa [show 1-x*y=z by rw [←he,mul_comm x y,add_sub_cancel_left]]

theorem integer_contraction_transitive {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (P : Ideal (integerRing C)) :
    contraction (integersMap f) (contraction (integersMap g) P) =
      contraction (integersMap (g.comp f)) P := by ext x; rfl

theorem adjacent_integer_contraction {A : Type*} [CommRing A] {K L : Subring A}
    (h : K ≤ L) (P : Ideal (integerRing A)) :
    contraction (integersMap (Subring.inclusion h)) (contraction (integersMap L.subtype) P) =
      contraction (integersMap K.subtype) P := by ext x; rfl

/-- Every lower maximal prime containing two yields a global maximal ideal, maximal primes
at all finite levels, and the local residue-field input for finite lift correction. -/
theorem dyadic_prime_tower {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
    (layer : ℕ → Subring Ω) (exhaustive : ∀ x : Ω, ∃ n, x ∈ layer n)
    (p : Ideal (integerRing K)) (hp : p.IsMaximal) (two : (2:integerRing K)∈p) :
    ∃ P : Ideal (integerRing Ω), P.IsMaximal ∧ contraction (integersMap j) P=p ∧
      (∀ n, let Q := contraction (integersMap (layer n).subtype) P
            Q.IsMaximal ∧ (2 : integerRing (layer n)) ∈ Q ∧
              DyadicPrimeConjugacy69.ResidueMaximal (fun x => x∈Q)) ∧
      ∀ x : integerRing Ω, x∈P ↔ ∃ n, ∃ y : integerRing (layer n),
        y ∈ contraction (integersMap (layer n).subtype) P ∧ integersMap (layer n).subtype y=x := by
  obtain ⟨P,hP,hc⟩ := prolong_integer_prime j j.injective p hp
  have h2 : (2 : integerRing Ω)∈P := by
    have h : (2 : integerRing K)∈contraction (integersMap j) P := hc.symm ▸ two
    simpa only [mem_contraction,map_ofNat] using h
  refine ⟨P,hP,hc,?_,contracted_integer_tower layer exhaustive P⟩
  intro n
  have hm := maximal_integer_contraction (layer n).subtype P hP
  exact ⟨hm,by simpa only [mem_contraction,map_ofNat] using h2,residueMaximal_of_maximal _ hm⟩

theorem distinct_prolongations {K Ω : Type*} [Field K] [Field Ω] (j : K →+* Ω)
    (p q : Ideal (integerRing K)) (hp : p.IsMaximal) (hq : q.IsMaximal) (hne : p≠q) :
    ∃ P Q : Ideal (integerRing Ω), P.IsMaximal ∧ Q.IsMaximal ∧
      contraction (integersMap j) P=p ∧ contraction (integersMap j) Q=q ∧ P≠Q := by
  obtain ⟨P,hP,hp'⟩ := prolong_integer_prime j j.injective p hp
  obtain ⟨Q,hQ,hq'⟩ := prolong_integer_prime j j.injective q hq
  exact ⟨P,Q,hP,hQ,hp',hq',fun h => hne (hp'.symm.trans ((congrArg _ h).trans hq'))⟩

end Reimann.DyadicIntegerPrime69
