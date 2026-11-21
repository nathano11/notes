import ReimannNative69.DyadicPrimeGalois69
import ReimannNative69.DyadicTowerCenters69
import ReimannNative69.DyadicPrimeGeneratorValue69
import ReimannNative69.DyadicFiniteModel69
import ReimannNative69.DyadicPrimeValueTower69

/-! Absolute decomposition at the two dyadic primes above the conductor-69 biquadratic field. -/
namespace Reimann.DyadicAbsoluteCenters69

open scoped Pointwise
open DyadicNormalTower69 DyadicPrimeGalois69 DyadicIntegerPrime69 DyadicTowerCenters69

/-- A decomposition-preserving lift in the algebraic closure restricts to a lift preserving
the contracted prime in every intervening normal field. -/
theorem normal_intermediate_lift {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    (F M : IntermediateField E Ω) [Normal E F] [Normal E M] (hFM : F ≤ M)
    (P : Ideal (integralClosure ℤ Ω))
    (lifts : Function.Surjective ((AlgEquiv.restrictNormalHom F).comp
      (MulAction.stabilizer Gal(Ω/E) P).subtype)) (s : Gal(F/E)) :
    ∃ m : MulAction.stabilizer Gal(M/E) (P.comap (integersInclusion M Ω)),
      ∀ x : F, ((m.val (⟨x.val,hFM x.property⟩ : M)) : Ω) = ((s x) : Ω) := by
  obtain ⟨g,hg⟩ := lifts s
  have hm : (AlgEquiv.restrictNormalHom M g.val) • P.comap (integersInclusion M Ω) =
      P.comap (integersInclusion M Ω) :=
    (contraction_conjugate M g.val P).symm.trans
      (congrArg (Ideal.comap (integersInclusion M Ω)) g.property)
  refine ⟨⟨AlgEquiv.restrictNormalHom M g.val,hm⟩,fun x => ?_⟩
  change AlgEquiv.restrictNormalHom F g.val = s at hg
  rw [← hg]
  exact (AlgEquiv.restrictNormalHom_apply M g.val ⟨x.val,hFM x.property⟩).trans
    (AlgEquiv.restrictNormalHom_apply F g.val x).symm

/-- The actual restriction on the stabilizer of an integral prime at the displayed real level. -/
def SurjectsAt (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (x y : Ω) (ζ : ℕ → Ω) (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ) = -1)
    (P : Ideal (integralClosure ℤ Ω)) (a : ℕ) : Prop :=
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI := fullCyclotomic_normal Ω x y ζ a hz
  Function.Surjective ((AlgEquiv.restrictNormalHom (fullCyclotomic Ω x y ζ a)).comp
    (MulAction.stabilizer Gal(Ω/(realLayer Ω x y (ζ a))) P).subtype)

open DyadicCyclotomicModel69 DyadicPrimeGeneratorValue69 in
/-- The two generator labels in a contracted lower integer ring agree with the explicit
biquadratic embedding. Both equalities are in the full lower field. -/
theorem contracted_generators (Ω : Type) [Field Ω] [CharZero Ω] (x y : Ω)
    (ζ : ℕ → Ω) (a : ℕ) (hx : x^2 = -3) (hy : y^2 = -23)
    (w : integerRing (fullCyclotomic Ω x y ζ a)) (hw : ((w.val : fullCyclotomic Ω x y ζ a) : Ω) = (1+y)/2) :
    (bottom Ω x y ζ a hx hy).app (DyadicArithmetic69.primeGenerator false).val = w.val ∧
      (bottom Ω x y ζ a hx hy).app (DyadicArithmetic69.primeGenerator true).val =
        (1 - w : integerRing (fullCyclotomic Ω x y ζ a)).val := by
  constructor
  · apply Subtype.ext
    exact (prime_generator_value Ω x y ζ a hx hy false).trans hw.symm
  · apply Subtype.ext
    change ((bottom Ω x y ζ a hx hy).app _ : Ω) = 1 - ((w.val : fullCyclotomic Ω x y ζ a) : Ω)
    rw [hw, prime_generator_value]
    rfl

open DyadicCyclotomicModel69 DyadicFiniteModel69 DyadicPrimeValueTower69 in
/-- A labeled integral generator in the contracted prime gives a decomposition-preserving lift
of every automorphism. The lower valuation is constructed by gluing finite prime valuations. -/
theorem surjects_from_generator (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (x y : Ω) (ζ : ℕ → Ω) (a : ℕ) (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ) = -1) (hs : ∀ n, (ζ (n+1))^2 = ζ n)
    (P : Ideal (integralClosure ℤ Ω)) [P.IsPrime] (v : Bool)
    (h₂ : (2 : integerRing (fullCyclotomic Ω x y ζ a)) ∈
      P.comap (integersInclusion (fullCyclotomic Ω x y ζ a) Ω))
    (w : integerRing (fullCyclotomic Ω x y ζ a))
    (hw : w ∈ P.comap (integersInclusion (fullCyclotomic Ω x y ζ a) Ω))
    (he : (bottom Ω x y ζ a hx hy).app (DyadicArithmetic69.primeGenerator v).val = w.val) :
    SurjectsAt Ω x y ζ hz P a := by
  let F := fullCyclotomic Ω x y ζ a
  let f := bottom Ω x y ζ a hx hy
  let p := P.comap (integersInclusion F Ω)
  obtain ⟨S,num,inc,covers,base,z,_,prim,gen⟩ := lower_stage_data Ω x y ζ a hx hy hz hs
  letI : ∀ n, NumberField (S n) := num
  obtain ⟨V,center,support⟩ := centered_union_of_generator p h₂ S inc covers f v base w hw he
    (fun n => a+n+1) z prim gen
  exact cyclotomic_surjective_at_center Ω x y ζ a hx hy hz (fun n => by simpa only [pow_two] using hs n)
    P v V center support

/-- One pair of distinct upper primes works simultaneously at every real layer. -/
theorem chosen_roots_both_primes (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (x y : Ω) (ζ : ℕ → Ω) (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ) = -1) (hs : ∀ n, (ζ (n+1))^2 = ζ n) :
    ∃ u : integerRing Ω, u.val = (1+y)/2 ∧ ∃ P Q : Ideal (integerRing Ω),
      Labels P Q u ∧ P ≠ Q ∧ ∀ a, contractsAt P Q u (realLayer Ω x y (ζ a)).toSubfield ∧
        SurjectsAt Ω x y ζ hz P a ∧ SurjectsAt Ω x y ζ hz Q a := by
  obtain ⟨u,hu,P,Q,labels,contracts⟩ := all_real_layer_centers Ω x y ζ hy
  letI : P.IsPrime := labels.left_maximal.isPrime
  letI : Q.IsPrime := labels.right_maximal.isPrime
  refine ⟨u,hu,P,Q,labels,labels_distinct labels,fun a => ?_⟩
  let F := fullCyclotomic Ω x y ζ a
  obtain ⟨w,hw,lower⟩ := (contracts a).2 F
  have value : ((w.val : F) : Ω) = (1+y)/2 := (congrArg Subtype.val hw).trans hu
  obtain ⟨left,right⟩ := contracted_generators Ω x y ζ a hx hy w value
  exact ⟨(contracts a).1,
    surjects_from_generator Ω x y ζ a hx hy hz hs P false lower.left_two w lower.left_root left,
    surjects_from_generator Ω x y ζ a hx hy hz hs Q true lower.right_two (1-w) lower.right_root right⟩

/-- In any algebraic closure of the rationals choose the two radicals, a compatible tower
of primitive dyadic roots, and two distinct labeled primes above 2. For every a, restriction
from either absolute decomposition group to Gal(E_a(μ₂∞)/E_a) is surjective. -/
theorem both_dyadic_primes_surject (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] :
    ∃ x y : Ω, ∃ ζ : ℕ → Ω, x^2 = -3 ∧ y^2 = -23 ∧ (∀ n, (ζ (n+1))^2 = ζ n) ∧
      ∃ hz : ∀ n, (ζ n)^(2^(n+1) : ℕ) = -1,
        ∃ u : integerRing Ω, u.val = (1+y)/2 ∧ ∃ P Q : Ideal (integerRing Ω),
          Labels P Q u ∧ P ≠ Q ∧
            ∀ a, contractsAt P Q u (realLayer Ω x y (ζ a)).toSubfield ∧
              SurjectsAt Ω x y ζ hz P a ∧ SurjectsAt Ω x y ζ hz Q a := by
  obtain ⟨x,y,ζ,hx,hy,hs,hz,_⟩ := absolute_real_layer_tower Ω
  exact ⟨x,y,ζ,hx,hy,hs,hz,chosen_roots_both_primes Ω x y ζ hx hy hz hs⟩

/-- A normal upper field over E_a containing all dyadic roots inherits the same lifting
property, with its own integral prime obtained by contraction. -/
theorem surjects_in_normal_field (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (x y : Ω) (ζ : ℕ → Ω) (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ) = -1)
    (P : Ideal (integralClosure ℤ Ω)) (a : ℕ) (hP : SurjectsAt Ω x y ζ hz P a)
    (M : IntermediateField (realLayer Ω x y (ζ a)) Ω) [Normal (realLayer Ω x y (ζ a)) M]
    (hFM : fullCyclotomic Ω x y ζ a ≤ M) (s : Gal((fullCyclotomic Ω x y ζ a)/(realLayer Ω x y (ζ a)))) :
    ∃ m : MulAction.stabilizer Gal(M/(realLayer Ω x y (ζ a))) (P.comap (integersInclusion M Ω)),
      ∀ b : fullCyclotomic Ω x y ζ a, ((m.val ⟨b.val,hFM b.property⟩) : Ω) = ((s b) : Ω) := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI := fullCyclotomic_normal Ω x y ζ a hz
  exact normal_intermediate_lift _ M hFM P hP s

end Reimann.DyadicAbsoluteCenters69
