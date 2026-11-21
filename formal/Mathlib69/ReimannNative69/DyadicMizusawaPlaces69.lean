import ReimannNative69.DyadicAbsoluteCenters69
import ReimannNative69.DyadicUnramifiedClosure69

/-! Restriction of continuous decomposition group actions from the intrinsic
unramified pro-2 extension over the conductor-69 cyclotomic base. -/
namespace Reimann.DyadicMizusawaPlaces69

open scoped Pointwise
open DyadicAbsoluteCenters69 DyadicNormalTower69 DyadicUnramifiedClosure69 DyadicPrimeGalois69
open DyadicIntegerPrime69 DyadicTowerCenters69

variable {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    (F M : IntermediateField E Ω) [Normal E F] (hFM : F ≤ M)

/-- Canonical restriction from M to the contained normal intermediate field F. -/
noncomputable def relativeHom : Gal(M/E) →* Gal(F/E) := by
  letI : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  letI : IsScalarTower E F M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact AlgEquiv.restrictNormalHom F

theorem relative_agrees (g : Gal(M/E)) (b : F) :
    ((relativeHom F M hFM g b : F) : Ω) = (g (⟨b.val,hFM b.property⟩ : M) : Ω) := by
  letI : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  letI : IsScalarTower E F M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact congrArg (fun v : M => (v : Ω)) (g.restrictNormal_commutes F b)

/-- Restriction between the two finite or infinite normal intermediates is
continuous in their Krull topologies. -/
theorem relative_continuous [IsGalois E Ω] [Normal E M] : Continuous (relativeHom F M hFM) := by
  let q := Topology.IsQuotientMap.of_surjective_continuous
    (AlgEquiv.restrictNormalHom_surjective (F:=E) (K₁:=M) Ω)
    (InfiniteGalois.restrictNormalHom_continuous M)
  apply q.continuous_iff.mpr
  have eq : (relativeHom F M hFM) ∘ (AlgEquiv.restrictNormalHom M : Gal(Ω/E) →* Gal(M/E)) =
      (AlgEquiv.restrictNormalHom F : Gal(Ω/E) →* Gal(F/E)) := by
    funext g
    apply AlgEquiv.ext
    intro b
    apply Subtype.ext
    exact (relative_agrees F M hFM _ b).trans ((g.restrictNormal_commutes M
      (⟨b.val,hFM b.property⟩ : M)).trans (g.restrictNormal_commutes F b).symm)
  rw [eq]
  exact InfiniteGalois.restrictNormalHom_continuous F

/-- Restriction to the actual stabilizer of the contracted integral prime. -/
noncomputable def decompositionRestriction (P : Ideal (integralClosure ℤ Ω)) :
    MulAction.stabilizer Gal(M/E) (P.comap (integersInclusion M Ω)) →* Gal(F/E) :=
  (relativeHom F M hFM).comp (MulAction.stabilizer Gal(M/E) _).subtype

theorem restriction_continuous [IsGalois E Ω] [Normal E M] (P : Ideal (integralClosure ℤ Ω)) :
    Continuous (decompositionRestriction F M hFM P) :=
  (relative_continuous F M hFM).comp continuous_subtype_val

theorem restriction_surjective [Normal E M] (P : Ideal (integralClosure ℤ Ω))
    (hsur : Function.Surjective ((AlgEquiv.restrictNormalHom F).comp
      (MulAction.stabilizer Gal(Ω/E) P).subtype)) :
    Function.Surjective (decompositionRestriction F M hFM P) := by
  intro s
  obtain ⟨m,hm⟩ := normal_intermediate_lift F M hFM P hsur s
  refine ⟨m,AlgEquiv.ext (fun b => Subtype.ext ?_)⟩
  exact (relative_agrees F M hFM m.val b).trans (hm b)

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
  (x y : Ω) (ζ : ℕ → Ω)

noncomputable def intrinsicField : IntermediateField ℚ Ω :=
  maximalField Ω (cyclotomicBase Ω (ζ 0*x*y) ζ)

theorem radicand (hx : x^2 = -3) (hy : y^2 = -23) (hi : (ζ 0)^2 = -1) :
    (ζ 0*x*y)^2 = -69 := by
  rw [mul_pow,mul_pow,hi,hx,hy]
  norm_num

/-- The restriction map on the contracted prime of M over the actual Eₐ;
the normality of F/Eₐ follows from the explicit primitive root orders. -/
noncomputable def intrinsicRestriction (a : ℕ) (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1)
    (hE : realLayer Ω x y (ζ a) ≤ intrinsicField Ω x y ζ)
    (hF : fullCyclotomic Ω x y ζ a ≤ IntermediateField.extendScalars hE)
    (P : Ideal (integralClosure ℤ Ω)) :
    MulAction.stabilizer Gal((IntermediateField.extendScalars hE)/(realLayer Ω x y (ζ a)))
      (P.comap (integersInclusion (IntermediateField.extendScalars hE) Ω)) →*
      Gal((fullCyclotomic Ω x y ζ a)/(realLayer Ω x y (ζ a))) := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI := fullCyclotomic_normal Ω x y ζ a hz
  exact decompositionRestriction _ _ hF P

theorem intrinsic_restriction_at_prime (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1) (a : ℕ)
    (hE : realLayer Ω x y (ζ a) ≤ intrinsicField Ω x y ζ)
    (hF : fullCyclotomic Ω x y ζ a ≤ IntermediateField.extendScalars hE)
    (P : Ideal (integralClosure ℤ Ω)) (hsur : SurjectsAt Ω x y ζ hz P a) :
    Continuous (intrinsicRestriction Ω x y ζ a hz hE hF P) ∧
      Function.Surjective (intrinsicRestriction Ω x y ζ a hz hE hF P) := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI := fullCyclotomic_normal Ω x y ζ a hz
  have hd := radicand Ω x y ζ hx hy (hz 0)
  let : Normal (realLayer Ω x y (ζ a)) (IntermediateField.extendScalars hE) :=
    (conductor69_maximal_normal Ω (ζ 0*x*y) ζ hd hz _ hE).2.to_normal
  exact ⟨restriction_continuous _ _ hF P,restriction_surjective _ _ hF P hsur⟩

/-- A single pair of actual primes contracts to different labeled dyadic
primes of the intrinsic field M. Their restriction maps are continuous
surjections at every real level a. -/
def TwoPrimeRestriction (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1) : Prop :=
    ∃ u : integerRing Ω, u.val = (1+y)/2 ∧ ∃ P Q : Ideal (integerRing Ω),
      Labels P Q u ∧ contractsAt P Q u (intrinsicField Ω x y ζ).toSubfield ∧
        P.comap (integersInclusion (intrinsicField Ω x y ζ) Ω) ≠
          Q.comap (integersInclusion (intrinsicField Ω x y ζ) Ω) ∧
        ∀ a, ∃ hE : realLayer Ω x y (ζ a) ≤ intrinsicField Ω x y ζ,
          ∃ hF : fullCyclotomic Ω x y ζ a ≤ IntermediateField.extendScalars hE,
            (Continuous (intrinsicRestriction Ω x y ζ a hz hE hF P) ∧
              Function.Surjective (intrinsicRestriction Ω x y ζ a hz hE hF P)) ∧
            (Continuous (intrinsicRestriction Ω x y ζ a hz hE hF Q) ∧
              Function.Surjective (intrinsicRestriction Ω x y ζ a hz hE hF Q))

theorem two_places_from_genus (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1) (hs : ∀ j, (ζ (j+1))^2 = ζ j)
    (genus : ∀ a, (fullCyclotomic Ω x y ζ a).restrictScalars ℚ ≤ intrinsicField Ω x y ζ) :
    TwoPrimeRestriction Ω x y ζ hz := by
  have subE (a : ℕ) : realLayer Ω x y (ζ a) ≤ intrinsicField Ω x y ζ := by
    intro s h
    exact genus a ((fullCyclotomic Ω x y ζ a).algebraMap_mem (⟨s,h⟩ : realLayer Ω x y (ζ a)))
  obtain ⟨u,hu,P,Q,labels,_,all⟩ := chosen_roots_both_primes Ω x y ζ hx hy hz hs
  let M := intrinsicField Ω x y ζ
  have ym : y ∈ M := subE 0 (DyadicCyclotomicModel69.lower_generators Ω x y ζ 0).2.1
  have um : u.val ∈ M := hu ▸ M.div_mem (M.add_mem M.one_mem ym) (M.natCast_mem 2)
  have lower := contract_labels labels M.toSubfield um
  obtain ⟨w,hw,hwlabel⟩ := lower
  refine ⟨u,hu,P,Q,labels,⟨w,hw,hwlabel⟩,labels_distinct hwlabel,?_⟩
  intro a
  have hf : fullCyclotomic Ω x y ζ a ≤ IntermediateField.extendScalars (subE a) := genus a
  exact ⟨subE a,hf,intrinsic_restriction_at_prime Ω x y ζ hx hy hz a _ hf P (all a).2.1,
    intrinsic_restriction_at_prime Ω x y ζ hx hy hz a _ hf Q (all a).2.2⟩

end Reimann.DyadicMizusawaPlaces69
