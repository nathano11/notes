import Reimann2893.SignedArithmeticTower2893
import Reimann2893.SignedFiniteClasses2893
import Reimann2893.SignedProfiniteLimit2893
import Reimann2893.SignedClassScalars2893

/-! The inverse-limit topology of the finite discrete two-primary class groups. -/
namespace Reimann.SignedClassTopology2893

open SignedLayerClasses2893 SignedArithmeticTower2893

scoped instance levelTopology (n : ℕ) : TopologicalSpace (layerTwoClass n) := ⊥

scoped instance levelDiscrete (n : ℕ) : DiscreteTopology (layerTwoClass n) := ⟨rfl⟩

scoped instance levelFinite (n : ℕ) : Finite (layerTwoClass n) :=
  SignedFiniteClasses2893.finite_two_classes n

theorem profinite_limit : CompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X :=
  SignedProfiniteLimit2893.profinite_limit norm

theorem topological_group : IsTopologicalGroup X := SignedProfiniteLimit2893.topological_group norm

theorem continuous_projection (n : ℕ) : Continuous (fun x : X => x.val n) :=
  SignedProfiniteLimit2893.continuous_projection norm n

theorem continuous_forward : Continuous (gamma : X → X) :=
  SignedProfiniteLimit2893.continuous_forward norm primaryForward norm_forward

theorem continuous_gammaPower :
    Continuous (fun p : ℤ_[2] × X => gammaPower (SignedNativeScalar2893.read p.1) p.2) :=
  SignedProfiniteLimit2893.continuous_adic_action norm primaryForward norm_forward primary_period


/-- For discrete classes of two-power order, scalar multiplication is continuous
in both the dyadic integer and the class. The required precision depends on the class. -/
theorem continuous_level_scalar {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (h : SignedClassScalars2893.KilledByTwoPowers G) :
    Continuous (fun p : ℤ_[2] × G => SignedClassScalars2893.power h p.1 p.2) := by
  apply continuous_prod_of_discrete_right.mpr
  intro x
  obtain ⟨k,hk⟩ := h x
  simp only [SignedClassScalars2893.power_at h _ x k hk]
  apply (continuous_of_discreteTopology (f := fun r : ℕ => x^r)).comp
  convert SignedProfiniteLimit2893.continuous_exponent k using 1
  funext z
  cases k with
  | zero => have hz := z.appr_lt 0; simpa using Nat.eq_zero_of_lt_one hz
  | succ i => simp [SignedAdicAction2893.exponent, SignedNativeScalar2893.read,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (z.appr_lt _)]

theorem continuous_smul :
    letI := SignedClassScalars2893.limitModule layerClass norm
    ContinuousSMul ℤ_[2] (Additive X) := by
  letI := SignedClassScalars2893.limitModule layerClass norm
  constructor
  change Continuous (fun p : ℤ_[2] × X => SignedClassScalars2893.limitPower layerClass norm p.1 p.2)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_level_scalar (SignedClassScalars2893.primary_killed (layerClass n))).comp
    (continuous_fst.prodMk ((continuous_projection n).comp continuous_snd))

end Reimann.SignedClassTopology2893
