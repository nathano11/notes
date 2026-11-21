import Reimann2893.SignedNormLimit2893
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Instances.Nat
import Reimann2893.SignedAdicAction2893
import Reimann2893.SignedNativeScalar2893

/-! The topology on a tower of finite discrete groups with compatible norm maps. -/
namespace Reimann.SignedProfiniteLimit2893

open SignedNormLimit2893

variable {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
  [∀ n, DiscreteTopology (G n)]

theorem closed_coherent (N : ∀ n, G (n+1) →* G n) :
    IsClosed ((coherent N : Subgroup (∀ n, G n)) : Set (∀ n, G n)) := by
  have eqn : ((coherent N : Subgroup (∀ n, G n)) : Set (∀ n, G n)) =
      ⋂ n, {x : ∀ n, G n | N n (x (n+1)) = x n} := by
    ext x
    change (∀ n, N n (x (n+1)) = x n) ↔ _
    simp
  rw [eqn]
  apply isClosed_iInter
  intro n
  exact isClosed_eq ((continuous_of_discreteTopology (f := (N n : G (n+1) → G n))).comp
    (continuous_apply (n+1))) (continuous_apply n)

theorem profinite_limit [∀ n, Finite (G n)] (N : ∀ n, G (n+1) →* G n) :
    CompactSpace (coherent N) ∧ T2Space (coherent N) ∧ TotallyDisconnectedSpace (coherent N) :=
  ⟨isCompact_iff_compactSpace.mp (closed_coherent N).isCompact, inferInstance, inferInstance⟩

theorem continuous_projection (N : ∀ n, G (n+1) →* G n) (n : ℕ) :
    Continuous (projection N n : coherent N → G n) :=
  (continuous_apply n).comp continuous_subtype_val

theorem continuous_forward (N : ∀ n, G (n+1) →* G n) (γ : ∀ n, G n ≃* G n)
    (comm : ∀ n x, N n (γ (n+1) x) = γ n (N n x)) :
    Continuous (forward N γ comm : coherent N → coherent N) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := (γ n : G n → G n))).comp (continuous_projection N n)

theorem topological_group (N : ∀ n, G (n+1) →* G n) : IsTopologicalGroup (coherent N) :=
  inferInstance

/-- In a sufficiently small ball the residue of the exponent is constant. -/
theorem exponent_eq_of_dist {z w : ℤ_[2]} (n : ℕ)
    (h : dist z w ≤ (2:ℝ)^(-(n:ℤ))) :
    SignedAdicAction2893.exponent (SignedNativeScalar2893.read z) n =
      SignedAdicAction2893.exponent (SignedNativeScalar2893.read w) n := by
  cases n with
  | zero => rfl
  | succ i =>
    change ((SignedNativeScalar2893.read z).residue i).toNat = ((SignedNativeScalar2893.read w).residue i).toNat
    apply congrArg BitVec.toNat
    apply SignedNativeScalar2893.word_ext
    rw [SignedNativeScalar2893.read_reduction, SignedNativeScalar2893.read_reduction]
    rw [dist_eq_norm] at h
    have hm := ((z-w).norm_le_pow_iff_mem_span_pow (i+1)).mp (by simpa using h)
    rwa [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hm

theorem continuous_exponent (n : ℕ) :
    Continuous (fun z : ℤ_[2] => SignedAdicAction2893.exponent (SignedNativeScalar2893.read z) n) := by
  apply continuous_def.mpr
  intro U _
  rw [Metric.isOpen_iff]
  intro x hx
  refine ⟨(2:ℝ)^(-(n:ℤ)), zpow_pos (by norm_num) _, ?_⟩
  intro y hy
  change SignedAdicAction2893.exponent (SignedNativeScalar2893.read y) n ∈ U
  rw [exponent_eq_of_dist n (le_of_lt hy)]
  exact hx

/-- Joint continuity in the standard metric topology on the native dyadic integers. -/
theorem continuous_adic_action (N : ∀ n, G (n+1) →* G n) (γ : ∀ n, G n ≃* G n)
    (comm : ∀ n x, N n (γ (n+1) x) = γ n (N n x))
    (period : ∀ n x, SignedAdicAction2893.iterate (γ n) (2^n) x = x) :
    Continuous (fun p : ℤ_[2] × coherent N =>
      SignedAdicAction2893.act N γ comm period (SignedNativeScalar2893.read p.1) p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  have c := ((continuous_exponent n).comp (continuous_fst (X := ℤ_[2]) (Y := coherent N))).prodMk
    ((continuous_projection N n).comp continuous_snd)
  exact (continuous_of_discreteTopology (f := fun q : ℕ × G n =>
    SignedAdicAction2893.iterate (γ n) q.1 q.2)).comp c

end Reimann.SignedProfiniteLimit2893
