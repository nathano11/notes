import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.GroupTheory.Index
import ReimannNative69.DyadicIntegerPrime69
import Reimann.DyadicGenusField69

/-! The intrinsic maximal extension of a normal infinite base obtained
from all unramified finite Galois 2-quotients of its absolute Galois group.
Finite-place inertia is computed on the absolute algebraic integers. -/
namespace Reimann.DyadicUnramifiedClosure69

open scoped Pointwise

variable {G : Type*} [Group G] (R : Type*) [CommRing R] [MulSemiringAction G R]

/-- The element fixes a nonzero finite prime and acts trivially on every
residue of an algebraic integer. -/
def finiteInertia (t : G) : Prop :=
  ∃ P : Ideal R, P.IsPrime ∧ P ≠ ⊥ ∧ t • P = P ∧ ∀ u : R, t • u-u ∈ P

theorem conjugate_inertia (g t : G) (ht : finiteInertia R t) :
    finiteInertia R (g*t*g⁻¹) := by
  obtain ⟨P,hp,hn,hs,hr⟩ := ht
  refine ⟨g • P,(Ideal.IsPrime.smul_iff g).mpr hp,?_,?_,?_⟩
  · intro eq
    exact hn (by simpa using congrArg (fun Q : Ideal R => g⁻¹ • Q) eq)
  · simp only [mul_smul,inv_smul_smul,hs]
  · intro u
    have h := Ideal.smul_mem_pointwise_smul g _ P (hr (g⁻¹ • u))
    simpa only [smul_sub,smul_inv_smul,mul_smul] using h

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- H is an open normal subgroup of the closed base group A. Its index is
a power of two and it kills every finite-place inertia element in A. -/
structure Admissible (A H : Subgroup G) : Prop where
  contained : H ≤ A
  closed : IsClosed (H : Set G)
  openOver : IsOpen ((H.subgroupOf A : Subgroup A) : Set A)
  normalOver : ∀ g ∈ A, ∀ t ∈ H, g*t*g⁻¹ ∈ H
  index : ∃ e : ℕ, H.relIndex A = 2^e
  kills : ∀ t ∈ A, finiteInertia R t → t ∈ H

theorem conjugate_preimage {A H : Subgroup G} [hA : A.Normal]
    (h : Admissible R A H) (g : G) :
    Admissible R A (H.comap (MulAut.conj g)) := by
  let e := MulAut.conj g
  have mem (v : G) (hv : v∈A) : e v ∈ A := hA.conj_mem v hv g
  have eqA : A.map e.toMonoidHom = A := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact mem w hw
    · intro hv
      exact ⟨e.symm v,hA.conj_mem' v hv g,e.apply_symm_apply v⟩
  have ct : Continuous (fun v : G => e v) :=
    (continuous_const.mul continuous_id).mul continuous_const
  constructor
  · intro v hv
    have he : e v ∈ A := h.contained hv
    simpa [e,MulAut.conj_apply,mul_assoc] using hA.conj_mem' (e v) he g
  · exact h.closed.preimage ct
  · exact h.openOver.preimage ((ct.comp continuous_subtype_val).subtype_mk (fun v => mem v v.2))
  · intro v hv t ht
    change e (v*t*v⁻¹) ∈ H
    rw [map_mul,map_mul,map_inv]
    exact h.normalOver (e v) (mem v hv) (e t) ht
  · obtain ⟨n,hn⟩ := h.index
    refine ⟨n,?_⟩
    change (H.comap e.toMonoidHom).relIndex A = _
    rw [Subgroup.relIndex_comap,eqA,hn]
  · intro t ht hi
    exact h.kills (e t) (mem t ht) (conjugate_inertia R g t hi)

def kernel (A : Subgroup G) : Subgroup G := sInf {H | Admissible R A H}

theorem kernel_normal (A : Subgroup G) [A.Normal] : (kernel R A).Normal := by
  constructor
  intro t ht g
  simp only [kernel,Subgroup.mem_sInf,Set.mem_ofPred_eq] at ht ⊢
  intro H h
  exact ht (H.comap (MulAut.conj g)) (conjugate_preimage R h g)

theorem kernel_closed (A : Subgroup G) : IsClosed (kernel R A : Set G) := by
  have eq : (kernel R A : Set G) = ⋂ H : {H : Subgroup G // Admissible R A H}, (H.val : Set G) := by
    ext t
    simp only [kernel,Subgroup.mem_sInf,Set.mem_ofPred_eq,Set.mem_iInter,SetLike.mem_coe,Subtype.forall]
  rw [eq]
  exact isClosed_iInter (fun H => H.property.closed)

theorem kernel_kills (A : Subgroup G) (g : G) (ha : g∈A) (hi : finiteInertia R g) :
    g ∈ kernel R A := by
  simp only [kernel,Subgroup.mem_sInf,Set.mem_ofPred_eq]
  exact fun _ h => h.kills g ha hi

theorem kernel_le (A H : Subgroup G) (h : Admissible R A H) : kernel R A ≤ H :=
  sInf_le h

theorem base_admissible (A : Subgroup G) (hc : IsClosed (A : Set G)) :
    Admissible R A A where
  contained := le_rfl
  closed := hc
  openOver := by simp
  normalOver _ hg _ ht := A.mul_mem (A.mul_mem hg ht) (A.inv_mem hg)
  index := ⟨0,by simp⟩
  kills _ h _ := h

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsGalois ℚ Ω]

/-- The fixed field of precisely the intersection of the unramified normal
2-power quotient kernels over K. Its arithmetic interpretation uses Ω = ℚbar. -/
noncomputable def maximalField (K : IntermediateField ℚ Ω) : IntermediateField ℚ Ω :=
  IntermediateField.fixedField (kernel (integralClosure ℤ Ω) K.fixingSubgroup)

theorem fixes_exactly (K : IntermediateField ℚ Ω) :
    (maximalField Ω K).fixingSubgroup = kernel (integralClosure ℤ Ω) K.fixingSubgroup :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨_,kernel_closed _ _⟩

theorem contains_base (K : IntermediateField ℚ Ω) : K ≤ maximalField Ω K := by
  apply (IntermediateField.le_fixedField_iff_le_fixingSubgroup _ _).mpr
  exact kernel_le _ _ _ (base_admissible _ _ (InfiniteGalois.fixingSubgroup_isClosed K))

theorem contains_candidate (K : IntermediateField ℚ Ω) (H : Subgroup (Ω ≃ₐ[ℚ] Ω))
    (h : Admissible (integralClosure ℤ Ω) K.fixingSubgroup H) :
    IntermediateField.fixedField H ≤ maximalField Ω K :=
  IntermediateField.fixedField_le (kernel_le _ _ _ h)

/-- Every finite quotient in the defining family is unramified at each
finite place; the same inertia elements vanish in the full inverse limit. -/
theorem inertia_fixes_maximalField (K : IntermediateField ℚ Ω) (g : Ω ≃ₐ[ℚ] Ω)
    (hk : g ∈ K.fixingSubgroup) (hi : finiteInertia (integralClosure ℤ Ω) g) :
    g ∈ (maximalField Ω K).fixingSubgroup :=
  fixes_exactly Ω K ▸ kernel_kills _ K.fixingSubgroup g hk hi

theorem maximal_unramified_normal (K : IntermediateField ℚ Ω) [IsGalois ℚ K] :
    IsGalois ℚ (maximalField Ω K) := by
  let : K.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois K).mpr inferInstance
  let : (kernel (integralClosure ℤ Ω) K.fixingSubgroup).Normal := kernel_normal _ _
  unfold maximalField
  infer_instance

theorem maximal_over_intermediate (K E : IntermediateField ℚ Ω) [IsGalois ℚ K]
    (h : E ≤ maximalField Ω K) : IsGalois E (IntermediateField.extendScalars h) := by
  let : IsGalois ℚ (IntermediateField.extendScalars h) := maximal_unramified_normal Ω K
  exact IsGalois.tower_top_of_isGalois ℚ E _

/-- The arithmetic base k∞ = ℚ(√−69, ζ_j+ζ_j⁻¹ : j≥0). -/
noncomputable def cyclotomicBase (d : Ω) (ζ : ℕ → Ω) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ (insert d (Set.range (fun j => ζ j+(ζ j)⁻¹)))

theorem base_trace_conjugate (d : Ω) (ζ : ℕ → Ω) (j : ℕ)
    (hz : (ζ j)^(2^(j+1) : ℕ) = -1) (σ : Ω →ₐ[ℚ] Ω) :
    σ (ζ j+(ζ j)⁻¹) ∈ cyclotomicBase Ω d ζ := by
  let K := cyclotomicBase Ω d ζ
  have hζ : ζ j ≠ 0 := by
    intro h
    simp [h] at hz
  have hσ : (σ (ζ j))^(2^(j+1) : ℕ) = -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg σ hz
  have h1 : (σ (ζ j))^(2^(j+1+1) : ℕ) = 1 := by
    rw [Nat.pow_succ,pow_mul,hσ]
    simp
  obtain ⟨m,hm⟩ := DyadicGenusField69.powers_exhaust_roots (j+1) (ζ j) (σ (ζ j)) hz h1
  have glob : DyadicCyclotomicSpan69.Subfield (fun v => v ∈ K) := {
    zero := K.zero_mem, one := K.one_mem, add := K.add_mem, neg := K.neg_mem,
    mul := K.mul_mem, inv := K.inv_mem }
  have tr : ζ j+(ζ j)⁻¹ ∈ K := IntermediateField.subset_adjoin _ _
    (Set.mem_insert_of_mem _ (Set.mem_range_self j))
  rw [map_add,map_inv₀,hm]
  exact DyadicGenusField69.traces_of_powers glob _ hζ tr m

theorem cyclotomicBase_galois (d : Ω) (ζ : ℕ → Ω) (hd : d^2 = -69)
    (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1) : IsGalois ℚ (cyclotomicBase Ω d ζ) := by
  have hN : Normal ℚ (cyclotomicBase Ω d ζ) := by
    apply IntermediateField.normal_iff_forall_map_le.mpr
    intro σ
    rw [cyclotomicBase,IntermediateField.adjoin_map,IntermediateField.adjoin_le_iff]
    rintro _ ⟨v,hv,rfl⟩
    rcases hv with rfl | ⟨j,rfl⟩
    · have eq : (σ v)^2 = v^2 := by
        rw [← map_pow,hd,map_neg,map_ofNat]
      have hmem : v ∈ cyclotomicBase Ω v ζ := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
      obtain he | he := sq_eq_sq_iff_eq_or_eq_neg.mp eq
      · rw [he]
        exact hmem
      · rw [he]
        exact (cyclotomicBase Ω v ζ).neg_mem hmem
    · exact base_trace_conjugate Ω d ζ j (hz j) σ
  exact { to_normal := hN }

/-- In the chosen algebraic closure the intrinsic unramified pro-2 field
above k∞ is Galois over ℚ, and over every specified subfield it contains. -/
theorem conductor69_maximal_normal (d : Ω) (ζ : ℕ → Ω) (hd : d^2 = -69)
    (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1)
    (E : IntermediateField ℚ Ω) (hE : E ≤ maximalField Ω (cyclotomicBase Ω d ζ)) :
    IsGalois ℚ (maximalField Ω (cyclotomicBase Ω d ζ)) ∧
      IsGalois E (IntermediateField.extendScalars hE) := by
  let : IsGalois ℚ (cyclotomicBase Ω d ζ) := cyclotomicBase_galois Ω d ζ hd hz
  exact ⟨maximal_unramified_normal Ω _,maximal_over_intermediate Ω _ E hE⟩

/-- The intrinsic field equals the compositum of all admitted finite normal
2-extensions. Membership in the defining intersection loses no fixed field. -/
theorem compositum_of_candidates (K : IntermediateField ℚ Ω) :
    maximalField Ω K =
      ⨆ H : {H : Subgroup (Ω ≃ₐ[ℚ] Ω) //
        Admissible (integralClosure ℤ Ω) K.fixingSubgroup H}, IntermediateField.fixedField H.val := by
  let U := ⨆ H : {H : Subgroup (Ω ≃ₐ[ℚ] Ω) //
    Admissible (integralClosure ℤ Ω) K.fixingSubgroup H}, IntermediateField.fixedField H.val
  apply le_antisymm
  · have hu : U.fixingSubgroup ≤ kernel (integralClosure ℤ Ω) K.fixingSubgroup := by
      intro g hg
      simp only [kernel,Subgroup.mem_sInf,Set.mem_ofPred_eq]
      intro H h
      have inc : IntermediateField.fixedField H ≤ U :=
        le_iSup (fun H : {H : Subgroup (Ω ≃ₐ[ℚ] Ω) // Admissible (integralClosure ℤ Ω)
          K.fixingSubgroup H} => IntermediateField.fixedField H.val) ⟨H,h⟩
      have hm := IntermediateField.fixingSubgroup_le inc hg
      rwa [InfiniteGalois.fixingSubgroup_fixedField (⟨H,h.closed⟩ : ClosedSubgroup (Ω ≃ₐ[ℚ] Ω))] at hm
    exact (IntermediateField.fixedField_le hu).trans_eq (InfiniteGalois.fixedField_fixingSubgroup U)
  · exact iSup_le (fun H => contains_candidate Ω K H.val H.property)

/-- For an element of the base Galois group, failure to fix the intrinsic
field is detected by an actual open normal quotient of 2-power order. -/
theorem detected_in_finite_quotient (K : IntermediateField ℚ Ω) (g : Ω ≃ₐ[ℚ] Ω)
    (hg : g ∉ (maximalField Ω K).fixingSubgroup) :
    ∃ H : Subgroup (Ω ≃ₐ[ℚ] Ω), Admissible (integralClosure ℤ Ω) K.fixingSubgroup H ∧ g ∉ H := by
  classical
  rw [fixes_exactly,kernel,Subgroup.mem_sInf] at hg
  simp only [Set.mem_ofPred_eq,not_forall] at hg
  obtain ⟨H,hH,hn⟩ := hg
  exact ⟨H,hH,hn⟩

end Reimann.DyadicUnramifiedClosure69
