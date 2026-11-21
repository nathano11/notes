import ReimannNative69.DyadicUnramifiedClosure69
import ReimannNative69.DyadicCyclotomicModel69
import ReimannNative69.DyadicGenusInertia69
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-! Below the maximal unramified pro-2 field, the genus extension is
detected by the two quadratic signs of the bottom field. -/
namespace Reimann.DyadicGenusContainment69

open DyadicNormalTower69 DyadicUnramifiedClosure69 DyadicCyclotomicModel69

variable (Ω : Type) [Field Ω] [CharZero Ω]

theorem radical_sign (z : Ω) (m : ℤ) (hm : z^2=(m:Ω)) (g : Gal(Ω/ℚ)) :
    g z=z ∨ g z= -z := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow,hm,map_intCast]

abbrev Signs := Multiplicative (ZMod 2)

noncomputable def signCharacter (z : Ω) (nz : z≠0) (sign : ∀ g : Gal(Ω/ℚ), g z=z ∨ g z= -z) :
    Gal(Ω/ℚ) →* Signs := by
  classical
  have hn : -z≠z := by
    intro h
    apply nz
    linear_combination (-1/2)*h
  let minus := Multiplicative.ofAdd (1 : ZMod 2)
  let signOf (g : Gal(Ω/ℚ)) : Signs := if g z=z then 1 else minus
  have mm : minus*minus=1 := by decide
  exact {
    toFun := signOf
    map_one' := by simp [signOf]
    map_mul' := by
      intro g h
      rcases sign g with eg|eg <;> rcases sign h with eh|eh <;>
        simp [signOf,AlgEquiv.mul_apply,eg,eh,map_neg,hn,mm] }

theorem signCharacter_one (z : Ω) (nz : z≠0) (sign : ∀ g : Gal(Ω/ℚ), g z=z ∨ g z= -z)
    (g : Gal(Ω/ℚ)) : signCharacter Ω z nz sign g=1 ↔ g z=z := by
  classical
  change (if g z=z then (1:Signs) else Multiplicative.ofAdd (1:ZMod 2))=1 ↔ _
  split <;> rename_i h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

variable (x y : Ω) (ζ : ℕ → Ω) (a : ℕ)
local notation "K" => cyclotomicBase Ω (ζ 0*x*y) ζ
local notation "F" => IntermediateField.restrictScalars ℚ (fullCyclotomic Ω x y ζ a)

theorem base_in_genus : K ≤ F := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z (rfl|⟨n,rfl⟩)
  · exact (F).mul_mem ((F).mul_mem (rootAt Ω x y ζ a 0).property (lowerX Ω x y ζ a).property)
      (lowerY Ω x y ζ a).property
  · exact (F).add_mem (rootAt Ω x y ζ a n).property ((F).inv_mem (rootAt Ω x y ζ a n).property)

theorem fixes_genus (g : Gal(Ω/ℚ)) :
    g∈(F).fixingSubgroup ↔ g x=x ∧ g y=y ∧ ∀ n, g (ζ n)=ζ n := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact ⟨h _ (lowerX Ω x y ζ a).property,h _ (lowerY Ω x y ζ a).property,
      fun n => h _ (rootAt Ω x y ζ a n).property⟩
  · rintro ⟨hx,hy,hz⟩ b hb
    exact generated_in_subfield Ω x y ζ a (FixedBy.subfield Ω g) hx hy hz hb

theorem fixes_genus_over_base (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1) (g : Gal(Ω/ℚ)) (hk : g∈(K).fixingSubgroup) :
    g∈(F).fixingSubgroup ↔ g x=x ∧ g y=y := by
  rw [fixes_genus]
  refine ⟨fun h => ⟨h.1,h.2.1⟩,?_⟩
  rintro ⟨ex,ey⟩
  have nx : x≠0 := by rintro rfl; norm_num at hx
  have ny : y≠0 := by rintro rfl; norm_num at hy
  have base := (IntermediateField.mem_fixingSubgroup_iff K g).mp hk
  have d := base _ (IntermediateField.subset_adjoin _ _ (Set.mem_insert (ζ 0*x*y) _))
  rw [map_mul,map_mul,ex,ey] at d
  have ei : g (ζ 0)=ζ 0 := mul_right_cancel₀ nx (mul_right_cancel₀ ny d)
  have hi : ζ 0*ζ 0= -1 := by
    have h : ζ 0^2= -1 := hz 0
    simpa only [pow_two] using h
  let U := FixedBy.subfield Ω g
  have alg : DyadicCyclotomicSpan69.Subfield (fun b => b∈U) :=
    ⟨U.zero_mem,U.one_mem,U.add_mem,U.neg_mem,U.mul_mem,U.inv_mem⟩
  refine ⟨ex,ey,fun n => ?_⟩
  exact (DyadicGenusField69.finite_generators_iff alg (ζ 0) (ζ n) n hi (hz n)).mpr
    ⟨base _ (IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_range_self n))),ei⟩

noncomputable def pairedSigns (hx : x^2= -3) (hy : y^2= -23) :
    Gal(Ω/ℚ) →* Signs × Signs :=
  (signCharacter Ω x (by rintro rfl; norm_num at hx) (radical_sign Ω x (-3) (by simpa using hx))).prod
    (signCharacter Ω y (by rintro rfl; norm_num at hy) (radical_sign Ω y (-23) (by simpa using hy)))

theorem pairedSigns_kernel (hx : x^2= -3) (hy : y^2= -23) (g : Gal(Ω/ℚ)) :
    g∈(pairedSigns Ω x y hx hy).ker ↔ g x=x ∧ g y=y := by
  change (signCharacter Ω x _ _ g,signCharacter Ω y _ _ g)=(1,1) ↔ _
  rw [Prod.mk.injEq,signCharacter_one,signCharacter_one]

theorem fixing_as_kernel (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1) :
    (F).fixingSubgroup=(pairedSigns Ω x y hx hy).ker ⊓ (K).fixingSubgroup := by
  ext g
  constructor
  · intro hg
    have hk := IntermediateField.fixingSubgroup_le (base_in_genus Ω x y ζ a) hg
    exact ⟨(pairedSigns_kernel Ω x y hx hy g).mpr ((fixes_genus_over_base Ω x y ζ a hx hy hz g hk).mp hg),hk⟩
  · rintro ⟨hs,hk⟩
    exact (fixes_genus_over_base Ω x y ζ a hx hy hz g hk).mpr ((pairedSigns_kernel Ω x y hx hy g).mp hs)

theorem genus_relative_index (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1) :
    ∃ e ≤ 2, (F).fixingSubgroup.relIndex (K).fixingSubgroup=2^e := by
  rw [fixing_as_kernel Ω x y ζ a hx hy hz,Subgroup.inf_relIndex_right,Subgroup.relIndex_ker]
  have h := ((K).fixingSubgroup.map (pairedSigns Ω x y hx hy)).card_subgroup_dvd_card
  have four : Nat.card (Signs×Signs)=2^2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [four] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).mp h

theorem genus_candidate_of_inertia [IsGalois ℚ Ω] (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1)
    (inertia : ∀ g : Gal(Ω/ℚ), g∈(K).fixingSubgroup → finiteInertia (integralClosure ℤ Ω) g →
      g x=x ∧ g y=y) :
    Admissible (integralClosure ℤ Ω) (K).fixingSubgroup (F).fixingSubgroup := by
  let A := (K).fixingSubgroup
  let H := (F).fixingSubgroup
  let χ := pairedSigns Ω x y hx hy
  obtain ⟨e,_,he⟩ := genus_relative_index Ω x y ζ a hx hy hz
  have closed : IsClosed (H : Set Gal(Ω/ℚ)) := InfiniteGalois.fixingSubgroup_isClosed F
  let : (H.subgroupOf A).FiniteIndex := ⟨show H.relIndex A≠0 from he ▸ pow_ne_zero _ (by decide)⟩
  refine ⟨IntermediateField.fixingSubgroup_le (base_in_genus Ω x y ζ a),closed,
    (H.subgroupOf A).isOpen_of_isClosed_of_finiteIndex (closed.preimage continuous_subtype_val),
    ?_,⟨e,he⟩,?_⟩
  · intro g hg t ht
    rw [fixing_as_kernel Ω x y ζ a hx hy hz] at ht ⊢
    exact ⟨(inferInstance : χ.ker.Normal).conj_mem t ht.1 g,A.mul_mem (A.mul_mem hg ht.2) (A.inv_mem hg)⟩
  · intro g hg hi
    exact (fixes_genus_over_base Ω x y ζ a hx hy hz g hg).mpr (inertia g hg hi)

theorem le_maximal_of_inertia [IsGalois ℚ Ω] (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1)
    (inertia : ∀ g : Gal(Ω/ℚ), g∈(K).fixingSubgroup → finiteInertia (integralClosure ℤ Ω) g →
      g x=x ∧ g y=y) :
    F ≤ maximalField Ω K :=
  (InfiniteGalois.fixedField_fixingSubgroup F).symm.le.trans
    (contains_candidate Ω K (F).fixingSubgroup (genus_candidate_of_inertia Ω x y ζ a hx hy hz inertia))

/-- Uniformly at every real level, the whole genus-cyclotomic extension is
contained in the intrinsic maximal unramified pro-2 field over k∞. -/
theorem full_cyclotomic_le_maximal [IsGalois ℚ Ω] (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1) :
    F ≤ maximalField Ω K := by
  apply le_maximal_of_inertia Ω x y ζ a hx hy hz
  intro g hk hi
  have h := DyadicGenusInertia69.inertia_fixes_marked_genus Ω x y ζ hx hy hz g hk hi
  exact ⟨h.1,h.2.1⟩

end Reimann.DyadicGenusContainment69
