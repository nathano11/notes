import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Reimann277.NumberFieldPrime

namespace Reimann.TameFinitePlaces277

open NumberField IsDedekindDomain
open scoped NumberField

local instance prime277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- The ordinary finite places of K above 277. On an integral rational prime,
the open-unit-ball condition is equivalent to membership in the underlying prime ideal. -/
def Above (K : Type*) [Field K] [NumberField K] := { w : FinitePlace K // w 277 < 1 }

variable {K : Type*} [Field K] [NumberField K]

theorem above_iff_ideal (w : FinitePlace K) :
    w 277 < 1 ↔ (277 : 𝓞 K) ∈ w.maximalIdeal.asIdeal := by
  simpa only [FinitePlace.norm_embedding_eq, map_ofNat] using
    (FinitePlace.norm_lt_one_iff_mem K w.maximalIdeal (277 : 𝓞 K))

theorem integer_bound (w : FinitePlace K) (z : ℤ) : w (z : K) ≤ 1 := by
  simpa only [FinitePlace.norm_embedding_eq, map_intCast] using
    (FinitePlace.norm_le_one K w.maximalIdeal (z : 𝓞 K))

theorem integer_radii (v : Above K) (n : ℕ) (z : ℤ) :
    v.val (z : K) ≤ v.val (((277 : ℤ)^n : ℤ) : K) ↔ (277 : ℤ)^n ∣ z :=
  TameFiniteRadii277.integer_radii v.val.val v.val.add_le (integer_bound v.val) v.property n z

noncomputable def embeddingPlace (f : K →ₐ[ℚ] ℚ_[277]) : Above K :=
  ⟨FinitePlace.mk (embeddingPrime f), (above_iff_ideal _).mpr (by
      rw [FinitePlace.maximalIdeal_mk]
      exact prime_mem_embeddingIdeal f)⟩

theorem embeddingPlace_center (f : K →ₐ[ℚ] ℚ_[277]) (x : 𝓞 K) :
    (embeddingPlace f).val (x : K) < 1 ↔ ‖f (x : K)‖ < 1 :=
  FinitePlace.norm_lt_one_iff_mem K (embeddingPrime f) x

theorem embeddingPrime_absNorm (f : K →ₐ[ℚ] ℚ_[277]) :
    (embeddingPrime f).asIdeal.absNorm = 277 := by
  letI : Infinite (𝓞 K) := Infinite.of_injective (fun n : ℕ => (n : 𝓞 K)) Nat.cast_injective
  rw [Ideal.absNorm_eq_natCard]
  exact residue_cardinality f

/-- The norm group of the place is made explicit using the residue field just computed. -/
theorem prime_value (f : K →ₐ[ℚ] ℚ_[277]) {x : K} (hx : x ≠ 0) :
    ∃ k : ℤ, (embeddingPlace f).val x = (277 : ℝ)^k := by
  let P := embeddingPrime f
  refine ⟨WithZero.log (P.valuation K x),?_⟩
  change ‖FinitePlace.embedding P x‖ = _
  rw [FinitePlace.norm_embedding,NumberField.HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((P.valuation K).ne_zero_iff.mpr hx),
    NNReal.coe_zpow,NNReal.coe_natCast]
  rw [show P.asIdeal.absNorm = 277 from embeddingPrime_absNorm f]
  norm_num

theorem exists_prime_unit_step (f : K →ₐ[ℚ] ℚ_[277]) :
    ∃ x : K, (embeddingPlace f).val x = (277 : ℝ)⁻¹ := by
  let P := embeddingPrime f
  obtain ⟨x,hx⟩ := P.valuation_exists_uniformizer K
  refine ⟨x,?_⟩
  change ‖FinitePlace.embedding P x‖ = _
  rw [FinitePlace.norm_embedding,NumberField.HeightOneSpectrum.adicAbv_def,hx,
    WithZeroMulInt.toNNReal_neg_apply _ (by simp),WithZero.log_exp,
    NNReal.coe_zpow,NNReal.coe_natCast]
  rw [show P.asIdeal.absNorm = 277 from embeddingPrime_absNorm f]
  norm_num

open TameBiquadraticField277 TameRationalField277 TamePlaceRestriction277
open TameArithmetic277 TameOrderFaithful277 TamePadicEmbeddings277

/-- The valuation comparison of an actual height-one place over 277 on the global field. -/
def comparison (v : Above Biquadratic) : PlaceOrder where
  le x y := v.val ⟨x⟩ ≤ v.val ⟨y⟩
  refl _ := le_rfl
  trans := le_trans
  total _ _ := le_total _ _
  mul z h := by
    change v.val (_ * Biquadratic.mk z) ≤ v.val (_ * Biquadratic.mk z)
    rw [map_mul,map_mul]
    exact mul_le_mul_of_nonneg_right h (apply_nonneg _ _)
  cancel {x y z} hz h := by
    change v.val (Biquadratic.mk x * Biquadratic.mk z) ≤
      v.val (Biquadratic.mk y * Biquadratic.mk z) at h
    rw [map_mul,map_mul] at h
    have hn : Biquadratic.mk z ≠ 0 := fun he => hz (congrArg Biquadratic.coord he)
    exact le_of_mul_le_mul_right h (FinitePlace.pos_iff.mpr hn)
  add {x y z} hx hy := (v.val.add_le (Biquadratic.mk x) (Biquadratic.mk y)).trans (max_le hx hy)
  integers n a := by
    rw [scalar_int,scalar_int]
    exact integer_radii v n a

theorem less_one_iff_mem (w : FinitePlace K) (x : 𝓞 K) :
    w (x : K) < 1 ↔ x ∈ w.maximalIdeal.asIdeal := by
  simpa only [FinitePlace.norm_embedding_eq] using
    (FinitePlace.norm_lt_one_iff_mem K w.maximalIdeal x)

theorem comparison_lt_one (v : Above Biquadratic) (x : Biquadratic) :
    (¬ (comparison v).le (scalar 1) x.coord) ↔ v.val x < 1 := by
  change (¬ v.val 1 ≤ v.val x) ↔ _
  rw [map_one,not_le]

theorem comparison_injective : Function.Injective comparison := by
  intro v w h
  apply Subtype.ext
  apply FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
  ext x
  rw [← less_one_iff_mem,← less_one_iff_mem,← comparison_lt_one v,← comparison_lt_one w,h]

theorem comparison_embeddingPlace (s : Bool × Bool) :
    comparison (embeddingPlace (embedding s)) = TamePadicPlaces277.order s := by
  apply place_order_ext
  funext a
  apply propext
  let x : 𝓞 Biquadratic := ⟨Biquadratic.mk (rationalize a), integral_on_order a⟩
  have hc := (comparison_lt_one (embeddingPlace (embedding s)) (x : Biquadratic)).trans
    (embeddingPlace_center (embedding s) x)
  change (¬ (comparison (embeddingPlace (embedding s))).le (scalar 1) (x : Biquadratic).coord) ↔
    ¬ ‖embedding s 1‖ ≤ ‖embedding s (x : Biquadratic)‖
  simpa only [map_one,norm_one,not_le] using hc

/-- Four signed prime ideals, as actual finite places of the number field over 277.
The inverse reads the two signs from the given finite place's valuation comparison. -/
noncomputable def four_finite_places : (Bool × Bool) ≃ Above Biquadratic where
  toFun s := embeddingPlace (embedding s)
  invFun v := signs (comparison v)
  left_inv s := by rw [comparison_embeddingPlace,TamePadicPlaces277.signs_order]
  right_inv v := comparison_injective <| (comparison_embeddingPlace _).trans
    (TamePadicPlaces277.equiv.apply_symm_apply (comparison v))

theorem signed_prime_norm_test (s : Bool × Bool) (x : 𝓞 Biquadratic) :
    x ∈ (four_finite_places s).val.maximalIdeal.asIdeal ↔ ‖embedding s (x : Biquadratic)‖ < 1 :=
  (less_one_iff_mem (four_finite_places s).val x).symm.trans (embeddingPlace_center _ x)

theorem finite_comparison (s : Bool × Bool) (x y : Biquadratic) :
    (four_finite_places s).val x ≤ (four_finite_places s).val y ↔
      ‖embedding s x‖ ≤ ‖embedding s y‖ :=
  (congrArg (fun w : PlaceOrder => w.le x.coord y.coord) (comparison_embeddingPlace s)).to_iff

theorem norm_277 (s : Bool × Bool) : (four_finite_places s).val 277 = (277 : ℝ)⁻¹ :=
  TameFiniteAbsolute277.normalize_prime (four_finite_places s).val.val (embedding s).toRingHom
    (finite_comparison s) (prime_value (embedding s) (x := (277:Biquadratic)) (by norm_num))
    (exists_prime_unit_step (embedding s))

theorem signed_absolute_value (s : Bool × Bool) (x : Biquadratic) :
    (four_finite_places s).val x = ‖embedding s x‖ :=
  TameFiniteAbsolute277.normalized_absolute_value (four_finite_places s).val.val
    (embedding s).toRingHom (finite_comparison s) (norm_277 s) x

theorem finite_absolute_value (v : Above Biquadratic) (x : Biquadratic) :
    v.val x = ‖embedding (four_finite_places.symm v) x‖ := by
  obtain ⟨s,rfl⟩ := four_finite_places.surjective v
  simpa only [Equiv.symm_apply_apply] using signed_absolute_value s x

open UniformSpace

/-- The canonical completion at the actual number-field place, including
the specified embedding of every global element and the normalized isometry. -/
theorem finite_completion (v : Above Biquadratic) :
    ∃ e : v.val.maximalIdeal.adicCompletion Biquadratic ≃+* ℚ_[277],
      Isometry e ∧ ∀ x : Biquadratic,
        e (FinitePlace.embedding v.val.maximalIdeal x) = embedding (four_finite_places.symm v) x := by
  let s := four_finite_places.symm v
  let f := (embedding s).toRingHom
  letI := NormedField.induced Biquadratic ℚ_[277] f (embedding s).injective
  let j : Biquadratic →+* v.val.maximalIdeal.adicCompletion Biquadratic :=
    FinitePlace.embedding v.val.maximalIdeal
  have hjnorm (x : Biquadratic) : ‖j x‖ = ‖x‖ := by
    change ‖FinitePlace.embedding v.val.maximalIdeal x‖ = ‖embedding s x‖
    rw [FinitePlace.norm_embedding_eq]
    exact finite_absolute_value v x
  have hji : Isometry j := Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm,dist_eq_norm,← map_sub,hjnorm]
  have hjd : DenseRange j := v.val.maximalIdeal.denseRange_algebraMap Biquadratic
  obtain ⟨ej,hj,he⟩ := TameMetricCompletion277.dense_completion j hji hjd
  have hfi : Isometry f := by intro x y; rfl
  obtain ⟨ef,hf,hfe⟩ := TameMetricCompletion277.dense_completion f hfi (embedding_dense (embedding s))
  refine ⟨ej.symm.trans ef,?_,?_⟩
  · apply Isometry.of_dist_eq
    intro a b
    change dist (ef (ej.symm a)) (ef (ej.symm b)) = _
    rw [hf.dist_eq, ← hj.dist_eq (ej.symm a) (ej.symm b),ej.apply_symm_apply,ej.apply_symm_apply]
  · intro x
    change ef (ej.symm (j x)) = _
    rw [← he,ej.symm_apply_apply,hfe]

/-- The dense rational subfield determines every continuous endomorphism
of the standard p-adic field. -/
theorem padic_endomorphism (f : ℚ_[277] →+* ℚ_[277]) (hf : Continuous f) :
    f = RingHom.id _ := by
  apply RingHom.ext
  have h := (Padic.denseRange_ratCast 277).equalizer hf continuous_id (show
      (f : ℚ_[277] → ℚ_[277]) ∘ ((↑) : ℚ → ℚ_[277]) = id ∘ ((↑) : ℚ → ℚ_[277]) from
      funext (fun q => map_ratCast f q))
  exact congrFun h

/-- Any continuous p-adic scalar inclusion into the canonical local field is
the inverse of the normalized completion isomorphism. -/
theorem finite_completion_scalars (v : Above Biquadratic) :
    ∃ e : v.val.maximalIdeal.adicCompletion Biquadratic ≃+* ℚ_[277],
      Isometry e ∧ (∀ x : Biquadratic,
        e (FinitePlace.embedding v.val.maximalIdeal x) = embedding (four_finite_places.symm v) x) ∧
      ∀ j : ℚ_[277] →+* v.val.maximalIdeal.adicCompletion Biquadratic,
        Continuous j → ∀ q, e (j q) = q := by
  obtain ⟨e,hi,he⟩ := finite_completion v
  refine ⟨e,hi,he,?_⟩
  intro j hj q
  exact DFunLike.congr_fun (padic_endomorphism (e.toRingHom.comp j) (hi.continuous.comp hj)) q

theorem unique_scalar_inclusion (v : Above Biquadratic) :
    ∃! j : ℚ_[277] →+* v.val.maximalIdeal.adicCompletion Biquadratic, Continuous j := by
  obtain ⟨e,hi,_,he⟩ := finite_completion_scalars v
  have hs : Isometry e.symm := Isometry.of_dist_eq (fun x y => by
    rw [← hi.dist_eq (e.symm x) (e.symm y),e.apply_symm_apply,e.apply_symm_apply])
  refine ⟨e.symm.toRingHom,hs.continuous,?_⟩
  intro j hj
  apply RingHom.ext
  intro q
  exact e.injective ((he j hj q).trans (e.apply_symm_apply q).symm)

/-- With any continuous p-adic scalar action, the canonical local comparison
is an isometric algebra equivalence over the standard p-adic field. -/
theorem finite_completion_over_padic (v : Above Biquadratic)
    [Algebra ℚ_[277] (v.val.maximalIdeal.adicCompletion Biquadratic)]
    [ContinuousSMul ℚ_[277] (v.val.maximalIdeal.adicCompletion Biquadratic)] :
    ∃ e : v.val.maximalIdeal.adicCompletion Biquadratic ≃ₐ[ℚ_[277]] ℚ_[277],
      Isometry e ∧ ∀ x : Biquadratic,
        e (FinitePlace.embedding v.val.maximalIdeal x) = embedding (four_finite_places.symm v) x := by
  obtain ⟨e,hi,he,hj⟩ := finite_completion_scalars v
  exact ⟨{ e with commutes' := hj (algebraMap _ _) (continuous_algebraMap _ _) },hi,he⟩

end Reimann.TameFinitePlaces277

namespace Reimann.TameArithmetic277

open NumberField TameBiquadraticField277 TamePadicEmbeddings277 TameFinitePlaces277
open scoped NumberField

local instance endpointPrime : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- The four genuine finite places of the rational biquadratic field over 277
and the isometric identification of each canonical adic completion with ℚ_[277].
The isomorphism agrees with its specified signed embedding on every field element. -/
theorem four_completions :
    ∃ index : (Bool × Bool) ≃ Above Biquadratic, ∀ v : Above Biquadratic,
      ∃ e : v.val.maximalIdeal.adicCompletion Biquadratic ≃+* ℚ_[277],
        Isometry e ∧ ∀ x : Biquadratic,
          e (FinitePlace.embedding v.val.maximalIdeal x) = embedding (index.symm v) x :=
  ⟨four_finite_places,finite_completion⟩

end Reimann.TameArithmetic277
