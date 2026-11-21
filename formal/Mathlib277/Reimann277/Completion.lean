import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion

namespace Reimann.TameMetricCompletion277

open UniformSpace

local instance prime277 : Fact (Nat.Prime 277) := ⟨by decide +kernel⟩

variable {K : Type*} [NormedField K]

/-- For a field embedding, checking the normalized absolute value at each element
suffices to check the full metric on pairs of elements. -/
theorem isometry_of_norm (f : K →+* ℚ_[277]) (hn : ∀ x : K, ‖f x‖ = ‖x‖) :
    Isometry f := Isometry.of_dist_eq fun x y => by
  rw [dist_eq_norm, dist_eq_norm, ← f.map_sub, hn]

/-- Every subfield of the standard 277-adic field contains its dense rational subfield. -/
theorem dense_of_rationals (f : K →+* ℚ_[277]) : DenseRange f := by
  apply DenseRange.of_comp (g := ((↑) : ℚ → K))
  have h : (f : K → ℚ_[277]) ∘ ((↑) : ℚ → K) = ((↑) : ℚ → ℚ_[277]) :=
    funext (fun r => map_ratCast f r)
  rw [h]
  exact Padic.denseRange_ratCast 277

/-- The extension of the given field embedding, as a morphism on its metric completion. -/
noncomputable def extend (f : K →+* ℚ_[277]) (hf : Isometry f) :
    Completion K →+* ℚ_[277] :=
  Completion.extensionHom f hf.continuous

theorem extend_coe (f : K →+* ℚ_[277]) (hf : Isometry f) (x : K) :
    extend f hf (x : Completion K) = f x :=
  Completion.extensionHom_coe f hf.continuous x

theorem extend_isometry (f : K →+* ℚ_[277]) (hf : Isometry f) :
    Isometry (extend f hf) :=
  hf.completion_extension

theorem extend_closed_range (f : K →+* ℚ_[277]) (hf : Isometry f) :
    IsClosed (Set.range (extend f hf)) :=
  (extend_isometry f hf).isClosedEmbedding.isClosed_range

theorem extend_dense (f : K →+* ℚ_[277]) (hf : Isometry f) :
    DenseRange (extend f hf) := by
  apply DenseRange.of_comp (g := ((↑) : K → Completion K))
  have h : ((extend f hf : Completion K → ℚ_[277]) ∘ ((↑) : K → Completion K)) =
      (f : K → ℚ_[277]) := funext (extend_coe f hf)
  rw [h]
  exact dense_of_rationals f

theorem extend_surjective (f : K →+* ℚ_[277]) (hf : Isometry f) :
    Function.Surjective (extend f hf) := by
  apply Set.range_eq_univ.mp
  exact (extend_closed_range f hf).closure_eq.symm.trans (extend_dense f hf).closure_range

noncomputable def completionEquiv (f : K →+* ℚ_[277]) (hf : Isometry f) :
    Completion K ≃+* ℚ_[277] :=
  RingEquiv.ofBijective (extend f hf) ⟨(extend_isometry f hf).injective, extend_surjective f hf⟩

theorem completionEquiv_dist (f : K →+* ℚ_[277]) (hf : Isometry f) (x y : Completion K) :
    dist (completionEquiv f hf x) (completionEquiv f hf y) = dist x y :=
  (extend_isometry f hf).dist_eq x y

theorem inverse_dist (f : K →+* ℚ_[277]) (hf : Isometry f) (x y : ℚ_[277]) :
    dist ((completionEquiv f hf).symm x) ((completionEquiv f hf).symm y) = dist x y := by
  rw [← completionEquiv_dist f hf, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- To realize a place above 277 it suffices to identify its metric with the norm pulled
back by an actual embedding. Density, completion surjectivity and both isometries follow. -/
theorem completion_of_padic_embedding (f : K →+* ℚ_[277]) (hf : Isometry f) :
    ∃ e : Completion K ≃+* ℚ_[277],
      (∀ x : K, e (x : Completion K) = f x) ∧
      (∀ x y, dist (e x) (e y) = dist x y) ∧
      (∀ x y, dist (e.symm x) (e.symm y) = dist x y) :=
  ⟨completionEquiv f hf, extend_coe f hf, completionEquiv_dist f hf, inverse_dist f hf⟩

/-- In a proposed completion, an isometric copy of ℚ_[277] that contains the dense
global image exhausts the whole field. -/
theorem surjective_of_contains_dense {L : Type*} [NormedField L] (j : ℚ_[277] →+* L)
    (hj : Isometry j) (f : K →+* L) (hf : DenseRange f)
    (covers : ∀ x : K, ∃ a : ℚ_[277], j a = f x) :
    Function.Surjective j := by
  have sub : Set.range f ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact covers x
  have hd : DenseRange j := Dense.mono sub hf
  apply Set.range_eq_univ.mp
  exact hj.isClosedEmbedding.isClosed_range.closure_eq.symm.trans hd.closure_range

/-- Two realizations of a dense valued subfield agree on its uniform completion. -/
theorem dense_completion {A B : Type*} [NormedField A] [NormedField B] [CompleteSpace B]
    (f : A →+* B) (hi : Isometry f) (hd : DenseRange f) :
    ∃ e : Completion A ≃+* B, Isometry e ∧ ∀ x : A, e (x : Completion A) = f x := by
  let h := Completion.extensionHom f hi.continuous
  have hc (x : A) : h (x : Completion A) = f x := Completion.extensionHom_coe _ _ _
  have hh : Isometry h := hi.completion_extension
  have dense : DenseRange h := by
    apply DenseRange.of_comp (g := ((↑) : A → Completion A))
    have eq : (h : Completion A → B) ∘ ((↑) : A → Completion A) = f := funext hc
    rw [eq]
    exact hd
  have onto : Function.Surjective h := Set.range_eq_univ.mp
    (hh.isClosedEmbedding.isClosed_range.closure_eq.symm.trans dense.closure_range)
  exact ⟨RingEquiv.ofBijective h ⟨hh.injective,onto⟩, hh,hc⟩

end Reimann.TameMetricCompletion277
