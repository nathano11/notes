import Mathlib.Algebra.Field.Subfield.Basic
import Reimann.DyadicLocalRestriction69

/-! Rational normalized values on a directed union of finite dyadic layers. -/
namespace Reimann.DyadicValueUnion69

open DyadicDecomposition69 DyadicLocalRestriction69 DyadicBottomValue69

variable {L : Type} [Field L]

/-- Restrict a normalized finite or infinite valuation to a subfield. -/
def restrictValue {F K : Type} [Field F] [Field K] (g : F →+* K) (V : DyadicValue K) :
    DyadicValue F where
  val x := V.val (g x)
  zero := by simpa only [map_zero] using V.zero
  two_ne := by
    intro h
    exact V.two_ne (by simpa only [map_ofNat,map_zero] using congrArg g h)
  two := by simpa only [map_ofNat] using V.two
  mul hx hy := by simpa only [map_mul] using V.mul ((map_ne_zero g).mpr hx) ((map_ne_zero g).mpr hy)
  smaller {x y} hx hy less := by
    obtain ⟨hne,he⟩ := V.smaller ((map_ne_zero g).mpr hx) ((map_ne_zero g).mpr hy) less
    exact ⟨fun h => hne (by simpa only [map_add,map_zero] using congrArg g h),by simpa only [map_add] using he⟩

/-- The ambient bottom embedding viewed in a stage containing its image. -/
def stageEmbedding (f : Embedding L) (S : Subfield L) (base : ∀ t, f.app t ∈ S) :
    Embedding S where
  app t := ⟨f.app t,base t⟩
  scalar_int n := Subtype.ext (f.scalar_int n)
  add x y := Subtype.ext (f.add x y)
  mul x y := Subtype.ext (f.mul x y)
  faithful x hx := f.faithful x (congrArg Subtype.val hx)

/-- Agreement on a smaller cyclotomic layer follows from the bottom label. -/
theorem finite_value_compatible (f : Embedding L) {S T : Subfield L} (h : S ≤ T)
    (sbase : ∀ t, f.app t ∈ S) (tbase : ∀ t, f.app t ∈ T)
    (i : Bool) (V : DyadicValue S) (W : DyadicValue T)
    (cV : Centered (stageEmbedding f S sbase) V i) (cW : Centered (stageEmbedding f T tbase) W i)
    (n : ℕ) (z : S) (hz : z^(2^n : ℕ) = -1)
    (gen : ∀ x : S, DyadicCyclotomicSpan69.Generated (DyadicEmbeddedBase69.baseImage (stageEmbedding f S sbase)) z x)
    (x : S) : V.val x = W.val (Subfield.inclusion h x) := by
  let U := restrictValue (Subfield.inclusion h) W
  have cU : Centered (stageEmbedding f S sbase) U i := ⟨cW.nonneg, fun x => by
    have e : ((stageEmbedding f S sbase).app x.val = 0) ↔
        ((stageEmbedding f T tbase).app x.val = 0) := by
      constructor
      · exact fun a => Subtype.ext (congrArg (fun u : S => (u:L)) a)
      · exact fun a => Subtype.ext (congrArg (fun u : T => (u:L)) a)
    exact (cW.center x).trans (or_congr e.symm Iff.rfl)⟩
  exact finite_layer_place_unique _ i V U cV cU n hz (gen x)

/-- Finite-stage data with transitions normalized by the same value of two. -/
structure Stages (L : Type) [Field L] where
  stage : ℕ → Subfield L
  increasing : Monotone stage
  covers : ∀ x, ∃ n, x ∈ stage n
  value : ∀ n, DyadicValue (stage n)
  compatible : ∀ {n m} (h : n ≤ m) (x : stage n),
    (value n).val x = (value m).val (Subfield.inclusion (increasing h) x)

variable (D : Stages L)

noncomputable def unionValue (x : L) : ℚ :=
  (D.value (D.covers x).choose).val ⟨x,(D.covers x).choose_spec⟩

theorem on_stage {n : ℕ} (x : D.stage n) : unionValue D x.val = (D.value n).val x := by
  let k := (D.covers x.val).choose
  let y : D.stage k := ⟨x.val,(D.covers x.val).choose_spec⟩
  change (D.value k).val y = _
  exact (D.compatible (Nat.le_max_left k n) y).trans (D.compatible (Nat.le_max_right k n) x).symm

theorem common_stage (x y : L) : ∃ n, x ∈ D.stage n ∧ y ∈ D.stage n := by
  obtain ⟨k,hk⟩ := D.covers x
  obtain ⟨m,hm⟩ := D.covers y
  exact ⟨max k m,D.increasing (Nat.le_max_left ..) hk,D.increasing (Nat.le_max_right ..) hm⟩

/-- On the infinite union no discrete value group is required. -/
noncomputable def normalized_union : DyadicValue L where
  val := unionValue D
  zero := (on_stage D (0 : D.stage 0)).trans (D.value 0).zero
  two_ne := fun h => (D.value 0).two_ne (Subtype.ext h)
  two := (on_stage D (2 : D.stage 0)).trans (D.value 0).two
  mul {x y} hx hy := by
    obtain ⟨n,s,t⟩ := common_stage D x y
    let X : D.stage n := ⟨x,s⟩
    let Y : D.stage n := ⟨y,t⟩
    change unionValue D (X*Y : D.stage n).val = unionValue D X.val + unionValue D Y.val
    rw [on_stage,on_stage,on_stage]
    exact (D.value n).mul (fun h => hx (congrArg Subtype.val h)) (fun h => hy (congrArg Subtype.val h))
  smaller {x y} hx hy less := by
    obtain ⟨n,s,t⟩ := common_stage D x y
    let X : D.stage n := ⟨x,s⟩
    let Y : D.stage n := ⟨y,t⟩
    change unionValue D X.val < unionValue D Y.val at less
    rw [on_stage,on_stage] at less
    obtain ⟨hne,he⟩ := (D.value n).smaller (fun h => hx (congrArg Subtype.val h : X.val=0))
      (fun h => hy (congrArg Subtype.val h : Y.val=0)) less
    refine ⟨fun h => hne (Subtype.ext h),?_⟩
    exact (on_stage D (X+Y)).trans (he.trans (on_stage D X).symm)

/-- One centered stage certifies the center of the glued valuation. -/
theorem union_centered (f : Embedding L) (i : Bool) (n : ℕ)
    (base : ∀ t, f.app t ∈ D.stage n)
    (center : Centered (stageEmbedding f _ base) (D.value n) i) :
    Centered f (normalized_union D) i where
  nonneg x := by
    change 0 ≤ unionValue D ((stageEmbedding f _ base).app x.val).val
    rw [on_stage]
    exact center.nonneg x
  center x := by
    let y := (stageEmbedding f _ base).app x.val
    change _ ↔ y.val=0 ∨ 0 < unionValue D y.val
    rw [on_stage]
    exact (center.center x).trans (or_congr Subtype.ext_iff Iff.rfl)

/-- Construct compatibility on all stages from their common bottom label and
root-generation, so no normalization transition is a separate hypothesis. -/
def of_centered_cyclotomic (f : Embedding L) (i : Bool) (S : ℕ → Subfield L)
    (inc : Monotone S) (cover : ∀ x, ∃ n, x ∈ S n) (base : ∀ n t, f.app t ∈ S n)
    (V : ∀ n, DyadicValue (S n)) (center : ∀ n, Centered (stageEmbedding f _ (base n)) (V n) i)
    (level : ℕ → ℕ) (z : ∀ n, S n) (prim : ∀ n, (z n)^(2^(level n) : ℕ) = -1)
    (gen : ∀ n x, DyadicCyclotomicSpan69.Generated
      (DyadicEmbeddedBase69.baseImage (stageEmbedding f _ (base n))) (z n) x) : Stages L where
  stage := S
  increasing := inc
  covers := cover
  value := V
  compatible {n m} h := finite_value_compatible f (inc h) (base n) (base m) i
    (V n) (V m) (center n) (center m) (level n) (z n) (prim n) (gen n)


end Reimann.DyadicValueUnion69

