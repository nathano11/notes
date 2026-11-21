import ReimannNative69.DyadicCyclotomicModel69
import ReimannNative69.DyadicValueUnion69
import Mathlib.NumberTheory.NumberField.Basic

/-! The core field-expression model for the finite layers
Eₐ(ζ_{a+n}) at and above the chosen real base. -/
namespace Reimann.DyadicFiniteModel69

open DyadicNormalTower69
open DyadicCyclotomicSpan69 (Generated)
open DyadicEmbeddedBase69 (baseImage)

variable (Ω : Type) [Field Ω] [CharZero Ω] (x y : Ω) (ζ : ℕ → Ω) (a n : ℕ)

noncomputable def stage : IntermediateField (realLayer Ω x y (ζ a)) Ω :=
  IntermediateField.adjoin _ {ζ (a+n)}

theorem stage_roots : x ∈ stage Ω x y ζ a n ∧ y ∈ stage Ω x y ζ a n := by
  have into {u : Ω} (h : u ∈ realLayer Ω x y (ζ a)) : u ∈ stage Ω x y ζ a n :=
    (stage Ω x y ζ a n).algebraMap_mem (⟨u,h⟩ : realLayer Ω x y (ζ a))
  exact ⟨into (IntermediateField.subset_adjoin _ _ (by simp)),
    into (IntermediateField.subset_adjoin _ _ (by simp))⟩

def stageRoot : stage Ω x y ζ a n :=
  ⟨ζ (a+n),IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩

noncomputable def stageEmbedding (hx : x^2 = -3) (hy : y^2 = -23) :
    DyadicBottomValue69.Embedding (stage Ω x y ζ a n) :=
  DyadicNativeEmbedding69.root_embedding
    ⟨x,(stage_roots Ω x y ζ a n).1⟩ ⟨y,(stage_roots Ω x y ζ a n).2⟩
    (Subtype.ext hx) (Subtype.ext hy)

theorem earlier_root (hs : ∀ j, (ζ (j+1))^2 = ζ j) :
    (ζ (a+n))^(2^n : ℕ) = ζ a := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.pow_succ,Nat.mul_comm,pow_mul,show a+(n+1) = (a+n)+1 from rfl,hs,ih]

/-- Every ambient subfield containing the two square roots and ζ_{a+n}
contains the whole finite layer, because it also contains the real trace at a. -/
theorem stage_in_subfield (hs : ∀ j, (ζ (j+1))^2 = ζ j) (U : _root_.Subfield Ω)
    (hx : x∈U) (hy : y∈U) (hz : ζ (a+n)∈U) :
    ∀ b ∈ stage Ω x y ζ a n, b∈U := by
  have hza : ζ a∈U := earlier_root Ω ζ a n hs ▸ pow_mem hz (2^n)
  let Q := U.toIntermediateField (K:=ℚ) (fun r => SubfieldClass.ratCast_mem U r)
  have hK : realLayer Ω x y (ζ a) ≤ Q :=
    IntermediateField.adjoin_le_iff.mpr (by
      intro v hv
      rcases hv with rfl | rfl | hv
      · exact hx
      · exact hy
      · have e : v = ζ a + (ζ a)⁻¹ := hv
        exact e ▸ U.add_mem hza (U.inv_mem hza))
  let V := U.toIntermediateField (K:=realLayer Ω x y (ζ a)) (fun k => hK k.2)
  have hS : stage Ω x y ζ a n ≤ V :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hz)
  exact fun _ hb => hS hb

/-- In Eₐ(ζ_{a+n}) every element is a field expression in the actual bottom
biquadratic coordinates and the single root ζ_{a+n}. -/
theorem stage_generation (hx : x^2 = -3) (hy : y^2 = -23)
    (hs : ∀ j, (ζ (j+1))^2 = ζ j) (b : stage Ω x y ζ a n) :
    Generated (baseImage (stageEmbedding Ω x y ζ a n hx hy)) (stageRoot Ω x y ζ a n) b := by
  let S := stage Ω x y ζ a n
  let f := stageEmbedding Ω x y ζ a n hx hy
  let z := stageRoot Ω x y ζ a n
  let G := DyadicCyclotomicModel69.nativeSubfield (Generated (baseImage f) z)
    (DyadicCyclotomicSpan69.generated_subfield (DyadicEmbeddedBase69.base_subfield f) z)
  let U := G.map S.val.toRingHom
  have he := DyadicNativeEmbedding69.roots_evaluate
    (⟨x,(stage_roots Ω x y ζ a n).1⟩ : S) (⟨y,(stage_roots Ω x y ζ a n).2⟩ : S)
    (Subtype.ext hx) (Subtype.ext hy)
  have witness (w : S) (h : Generated (baseImage f) z w) : (w:Ω) ∈ U :=
    Subfield.mem_map.mpr ⟨w,h,rfl⟩
  have xu : x ∈ U := witness ⟨x,(stage_roots Ω x y ζ a n).1⟩
    (Generated.base ⟨TameRationalField277.gen3, he.1⟩)
  have yu : y ∈ U := witness ⟨y,(stage_roots Ω x y ζ a n).2⟩
    (Generated.base ⟨TameRationalField277.gen23, he.2⟩)
  have zu : ζ (a+n) ∈ U := witness z Generated.gen
  obtain ⟨c,hc,heq⟩ := Subfield.mem_map.mp (stage_in_subfield Ω x y ζ a n hs U xu yu zu b b.property)
  exact (Subtype.ext heq : c=b) ▸ hc

theorem stage_increasing (hs : ∀ j, (ζ (j+1))^2 = ζ j) :
    Monotone (fun n => (stage Ω x y ζ a n).toSubfield) := by
  apply monotone_nat_of_le_succ
  intro n
  change stage Ω x y ζ a n ≤ stage Ω x y ζ a (n+1)
  apply IntermediateField.adjoin_le_iff.mpr
  apply Set.singleton_subset_iff.mpr
  rw [← hs (a+n)]
  exact pow_mem (stageRoot Ω x y ζ a (n+1)).property 2

theorem stage_number_field [Algebra.IsAlgebraic ℚ Ω] :
    NumberField ((stage Ω x y ζ a n).toSubfield) := by
  let E := realLayer Ω x y (ζ a)
  let : FiniteDimensional ℚ E := realLayer_finite Ω x y (ζ a)
  let : FiniteDimensional E (stage Ω x y ζ a n) :=
    IntermediateField.finiteDimensional_adjoin (fun v _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R:=ℚ) v).isIntegral.tower_top)
  exact { to_finiteDimensional := FiniteDimensional.trans ℚ E (stage Ω x y ζ a n) }

theorem stage_evaluation (hx : x^2 = -3) (hy : y^2 = -23) (u : TameRationalField277.Biquad) :
    ((stageEmbedding Ω x y ζ a n hx hy).app u : Ω) =
      (DyadicNativeEmbedding69.root_embedding x y hx hy).app u := by
  simp [stageEmbedding,DyadicNativeEmbedding69.root_embedding,
    DyadicNativeEmbedding69.value,DyadicNativeEmbedding69.quadValue]

theorem stage_base (hx : x^2 = -3) (hy : y^2 = -23) (u : TameRationalField277.Biquad) :
    (DyadicNativeEmbedding69.root_embedding x y hx hy).app u ∈ (stage Ω x y ζ a n).toSubfield :=
  stage_evaluation Ω x y ζ a n hx hy u ▸ ((stageEmbedding Ω x y ζ a n hx hy).app u).property

theorem restricted_generation (hx : x^2 = -3) (hy : y^2 = -23)
    (hs : ∀ j, (ζ (j+1))^2 = ζ j) (b : (stage Ω x y ζ a n).toSubfield) :
    Generated (baseImage (DyadicValueUnion69.stageEmbedding
      (DyadicNativeEmbedding69.root_embedding x y hx hy) _
      (stage_base Ω x y ζ a n hx hy))) (stageRoot Ω x y ζ a n) b := by
  have e : (stageEmbedding Ω x y ζ a n hx hy).app =
      (DyadicValueUnion69.stageEmbedding (DyadicNativeEmbedding69.root_embedding x y hx hy) _
        (stage_base Ω x y ζ a n hx hy)).app :=
    funext (fun u => Subtype.ext (stage_evaluation Ω x y ζ a n hx hy u))
  have h := stage_generation Ω x y ζ a n hx hy hs b
  unfold baseImage at *
  rwa [e] at h

theorem earlier_root_in_stage (hs : ∀ j, (ζ (j+1))^2 = ζ j) (j : ℕ) :
    ζ j ∈ (stage Ω x y ζ a j).toSubfield := by
  rw [← earlier_root Ω ζ j a hs,Nat.add_comm j a]
  exact pow_mem (stageRoot Ω x y ζ a j).property _

open DyadicCyclotomicModel69 (lowerX lowerY lower_squares rootAt bottom)
local notation "L" => fullCyclotomic Ω x y ζ a
local notation "Xr" => lowerX Ω x y ζ a
local notation "Yr" => lowerY Ω x y ζ a
local notation "Zr" => rootAt Ω x y ζ a

/-- The reindexed stages are literal subfields of L, carrying the roots
already used in its infinite model. -/
noncomputable def lowerStages : ℕ → Subfield L :=
  fun j => (stage L Xr Yr Zr a j).toSubfield

theorem lower_cover (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1)
    (hs : ∀ j, (ζ (j+1))^2 = ζ j) (v : L) : ∃ j, v ∈ lowerStages Ω x y ζ a j := by
  let S := lowerStages Ω x y ζ a
  let U := ⨆ j, S j
  have hsq (j : ℕ) : (Zr (j+1))^2 = Zr j := Subtype.ext (hs j)
  have inc : Monotone S := stage_increasing L Xr Yr Zr a hsq
  have g := DyadicCyclotomicModel69.full_generation Ω x y ζ a hx hy hz
    (fun j => by simpa only [pow_two] using hs j)
  have hU : DyadicCyclotomicSpan69.Subfield (fun v => v ∈ U) := {
    zero := U.zero_mem, one := U.one_mem, add := U.add_mem, neg := U.neg_mem,
    mul := U.mul_mem, inv := U.inv_mem }
  have base : ∀ e, baseImage (bottom Ω x y ζ a hx hy) e → e ∈ U := by
    rintro _ ⟨u,rfl⟩
    exact le_iSup S 0 (stage_base L Xr Yr Zr a 0 (lower_squares Ω x y ζ a hx hy).1
      (lower_squares Ω x y ζ a hx hy).2 u)
  apply (Subfield.mem_iSup_of_directed inc.directed_le).mp
  apply g _ hU base _ v
  intro j
  cases j with
  | zero => exact U.neg_mem U.one_mem
  | succ j => exact le_iSup S j (earlier_root_in_stage L Xr Yr Zr a hsq j)

/-- The finite number fields, their compatible bottom embeddings and their
individual primitive generators, all inside the same actual L = Eₐ(μ₂∞). -/
theorem lower_stage_data [Algebra.IsAlgebraic ℚ Ω] (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ j, (ζ j)^(2^(j+1) : ℕ) = -1) (hs : ∀ j, (ζ (j+1))^2 = ζ j) :
    ∃ S : ℕ → Subfield L, (∀ j, NumberField (S j)) ∧ Monotone S ∧
      (∀ v : L, ∃ j, v ∈ S j) ∧
      ∃ base : ∀ j u, (bottom Ω x y ζ a hx hy).app u ∈ S j, ∃ z : ∀ j, S j,
        (∀ j, (z j : L) = Zr (a+j)) ∧
        (∀ j, (z j)^(2^(a+j+1) : ℕ) = -1) ∧
        ∀ j (b : S j), Generated (baseImage (DyadicValueUnion69.stageEmbedding
          (bottom Ω x y ζ a hx hy) _ (base j))) (z j) b := by
  let : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.tower_bot ℚ L Ω
  have hsq (j : ℕ) : (Zr (j+1))^2 = Zr j := Subtype.ext (hs j)
  obtain ⟨ex,ey⟩ := lower_squares Ω x y ζ a hx hy
  refine ⟨lowerStages Ω x y ζ a,fun j => stage_number_field L Xr Yr Zr a j,
    stage_increasing L Xr Yr Zr a hsq,lower_cover Ω x y ζ a hx hy hz hs,
    fun j => stage_base L Xr Yr Zr a j ex ey,fun j => stageRoot L Xr Yr Zr a j,
    fun _ => rfl,fun j => Subtype.ext (Subtype.ext (hz (a+j))),?_⟩
  exact fun j b => restricted_generation L Xr Yr Zr a j ex ey hsq b


end Reimann.DyadicFiniteModel69
