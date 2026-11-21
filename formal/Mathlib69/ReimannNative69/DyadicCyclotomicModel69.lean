import ReimannNative69.DyadicNativeEmbedding69
import ReimannNative69.DyadicNormalTower69
import Reimann.DyadicLocalRestriction69

/-! The native cyclotomic compositum carries the generated root tower and
bottom embedding used in the dyadic place comparison. -/
namespace Reimann.DyadicCyclotomicModel69

open DyadicNormalTower69 DyadicLocalRestriction69 DyadicEmbeddedBase69
open DyadicNativeEmbedding69 TameRationalField277

variable (Ω : Type) [Field Ω] [CharZero Ω] (x y : Ω) (ζ : ℕ → Ω) (a : ℕ)
local notation "E" => realLayer Ω x y (ζ a)
local notation "L" => fullCyclotomic Ω x y ζ a

theorem lower_generators : x ∈ E ∧ y ∈ E ∧ ζ a + (ζ a)⁻¹ ∈ E := by
  refine ⟨IntermediateField.subset_adjoin _ _ ?_, IntermediateField.subset_adjoin _ _ ?_,
    IntermediateField.subset_adjoin _ _ ?_⟩ <;> simp

noncomputable def rootAt (n : ℕ) : L :=
  ⟨ζ n, IntermediateField.subset_adjoin E (Set.range ζ) (Set.mem_range_self n)⟩

noncomputable def lowerX : L :=
  algebraMap E L ⟨x,(lower_generators Ω x y ζ a).1⟩

noncomputable def lowerY : L :=
  algebraMap E L ⟨y,(lower_generators Ω x y ζ a).2.1⟩

theorem lower_squares (hx : x^2= -3) (hy : y^2= -23) :
    (lowerX Ω x y ζ a)^2= -3 ∧ (lowerY Ω x y ζ a)^2= -23 :=
  ⟨Subtype.ext hx,Subtype.ext hy⟩

noncomputable def bottom (hx : x^2= -3) (hy : y^2= -23) : DyadicBottomValue69.Embedding L :=
  root_embedding (lowerX Ω x y ζ a) (lowerY Ω x y ζ a)
    (lower_squares Ω x y ζ a hx hy).1 (lower_squares Ω x y ζ a hx hy).2

noncomputable def tower (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1)
    (hs : ∀ n, ζ (n+1)*ζ (n+1)=ζ n) : RootTower L where
  root
    | 0 => -1
    | n+1 => rootAt Ω x y ζ a n
  half_order n := by
    cases n with
    | zero => simp
    | succ n => exact Subtype.ext (hz n)
  square n := by
    cases n with
    | zero =>
      apply Subtype.ext
      change ζ 0 * ζ 0= -1
      have e : ζ 0 ^ 2= -1 := hz 0
      simpa only [pow_two] using e
    | succ n => exact Subtype.ext (hs n)

def nativeSubfield {K : Type} [Field K] (S : K → Prop) (h : DyadicCyclotomicSpan69.Subfield S) :
    Subfield K where
  carrier := {z | S z}
  zero_mem' := h.zero
  one_mem' := h.one
  add_mem' := h.add
  mul_mem' := h.mul
  neg_mem' := h.neg
  inv_mem' _ hz := h.inv hz

theorem generated_in_subfield (U : Subfield Ω) (hx : x ∈ U) (hy : y ∈ U)
    (hζ : ∀ n, ζ n ∈ U) {b : Ω} (hb : b ∈ L) : b ∈ U := by
  let UQ : IntermediateField ℚ Ω := U.toIntermediateField (fun q => SubfieldClass.ratCast_mem U q)
  have hE : E ≤ UQ := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    rcases hz with rfl | rfl | hz
    · exact hx
    · exact hy
    · have : z=ζ a+(ζ a)⁻¹ := hz
      exact this ▸ U.add_mem (hζ a) (U.inv_mem (hζ a))
  let UE : IntermediateField E Ω := U.toIntermediateField (fun e => hE e.property)
  have hL : L ≤ UE := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨n,rfl⟩
    exact hζ n
  exact hL hb

theorem full_generation (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1) (hs : ∀ n, ζ (n+1)*ζ (n+1)=ζ n) :
    GeneratesField (baseImage (bottom Ω x y ζ a hx hy)) (tower Ω x y ζ a hz hs) := by
  intro S hS hbase hroot z
  let U := (nativeSubfield S hS).map (algebraMap L Ω)
  obtain ⟨ex,ey⟩ := roots_evaluate (lowerX Ω x y ζ a) (lowerY Ω x y ζ a)
    (lower_squares Ω x y ζ a hx hy).1 (lower_squares Ω x y ζ a hx hy).2
  have witness (w : L) (hw : S w) : (w : Ω) ∈ U := Subfield.mem_map.mpr ⟨w,hw,rfl⟩
  have xmem : x ∈ U := witness (lowerX Ω x y ζ a)
    (ex ▸ hbase _ ⟨gen3,rfl⟩)
  have ymem : y ∈ U := witness (lowerY Ω x y ζ a)
    (ey ▸ hbase _ ⟨gen23,rfl⟩)
  have zmem (n : ℕ) : ζ n ∈ U := witness (rootAt Ω x y ζ a n) (hroot (n+1))
  have mem := generated_in_subfield Ω x y ζ a U xmem ymem zmem z.property
  obtain ⟨w,hw,eq⟩ := Subfield.mem_map.mp mem
  have e : w=z := Subtype.ext eq
  exact e ▸ hw

theorem base_containment (hx : x^2= -3) (hy : y^2= -23) (z : Biquad) :
    ∃ e : E, algebraMap E L e=(bottom Ω x y ζ a hx hy).app z := by
  let S : L → Prop := fun w => ∃ e : E, algebraMap E L e=w
  have closure : DyadicCyclotomicSpan69.Subfield S := {
    zero := ⟨0,map_zero _⟩
    one := ⟨1,map_one _⟩
    add := by rintro _ _ ⟨s,rfl⟩ ⟨t,rfl⟩; exact ⟨s+t,map_add _ _ _⟩
    neg := by rintro _ ⟨s,rfl⟩; exact ⟨-s,map_neg _ _⟩
    mul := by rintro _ _ ⟨s,rfl⟩ ⟨t,rfl⟩; exact ⟨s*t,map_mul _ _ _⟩
    inv := by rintro _ ⟨s,rfl⟩; exact ⟨s⁻¹,map_inv₀ _ _⟩ }
  obtain ⟨ex,ey⟩ := roots_evaluate (lowerX Ω x y ζ a) (lowerY Ω x y ζ a)
    (lower_squares Ω x y ζ a hx hy).1 (lower_squares Ω x y ζ a hx hy).2
  change (bottom Ω x y ζ a hx hy).app gen3=_ at ex
  change (bottom Ω x y ζ a hx hy).app gen23=_ at ey
  apply (DyadicGenusField69.bottom_image_iff closure (bottom Ω x y ζ a hx hy)).mpr _ _ ⟨z,rfl⟩
  rw [ex,ey]
  exact ⟨⟨⟨x,(lower_generators Ω x y ζ a).1⟩,rfl⟩,⟨⟨y,(lower_generators Ω x y ζ a).2.1⟩,rfl⟩⟩

/-- Uniformly in the real level a, these data discharge both generation
and bottom-field containment in the centered-place surjectivity theorem. -/
theorem cyclotomic_model (hx : x^2= -3) (hy : y^2= -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ)= -1) (hs : ∀ n, ζ (n+1)*ζ (n+1)=ζ n) :
    ∃ f : DyadicBottomValue69.Embedding L, ∃ C : RootTower L,
      GeneratesField (baseImage f) C ∧ (∀ z, ∃ e : E, algebraMap E L e=f.app z) ∧
      (f.app gen3 : Ω)=x ∧ (f.app gen23 : Ω)=y ∧ C.root 0= -1 ∧
      ∀ n, (C.root (n+1) : Ω)=ζ n := by
  obtain ⟨ex,ey⟩ := roots_evaluate (lowerX Ω x y ζ a) (lowerY Ω x y ζ a)
    (lower_squares Ω x y ζ a hx hy).1 (lower_squares Ω x y ζ a hx hy).2
  refine ⟨bottom Ω x y ζ a hx hy,tower Ω x y ζ a hz hs,
    full_generation Ω x y ζ a hx hy hz hs,base_containment Ω x y ζ a hx hy,
    congrArg Subtype.val ex,congrArg Subtype.val ey,rfl,fun _ => rfl⟩

end Reimann.DyadicCyclotomicModel69
