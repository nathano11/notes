import Mathlib.Algebra.Field.Subfield.Basic
import Reimann.CircularRealUnit69

/-! The conductor compositum and its real part as subfields of the common ambient field. -/

namespace Reimann.CommonRealPart69

open CircularRealUnit69 CircularPolynomialField69

variable {R : Type} [Field R]

theorem rat_mem (S : Subfield R) (q : ℚ) :
    Lean.Grind.Field.NormNum.ofRat q ∈ S :=
  S.div_mem (S.intCast_mem _) (natCast_mem S _)

theorem predicate_of_subfield (S : Subfield R) {u : R} (hu : u ∈ S) :
    SubfieldContaining u (fun y => y ∈ S) where
  rational := rat_mem S
  root := hu
  add := fun _ _ => S.add_mem
  sub := fun _ _ => S.sub_mem
  mul := fun _ _ => S.mul_mem
  inv := fun _ _ => S.inv_mem

def subfieldOfPredicate {u : R} (S : R → Prop) (h : SubfieldContaining u S) : Subfield R where
  carrier := {a | S a}
  zero_mem' := by
    change S 0
    simpa only [CircularRelationEval69.ofRat_zero] using h.rational 0
  one_mem' := by
    change S 1
    simpa only [CircularRelationEval69.ofRat_one] using h.rational 1
  add_mem' := h.add _ _
  neg_mem' := fun {x} ha => by
    change S (-x)
    have h0 : S 0 := by simpa only [CircularRelationEval69.ofRat_zero] using h.rational 0
    simpa only [zero_sub] using h.sub _ _ h0 ha
  mul_mem' := h.mul _ _
  inv_mem' := fun {a} ha => by
    by_cases h0 : a = 0
    · simpa only [h0, inv_zero] using ha
    · exact h.inv a h0 ha

def generators (u v : R) : Set R := {y | y = u ∨ y = v ∨ y ^ 277 = 1}

def compositum (u v : R) : Subfield R := Subfield.closure (generators u v)

theorem mem_compositum_iff (u v y : R) : y ∈ compositum u v ↔ Compositum u v y := by
  constructor
  · intro hy S h hv hroots
    apply ((Subfield.closure_le (t := subfieldOfPredicate S h)).mpr ?_) hy
    intro w hw
    rcases hw with rfl | rfl | hw
    · exact h.root
    · exact hv
    · exact hroots _ hw
  · intro hy
    have mem_gen (w : R) (h : w ∈ generators u v) : w ∈ compositum u v :=
      Subfield.subset_closure h
    exact hy _ (predicate_of_subfield _ (mem_gen u (Or.inl rfl)))
      (mem_gen v (Or.inr (Or.inl rfl))) (fun w hw => mem_gen w (Or.inr (Or.inr hw)))

def fixedField (c : Conjugation R) : Subfield R :=
  subfieldOfPredicate _ (fixed_subfield c 1 (map_one c))

def realCompositum (c : Conjugation R) (u v : R) : Subfield R :=
  compositum u v ⊓ fixedField c

theorem mem_realCompositum_iff (c : Conjugation R) (u v y : R) :
    y ∈ realCompositum c u v ↔ RealPart c u v y := by
  change (y ∈ compositum u v ∧ c.app y = y) ↔ (Compositum u v y ∧ c.app y = y)
  rw [mem_compositum_iff]

def threeGenerators (u v z : R) : Set R := {w | w = u ∨ w = v ∨ w = z}

theorem primitive_generates (u v z : R) (hz : z ^ 277 = 1)
    (hpow : ∀ w : R, w ^ 277 = 1 → ∃ a : ℕ, a < 277 ∧ z ^ a = w) :
    compositum u v = Subfield.closure (threeGenerators u v z) := by
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    intro w hw
    rcases hw with rfl | rfl | hr
    · exact Subfield.subset_closure (s := threeGenerators _ _ _) (Or.inl rfl)
    · exact Subfield.subset_closure (s := threeGenerators _ _ _) (Or.inr (Or.inl rfl))
    · obtain ⟨a, _, rfl⟩ := hpow _ hr
      exact (Subfield.closure (threeGenerators u v z)).pow_mem
        (Subfield.subset_closure (Or.inr (Or.inr rfl) : z ∈ threeGenerators u v z)) a
  · apply Subfield.closure_le.mpr
    intro w hw
    apply Subfield.subset_closure
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hz)

theorem fixed_three_generator_field (c : Conjugation R) (u v z : R) (hz : z ^ 277 = 1)
    (hpow : ∀ w : R, w ^ 277 = 1 → ∃ a : ℕ, a < 277 ∧ z ^ a = w) :
    realCompositum c u v = Subfield.closure (threeGenerators u v z) ⊓ fixedField c := by
  unfold realCompositum
  rw [primitive_generates u v z hz hpow]

end Reimann.CommonRealPart69
