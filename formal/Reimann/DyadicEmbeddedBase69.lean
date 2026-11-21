import Reimann.DyadicBottomValue69
import Reimann.DyadicCyclotomicSpan69

/-! The image of the actual bottom biquadratic field as a subfield of a valuation field. -/

namespace Reimann.DyadicEmbeddedBase69

open Lean.Grind Reimann.TameRationalField277
open Reimann.DyadicBottomValue69 (Embedding)
open Reimann.DyadicCyclotomicSpan69 (Subfield)

variable {F : Type} [Field F]

def baseImage (f : Embedding F) (y : F) : Prop := ∃ x : Biquad, f.app x=y

theorem map_zero_one (f : Embedding F) : f.app (scalar 0) = 0 ∧ f.app (scalar 1) = 1 := by
  constructor
  · simpa only [Ring.intCast_zero] using f.scalar_int 0
  · simpa only [Ring.intCast_one] using f.scalar_int 1

theorem map_neg (f : Embedding F) (x : Biquad) : f.app (bn x) = -(f.app x) := by
  have e := congrArg f.app (add_group_laws x x x).2.2.2
  change f.app (ba x (bn x)) = f.app (scalar 0) at e
  rw [f.add,(map_zero_one f).1] at e
  grind

theorem map_nonzero_inverse (f : Embedding F) (x : Biquad) (h : f.app x ≠ 0) :
    f.app (bi x) = (f.app x)⁻¹ := by
  have hx : x ≠ scalar 0 := by
    intro e
    exact h (e ▸ (map_zero_one f).1)
  have e := congrArg f.app (biquad_mul_inverse x hx)
  change f.app (bm x (bi x)) = f.app (scalar 1) at e
  rw [f.mul,(map_zero_one f).2] at e
  exact Field.eq_inv_of_mul_eq_one ((CommSemiring.mul_comm _ _).trans e)

theorem base_subfield (f : Embedding F) : Subfield (baseImage f) where
  zero := ⟨scalar 0,(map_zero_one f).1⟩
  one := ⟨scalar 1,(map_zero_one f).2⟩
  add := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨ba x y,f.add x y⟩
  neg := by rintro _ ⟨x,rfl⟩; exact ⟨bn x,map_neg f x⟩
  mul := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨bm x y,f.mul x y⟩
  inv := by
    rintro _ ⟨x,rfl⟩
    by_cases h : f.app x = 0
    · exact ⟨scalar 0,by rw [h,Field.inv_zero,(map_zero_one f).1]⟩
    · exact ⟨bi x,map_nonzero_inverse f x h⟩

end Reimann.DyadicEmbeddedBase69
