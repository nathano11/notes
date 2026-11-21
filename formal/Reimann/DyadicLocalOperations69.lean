import Reimann.DyadicLocalizedCompletion69

/-! Field operations at every precision of the localized integral order. -/

namespace Reimann.DyadicLocalOperations69

open Reimann.DyadicOrderCompletion69 Reimann.DyadicLocalizedCompletion69
open Reimann.DyadicLocalizedPrimes69 (Represents represents_add represents_mul)
open Reimann.TameBiquadratic277 (Quad componentAdd)
open Reimann.TameRationalField277 (Biquad ba bm)

theorem odd_word_product (n : Nat) (k l : Int) :
    BitVec.ofInt (n+1) (1+2*(k+l+2*k*l)) =
      BitVec.ofInt (n+1) (1+2*k)*BitVec.ofInt (n+1) (1+2*l) := by
  rw [← BitVec.ofInt_mul]
  congr 1
  grind

/-- Clearing a common denominator in an addition multiplies the first
numerator by the second denominator and conversely. -/
theorem wordScale_cross_add {n : Nat} (s t : BitVec (n+1)) (x y : Quad (BitVec (n+1))) :
    wordScale (s*t) (componentAdd x y) =
      componentAdd (wordScale t (wordScale s x)) (wordScale s (wordScale t y)) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [wordScale,mapFour,componentAdd] <;> grind

theorem wordScale_product {n : Nat} (s t : BitVec (n+1)) (x y : Quad (BitVec (n+1))) :
    wordScale (s*t) (product x y) = product (wordScale s x) (wordScale t y) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [wordScale,mapFour,product,pairProduct] <;> grind

theorem level_add (n : Nat) (x y z : {t : Biquad // Local t}) (hz : z.val = ba x.val y.val) :
    level n z = componentAdd (level n x) (level n y) := by
  obtain ⟨k,p,hp⟩ := x.property
  obtain ⟨l,q,hq⟩ := y.property
  have hs := represents_add hp hq
  rw [← hz] at hs
  apply level_unique n z hs
  unfold ScalesTo
  rw [odd_word_product,wordScale_cross_add, level_spec n x hp,level_spec n y hq,
    integer_reduction_add,scale_reduction,scale_reduction]

theorem level_mul (n : Nat) (x y z : {t : Biquad // Local t}) (hz : z.val = bm x.val y.val) :
    level n z = product (level n x) (level n y) := by
  obtain ⟨k,p,hp⟩ := x.property
  obtain ⟨l,q,hq⟩ := y.property
  have hs := represents_mul hp hq
  rw [← hz] at hs
  apply level_unique n z hs
  unfold ScalesTo
  rw [odd_word_product,wordScale_product,level_spec n x hp,level_spec n y hq,integer_reduction_mul]

theorem completed_add (x y z : {t : Biquad // Local t}) (hz : z.val = ba x.val y.val) :
    completedPoint z = completedSum (completedPoint x) (completedPoint y) :=
  completion_ext (fun n => level_add n x y z hz)

theorem completed_mul (x y z : {t : Biquad // Local t}) (hz : z.val = bm x.val y.val) :
    completedPoint z = completedProduct (completedPoint x) (completedPoint y) :=
  completion_ext (fun n => level_mul n x y z hz)

end Reimann.DyadicLocalOperations69
