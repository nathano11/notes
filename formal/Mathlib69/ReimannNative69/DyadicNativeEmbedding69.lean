import Reimann.DyadicEmbeddedBase69
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Evaluation of the rational biquadratic coordinates at two actual roots. -/
namespace Reimann.DyadicNativeEmbedding69

open Reimann.TameRationalField277

variable {F : Type} [Field F] [CharZero F]

def quadValue (x : F) (u : Quad) : F := (u.1 : F) + (u.2 : F)*x

theorem quad_product (x : F) (hx : x^2 = -3) (u v : Quad) :
    quadValue x (qm u v) = quadValue x u * quadValue x v := by
  simp only [quadValue, qm, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add]
  linear_combination -(u.2:F)*(v.2:F)*hx

def value (x y : F) (u : Biquad) : F := quadValue x u.1 + quadValue x u.2*y

theorem value_add (x y : F) (u v : Biquad) :
    value x y (ba u v) = value x y u + value x y v := by
  simp only [value, ba, qa, quadValue, Rat.cast_add]
  ring

theorem value_mul (x y : F) (hx : x^2 = -3) (hy : y^2 = -23) (u v : Biquad) :
    value x y (bm u v) = value x y u * value x y v := by
  have hadd (p q : Quad) : quadValue x (qa p q) = quadValue x p + quadValue x q := by
    simp only [quadValue, qa, Rat.cast_add]
    ring
  have hscale (p : Quad) : quadValue x (qs (-23) p) = -23*quadValue x p := by
    simp only [quadValue, qs, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat]
    ring
  simp only [value, bm, hadd, hscale, quad_product x hx]
  linear_combination -(quadValue x u.2)*(quadValue x v.2)*hy

/-- The two chosen square roots alone give a faithful evaluation of the bottom field. -/
def root_embedding (x y : F) (hx : x^2 = -3) (hy : y^2 = -23) :
    DyadicBottomValue69.Embedding F where
  app := value x y
  scalar_int n := by simp [value, quadValue, scalar]
  add := value_add x y
  mul := value_mul x y hx hy
  faithful := by
    intro u hu
    by_contra hn
    have e := congrArg (value x y) (biquad_mul_inverse u hn)
    rw [value_mul x y hx hy,hu,zero_mul] at e
    simpa [value, quadValue] using e

theorem roots_evaluate (x y : F) (hx : x^2 = -3) (hy : y^2 = -23) :
    (root_embedding x y hx hy).app gen3=x ∧ (root_embedding x y hx hy).app gen23=y := by
  simp [root_embedding, value, quadValue, gen3, gen23]

end Reimann.DyadicNativeEmbedding69
