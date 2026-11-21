import Reimann.CircularFieldReduction69
import Reimann.CircularKernel69
import Reimann.CircularNormAction69
import Reimann.CircularSubstitution69

/-! Power actions and the stabilizer of the embedded quadratic period field. -/

namespace Reimann.CircularGalois69

open Lean.Grind CircularKernel69 CircularPolynomial69 CircularFactor69 CircularFieldReduction69
open CircularSubstitution69 CircularPolynomialField69 CircularRationalPeriod69

variable {R : Type} [Field R] [IsCharP R 0]

theorem positive_period_fixed {R : Type} [Field R] (x : R) (hx : Primitive69 x)
    (a : Fin 69) (ha : eta a.val = 1) : periodTheta (x^a.val) = periodTheta x := by
  rw [period_theta_formula, period_theta_formula]
  exact congrArg (fun k : R => 1-k) (positive_period_action x hx.order69 a ha).1

theorem period_fixed_iff_positive {R : Type} [Field R] [IsCharP R 0] (x : R)
    (hx : Primitive69 x) (a : Fin 69) (hu : Nat.gcd a.val 69 = 1)
    (ha : Primitive69 (x^a.val)) : periodTheta (x^a.val) = periodTheta x ↔ eta a.val = 1 := by
  constructor
  · intro hp
    apply (primitive_positive_stabilizer x hx.order69 hx.not23 hx.not3 a hu).mp
    rw [positive_signed_value _ (primitive_phi ha), positive_signed_value _ (primitive_phi hx), hp]
  · exact positive_period_fixed x hx a

def generatorImage {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) : R :=
  (e.forward (generator x)).val

theorem power_eq_one_iff {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) (n : Nat) :
    (generatorImage e)^n = 1 ↔ x^n = 1 := by
  have h (u : Carrier x) : power x u n = constant x 1 ↔ u.val^n = 1 := by
    constructor
    · intro t
      exact (congrArg Subtype.val t).trans CircularRelationEval69.ofRat_one
    · intro t
      exact Subtype.ext (t.trans CircularRelationEval69.ofRat_one.symm)
  change (e.forward (generator x)).val^n = 1 ↔ (generator x).val^n = 1
  calc
    _ ↔ power x (e.forward (generator x)) n = constant x 1 := (h _).symm
    _ ↔ e.forward (power x (generator x) n) = e.forward (constant x 1) := by
      rw [map_power, e.map_constant]
    _ ↔ power x (generator x) n = constant x 1 := by
      constructor
      · exact fun t => (e.leftInv _).symm.trans ((congrArg e.backward t).trans (e.leftInv _))
      · exact congrArg e.forward
    _ ↔ _ := h _

theorem generator_image_primitive {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) :
    Primitive69 (generatorImage e) :=
  ⟨(power_eq_one_iff e 69).mpr hx.order69, fun h => hx.not23 ((power_eq_one_iff e 23).mp h),
    fun h => hx.not3 ((power_eq_one_iff e 3).mp h)⟩

theorem map_int_poly {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx)
    (u : Carrier x) (p : List Int) (he : eval x p = u.val) :
    (e.forward u).val = eval (generatorImage e) p :=
  (map_eval e u (ratCoeffs p) p.length ((eval_integer_at_cutoff x p _ (Nat.le_refl _)).trans he)).trans
    (eval_integer_at_cutoff (generatorImage e) p _ (Nat.le_refl _))

def periodCarrier (x : R) (hx : Primitive69 x) : Carrier x :=
  ⟨periodTheta x, by
    have h := CircularNormAction69.coefficient_in_generated_field x hx.order69 hx.not23 hx.not3
      CircularRational69.theta
    rwa [eval_theta] at h⟩

theorem map_period {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) :
    (e.forward (periodCarrier x hx)).val = periodTheta (generatorImage e) :=
  map_int_poly e (periodCarrier x hx) periodPoly rfl

def coefficient (x : R) (hx : Primitive69 x) (c : CircularRational69.Element) : Carrier x :=
  plus x (constant x c.a) (times x (constant x c.b) (periodCarrier x hx))

theorem map_coefficient {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx)
    (c : CircularRational69.Element) :
    (e.forward (coefficient x hx c)).val = evaluate (periodTheta (generatorImage e)) c := by
  unfold coefficient
  rw [e.map_plus, e.map_constant, e.map_times, e.map_constant]
  change _ + _ * (e.forward (periodCarrier x hx)).val = _
  rw [map_period]
  rfl

def FixesQuadratic {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) : Prop :=
  ∀ c, e.forward (coefficient x hx c) = coefficient x hx c

theorem fixes_quadratic_iff {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) :
    FixesQuadratic e ↔ periodTheta (generatorImage e) = periodTheta x := by
  constructor
  · intro h
    have ht := (map_coefficient e CircularRational69.theta).symm.trans
      (congrArg Subtype.val (h CircularRational69.theta))
    change evaluate (periodTheta (generatorImage e)) CircularRational69.theta =
      evaluate (periodTheta x) CircularRational69.theta at ht
    simpa only [eval_theta] using ht
  · intro ht c
    apply Subtype.ext
    exact (map_coefficient e c).trans (congrArg (fun t => evaluate t c) ht)

end Reimann.CircularGalois69
