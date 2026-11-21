import Reimann.CircularIndependence69
import Reimann.CircularFiniteSum69
import Reimann.CircularRelativeBasis69

/-! The ordinary and relative power bases on actual polynomial values. -/

namespace Reimann.CircularFieldBasis69

open Lean.Grind CircularMonomial69 CircularIndependence69 CircularNormalForm69
  CircularRelativeBasis69 CircularFiniteSum69 CircularRelationEval69 CircularBasis69 CircularBasisData69

theorem primitive_ordinary_independent {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) : OrdinaryIndependent x := by
  intro v hv
  have h := primitive_monomials_independent x h69 h23 h3 (extendCoeffs v) (extend_bounded v)
    ((evalAt_extendCoeffs_right x v).trans hv)
  funext i
  exact (extend_at v i).symm.trans (h i.val)

theorem primitive_relative_independent {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) : RelativeIndependent x :=
  (primitive_independence_iff x h69 h23 h3).mp (primitive_ordinary_independent x h69 h23 h3)

theorem restrict_extend (r : Nat → Rat) (n : Nat) (br : Bounded r n) :
    extendCoeffs (fun i : Fin n => r i.val) = r := by
  funext k
  by_cases h : k < n
  · simp [extendCoeffs,h]
  · simp [extendCoeffs,h,br k (by omega)]

theorem ordinary_value_injective {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (p q : Fin 44 → Rat)
    (he : ordinaryValue x p = ordinaryValue x q) : p = q := by
  have h := unique_at_degree x 44 (primitive_monomials_independent x h69 h23 h3) _ _
    (extend_bounded p) (extend_bounded q)
    ((evalAt_extendCoeffs_right x p).trans (he.trans (evalAt_extendCoeffs_right x q).symm))
  funext i
  exact (extend_at p i).symm.trans ((congrFun h i.val).trans (extend_at q i))

theorem relative_value_injective {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (p q : Fin 22 → CircularRational69.Element)
    (he : relativeValue x p = relativeValue x q) : p = q := by
  have hx := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  have hn := ordinary_value_injective x h69 h23 h3 _ _
    ((change_to_ordinary x hx p).trans (he.trans (change_to_ordinary x hx q).symm))
  have hf := congrArg (applyMatrix inverseColumns) hn
  rw [relative_coordinates_recovered, relative_coordinates_recovered] at hf
  have hc := congrArg pair hf
  simpa only [pair_flatten] using hc

theorem primitive_relative_coordinates {R : Type} [Field R] [IsCharP R 0] (x y : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (p : Nat → Rat) (hy : Represents x p y) :
    ∃ c : Fin 22 → CircularRational69.Element, relativeValue x c = y ∧
      ∀ v, relativeValue x v = y → v = c := by
  obtain ⟨m,bp,ep⟩ := hy
  obtain ⟨r,br,er,_⟩ := unique_rational_coordinates x h69 h23 h3 p m bp
  let v := fun i : Fin 44 => r i.val
  have hv := evalAt_extendCoeffs_right x v
  rw [show extendCoeffs v = r from restrict_extend r 44 br] at hv
  have hx := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  let c := pair (applyMatrix inverseColumns v)
  have ec : relativeValue x c = y := (change_to_relative x hx v).trans (hv.symm.trans (er.trans ep))
  exact ⟨c,ec,fun w ew => relative_value_injective x h69 h23 h3 w c (ew.trans ec.symm)⟩

end Reimann.CircularFieldBasis69
