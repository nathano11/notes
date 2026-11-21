import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.Field.Basic
import Reimann.TameEmbeddings277

namespace Reimann.TameBiquadraticField277

open TameRationalField277 TameEmbeddings277

/-- A separate carrier keeps the biquadratic multiplication distinct from
the coordinatewise multiplication on the product of four rationals. -/
structure Biquadratic where
  coord : Biquad
  deriving DecidableEq

theorem coord_injective : Function.Injective Biquadratic.coord := by
  rintro ⟨x⟩ ⟨y⟩ h
  exact congrArg Biquadratic.mk h

instance biquadAdd : Add Biquadratic := ⟨fun x y => ⟨ba x.coord y.coord⟩⟩
instance biquadMul : Mul Biquadratic := ⟨fun x y => ⟨bm x.coord y.coord⟩⟩
instance biquadNeg : Neg Biquadratic := ⟨fun x => ⟨bn x.coord⟩⟩
instance biquadInv : Inv Biquadratic := ⟨fun x => ⟨bi x.coord⟩⟩
instance biquadZero : Zero Biquadratic := ⟨⟨scalar 0⟩⟩
instance biquadOne : One Biquadratic := ⟨⟨scalar 1⟩⟩

theorem zero_add_coord (x : Biquadratic) : 0 + x = x :=
  coord_injective (((add_group_laws (scalar 0) x.coord x.coord).2.1).trans
    (add_group_laws x.coord x.coord x.coord).2.2.1)

theorem neg_add_coord (x : Biquadratic) : -x + x = 0 :=
  coord_injective (((add_group_laws (bn x.coord) x.coord x.coord).2.1).trans
    (add_group_laws x.coord x.coord x.coord).2.2.2)

theorem one_mul_coord (x : Biquadratic) : 1 * x = x :=
  coord_injective ((TameRationalField277.mul_comm (scalar 1) x.coord).trans
    (TameRationalField277.mul_one x.coord))

theorem mul_inv_coord (x : Biquadratic) (hx : x ≠ 0) : x * x⁻¹ = 1 :=
  coord_injective (biquad_mul_inverse x.coord (fun e => hx (coord_injective e)))

theorem inv_zero_coord : (0 : Biquadratic)⁻¹ = 0 := by decide +kernel

theorem zero_ne_one_coord : (0 : Biquadratic) ≠ 1 := by decide +kernel

instance biquadraticField : Field Biquadratic :=
  Field.ofMinimalAxioms Biquadratic
    (fun x y z => coord_injective (add_group_laws x.coord y.coord z.coord).1)
    zero_add_coord neg_add_coord
    (fun x y z => coord_injective (TameRationalField277.mul_assoc x.coord y.coord z.coord))
    (fun x y => coord_injective (TameRationalField277.mul_comm x.coord y.coord))
    one_mul_coord mul_inv_coord inv_zero_coord
    (fun x y z => coord_injective (distributive x.coord y.coord z.coord))
    ⟨0,1,zero_ne_one_coord⟩

def coefficientHom : ℚ →+* Biquadratic where
  toFun a := ⟨scalar a⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := coord_injective (scalar_embedding a b).2.1.symm
  map_mul' a b := coord_injective (scalar_embedding a b).2.2.symm

theorem coefficientHom_injective : Function.Injective coefficientHom :=
  fun {a b} h => (scalar_embedding a b).1.mp (congrArg Biquadratic.coord h)

instance biquadraticCharZero : CharZero Biquadratic where
  cast_injective m n h := CharZero.cast_injective (R := ℚ)
    (coefficientHom_injective (by simpa only [map_natCast] using h))

theorem coefficientHom_apply (r : ℚ) : algebraMap ℚ Biquadratic r = ⟨scalar r⟩ :=
  DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ Biquadratic) coefficientHom) r

variable (K : Type) [Field K] [Algebra ℚ K]

def coefficients : RatMap K where
  app := algebraMap ℚ K
  zero := map_zero _
  one := map_one _
  add := map_add _
  mul := map_mul _
  sub := map_sub _

variable {K}

def toCoordinateMap (g : Biquadratic →ₐ[ℚ] K) : OverRat (coefficients K) where
  app x := g ⟨x⟩
  onScalar r := (congrArg g (coefficientHom_apply r).symm).trans (g.commutes r)
  onAdd x y := g.map_add ⟨x⟩ ⟨y⟩
  onMul x y := g.map_mul ⟨x⟩ ⟨y⟩

def toAlgHom (h : OverRat (coefficients K)) : Biquadratic →ₐ[ℚ] K where
  toFun x := h.app x.coord
  map_zero' := (h.onScalar 0).trans (coefficients K).zero
  map_one' := (h.onScalar 1).trans (coefficients K).one
  map_add' x y := h.onAdd x.coord y.coord
  map_mul' x y := h.onMul x.coord y.coord
  commutes' r := by rw [coefficientHom_apply]; exact h.onScalar r

theorem toAlgHom_toCoordinateMap (g : Biquadratic →ₐ[ℚ] K) :
    toAlgHom (toCoordinateMap g) = g := by
  apply AlgHom.ext
  intro x
  rfl

theorem toCoordinateMap_toAlgHom (h : OverRat (coefficients K)) :
    toCoordinateMap (toAlgHom h) = h := by
  apply algebra_map_ext <;> rfl

end Reimann.TameBiquadraticField277
