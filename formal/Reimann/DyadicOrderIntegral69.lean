import Reimann.DyadicOrderCompletion69
import Reimann.DyadicIntegralCriterion69

/-! The monic quartic of a+be+cw+dew, where e²=e−1 and w²=w−6.
Its coefficients are two successive quadratic norms of the linear polynomial. -/

namespace Reimann.DyadicOrderIntegral69

open Lean.Grind
open Reimann.Dyadic (Matrix)

/-- Product of two elements of Z[e] in the basis 1,e. -/
abbrev quadraticProduct := @DyadicOrderCompletion69.pairProduct Int _

/-- The trace of A+Bw relative to Q(e) is 2A+B. -/
def relativeTrace (x : Matrix) : Int × Int := (2*x.a+x.c, 2*x.b+x.d)

/-- The relative norm of A+Bw is A²+AB+6B². -/
def relativeNorm (x : Matrix) : Int × Int :=
  let A := (x.a,x.b)
  let B := (x.c,x.d)
  let AA := quadraticProduct A A
  let AB := quadraticProduct A B
  let BB := quadraticProduct B B
  (AA.1 + AB.1 + 6*BB.1, AA.2 + AB.2 + 6*BB.2)

/-- Low to high coefficients of N(T²−tT+n), with leading coefficient 1. -/
def normQuartic (t n : Int × Int) : Matrix :=
  ⟨n.1*n.1+n.1*n.2+n.2*n.2,
   -(2*t.1*n.1+t.1*n.2+t.2*n.1+2*t.2*n.2),
   t.1*t.1+t.1*t.2+t.2*t.2+2*n.1+n.2,
   -(2*t.1+t.2)⟩

/-- Over Z[e], N(A+Be)=A²+AB+B². Applied to A=T²−t₀T+n₀ and
B=−t₁T+n₁, its four integer coefficients are those of normQuartic. -/
theorem norm_polynomial_identity (t n : Int × Int) (z : Int) :
    let p := normQuartic t n
    let A := z*z-t.1*z+n.1
    let B := -t.2*z+n.2
    z*(z*(z*(z+p.d)+p.c)+p.b)+p.a = A*A+A*B+B*B := by
  simp only [normQuartic]
  grind

open Reimann.DyadicOrderCompletion69

def quadraticValue (v : Int × Int) : Matrix := ⟨v.1,v.2,0,0⟩

/-- The relative polynomial T²−Tr(T)T+N(T) vanishes in the actual tensor order. -/
theorem relative_quadratic_equation (x : Matrix) :
    integerSum (integerProduct x x) (quadraticValue (relativeNorm x)) =
      integerProduct x (quadraticValue (relativeTrace x)) := by
  simp only [relativeTrace,relativeNorm,quadraticValue,quadraticProduct,integerSum,integerProduct,
    fromCoords,coords,TameBiquadratic277.componentAdd,product,pairProduct,Matrix.mk.injEq]
  grind

def integerMonicAt (x : Matrix) : List Int → Matrix
  | [] => ⟨1,0,0,0⟩
  | a :: chain => integerSum (integerProduct x (integerMonicAt x chain)) ⟨a,0,0,0⟩

def quarticCoefficients (x : Matrix) : List Int :=
  let p := normQuartic (relativeTrace x) (relativeNorm x)
  [p.a,p.b,p.c,p.d]

theorem quartic_length (x : Matrix) : (quarticCoefficients x).length = 4 := rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem quartic_annihilates_coordinates (x : Matrix) :
    integerMonicAt x (quarticCoefficients x) = ⟨0,0,0,0⟩ := by
  simp only [integerMonicAt,quarticCoefficients,normQuartic,relativeTrace,relativeNorm,
    quadraticProduct,integerSum,integerProduct,fromCoords,coords,TameBiquadratic277.componentAdd,
    product,pairProduct,Matrix.mk.injEq]
  grind

open Reimann.DyadicFieldTrace69 (embed)
open Reimann.TameRationalField277 (scalar)
open Reimann.DyadicIntegralCriterion69 (monicAt IsIntegral)

/-- The cubic coefficient is minus the trace computed in the rational field. -/
theorem cubic_coefficient_is_negative_trace (x : Matrix) :
    ((normQuartic (relativeTrace x) (relativeNorm x)).d : Rat) =
      -DyadicFieldTrace69.regularTrace (embed x) := by
  rw [DyadicFieldTrace69.field_trace_embed, DyadicTraceOrder.trace_formula]
  simp only [normQuartic,relativeTrace,Rat.intCast_neg,Rat.intCast_add,Rat.intCast_mul]
  grind

theorem embed_integer_scalar (c : Int) : embed ⟨c,0,0,0⟩ = scalar (c : Rat) := by
  simp [embed, DyadicBasisComparison.fromIntegral, scalar] <;> grind

/-- Horner evaluation commutes with the half-integral basis embedding at
every degree. Coefficients run from the constant term to the leading term. -/
theorem monicAt_embed (x : Matrix) (coeff : List Int) :
    monicAt (embed x) coeff = embed (integerMonicAt x coeff) := by
  induction coeff with
  | nil => exact (embed_integer_scalar 1).symm
  | cons c cs ih =>
    simp only [monicAt, integerMonicAt, embed_integerSum, embed_integerProduct, embed_integer_scalar, ih]

theorem quartic_annihilates_embed (x : Matrix) :
    monicAt (embed x) (quarticCoefficients x) = scalar 0 := by
  rw [monicAt_embed,quartic_annihilates_coordinates]
  exact embed_integer_scalar 0

theorem order_is_integral (x : Matrix) : IsIntegral (embed x) :=
  ⟨quarticCoefficients x, quartic_annihilates_embed x⟩

end Reimann.DyadicOrderIntegral69
