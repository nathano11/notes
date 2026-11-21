import Reimann.TameLocalOrders277
import Reimann.TameRationalField277

namespace Reimann.TameOrderFaithful277

open Lean.Grind

open Reimann.TameBiquadratic277 Reimann.TameArithmetic277
open Reimann.TameLimit277 Reimann.TameOrderCompletion277 Reimann.TameLocalOrders277

def rationalize (v : OrderCoordinates) : TameRationalField277.Biquad :=
  (((v.1.1 : Rat),(v.1.2 : Rat)),((v.2.1 : Rat),(v.2.2 : Rat)))

theorem rationalize_nonzero (v : OrderCoordinates) (hv : v ≠ integerCoordinates 0) :
    rationalize v ≠ ((0,0),(0,0)) := by
  intro h
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [rationalize] at h
  exact hv (by simp [integerCoordinates,h.1.1,h.1.2,h.2.1,h.2.2])

/-- Relative norm from the biquadratic order to Z[X]/(X²+3). -/
def relative (v : OrderCoordinates) : Int × Int :=
  let ((a,b),(c,d)) := v
  (a*a-3*b*b+23*(c*c-3*d*d), 2*a*b+46*c*d)

def absolute (v : OrderCoordinates) : Int :=
  let (e,f) := relative v
  e*e+3*f*f

theorem relative_to_rational (v : OrderCoordinates) :
    (((relative v).1 : Rat),((relative v).2 : Rat)) =
      TameRationalField277.relativeNorm (rationalize v) := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  apply Prod.ext <;> simp only [relative,TameRationalField277.relativeNorm,
    TameRationalField277.qa,TameRationalField277.qm,TameRationalField277.qs,rationalize,
    Ring.intCast_add,Ring.intCast_mul,Ring.intCast_sub] <;> grind

theorem absolute_nonzero (v : OrderCoordinates) (hv : v ≠ integerCoordinates 0) :
    absolute v ≠ 0 := by
  have h := TameRationalField277.quad_norm_nonzero _
    (TameRationalField277.norm_nonzero _ (rationalize_nonzero v hv))
  rw [← relative_to_rational] at h
  intro hz
  apply h
  have he := congrArg (fun x : Int => (x : Rat)) hz
  change ((((relative v).1*(relative v).1+3*(relative v).2*(relative v).2 : Int) : Rat)) = _ at he
  simp only [Ring.intCast_add,Ring.intCast_mul] at he
  grind

/-- The adjugate at v: the other Y-conjugate times the X-conjugate relative norm. -/
def cofactor (v : OrderCoordinates) : OrderCoordinates :=
  product (-3) (-23) (v.1,(-v.2.1,-v.2.2)) (((relative v).1,-(relative v).2),(0,0))

theorem product_cofactor (v : OrderCoordinates) :
    product (-3) (-23) v (cofactor v) = integerCoordinates (absolute v) := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [cofactor,product,absolute,relative,integerCoordinates] <;> grind

/-- The image of the integral order in the selected 277-adic integers. -/
def orderImage (sx sy : Bool) (v : OrderCoordinates) : Integer277 :=
  toInteger (evaluation sx sy) (ofOrder (evaluation sx sy) v)

theorem orderImage_residue (sx sy : Bool) (v : OrderCoordinates) (n : Nat) :
    (orderImage sx sy v).residue n = branchEval sx sy n v % modulus n := rfl

theorem orderImage_integer (sx sy : Bool) (z : Int) :
    orderImage sx sy (integerCoordinates z) = ofInt z := by
  apply equal_of_residues
  intro n
  rw [orderImage_residue,branchEval_integer]
  rfl

theorem orderImage_product (sx sy : Bool) (u v : OrderCoordinates) :
    orderImage sx sy (product (-3) (-23) u v) =
      mul (orderImage sx sy u) (orderImage sx sy v) := by
  apply equal_of_residues
  intro n
  change branchEval sx sy n (product (-3) (-23) u v) % modulus n =
    ((branchEval sx sy n u % modulus n)*(branchEval sx sy n v % modulus n)) % modulus n
  rw [evaluation_product,Int.mul_emod]

theorem zero_times (v : Integer277) : mul (ofInt 0) v = ofInt 0 := by
  apply equal_of_residues
  intro n
  change ((0 % modulus n)*v.residue n) % modulus n = 0 % modulus n
  simp

theorem orderImage_zero_kernel (sx sy : Bool) (v : OrderCoordinates)
    (h : orderImage sx sy v = ofInt 0) : v = integerCoordinates 0 := by
  by_cases hv : v = integerCoordinates 0
  · exact hv
  · have hn := absolute_nonzero v hv
    have hi : ofInt (absolute v) = ofInt 0 := by
      rw [← orderImage_integer sx sy, ← product_cofactor,orderImage_product,h,zero_times]
    exact (hn (ofInt_injective hi)).elim

def difference (v w : OrderCoordinates) : OrderCoordinates :=
  ((v.1.1-w.1.1,v.1.2-w.1.2),(v.2.1-w.2.1,v.2.2-w.2.2))

theorem branch_difference (sx sy : Bool) (n : Nat) (v w : OrderCoordinates) :
    branchEval sx sy n (difference v w) = branchEval sx sy n v - branchEval sx sy n w := by
  simp only [branchEval,evalAt,difference]
  grind

/-- All four embeddings are faithful on the original integral order. -/
theorem orderImage_injective (sx sy : Bool) {v w : OrderCoordinates}
    (h : orderImage sx sy v = orderImage sx sy w) : v = w := by
  have hz : orderImage sx sy (difference v w) = ofInt 0 := by
    apply equal_of_residues
    intro n
    have he := congrArg (fun a : Integer277 => a.residue n) h
    simp only [orderImage_residue] at he
    rw [orderImage_residue,branch_difference,Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he]
    simp [ofInt,ofCompatible]
  have hd := orderImage_zero_kernel sx sy _ hz
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases w with ⟨⟨e,f⟩,⟨g,h'⟩⟩
  simp only [difference,integerCoordinates,Prod.mk.injEq] at hd ⊢
  omega

end Reimann.TameOrderFaithful277
