import Reimann.DyadicBasisComparison
import Reimann.DyadicTraceOrder
import Reimann.TameRationalField277

/-! The trace of the rational field Q(√−3,√−23), evaluated on the dyadic
order with e=(1+√−3)/2 and w=(1+√−23)/2. -/

namespace Reimann.DyadicFieldTrace69

open Lean.Grind Reimann.Dyadic Reimann.DyadicTraceOrder
open Reimann.TameRationalField277 Reimann.DyadicBasisComparison

def half : Rat := 1/2

theorem twice_half : 2*half = 1 := by
  rw [Rat.mul_comm]
  exact Rat.div_mul_cancel (by decide : (2 : Rat) ≠ 0)

/-- The value of a+be+cw+dew in the radical basis of the field. -/
def embed (x : Matrix) : Biquad :=
  fromIntegral half (((x.a : Rat),(x.b : Rat)),((x.c : Rat),(x.d : Rat)))

theorem recover_coordinates (x : Matrix) :
    toIntegral (embed x) = (((x.a : Rat),(x.b : Rat)),((x.c : Rat),(x.d : Rat))) :=
  (inverses_at_odd_prime half twice_half _).2

theorem embed_injective {x y : Matrix} (h : embed x = embed y) : x=y := by
  have he := congrArg toIntegral h
  rw [recover_coordinates,recover_coordinates] at he
  cases x; cases y
  simp_all [Matrix.mk.injEq]

/-- Trace of left multiplication in the field basis (1,√−3,√−23,√69). -/
def regularTrace (z : Biquad) : Rat :=
  (bm z (scalar 1)).1.1 + (bm z gen3).1.2 + (bm z gen23).2.1 +
    (bm z (bm gen3 gen23)).2.2

theorem regularTrace_formula (z : Biquad) : regularTrace z = 4*z.1.1 := by
  simp only [regularTrace,scalar,gen3,gen23,bm,qa,qs,qm]
  grind

theorem embed_scale (m : Int) (x : Matrix) :
    embed (scale m x) = bm (scalar (m : Rat)) (embed x) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [embed,scale,fromIntegral,bm,scalar,qa,qm,qs,Ring.intCast_mul] <;> grind

def basisE : Biquad := ((half,half),(0,0))

def basisW : Biquad := ((half,0),(half,0))

theorem doubled_generators :
    ba basisE basisE = ba (scalar 1) gen3 ∧ ba basisW basisW = ba (scalar 1) gen23 := by
  have h := twice_half
  constructor <;> apply Prod.ext <;> apply Prod.ext <;>
    simp only [ba,basisE,basisW,scalar,gen3,gen23,qa] <;> grind

theorem embed_timesE (x : Matrix) : embed (timesE 1 x) = bm basisE (embed x) := by
  have h := twice_half
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [embed,fromIntegral,timesE,basisE,bm,qa,qm,qs,
      Ring.intCast_neg,Ring.intCast_add,Ring.intCast_mul,Ring.intCast_one] <;> grind

theorem embed_timesW (x : Matrix) : embed (timesW 6 x) = bm basisW (embed x) := by
  have h := twice_half
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [embed,fromIntegral,timesW,basisW,bm,qa,qm,qs,
      Ring.intCast_neg,Ring.intCast_add,Ring.intCast_mul] <;> grind

theorem embed_add (x y : Matrix) :
    embed ⟨x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d⟩ = ba (embed x) (embed y) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [embed,fromIntegral,ba,qa,Ring.intCast_add] <;> grind

theorem field_trace_embed (x : Matrix) :
    regularTrace (embed x) = (trace 1 6 x : Rat) := by
  have h := twice_half
  rw [regularTrace_formula,trace_formula]
  simp only [embed,fromIntegral,Ring.intCast_add,Ring.intCast_mul]
  grind

/-- Four rational-valued field traces against the specified integral basis. -/
def fieldPairings (z : Biquad) : Biquad :=
  ((regularTrace z,regularTrace (bm basisE z)),
   (regularTrace (bm basisW z),regularTrace (bm basisW (bm basisE z))))

theorem field_pairings_embed (x : Matrix) :
    fieldPairings (embed x) =
      let t := pairings 1 6 x
      (((t.a : Rat),(t.b : Rat)),((t.c : Rat),(t.d : Rat))) := by
  simp only [fieldPairings,← embed_timesE,← embed_timesW,field_trace_embed,pairings]

/-- Change the signs of the two independent radicals. -/
def conjugate (s t : Rat) (x : Biquad) : Biquad :=
  ((x.1.1,s*x.1.2),(t*x.2.1,(s*t)*x.2.2))

theorem conjugate_multiply (s t : Rat) (hs : s*s=1) (ht : t*t=1) (x y : Biquad) :
    conjugate s t (bm x y) = bm (conjugate s t x) (conjugate s t y) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [conjugate,bm,qa,qm,qs] <;> grind

theorem conjugate_involution (s t : Rat) (hs : s*s=1) (ht : t*t=1) (x : Biquad) :
    conjugate s t (conjugate s t x) = x := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [conjugate] <;> grind

theorem trace_as_conjugate_sum (x : Biquad) :
    ba (ba (conjugate 1 1 x) (conjugate (-1) 1 x))
      (ba (conjugate 1 (-1) x) (conjugate (-1) (-1) x)) = scalar (regularTrace x) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [regularTrace_formula,conjugate,ba,qa,scalar] <;> grind

theorem field_pairings_scale (s : Rat) (x : Biquad) :
    fieldPairings (bm (scalar s) x) = bm (scalar s) (fieldPairings x) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [fieldPairings,regularTrace_formula,bm,scalar,basisE,basisW,qa,qm,qs] <;> grind

theorem cancel_field_scalar (m : Int) (hm : m ≠ 0) (x y : Biquad)
    (he : bm (scalar (m : Rat)) x = bm (scalar (m : Rat)) y) : x=y := by
  have hn : (m : Rat) ≠ 0 := fun h => hm (Rat.intCast_inj.mp
    (show (m : Rat) = ((0 : Int) : Rat) from h))
  have h' := congrArg (bm (scalar (m : Rat)⁻¹)) he
  rw [← mul_assoc,← mul_assoc,(scalar_embedding _ _).2.2,Rat.inv_mul_cancel _ hn] at h'
  rw [mul_comm (scalar 1) x,mul_comm (scalar 1) y] at h'
  exact (mul_one x).symm.trans (h'.trans (mul_one y))

/-- If m*y is the integral numerator x and the four field traces of y
are integers t, then the numerator's four pairings are exactly m*t. -/
theorem field_trace_denominator (m : Int) (y : Biquad) (x t : Matrix)
    (hn : bm (scalar (m : Rat)) y = embed x)
    (ht : fieldPairings y = (((t.a : Rat),(t.b : Rat)),((t.c : Rat),(t.d : Rat)))) :
    pairings 1 6 x = scale m t := by
  have he := congrArg fieldPairings hn
  rw [field_pairings_scale,ht,field_pairings_embed] at he
  simp only [bm,scalar,qa,qm,qs] at he
  rcases hX : pairings 1 6 x with ⟨a,b,c,d⟩
  rw [hX] at he
  simp only [Prod.mk.injEq] at he
  simp only [scale,Matrix.mk.injEq]
  repeat' apply And.intro
  all_goals apply Rat.intCast_inj.mp; simp only [Ring.intCast_mul]; grind

/-- In the field itself, an element with dyadic denominator and integral
traces against all four basis elements belongs to the embedded order. -/
theorem field_trace_saturation (n : Nat) (y : Biquad) (x t : Matrix)
    (hn : bm (scalar (twoPower n : Rat)) y = embed x)
    (ht : fieldPairings y = (((t.a : Rat),(t.b : Rat)),((t.c : Rat),(t.d : Rat)))) :
    ∃ z : Matrix, y = embed z := by
  have hp := field_trace_denominator (twoPower n) y x t hn ht
  have hx := (trace_integral_iff 1 6 n x).mp ((coordinates_divisible _ _).mpr ⟨t,hp⟩)
  obtain ⟨z,hz⟩ := (coordinates_divisible _ _).mp hx
  have pos : ∀ j, 0 < twoPower j := by
    intro j; induction j with
    | zero => decide
    | succ j ih => unfold twoPower; omega
  exact ⟨z,cancel_field_scalar _ (by have := pos n; omega) _ _
    (hn.trans ((congrArg embed hz).trans (embed_scale _ z)))⟩

end Reimann.DyadicFieldTrace69
