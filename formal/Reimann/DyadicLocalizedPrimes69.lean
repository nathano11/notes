import Reimann.DyadicFieldTrace69
import Reimann.DyadicOrderCompletion69
import Reimann.DyadicFiberDescent

/-! Odd-denominator reduction from the rational field to the dyadic residue fiber. -/

namespace Reimann.DyadicLocalizedPrimes69

open Reimann.Dyadic Reimann.DyadicFieldTrace69 Reimann.TameRationalField277
open Reimann.DyadicFiberPrimes (Fiber)
open Reimann.DyadicOrderCompletion69 (integerSum integerProduct)

/-- Both linear factors of w²−w modulo two, in (1,e) coordinates. -/
def fiber (p : Matrix) : Fiber :=
  ((BitVec.ofInt 1 p.a, BitVec.ofInt 1 p.b),
    (BitVec.ofInt 1 (p.a+p.c), BitVec.ofInt 1 (p.b+p.d)))

theorem fiber_odd_scale (k : Int) (p : Matrix) : fiber (scale (1+2*k) p) = fiber p := by
  have h : BitVec.ofInt 1 (1+2*k) = 1 := by
    rw [BitVec.ofInt_add,BitVec.ofInt_mul]; change 1+0*_=1; simp
  apply Prod.ext <;> apply Prod.ext <;> simp only [fiber,scale,← Int.mul_add,BitVec.ofInt_mul,h] <;> grind

def Represents (z : Biquad) (k : Int) (p : Matrix) : Prop :=
  embed p = bm (scalar ((1+2*k : Int) : Rat)) z

/-- Equality in the field gives actual cross multiplication on numerators. -/
theorem cross_clear {z : Biquad} {k l : Int} {p q : Matrix}
    (hp : Represents z k p) (hq : Represents z l q) :
    scale (1+2*l) p = scale (1+2*k) q := by
  apply embed_injective
  rw [embed_scale,embed_scale,hp,hq,← mul_assoc,← mul_assoc,
    mul_comm (scalar ((1+2*l:Int) : Rat)) (scalar ((1+2*k:Int) : Rat))]

theorem same_reduction {z : Biquad} {k l : Int} {p q : Matrix}
    (hp : Represents z k p) (hq : Represents z l q) : fiber p = fiber q := by
  simpa only [fiber_odd_scale] using congrArg fiber (cross_clear hp hq)

/-- Reduction of an odd-denominator field element. -/
noncomputable def reduce (z : Biquad) (h : ∃ p : Matrix, ∃ k : Int, Represents z k p) : Fiber :=
  fiber (Classical.choose h)

theorem reduce_of_rep {z : Biquad} (h : ∃ p, ∃ k, Represents z k p) {k : Int} {p : Matrix}
    (hp : Represents z k p) : reduce z h = fiber p := by
  obtain ⟨l, hl⟩ := Classical.choose_spec h
  exact same_reduction hl hp

theorem bit_eq_iff (a b : Int) : BitVec.ofInt 1 a = BitVec.ofInt 1 b ↔ a%2=b%2 := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofInt]
  change (a%2).toNat = (b%2).toNat ↔ _
  omega

theorem fiber_eq_iff (p q : Matrix) :
    fiber p = fiber q ↔ p.a%2=q.a%2 ∧ p.b%2=q.b%2 ∧ p.c%2=q.c%2 ∧ p.d%2=q.d%2 := by
  simp only [fiber,Prod.mk.injEq,bit_eq_iff]
  omega

theorem fiber_zero_iff (p : Matrix) : fiber p = ((0,0),(0,0)) ↔
    2 ∣ p.a ∧ 2 ∣ p.b ∧ 2 ∣ p.c ∧ 2 ∣ p.d := by
  change fiber p = fiber ⟨0,0,0,0⟩ ↔ _
  rw [fiber_eq_iff]
  dsimp only
  omega

theorem fiber_add (p q : Matrix) :
    fiber (integerSum p q) = DyadicFiberPrimes.sum (fiber p) (fiber q) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [fiber,integerSum,DyadicOrderCompletion69.fromCoords,DyadicOrderCompletion69.coords,
      TameBiquadratic277.componentAdd,DyadicFiberPrimes.sum,DyadicInert.residueAdd,BitVec.ofInt_add] <;> grind

theorem fiber_mul (p q : Matrix) :
    fiber (integerProduct p q) = DyadicFiberPrimes.product (fiber p) (fiber q) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [fiber,integerProduct,DyadicOrderCompletion69.fromCoords,DyadicOrderCompletion69.coords,
      DyadicOrderCompletion69.product,DyadicOrderCompletion69.pairProduct,
      DyadicFiberPrimes.product,DyadicInert.residueProduct,Int.sub_eq_add_neg,BitVec.ofInt_neg,
      BitVec.sub_eq_add_neg,show BitVec.ofInt 1 6 = 0 by decide,
      BitVec.ofInt_add,BitVec.ofInt_mul] <;> grind

theorem odd_product (k l : Int) :
    scalar ((1+2*(k+l+2*k*l) : Int) : Rat) =
      bm (scalar ((1+2*k:Int) : Rat)) (scalar ((1+2*l:Int) : Rat)) := by
  rw [(scalar_embedding _ _).2.2]
  congr 1
  simp only [Rat.intCast_add,Rat.intCast_mul]
  grind

theorem represents_add {x y : Biquad} {k l : Int} {p q : Matrix}
    (hp : Represents x k p) (hq : Represents y l q) :
    Represents (ba x y) (k+l+2*k*l) (integerSum (scale (1+2*l) p) (scale (1+2*k) q)) := by
  unfold Represents
  rw [DyadicOrderCompletion69.embed_integerSum, embed_scale,embed_scale,hp,hq,odd_product,
    distributive,← mul_assoc,← mul_assoc,mul_comm (scalar ((1+2*l:Int) : Rat)) (scalar ((1+2*k:Int) : Rat))]

theorem represents_mul {x y : Biquad} {k l : Int} {p q : Matrix}
    (hp : Represents x k p) (hq : Represents y l q) :
    Represents (bm x y) (k+l+2*k*l) (integerProduct p q) := by
  unfold Represents
  rw [DyadicOrderCompletion69.embed_integerProduct,hp,hq,odd_product]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc,mul_comm x (scalar ((1+2*l:Int) : Rat)),mul_assoc]

theorem represents_self (p : Matrix) : Represents (embed p) 0 p := by
  change embed p = bm (scalar 1) (embed p)
  rw [mul_comm]
  exact (mul_one _).symm

theorem embed_integer (k : Int) : embed ⟨k,0,0,0⟩ = scalar (k:Rat) := by
  apply Prod.ext <;> apply Prod.ext <;> simp [embed,DyadicBasisComparison.fromIntegral,scalar] <;> grind

/-- A subring of the rational field containing the four-coordinate order,
and contained in its localization at all odd integers. -/
structure OverOrder (S : Biquad → Prop) : Prop where
  contains : ∀ p, S (embed p)
  add_mem : ∀ {x y}, S x → S y → S (ba x y)
  mul_mem : ∀ {x y}, S x → S y → S (bm x y)
  clear : ∀ {x}, S x → ∃ p, ∃ k, Represents x k p

theorem equal_fibers_translate (p q : Matrix) (h : fiber p = fiber q) :
    ∃ t, p = integerSum q (scale 2 t) := by
  obtain ⟨a,b,c,d⟩ := (fiber_eq_iff _ _).mp h
  refine ⟨⟨(p.a-q.a)/2,(p.b-q.b)/2,(p.c-q.c)/2,(p.d-q.d)/2⟩, ?_⟩
  cases p; cases q
  simp only [integerSum,DyadicOrderCompletion69.fromCoords,DyadicOrderCompletion69.coords,
    TameBiquadratic277.componentAdd,scale,Matrix.mk.injEq] at *
  omega

theorem fiber_surjective (w : Fiber) : ∃ p : Matrix, fiber p = w := by
  rcases w with ⟨⟨a,b⟩,c,d⟩
  refine ⟨⟨a.toNat,b.toNat,(c.toNat:Int)-a.toNat,(d.toNat:Int)-b.toNat⟩, ?_⟩
  revert a b c d
  decide

end Reimann.DyadicLocalizedPrimes69
