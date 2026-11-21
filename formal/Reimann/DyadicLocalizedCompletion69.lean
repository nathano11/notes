import Reimann.DyadicLocalizedPrimes69

/-! Quotients modulo 2^(n+1) of the odd-denominator half-basis order in
Q(√−3,√−23). A representative p/d reduces as the four coefficients of p
multiplied by the inverse of d modulo 2^(n+1). -/

namespace Reimann.DyadicLocalizedCompletion69

open Reimann.Dyadic Reimann.DyadicOrderCompletion69 Reimann.DyadicFieldTrace69
open Reimann.TameRationalField277
open Reimann.TameBiquadratic277 (Quad componentAdd)
open Reimann.DyadicLocalizedPrimes69 (Represents cross_clear)

def Local (z : Biquad) : Prop := ∃ k : Int, ∃ p : Matrix, Represents z k p

def wordScale {n : Nat} (v : BitVec (n+1)) (x : Quad (BitVec (n+1))) : Quad (BitVec (n+1)) :=
  mapFour (fun t => v*t) x

theorem scale_reduction (n : Nat) (v : Int) (p : Matrix) :
    integerReduction n (scale v p) = wordScale (BitVec.ofInt (n+1) v) (integerReduction n p) := by
  simp only [integerReduction,mapFour,coords,scale,wordScale,BitVec.ofInt_mul]

theorem odd_word_unit (n : Nat) (k : Int) :
    ∃ v : BitVec (n+1), BitVec.ofInt (n+1) (1+2*k) * v = 1 := by
  apply DyadicLattice.unit_at_precision
  have h := congrArg BitVec.toNat (truncate_signed (i:=0) (j:=n) (Nat.zero_le _) (1+2*k))
  have ho : BitVec.ofInt 1 (1+2*k) = 1 := by rw [BitVec.ofInt_add,BitVec.ofInt_mul]; change 1+0*_=1; simp
  rw [ho] at h
  simpa [BitVec.toNat_setWidth] using h

theorem word_scale_assoc {n : Nat} (a b : BitVec (n+1)) (x : Quad (BitVec (n+1))) :
    wordScale a (wordScale b x) = wordScale (a*b) x := by
  simp [wordScale,mapFour,BitVec.mul_assoc]

theorem word_scale_one {n : Nat} (x : Quad (BitVec (n+1))) : wordScale 1 x = x := by
  simp [wordScale,mapFour]

theorem word_scale_cancel {n : Nat} (k : Int) {x y : Quad (BitVec (n+1))}
    (h : wordScale (BitVec.ofInt (n+1) (1+2*k)) x = wordScale (BitVec.ofInt (n+1) (1+2*k)) y) :
    x=y := by
  obtain ⟨v,hv⟩ := odd_word_unit n k
  have e := congrArg (wordScale v) h
  rwa [word_scale_assoc,word_scale_assoc,BitVec.mul_comm v,hv,word_scale_one,word_scale_one] at e

/-- A candidate quotient vector whose denominator d clears to p at this precision. -/
def ScalesTo (n : Nat) (k : Int) (p : Matrix) (v : Quad (BitVec (n+1))) : Prop :=
  wordScale (BitVec.ofInt (n+1) (1+2*k)) v = integerReduction n p

theorem scaled_witness (n : Nat) (k : Int) (p : Matrix) :
    ∃ v : Quad (BitVec (n+1)), ScalesTo n k p v := by
  obtain ⟨u,hu⟩ := odd_word_unit n k
  exact ⟨wordScale u (integerReduction n p),by unfold ScalesTo; rw [word_scale_assoc,hu,word_scale_one]⟩

theorem scales_change_rep {z : Biquad} {k l : Int} {p q : Matrix} {n : Nat}
    (hp : Represents z k p) (hq : Represents z l q) {v : Quad (BitVec (n+1))}
    (hv : ScalesTo n k p v) : ScalesTo n l q v := by
  apply word_scale_cancel k
  have he := congrArg (integerReduction n) (cross_clear hp hq)
  rw [scale_reduction,scale_reduction] at he
  rw [← hv] at he
  rw [word_scale_assoc,BitVec.mul_comm,← word_scale_assoc] at he
  exact he

theorem all_representatives (n : Nat) {z : Biquad} (h : Local z) :
    ∃ v : Quad (BitVec (n+1)), ∀ k p, Represents z k p → ScalesTo n k p v := by
  obtain ⟨k,p,hp⟩ := h
  obtain ⟨v,hv⟩ := scaled_witness n k p
  exact ⟨v, fun _ _ hq => scales_change_rep hp hq hv⟩

noncomputable def level (n : Nat) (z : {x : Biquad // Local x}) : Quad (BitVec (n+1)) :=
  Classical.choose (all_representatives n z.property)

theorem level_spec (n : Nat) (z : {x : Biquad // Local x}) {k : Int} {p : Matrix}
    (hp : Represents z.val k p) : ScalesTo n k p (level n z) :=
  Classical.choose_spec (all_representatives n z.property) k p hp

theorem level_unique (n : Nat) (z : {x : Biquad // Local x}) {k : Int} {p : Matrix}
    (hp : Represents z.val k p) {v : Quad (BitVec (n+1))} (hv : ScalesTo n k p v) :
    level n z = v := word_scale_cancel k ((level_spec n z hp).trans hv.symm)

def orderPoint (p : Matrix) : {x : Biquad // Local x} :=
  ⟨embed p,0,p,DyadicLocalizedPrimes69.represents_self p⟩

theorem level_orderPoint (n : Nat) (p : Matrix) :
    level n (orderPoint p) = integerReduction n p := by
  apply level_unique n (orderPoint p) (DyadicLocalizedPrimes69.represents_self p)
  exact word_scale_one _

theorem level_surjective (n : Nat) (v : Quad (BitVec (n+1))) :
    ∃ p : Matrix, level n (orderPoint p) = v := by
  obtain ⟨p,hp⟩ := integer_reduction_surjective n v
  exact ⟨p,(level_orderPoint n p).trans hp⟩

theorem level_compatible (z : {x : Biquad // Local x}) {i j : Nat} (h : i ≤ j) :
    mapFour (BitVec.setWidth (i+1)) (level j z) = level i z := by
  obtain ⟨k,p,hp⟩ := z.property
  apply Eq.symm
  apply level_unique i z hp
  have e := congrArg (mapFour (BitVec.setWidth (i+1))) (level_spec j z hp)
  simpa only [ScalesTo,wordScale,integerReduction,mapFour,BitVec.setWidth_mul _ _ (by omega : i+1 ≤ j+1),
    truncate_signed h] using e

noncomputable def completedPoint (z : {x : Biquad // Local x}) : Completion :=
  ⟨fun n => level n z, fun h => level_compatible z h⟩

def fraction (k : Int) (p : Matrix) : Biquad :=
  bm (scalar (((1+2*k : Int) : Rat)⁻¹)) (embed p)

theorem fraction_represents (k : Int) (p : Matrix) : Represents (fraction k p) k p := by
  have h : (1+2*k : Int) ≠ 0 := by omega
  have hn : (((1+2*k : Int) : Rat)) ≠ 0 := fun hz => h (Rat.intCast_inj.mp
    (show ((1+2*k : Int) : Rat) = ((0:Int):Rat) from hz))
  unfold Represents fraction
  rw [← mul_assoc,(scalar_embedding _ _).2.2,Rat.mul_inv_cancel _ hn,mul_comm (scalar 1)]
  exact (mul_one _).symm

theorem commute_scalars (a b : Rat) (z : Biquad) :
    bm (scalar a) (bm (scalar b) z) = bm (scalar b) (bm (scalar a) z) := by
  rw [← mul_assoc,mul_comm (scalar a) (scalar b),mul_assoc]

theorem common_representatives {x y : Biquad} {k l : Int} {p q : Matrix}
    (hp : Represents x k p) (hq : Represents y l q) :
    Represents x (k+l+2*k*l) (scale (1+2*l) p) ∧
    Represents y (k+l+2*k*l) (scale (1+2*k) q) := by
  unfold Represents
  rw [embed_scale,embed_scale,hp,hq,DyadicLocalizedPrimes69.odd_product,mul_assoc]
  exact ⟨commute_scalars _ _ _, (mul_assoc _ _ _).symm⟩

theorem level_eq_common_iff (n : Nat) (x y : Subtype Local) {k : Int} {p q : Matrix}
    (hp : Represents x.val k p) (hq : Represents y.val k q) :
    level n x = level n y ↔ integerReduction n p = integerReduction n q := by
  have hx := level_spec n x hp
  have hy := level_spec n y hq
  unfold ScalesTo at hx hy
  rw [← hx,← hy]
  exact ⟨congrArg _,word_scale_cancel k⟩

theorem translate_fraction {x y : Biquad} {k : Int} {p q t : Matrix} (m : Int)
    (hp : Represents x k p) (hq : Represents y k q) (he : p = integerSum q (scale m t)) :
    x = ba y (bm (scalar (m:Rat)) (fraction k t)) := by
  have hf := fraction_represents k t
  unfold Represents at hp hq hf
  apply cancel_field_scalar (1+2*k) (by omega)
  rw [← hp,distributive,← hq,commute_scalars _ (m:Rat),← hf]
  rw [he,embed_integerSum,embed_scale]

theorem cross_translation {x y z : Biquad} {k l : Int} {p q r : Matrix} (m : Int)
    (hp : Represents x k p) (hq : Represents y k q) (hr : Represents z l r)
    (he : x = ba y (bm (scalar (m:Rat)) z)) :
    scale (1+2*l) p = integerSum (scale (1+2*l) q) (scale m (scale (1+2*k) r)) := by
  apply embed_injective
  unfold Represents at hp hq hr
  simp only [embed_integerSum,embed_scale,hp,hq,hr,he,distributive]
  apply Prod.ext <;> apply Prod.ext <;> simp only [ba,bm,scalar,qa,qm,qs] <;> grind

/-- This is equality in the actual field. The difference divided by 2^(n+1)
again belongs to the same odd-denominator order. -/
theorem level_eq_iff_two_power_difference (n : Nat) (x y : Subtype Local) :
    level n x = level n y ↔ ∃ t : Subtype Local,
      x.val = ba y.val (bm (scalar ((((2:Int)^(n+1) : Int)) : Rat)) t.val) := by
  obtain ⟨kx,px,hx⟩ := x.property
  obtain ⟨ky,py,hy⟩ := y.property
  obtain ⟨hp,hq⟩ := common_representatives hx hy
  rw [level_eq_common_iff n x y hp hq]
  constructor
  · intro hr
    obtain ⟨u,hu⟩ := (integer_reduction_eq_iff n _ _).mp hr
    exact ⟨⟨fraction (kx+ky+2*kx*ky) u,_,u,fraction_represents _ u⟩, translate_fraction _ hp hq hu⟩
  · rintro ⟨t,he⟩
    obtain ⟨l,r,ht⟩ := t.property
    have h := cross_translation ((2:Int)^(n+1)) hp hq ht he
    have hn := (integer_reduction_eq_iff n _ _).mpr ⟨_,h⟩
    rw [scale_reduction n (1+2*l),scale_reduction n (1+2*l)] at hn
    exact word_scale_cancel l hn

end Reimann.DyadicLocalizedCompletion69
