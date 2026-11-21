import Reimann.DyadicArithmetic69
import Reimann.DyadicDecomposition69

/-! Integral values at the two dyadic places of Q(√−3,√−23). We work
directly with elements of the embedded rational field and its localized
integer ring S. -/

namespace Reimann.DyadicBottomValue69

open Lean.Grind
open Reimann.TameRationalField277 Reimann.DyadicArithmetic69 Reimann.DyadicDecomposition69
open Reimann.DyadicFiberDescent (coordinateKernel)
open Reimann.DyadicFieldTrace69 (embed)
attribute [local instance] Ring.intCast

variable {F : Type} [Field F]

structure Embedding (F : Type) [Field F] where
  app : Biquad → F
  scalar_int : ∀ n : Int, app (scalar (n : Rat)) = (n : F)
  add : ∀ x y, app (ba x y)=app x+app y
  mul : ∀ x y, app (bm x y)=app x*app y
  faithful : ∀ x, app x=0 → x=scalar 0

structure Centered (f : Embedding F) (V : DyadicValue F) (i : Bool) : Prop where
  nonneg : ∀ x : LocalIntegers, 0 ≤ V.val (f.app x.val)
  center : ∀ x : LocalIntegers, coordinateKernel residueMap i x ↔
    f.app x.val=0 ∨ 0<V.val (f.app x.val)

theorem other_generator_outside (i : Bool) :
    ¬ coordinateKernel residueMap i (primeGenerator (!i)) := by
  unfold coordinateKernel
  rw [generator_residue]
  cases i <;> change ¬ ((1,0) : BitVec 1 × BitVec 1) = (0,0) <;> decide

theorem generator_pair_product (i : Bool) :
    bm (primeGenerator (!i)).val (primeGenerator i).val = scalar 6 := by
  have h := DyadicFieldTrace69.twice_half
  cases i <;> apply Prod.ext <;> apply Prod.ext <;>
    simp only [primeGenerator,Bool.not_true,Bool.not_false,ite_true,ite_false,
      DyadicFieldTrace69.embed,DyadicBasisComparison.fromIntegral,bm,qm,qa,qs,scalar] <;> grind

theorem other_generator_value (f : Embedding F) (V : DyadicValue F) (i : Bool)
    (h : Centered f V i) :
    f.app (primeGenerator (!i)).val ≠ 0 ∧ V.val (f.app (primeGenerator (!i)).val)=0 := by
  have hk := other_generator_outside i
  have hr := fun hz => hk ((h.center (primeGenerator (!i))).mpr hz)
  have nn := h.nonneg (primeGenerator (!i))
  exact ⟨fun e => hr (.inl e),by grind⟩

/-- β is the generator at the other prime. Its product with the selected
generator is 6, allowing one factor of 2 to be removed inside S. -/
theorem step_in_order (i : Bool) (x : LocalIntegers) (hx : coordinateKernel residueMap i x) :
    ∃ y : LocalIntegers, bm (primeGenerator (!i)).val x.val = bm (scalar 2) y.val := by
  obtain ⟨u,v,he⟩ := (prime_generated_by_two_and_root i x).mp hx
  have ex : x.val = ba (bm (primeGenerator i).val u.val) (bm (scalar 2) v.val) :=
    congrArg Subtype.val he
  let β := (primeGenerator (!i)).val
  let three : LocalIntegers := ⟨scalar 3,DyadicPrimeClassification69.scalar_mem localized_integer_order 3⟩
  let y := residueMap.add (residueMap.mul three u) (residueMap.mul (primeGenerator (!i)) v)
  refine ⟨y,?_⟩
  change bm β x.val = bm (scalar 2) (ba (bm (scalar 3) u.val) (bm β v.val))
  have ec : bm β (bm (scalar 2) v.val) = bm (scalar 2) (bm β v.val) := by
    rw [← mul_assoc,mul_comm β (scalar 2),mul_assoc]
  rw [ex,distributive,← mul_assoc β,show bm β (primeGenerator i).val = scalar 6 from generator_pair_product i,
    ec,distributive,← mul_assoc (scalar 2) (scalar 3),(scalar_embedding _ _).2.2]
  rw [show (2:Rat)*3=6 by grind]

theorem step_values (f : Embedding F) (V : DyadicValue F) (i : Bool)
    (h : Centered f V i) (x y : LocalIntegers) (nx : f.app x.val≠0)
    (he : bm (primeGenerator (!i)).val x.val = bm (scalar 2) y.val) :
    f.app y.val≠0 ∧ V.val (f.app x.val) = 1 + V.val (f.app y.val) := by
  obtain ⟨nb,bv⟩ := other_generator_value f V i h
  have eq := congrArg f.app he
  have fs : f.app (scalar 2)=(2:F) := by have h2 := f.scalar_int 2; grind
  rw [f.mul,f.mul,fs] at eq
  have ny : f.app y.val≠0 := by
    intro ez
    rw [ez,Semiring.mul_zero] at eq
    exact (Field.of_mul_eq_zero eq).elim nb nx
  have es := congrArg V.val eq
  rw [V.mul nb nx,bv,V.mul V.two_ne ny,V.two] at es
  exact ⟨ny,by grind⟩

theorem value_zero_iff_outside (f : Embedding F) (V : DyadicValue F) (i : Bool)
    (h : Centered f V i) (x : LocalIntegers) (nx : f.app x.val ≠ 0) :
    V.val (f.app x.val)=0 ↔ ¬ coordinateKernel residueMap i x := by
  rw [h.center]
  have he := h.nonneg x
  grind

/-- Descending to a nonnegative value by one at each step gives a common
integer, using any natural upper bound for the first valuation. -/
theorem paired_descent_bound {X : Type} (v w : X → Rat)
    (nv : ∀ x, 0 ≤ v x) (atZero : ∀ x, v x=0 → w x=0)
    (step : ∀ x, 0<v x → ∃ y, v x=1+v y ∧ w x=1+w y)
    (N : Nat) (x : X) (bound : v x ≤ (N:Rat)) :
    ∃ k : Nat, v x=(k:Rat) ∧ w x=(k:Rat) := by
  induction N generalizing x with
  | zero =>
    have hz : v x=0 := by have := nv x; change v x ≤ 0 at bound; grind
    exact ⟨0,hz,atZero x hz⟩
  | succ N ih =>
    by_cases hz : v x=0
    · exact ⟨0,hz,atZero x hz⟩
    · obtain ⟨y,hy,hw⟩ := step x (by have := nv x; grind)
      have hN : v y ≤ (N:Rat) := by rw [Rat.natCast_add] at bound; grind
      obtain ⟨k,hk,hl⟩ := ih y hN
      exact ⟨k+1,by rw [Rat.natCast_add]; grind,by rw [Rat.natCast_add]; grind⟩

theorem agree_on_order (f : Embedding F) (V W : DyadicValue F) (i : Bool)
    (hV : Centered f V i) (hW : Centered f W i) (x : LocalIntegers) :
    ∃ k : Nat, V.val (f.app x.val)=(k:Rat) ∧ W.val (f.app x.val)=(k:Rat) := by
  let v := fun y : LocalIntegers => V.val (f.app y.val)
  let w := fun y : LocalIntegers => W.val (f.app y.val)
  have hz (y : LocalIntegers) (hv : v y=0) : w y=0 := by
    by_cases q : f.app y.val=0
    · change W.val (f.app y.val)=0; rw [q,W.zero]
    · exact (value_zero_iff_outside f W i hW y q).mpr ((value_zero_iff_outside f V i hV y q).mp hv)
  have step (y : LocalIntegers) (hv : 0<v y) : ∃ t, v y = 1+v t ∧ w y = 1+w t := by
    have ny : f.app y.val ≠ 0 := by intro e; change 0 < V.val (f.app y.val) at hv; rw [e,V.zero] at hv; grind
    obtain ⟨t,ht⟩ := step_in_order i y ((hV.center y).mpr (.inr hv))
    exact ⟨t,(step_values f V i hV y t ny ht).2,(step_values f W i hW y t ny ht).2⟩
  have bound : v x ≤ (((v x).ceil.toNat:Nat):Rat) := by
    have a : ((v x).ceil : Rat) ≤ ((((v x).ceil.toNat:Nat):Int):Rat) :=
      Rat.intCast_le_intCast.mpr (Int.self_le_toNat _)
    exact Rat.le_trans Rat.le_ceil a
  exact paired_descent_bound v w hV.nonneg hz step _ x bound

theorem positive_integer_nonzero (f : Embedding F) (d : Nat) (hd : 0 < d) :
    f.app (scalar (((d:Nat):Int):Rat)) ≠ 0 := by
  intro hz
  have h := (scalar_embedding _ _).1.mp (f.faithful _ hz)
  have h' := Rat.intCast_inj.mp (show (((d:Nat):Int):Rat)=((0:Int):Rat) from h)
  omega

/-- Over the same chosen dyadic prime of the bottom field, two prolongations
give exactly the same integer value on every nonzero field coefficient. -/
theorem agree_integral_on_bottom (f : Embedding F) (V W : DyadicValue F) (i : Bool)
    (hV : Centered f V i) (hW : Centered f W i) (z : Biquad) :
    AgreeIntegral V W (f.app z) := by
  by_cases nz : f.app z = 0
  · exact .inl nz
  obtain ⟨d,hd,p,hp⟩ := positive_denominator z
  let s := scalar (((d:Nat):Int):Rat)
  let denominator : LocalIntegers := ⟨s,DyadicPrimeClassification69.scalar_mem localized_integer_order (d:Int)⟩
  let numerator : LocalIntegers := ⟨embed p,localized_integer_order.contains p⟩
  obtain ⟨a,ha,ka⟩ := agree_on_order f V W i hV hW numerator
  obtain ⟨b,hb,kb⟩ := agree_on_order f V W i hV hW denominator
  have en : f.app numerator.val = f.app denominator.val * f.app z := (congrArg f.app hp).trans (f.mul s z)
  have dn : f.app denominator.val≠0 := positive_integer_nonzero f d hd
  rw [en,V.mul dn nz] at ha
  rw [en,W.mul dn nz] at ka
  refine .inr ⟨(a:Int)-(b:Int),?_,?_⟩ <;> simp only [Rat.intCast_sub,Rat.intCast_natCast] <;> grind

theorem integral_on_bottom (f : Embedding F) (V : DyadicValue F) (i : Bool)
    (h : Centered f V i) (z : Biquad) :
    ∃ k : Int, V.val (f.app z)=(k:Rat) := by
  rcases agree_integral_on_bottom f V V i h h z with hz | ⟨k,hv,_⟩
  · exact ⟨0,by rw [hz,V.zero]; rfl⟩
  · exact ⟨k,hv⟩

end Reimann.DyadicBottomValue69
