import Reimann.DyadicLocalizedPrimes69

/-! Prime ideals above two in field suborders with odd-denominator representatives. -/

namespace Reimann.DyadicPrimeClassification69

open Reimann.TameRationalField277 Reimann.DyadicLocalizedPrimes69 Reimann.DyadicFieldTrace69
open Reimann.DyadicOrderCompletion69 (integerSum integerProduct)
open Reimann.Dyadic (Matrix scale)
open Reimann.DyadicFiberDescent
open Reimann.DyadicFiberPrimes (Fiber)

theorem scalar_mem {S : Biquad → Prop} (A : OverOrder S) (k : Int) : S (scalar (k:Rat)) :=
  embed_integer k ▸ A.contains ⟨k,0,0,0⟩

/-- A ring reduction on the field suborder, using its actual field operations. -/
noncomputable def orderReduction {S : Biquad → Prop} (A : OverOrder S) : Reduction (Subtype S) where
  zero := ⟨scalar 0, scalar_mem A 0⟩
  one := ⟨scalar 1, scalar_mem A 1⟩
  add x y := ⟨ba x.val y.val, A.add_mem x.property y.property⟩
  mul x y := ⟨bm x.val y.val, A.mul_mem x.property y.property⟩
  red x := reduce x.val (A.clear x.property)
  surj w := by
    obtain ⟨p, hp⟩ := fiber_surjective w
    exact ⟨⟨embed p, A.contains p⟩,(reduce_of_rep _ (represents_self p)).trans hp⟩
  red_zero := by
    have h := represents_self (⟨0,0,0,0⟩:Matrix)
    rw [embed_integer] at h
    exact (reduce_of_rep _ h).trans rfl
  red_one := by
    have h := represents_self (⟨1,0,0,0⟩:Matrix)
    rw [embed_integer] at h
    exact (reduce_of_rep _ h).trans rfl
  red_add x y := by
    obtain ⟨p,k,hp⟩ := A.clear x.property
    obtain ⟨q,l,hq⟩ := A.clear y.property
    rw [reduce_of_rep _ (represents_add hp hq),reduce_of_rep _ hp,reduce_of_rep _ hq,
      fiber_add,fiber_odd_scale,fiber_odd_scale]
  red_mul x y := by
    obtain ⟨p,k,hp⟩ := A.clear x.property
    obtain ⟨q,l,hq⟩ := A.clear y.property
    rw [reduce_of_rep _ (represents_mul hp hq),reduce_of_rep _ hp,reduce_of_rep _ hq,fiber_mul]

theorem cancel_odd_denominators (x y t : Biquad) (k l : Int)
    (h : bm (scalar ((1+2*k:Int):Rat)) x =
      ba (bm (scalar ((1+2*l:Int):Rat)) y) (bm (scalar 2) t)) :
    x = ba y (bm (scalar 2)
      (ba t (ba (bm (scalar ((-k:Int):Rat)) x) (bm (scalar (l:Rat)) y)))) := by
  rcases x with ⟨⟨_,_⟩,_,_⟩
  rcases y with ⟨⟨_,_⟩,_,_⟩
  rcases t with ⟨⟨_,_⟩,_,_⟩
  simp only [ba,bm,scalar,qa,qm,qs,Prod.mk.injEq,Rat.intCast_add,Rat.intCast_mul,Rat.intCast_neg] at *
  grind

/-- Two field elements with the same residue differ by an actual double
inside the given suborder. -/
theorem same_residue_double {S : Biquad → Prop} (A : OverOrder S) (x y : Subtype S)
    (h : (orderReduction A).red x = (orderReduction A).red y) :
    ∃ t : Subtype S, x.val = ba y.val (bm (scalar 2) t.val) := by
  obtain ⟨p,k,hp⟩ := A.clear x.property
  obtain ⟨q,l,hq⟩ := A.clear y.property
  change reduce _ _ = reduce _ _ at h
  rw [reduce_of_rep _ hp,reduce_of_rep _ hq] at h
  obtain ⟨u,hu⟩ := equal_fibers_translate _ _ h
  have e := congrArg embed hu
  rw [DyadicOrderCompletion69.embed_integerSum,embed_scale,hp,hq] at e
  refine ⟨⟨_,A.add_mem (A.contains u) (A.add_mem
    (A.mul_mem (scalar_mem A (-k)) x.property) (A.mul_mem (scalar_mem A l) y.property))⟩,?_⟩
  exact cancel_odd_denominators x.val y.val (embed u) k l e

def two {S : Biquad → Prop} (A : OverOrder S) : Subtype S := ⟨scalar 2,scalar_mem A 2⟩

theorem reduce_two {S : Biquad → Prop} (A : OverOrder S) :
    (orderReduction A).red (two A) = ((0,0),(0,0)) := by
  have h := represents_self (⟨2,0,0,0⟩:Matrix)
  rw [embed_integer] at h
  exact (reduce_of_rep _ h).trans rfl

theorem same_residue_iff {S : Biquad → Prop} (A : OverOrder S) (x y : Subtype S) :
    (orderReduction A).red x = (orderReduction A).red y ↔
      ∃ t : Subtype S, x = (orderReduction A).add y ((orderReduction A).mul (two A) t) := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := same_residue_double A x y h
    exact ⟨t,Subtype.ext ht⟩
  · rintro ⟨t,rfl⟩
    rw [(orderReduction A).red_add,(orderReduction A).red_mul,reduce_two]
    generalize (orderReduction A).red t = p
    generalize (orderReduction A).red y = q
    rcases p with ⟨⟨a,b⟩,c,d⟩
    rcases q with ⟨⟨e,f⟩,g,h⟩
    revert a b c d e f g h
    decide

theorem saturated_above_two {S : Biquad → Prop} (A : OverOrder S) (P : Subtype S → Prop)
    (hp : IsPrime (orderReduction A) P) (h2 : P (two A)) : Saturated (orderReduction A) P := by
  have forward (x y : Subtype S) (h : (orderReduction A).red x = (orderReduction A).red y)
      (hy : P y) : P x := by
    obtain ⟨t,rfl⟩ := (same_residue_iff A x y).mp h
    exact hp.add_mem _ _ hy (hp.absorb _ _ h2)
  exact fun x y h => ⟨forward y x h.symm,forward x y h⟩

/-- Exactly the two residue kernels are primes over 2 in every such
field suborder, using its intrinsic ring operations. -/
theorem primes_above_two {S : Biquad → Prop} (A : OverOrder S) (P : Subtype S → Prop) :
    (IsPrime (orderReduction A) P ∧ P (two A)) ↔
      P = coordinateKernel (orderReduction A) false ∨ P = coordinateKernel (orderReduction A) true := by
  constructor
  · rintro ⟨hp,h2⟩
    exact (prime_iff_coordinate_kernel _ _ (saturated_above_two A P hp h2)).mp hp
  · rintro (rfl | rfl)
    all_goals
      refine ⟨prime_pullback _ _ (DyadicFiberPrimes.kernel_prime _), ?_⟩
      unfold coordinateKernel
      rw [reduce_two]
      rfl

/-- Canonical enumeration of O/2O by the product of two copies of F₄. -/
theorem residue_quotient {S : Biquad → Prop} (A : OverOrder S) :
    let R := orderReduction A
    let rel := fun x y : Subtype S => ∃ t : Subtype S, x=R.add y (R.mul (two A) t)
    ∃ f : Quot rel → Fiber, ∃ g : Fiber → Quot rel,
      (∀ x : Subtype S, f (Quot.mk rel x)=R.red x) ∧
      (∀ c, g (f c) = c) ∧ (∀ w, f (g w) = w) := by
  dsimp only
  let R := orderReduction A
  let rel := fun x y : Subtype S => ∃ t : Subtype S, x=R.add y (R.mul (two A) t)
  let f := Quot.lift R.red (fun x y h => (same_residue_iff A x y).mpr h)
  let g := fun w : Fiber => Quot.mk rel (Classical.choose (R.surj w))
  refine ⟨f,g,fun _ => rfl, ?_, fun w => Classical.choose_spec (R.surj w)⟩
  intro c
  induction c using Quot.ind with
  | mk x =>
    apply Quot.sound
    exact (same_residue_iff A _ _).mp (Classical.choose_spec (R.surj (R.red x)))

theorem distinct_primes_with_residues {S : Biquad → Prop} (A : OverOrder S) :
    coordinateKernel (orderReduction A) false ≠ coordinateKernel (orderReduction A) true ∧
    ∀ (i : Bool) (r : DyadicFiberPrimes.F4), ∃ x : Subtype S,
      DyadicFiberPrimes.project i ((orderReduction A).red x) = r := by
  refine ⟨coordinate_kernels_distinct _, ?_⟩
  intro i r
  obtain ⟨p,hp⟩ := DyadicFiberPrimes.project_surjective i r
  obtain ⟨x,hx⟩ := (orderReduction A).surj p
  exact ⟨x,by rw [hx,hp]⟩

end Reimann.DyadicPrimeClassification69
