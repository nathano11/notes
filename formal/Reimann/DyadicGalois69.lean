import Reimann.DyadicPlaceAction69

/-! Rational endomorphisms and dyadic prime stabilizers of the bottom
field E₀ = ℚ(√-3,√-23), in its concrete rational coordinates. -/

namespace Reimann.DyadicGalois69

open Reimann.TameRationalField277 Reimann.DyadicPlaceAction69
open Reimann.DyadicFieldTrace69 (conjugate)
open Reimann.DyadicFiberPrimes (kernel)
open Reimann.DyadicLocalizedPrimes69 (reduce)

/-- The unital algebra-map laws written using the actual field operations. -/
structure RationalEnd (f : Biquad → Biquad) : Prop where
  onScalar : ∀ a, f (scalar a) = scalar a
  onAdd : ∀ x y, f (ba x y) = ba (f x) (f y)
  onMul : ∀ x y, f (bm x y) = bm (f x) (f y)

theorem field_action_end (s t : Bool) : RationalEnd (fieldAction s t) := by
  refine ⟨fieldAction_scalar s t, ?_, fieldAction_mul s t⟩
  intro x y
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [ba,qa,fieldAction,conjugate] <;> grind

/-- Multiply by the inverse of a nonzero factor in the biquadratic field. -/
theorem zero_product {x y : Biquad} (h : bm x y = scalar 0) : x=scalar 0 ∨ y=scalar 0 := by
  by_cases hx : x=scalar 0
  · exact Or.inl hx
  · right
    have he := congrArg (fun z => bm z (bi x)) h
    change bm (bm x y) (bi x) = bm (scalar 0) (bi x) at he
    rw [mul_comm x y, mul_assoc, biquad_mul_inverse x hx, mul_one] at he
    rw [he]
    apply Prod.ext <;> apply Prod.ext <;> simp only [bm,scalar,qm,qa,qs] <;> grind

theorem square_difference (x y : Biquad) :
    bm (ba x (bn y)) (ba x y) = ba (bm x x) (bn (bm y y)) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,qa,qs,qm,ba,bn] <;> grind

/-- In E₀ the only elements with square y² are y and -y. -/
theorem root_sign (x y : Biquad) (h : bm x x = bm y y) :
    ∃ s : Bool, x = if s then bn y else y := by
  have hz := square_difference x y
  rw [h,(add_group_laws (bm y y) (bm y y) (bm y y)).2.2.2] at hz
  obtain hz | hz := zero_product hz
  · refine ⟨false, ?_⟩
    simp only [ba,bn,qa,qs,scalar,Prod.mk.injEq] at hz
    apply Prod.ext <;> apply Prod.ext <;> grind
  · refine ⟨true, ?_⟩
    simp only [ba,qa,scalar,Prod.mk.injEq] at hz
    apply Prod.ext <;> apply Prod.ext <;> simp only [bn,qs] <;> grind

theorem actions_on_generators (s t : Bool) :
    fieldAction s t gen3 = (if s then bn gen3 else gen3) ∧
    fieldAction s t gen23 = (if t then bn gen23 else gen23) := by
  cases s <;> cases t <;> decide +kernel

/-- The images of the two radical generators determine the entire algebra map. -/
theorem equal_on_basis {f g : Biquad → Biquad} (hf : RationalEnd f) (hg : RationalEnd g)
    (h3 : f gen3=g gen3) (h23 : f gen23=g gen23) : f=g := by
  funext z
  rcases z with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rw [←basis_expansion]
  simp only [hf.onAdd,hf.onMul,hf.onScalar,hg.onAdd,hg.onMul,hg.onScalar,h3,h23]

theorem all_rational_endomorphisms (f : Biquad → Biquad) (hf : RationalEnd f) :
    ∃ s t : Bool, f=fieldAction s t := by
  have h3 : bm (f gen3) (f gen3) = bm gen3 gen3 := by
    rw [←hf.onMul, generator_squares.1, hf.onScalar]
  have h23 : bm (f gen23) (f gen23) = bm gen23 gen23 := by
    rw [←hf.onMul, generator_squares.2, hf.onScalar]
  obtain ⟨s,hs⟩ := root_sign _ _ h3
  obtain ⟨t,ht⟩ := root_sign _ _ h23
  exact ⟨s,t,equal_on_basis hf (field_action_end s t)
    (hs.trans (actions_on_generators s t).1.symm) (ht.trans (actions_on_generators s t).2.symm)⟩

theorem distinct_actions {s t u v : Bool} (h : fieldAction s t=fieldAction u v) : s=u ∧ t=v := by
  have hx := congrArg (fun z : Biquad => z.1.2) (congrFun h gen3)
  have hy := congrArg (fun z : Biquad => z.2.1) (congrFun h gen23)
  have inc : ∀ x y : Bool, sign x = sign y → x = y := by decide +kernel
  apply And.intro (inc _ _ ?_) (inc _ _ ?_)
  · simpa [fieldAction,conjugate,gen3] using hx
  · simpa [fieldAction,conjugate,gen23] using hy

theorem action_involution (s t : Bool) (x : Biquad) :
    fieldAction s t (fieldAction s t x) = x := by
  have hs (b : Bool) : sign b*sign b = 1 := by cases b <;> decide +kernel
  exact DyadicFieldTrace69.conjugate_involution _ _ (hs s) (hs t) x

/-- Every rational endomorphism is an automorphism with itself as inverse. -/
theorem rational_end_involution (f : Biquad → Biquad) (hf : RationalEnd f) (x : Biquad) :
    f (f x) = x := by
  obtain ⟨s,t,rfl⟩ := all_rational_endomorphisms f hf
  exact action_involution s t x

/-- Preservation of the localized dyadic prime on all elements of odd denominator. -/
def PreservesPrime (i : Bool) (f : Biquad → Biquad) : Prop :=
  ∀ z (hz : HasOddDenominator z), ∃ hy : HasOddDenominator (f z),
    kernel i (reduce (f z) hy) ↔ kernel i (reduce z hz)

theorem action_preserves_prime (s t i : Bool) : PreservesPrime i (fieldAction s t) ↔ t=false := by
  constructor
  · intro h
    apply (odd_denominator_stabilizer s t i).mp
    intro z hz
    obtain ⟨_,he⟩ := h z hz
    exact he
  · intro ht z hz
    exact ⟨action_odd_denominator s t hz, (odd_denominator_stabilizer s t i).mpr ht z hz⟩

/-- For either bottom prime, its full rational automorphism stabilizer is exactly
the two signs fixing √-23. Each acts involutively and the two are distinct. -/
theorem full_prime_stabilizer (i : Bool) (f : Biquad → Biquad) :
    RationalEnd f ∧ PreservesPrime i f ↔ ∃ s : Bool, f=fieldAction s false := by
  constructor
  · rintro ⟨hf,h⟩
    obtain ⟨s,t,rfl⟩ := all_rational_endomorphisms f hf
    have ht := (action_preserves_prime s t i).mp h
    exact ⟨s,by rw [ht]⟩
  · rintro ⟨s,rfl⟩
    exact ⟨field_action_end _ _,(action_preserves_prime s false i).mpr rfl⟩

end Reimann.DyadicGalois69
