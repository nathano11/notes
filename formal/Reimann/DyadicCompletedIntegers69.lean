import Reimann.DyadicArithmetic69
import Reimann.DyadicLocalOperations69

/-! The inverse limit of the quotients of the 2-local algebraic integers in E₀.
Elements in the nth quotient are classes of genuine field elements. -/
namespace Reimann.DyadicCompletedIntegers69

open DyadicArithmetic69 DyadicOrderCompletion69 TameRationalField277
open TameBiquadratic277 (Quad)

/-- The concrete localization is the one obtained by inverting the odd integers in the monic-integral elements. -/
theorem local_iff (z : Biquad) : LocalizeAtTwo DyadicIntegralCriterion69.IsIntegral z ↔
    DyadicLocalizedCompletion69.Local z := by
  rw [integers_localized_at_two]
  exact ⟨fun ⟨p,k,h⟩ => ⟨k,p,h⟩,fun ⟨k,p,h⟩ => ⟨p,k,h⟩⟩

noncomputable def level (n : Nat) (z : LocalIntegers) : Quad (BitVec (n+1)) :=
  DyadicLocalizedCompletion69.level n ⟨z.val,(local_iff z.val).mp z.property⟩

theorem level_compatible (z : LocalIntegers) {i j : Nat} (h : i ≤ j) :
    mapFour (BitVec.setWidth (i+1)) (level j z) = level i z :=
  DyadicLocalizedCompletion69.level_compatible _ h

theorem level_surjective (n : Nat) (w : Quad (BitVec (n+1))) : ∃ z : LocalIntegers, level n z = w := by
  obtain ⟨p,hp⟩ := DyadicLocalizedCompletion69.level_surjective n w
  exact ⟨⟨DyadicFieldTrace69.embed p,localized_integer_order.contains p⟩,hp⟩

abbrev Class (n : Nat) := Quot (fun x y : LocalIntegers => level n x = level n y)

noncomputable def readClass (n : Nat) : Class n → Quad (BitVec (n+1)) :=
  Quot.lift (level n) (fun _ _ h => h)

noncomputable def writeClass (n : Nat) (v : Quad (BitVec (n+1))) : Class n :=
  Quot.mk _ (Classical.choose (level_surjective n v))

theorem class_inverses (n : Nat) :
    (∀ c : Class n, writeClass n (readClass n c) = c) ∧
    (∀ v, readClass n (writeClass n v) = v) := by
  constructor
  · intro c
    induction c using Quot.ind with
    | _ z => exact Quot.sound (Classical.choose_spec (level_surjective n (level n z)))
  · intro v
    exact Classical.choose_spec (level_surjective n v)

/-- The transition sends the class of a field element to the class of that same element. -/
def lower {i j : Nat} (h : i ≤ j) : Class j → Class i :=
  Quot.lift (fun z => Quot.mk _ z) (by
    intro x y hxy
    apply Quot.sound
    exact (level_compatible x h).symm.trans ((congrArg (mapFour (BitVec.setWidth (i+1))) hxy).trans
      (level_compatible y h)))

theorem read_lower {i j : Nat} (h : i ≤ j) (c : Class j) :
    readClass i (lower h c) = mapFour (BitVec.setWidth (i+1)) (readClass j c) := by
  induction c using Quot.ind with
  | _ z => exact (level_compatible z h).symm

structure AdicCompletion where
  levelClass (n : Nat) : Class n
  compatible {i j : Nat} (h : i ≤ j) : lower h (levelClass j) = levelClass i

noncomputable def completion_to_words (x : AdicCompletion) : Completion where
  level n := readClass n (x.levelClass n)
  compatible h := (read_lower h _).symm.trans (congrArg _ (x.compatible h))

noncomputable def completion_from_words (x : Completion) : AdicCompletion where
  levelClass n := writeClass n (x.level n)
  compatible {i j} h := by
    rw [← (class_inverses i).1 (lower h (writeClass j (x.level j))),read_lower,
      (class_inverses j).2,x.compatible h]

theorem class_completion_ext {x y : AdicCompletion} (h : ∀ n, x.levelClass n = y.levelClass n) : x=y := by
  cases x; cases y; congr; exact funext h

theorem completion_inverses :
    (∀ x, completion_from_words (completion_to_words x) = x) ∧
    (∀ x, completion_to_words (completion_from_words x) = x) :=
  ⟨fun _ => class_completion_ext fun n => (class_inverses n).1 _,
   fun _ => completion_ext fun n => (class_inverses n).2 _⟩

/-- The completion of the localized algebraic integers in E₀ in the four integral coordinates. -/
theorem completed_order_at_two :
    ∃ f : AdicCompletion → DyadicIntegralPlaces.Order, ∃ g : DyadicIntegralPlaces.Order → AdicCompletion,
      (∀ x, g (f x)=x) ∧ (∀ y, f (g y)=y) ∧
      ∀ x n, (fromOrder (f x)).level n = readClass n (x.levelClass n) := by
  refine ⟨fun x => toOrder (completion_to_words x),fun y => completion_from_words (fromOrder y),?_,?_,?_⟩
  · intro x; dsimp only; rw [completion_inverse.1,completion_inverses.1]
  · intro y; dsimp only; rw [completion_inverses.2,completion_inverse.2]
  · intro x n; rw [completion_inverse.1]; rfl

def fieldPoint (z : LocalIntegers) : AdicCompletion where
  levelClass _ := Quot.mk _ z
  compatible _ := rfl

noncomputable def coordinates (x : AdicCompletion) : DyadicIntegralPlaces.Order :=
  toOrder (completion_to_words x)

noncomputable def sum (x y : AdicCompletion) : AdicCompletion :=
  completion_from_words (completedSum (completion_to_words x) (completion_to_words y))

noncomputable def product (x y : AdicCompletion) : AdicCompletion :=
  completion_from_words (completedProduct (completion_to_words x) (completion_to_words y))

theorem coordinates_sum (x y : AdicCompletion) :
    coordinates (sum x y) = DyadicIntegralPlaces.sum (coordinates x) (coordinates y) := by
  unfold coordinates sum
  rw [completion_inverses.2]
  have h := congrArg toOrder (completion_add (toOrder (completion_to_words x)) (toOrder (completion_to_words y)))
  simpa only [completion_inverse.1,completion_inverse.2] using h.symm

theorem coordinates_product (x y : AdicCompletion) :
    coordinates (product x y) = DyadicPlaceAlgebra.product (DyadicLattice.natScalar 1)
      (DyadicLattice.natScalar 6) (coordinates x) (coordinates y) := by
  unfold coordinates product
  rw [completion_inverses.2]
  have h := congrArg toOrder (completion_mul (toOrder (completion_to_words x)) (toOrder (completion_to_words y)))
  simpa only [completion_inverse.1,completion_inverse.2] using h.symm

/-- The actual completion splits as two copies of the quadratic order e²=e−1. -/
theorem two_completed_factors :
    let Q := DyadicPlaceAlgebra.Quadratic
    ∃ f : AdicCompletion → Q × Q, ∃ g : Q × Q → AdicCompletion,
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) ∧
      (∀ x y, f (sum x y) =
        (DyadicPlaceAlgebra.plus (f x).1 (f y).1,DyadicPlaceAlgebra.plus (f x).2 (f y).2)) ∧
      ∀ x y, f (product x y) =
        (DyadicInert.product (DyadicLattice.natScalar 1) (f x).1 (f y).1,
         DyadicInert.product (DyadicLattice.natScalar 1) (f x).2 (f y).2) := by
  obtain ⟨s,t,u,_,_,hre,her,hmul,_,_⟩ := DyadicPlaceAlgebra.two_dyadic_factors 3 23 (by decide) (by decide)
  refine ⟨fun x => DyadicPlaceAlgebra.evaluations s t (coordinates x),
    fun z => completion_from_words (fromOrder (DyadicPlaceAlgebra.interpolate s u z)),?_,?_,?_,?_⟩
  · intro x
    dsimp only
    rw [hre,coordinates,completion_inverse.1,completion_inverses.1]
  · intro z
    dsimp only
    rw [coordinates,completion_inverses.2,completion_inverse.2,her]
  · intro x y
    dsimp only
    rw [coordinates_sum]
    exact Prod.ext (DyadicPlaceAlgebra.evaluate_add s _ _) (DyadicPlaceAlgebra.evaluate_add t _ _)
  · intro x y
    dsimp only
    rw [coordinates_product]
    exact hmul _ _

/-- Equality defining the nth quotient is exactly congruence modulo 2^(n+1)
times the actual 2-local ring of integers. -/
theorem classes_are_ideal_congruences (n : Nat) (x y : LocalIntegers) :
    level n x = level n y ↔ ∃ t : LocalIntegers,
      x.val = ba y.val (bm (scalar (((2 : Int)^(n+1) : Int) : Rat)) t.val) := by
  have h := DyadicLocalizedCompletion69.level_eq_iff_two_power_difference n
    ⟨x.val,(local_iff _).mp x.property⟩ ⟨y.val,(local_iff _).mp y.property⟩
  refine h.trans ⟨?_,?_⟩
  · rintro ⟨t,ht⟩; exact ⟨⟨t.val,(local_iff _).mpr t.property⟩,ht⟩
  · rintro ⟨t,ht⟩; exact ⟨⟨t.val,(local_iff _).mp t.property⟩,ht⟩

theorem fieldPoint_sum (x y z : LocalIntegers) (hz : z.val = ba x.val y.val) :
    fieldPoint z = sum (fieldPoint x) (fieldPoint y) := by
  rw [← (completion_inverses.1 (fieldPoint z))]
  apply congrArg completion_from_words
  apply completion_ext
  intro n
  exact DyadicLocalOperations69.level_add n ⟨x.val,(local_iff _).mp x.property⟩
    ⟨y.val,(local_iff _).mp y.property⟩ ⟨z.val,(local_iff _).mp z.property⟩ hz

theorem fieldPoint_product (x y z : LocalIntegers) (hz : z.val = bm x.val y.val) :
    fieldPoint z = product (fieldPoint x) (fieldPoint y) := by
  rw [← (completion_inverses.1 (fieldPoint z))]
  apply congrArg completion_from_words
  apply completion_ext
  intro n
  exact DyadicLocalOperations69.level_mul n ⟨x.val,(local_iff _).mp x.property⟩
    ⟨y.val,(local_iff _).mp y.property⟩ ⟨z.val,(local_iff _).mp z.property⟩ hz

theorem fieldPoint_dense (x : AdicCompletion) (n : Nat) :
    ∃ z : LocalIntegers, (fieldPoint z).levelClass n = x.levelClass n := by
  generalize x.levelClass n = c
  induction c using Quot.ind with
  | _ z => exact ⟨z,rfl⟩

end Reimann.DyadicCompletedIntegers69
