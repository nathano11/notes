import Reimann.DyadicPlaceAlgebra
import Reimann.DyadicFiberDescent

/-! Prime ideals containing 2 in the integral biquadratic presentation.
In the special fiber the two evaluation maps are w ↦ 0 and w ↦ 1. -/

namespace Reimann.DyadicIntegralPlaces

open Reimann.DyadicLattice Reimann.DyadicPlaceAlgebra

abbrev Order := Quadratic × Quadratic

def zero : Order := ((natScalar 0,natScalar 0),(natScalar 0,natScalar 0))

def one : Order := (DyadicInert.one,zero.2)

def sum (x y : Order) : Order := (plus x.1 y.1, plus x.2 y.2)

def reduction (x : Order) : DyadicFiberPrimes.Fiber :=
  (DyadicInert.residue x.1, DyadicInert.residue (plus x.1 x.2))

theorem reduction_add (x y : Order) :
    reduction (sum x y) = DyadicFiberPrimes.sum (reduction x) (reduction y) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [sum,reduction,plus,DyadicFiberPrimes.sum,DyadicInert.residueAdd,DyadicInert.residue,add] <;> grind

theorem reduction_mul (cq cd : Scalar) (hq : cq.residue 0 = 1) (hd : cd.residue 0 = 0)
    (x y : Order) : reduction (product cq cd x y) =
    DyadicFiberPrimes.product (reduction x) (reduction y) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [reduction,product,DyadicInert.product,DyadicFiberPrimes.product,DyadicInert.residue,
      DyadicInert.residueProduct,plus,minus,scaleVector,add,neg,mul,hq,hd] <;> grind

theorem reduction_surjective (p : DyadicFiberPrimes.Fiber) : ∃ x, reduction x = p := by
  let lift := fun v : DyadicFiberPrimes.F4 => (natScalar v.1.toNat, natScalar v.2.toNat)
  refine ⟨(lift p.1, minus (lift p.2) (lift p.1)), Prod.ext (DyadicInert.residue_section _) ?_⟩
  have e : plus (lift p.1) (minus (lift p.2) (lift p.1)) = lift p.2 := by
    apply Prod.ext <;> apply scalar_ext <;> intro n <;> simp only [plus,minus,add,neg] <;> grind
  change DyadicInert.residue (plus _ _) = p.2
  rw [e]
  exact DyadicInert.residue_section _

theorem same_residue_translate (x y : Quadratic) (h : DyadicInert.residue x = DyadicInert.residue y) :
    ∃ z, x = plus y (plus z z) := by
  obtain ⟨a,ha⟩ := (DyadicQuotient.residue_eq_iff_multiple 0 x.1 y.1).mp (congrArg Prod.fst h)
  obtain ⟨b,hb⟩ := (DyadicQuotient.residue_eq_iff_multiple 0 x.2 y.2).mp (congrArg Prod.snd h)
  refine ⟨(a,b), Prod.ext ?_ ?_⟩
  · change x.1 = add y.1 (add a a)
    rw [ha]
    apply scalar_ext
    intro n
    simp only [add,mul,natScalar]
    grind
  · change x.2 = add y.2 (add b b)
    rw [hb]
    apply scalar_ext
    intro n
    simp only [add,mul,natScalar]
    grind

theorem equal_reductions_differ_by_double (x y : Order) (h : reduction x = reduction y) :
    ∃ z, x = sum y (sum z z) := by
  have left := congrArg Prod.fst h
  have right := congrArg Prod.snd h
  change DyadicInert.residue x.1 = DyadicInert.residue y.1 at left
  change DyadicInert.residue (plus x.1 x.2) = DyadicInert.residue (plus y.1 y.2) at right
  have e : DyadicInert.residue x.2 = DyadicInert.residue y.2 := by
    apply Prod.ext
    · have a := congrArg Prod.fst left
      have b := congrArg Prod.fst right
      simp only [DyadicInert.residue,plus,add] at *
      grind
    · have a := congrArg Prod.snd left
      have b := congrArg Prod.snd right
      simp only [DyadicInert.residue,plus,add] at *
      grind
  obtain ⟨a,ha⟩ := same_residue_translate _ _ left
  obtain ⟨b,hb⟩ := same_residue_translate _ _ e
  exact ⟨(a,b), Prod.ext ha hb⟩

theorem two_times (cq cd : Scalar) (x : Order) :
    product cq cd (sum one one) x = sum x x := by
  apply Prod.ext <;> apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [product,DyadicInert.product,DyadicInert.one,sum,one,zero,
      plus,minus,scaleVector,add,mul,neg,natScalar] <;> grind

def algebraReduction (cq cd : Scalar) (hq : cq.residue 0 = 1) (hd : cd.residue 0 = 0) :
    DyadicFiberDescent.Reduction Order where
  zero := zero
  one := one
  add := sum
  mul := product cq cd
  red := reduction
  surj := reduction_surjective
  red_zero := rfl
  red_one := rfl
  red_add := reduction_add
  red_mul := reduction_mul cq cd hq hd

theorem saturated_over_two (cq cd : Scalar) (hq : cq.residue 0 = 1) (hd : cd.residue 0 = 0)
    (P : Order → Prop) (hp : DyadicFiberDescent.IsPrime (algebraReduction cq cd hq hd) P)
    (h2 : P (sum one one)) : DyadicFiberDescent.Saturated (algebraReduction cq cd hq hd) P := by
  have stable (x y : Order) (hxy : reduction x = reduction y) (hy : P y) : P x := by
    obtain ⟨z,hz⟩ := equal_reductions_differ_by_double x y hxy
    have h := hp.absorb (sum one one) z h2
    change P (product cq cd (sum one one) z) at h
    rw [two_times] at h
    rw [hz]
    exact hp.add_mem y _ hy h
  intro x y h
  exact ⟨stable y x h.symm, stable x y h⟩

/-- Exactly the two displayed residue kernels are prime and contain 2
in the completed integral presentation. They evaluate w at 0 and 1 modulo 2. -/
theorem primes_above_two (q d : Nat) (hq : q%8=3) (hd : d%16=7) (P : Order → Prop) :
    let cq := natScalar ((q+1)/4)
    let cd := natScalar ((d+1)/4)
    let A := algebraReduction cq cd (DyadicInert.parameter_odd q hq)
      (DyadicSplitRoot.split_constant_even d hd)
    (DyadicFiberDescent.IsPrime A P ∧ P (sum one one)) ↔
      P = DyadicFiberDescent.coordinateKernel A false ∨ P = DyadicFiberDescent.coordinateKernel A true := by
  dsimp only
  let A := algebraReduction _ _ (DyadicInert.parameter_odd q hq) (DyadicSplitRoot.split_constant_even d hd)
  constructor
  · rintro ⟨hp,h2⟩
    exact (DyadicFiberDescent.prime_iff_coordinate_kernel A P (saturated_over_two _ _ _ _ P hp h2)).mp hp
  · intro hk
    have prime (i : Bool) : DyadicFiberDescent.IsPrime A (DyadicFiberDescent.coordinateKernel A i) :=
      DyadicFiberDescent.prime_pullback A _ (DyadicFiberPrimes.kernel_prime i)
    rcases hk with rfl | rfl
    · exact ⟨prime false, rfl⟩
    · exact ⟨prime true, rfl⟩

theorem conjugate_reduction (x : Order) :
    reduction (conjugateSplit x) = ((reduction x).2,(reduction x).1) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [reduction,conjugateSplit,DyadicInert.residue,plus,add,neg] <;> grind

theorem two_distinct_kernels_3_23 :
    let A := algebraReduction _ _ (DyadicInert.parameter_odd 3 (by decide))
      (DyadicSplitRoot.split_constant_even 23 (by decide))
    DyadicFiberDescent.coordinateKernel A false ≠ DyadicFiberDescent.coordinateKernel A true ∧
      ∀ x, DyadicFiberDescent.coordinateKernel A false (conjugateSplit x) ↔
        DyadicFiberDescent.coordinateKernel A true x := by
  dsimp only
  refine ⟨DyadicFiberDescent.coordinate_kernels_distinct _, fun x => ?_⟩
  change (reduction (conjugateSplit x)).1 = (0,0) ↔ (reduction x).2 = (0,0)
  rw [conjugate_reduction]

end Reimann.DyadicIntegralPlaces
