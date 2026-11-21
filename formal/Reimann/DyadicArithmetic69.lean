import Reimann.DyadicIntegralCriterion69
import Reimann.DyadicFieldTrace69
import Reimann.DyadicLocalizedPrimes69
import Reimann.DyadicOrderIntegral69
import Reimann.DyadicPrimeClassification69
import Reimann.DyadicMahler69

/-! Localization at two of the algebraic integers in E₀ = ℚ(√−3,√−23). -/
namespace Reimann.DyadicArithmetic69

open TameRationalField277 DyadicIntegralCriterion69 DyadicFieldTrace69 DyadicBasisComparison
open Reimann.Dyadic (Matrix)

/-- Clear one rational coordinate, retaining an arbitrary extra multiple of its denominator. -/
theorem clear_coordinate (a : Rat) (b : Nat) :
    (((a.den*b : Nat) : Int) : Rat)*a = (((b : Int)*a.num : Int) : Rat) := by
  have h := rational_numerator a
  simp only [Int.natCast_mul,Rat.intCast_mul]
  grind

theorem four_denominators (a b c d : Rat) : ∃ n : Nat, 0<n ∧ ∃ x : Matrix,
    (((n : Int) : Rat)*a, ((n : Int) : Rat)*b, ((n : Int) : Rat)*c, ((n : Int) : Rat)*d) =
    ((x.a : Rat), (x.b : Rat), (x.c : Rat), (x.d : Rat)) := by
  let n := a.den*(b.den*(c.den*d.den))
  have h₁ : n = a.den*(b.den*(c.den*d.den)) := rfl
  have h₂ : n = b.den*(a.den*(c.den*d.den)) := by dsimp [n]; ac_rfl
  have h₃ : n = c.den*(a.den*(b.den*d.den)) := by dsimp [n]; ac_rfl
  have h₄ : n = d.den*(a.den*(b.den*c.den)) := by dsimp [n]; ac_rfl
  refine ⟨n,Nat.mul_pos a.den_pos (Nat.mul_pos b.den_pos (Nat.mul_pos c.den_pos d.den_pos)),
    ⟨↑(b.den*(c.den*d.den))*a.num,↑(a.den*(c.den*d.den))*b.num,
     ↑(a.den*(b.den*d.den))*c.num,↑(a.den*(b.den*c.den))*d.num⟩,?_⟩
  exact Prod.ext (h₁.symm ▸ clear_coordinate a _) (Prod.ext (h₂.symm ▸ clear_coordinate b _)
    (Prod.ext (h₃.symm ▸ clear_coordinate c _) (h₄.symm ▸ clear_coordinate d _)))

theorem half_coordinates_dilate (n : Int) (z : Biquad) :
    toIntegral (dilate n z) =
      let v := toIntegral z
      ((((n : Rat)*v.1.1), (n : Rat)*v.1.2), ((n : Rat)*v.2.1, (n : Rat)*v.2.2)) := by
  simp only [dilate,TameTraceLattice277.scalar_mul_coords,toIntegral]
  apply Prod.ext <;> apply Prod.ext <;> grind

theorem positive_denominator (z : Biquad) :
    ∃ d : Nat, 0<d ∧ ∃ x : Matrix, embed x = dilate (d : Int) z := by
  let v := toIntegral z
  obtain ⟨n,hn,x,h⟩ := four_denominators v.1.1 v.1.2 v.2.1 v.2.2
  obtain ⟨ha,h⟩ := Prod.mk.inj h
  obtain ⟨hb,h⟩ := Prod.mk.inj h
  obtain ⟨hc,hd⟩ := Prod.mk.inj h
  have he : toIntegral (dilate (n : Int) z) = toIntegral (embed x) := by
    rw [half_coordinates_dilate,recover_coordinates]
    exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)
  refine ⟨n,hn,x,?_⟩
  have hh := congrArg (fromIntegral half) he
  simpa only [(inverses_at_odd_prime half twice_half _).1] using hh.symm

theorem half_even_step (x y : Matrix) (t : Int) :
    DyadicLocalizedPrimes69.fiber (DyadicOrderCompletion69.integerSum
      (DyadicOrderCompletion69.integerProduct x y) ⟨2*t,0,0,0⟩) =
    DyadicFiberPrimes.product (DyadicLocalizedPrimes69.fiber x) (DyadicLocalizedPrimes69.fiber y) := by
  rw [DyadicLocalizedPrimes69.fiber_add,DyadicLocalizedPrimes69.fiber_mul]
  have he := (DyadicLocalizedPrimes69.fiber_zero_iff ⟨2*t,0,0,0⟩).mpr
    ⟨⟨t,rfl⟩,⟨0,rfl⟩,⟨0,rfl⟩,⟨0,rfl⟩⟩
  rw [he]
  simp [DyadicFiberPrimes.sum,DyadicInert.residueAdd]

theorem half_zero_red (x : Matrix) (h : embed x = scalar 0) :
    DyadicLocalizedPrimes69.fiber x = ((0,0),(0,0)) := by
  have e := DyadicOrderIntegral69.embed_integer_scalar 0
  have hx : x=⟨0,0,0,0⟩ := embed_injective (h.trans e.symm)
  rw [hx]
  rfl

theorem half_fiber_halves (x : Matrix) (hr : DyadicLocalizedPrimes69.fiber x = ((0,0),(0,0))) :
    ∃ y, embed x = dilate 2 (embed y) := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ := (DyadicLocalizedPrimes69.fiber_zero_iff x).mp hr
  refine ⟨⟨a,b,c,d⟩,?_⟩
  rw [dilate,←embed_scale]
  exact congrArg embed (by cases x; simp_all [Reimann.Dyadic.scale])

def model : IntegralModel Matrix where
  embed := DyadicFieldTrace69.embed
  integer a := ⟨a,0,0,0⟩
  sum := DyadicOrderCompletion69.integerSum
  product := DyadicOrderCompletion69.integerProduct
  red := DyadicLocalizedPrimes69.fiber
  embed_int := DyadicOrderIntegral69.embed_integer_scalar
  embed_add := DyadicOrderCompletion69.embed_integerSum
  embed_mul := DyadicOrderCompletion69.embed_integerProduct
  red_one := rfl
  red_even_step := half_even_step
  zero_red := half_zero_red
  halve := half_fiber_halves

/-- Every algebraic integer of E₀ has odd common denominator in the half-integral basis. -/
theorem integral_odd_denominator (z : Biquad) (hz : IsIntegral z) :
    ∃ k : Int, ∃ x : Matrix, embed x = dilate (1+2*k) z := by
  obtain ⟨d,hd,x,hx⟩ := positive_denominator z
  obtain ⟨j,hj,y,hy⟩ := odd_denominator model z hz d hd x hx
  refine ⟨(j/2 : Nat),y,?_⟩
  have he : (j : Int) = 1+2*((j/2 : Nat) : Int) := by omega
  rw [←he]
  exact hy

/-- Invert every odd integer in a specified subset of the rational field. -/
def LocalizeAtTwo (S : Biquad → Prop) (z : Biquad) : Prop :=
  ∃ k : Int, S (dilate (1+2*k) z)

/-- The localization of the actual algebraic integers equals the localization of
ℤ[e,w] inside E₀. Integrality here means satisfying a monic integer polynomial. -/
theorem integers_localized_at_two (z : Biquad) :
    LocalizeAtTwo IsIntegral z ↔ ∃ p : Matrix, ∃ k : Int, DyadicLocalizedPrimes69.Represents z k p := by
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨l,p,hp⟩ := integral_odd_denominator _ hk
    refine ⟨p,k+l+2*k*l,?_⟩
    have hh := TameTraceLattice277.scale_twice (1+2*l) (1+2*k) z
    have he : (1+2*l)*(1+2*k)=1+2*(k+l+2*k*l) := by grind
    rw [he] at hh
    exact hp.trans hh
  · rintro ⟨p,k,h⟩
    refine ⟨k,?_⟩
    change embed p = dilate (1+2*k) z at h
    rw [←h]
    exact DyadicOrderIntegral69.order_is_integral p

theorem localized_integer_order : DyadicLocalizedPrimes69.OverOrder (LocalizeAtTwo IsIntegral) where
  contains p := (integers_localized_at_two _).mpr ⟨p,0,DyadicLocalizedPrimes69.represents_self p⟩
  clear := fun h => (integers_localized_at_two _).mp h
  add_mem := by
    intro x y hx hy
    obtain ⟨p,k,hp⟩ := (integers_localized_at_two x).mp hx
    obtain ⟨q,l,hq⟩ := (integers_localized_at_two y).mp hy
    exact (integers_localized_at_two _).mpr ⟨_,_,DyadicLocalizedPrimes69.represents_add hp hq⟩
  mul_mem := by
    intro x y hx hy
    obtain ⟨p,k,hp⟩ := (integers_localized_at_two x).mp hx
    obtain ⟨q,l,hq⟩ := (integers_localized_at_two y).mp hy
    exact (integers_localized_at_two _).mpr ⟨_,_,DyadicLocalizedPrimes69.represents_mul hp hq⟩

/-- The conductor-552 test holds for the series built from every inverse-generator row. -/
theorem unhalved_row_552 (j : Nat) :
    DyadicHalfPrecision.partialDouble DyadicMahler69.series (j+4) = DyadicHalfPrecision.literalRow16 :=
  DyadicMahler69.canonical_unhalved_row j

abbrev LocalIntegers := Subtype (LocalizeAtTwo IsIntegral)

noncomputable def residueMap : DyadicFiberDescent.Reduction LocalIntegers :=
  DyadicPrimeClassification69.orderReduction localized_integer_order

/-- At the w=0 prime use w, at the w=1 prime use 1−w. -/
def primeGenerator (i : Bool) : LocalIntegers :=
  let p : Matrix := if i then ⟨1,0,-1,0⟩ else ⟨0,0,1,0⟩
  ⟨embed p,localized_integer_order.contains p⟩

theorem generator_residue (i : Bool) :
    residueMap.red (primeGenerator i) = DyadicFiberPrimes.axis (!i) (1,0) := by
  let p : Matrix := if i then ⟨1,0,-1,0⟩ else ⟨0,0,1,0⟩
  have h := DyadicLocalizedPrimes69.reduce_of_rep
    (localized_integer_order.clear (localized_integer_order.contains p)) (DyadicLocalizedPrimes69.represents_self p)
  exact h.trans (by cases i <;> rfl)

theorem prime_generated_by_two_and_root (i : Bool) (x : LocalIntegers) :
    DyadicFiberDescent.coordinateKernel residueMap i x ↔
      ∃ u v : LocalIntegers, x = residueMap.add (residueMap.mul (primeGenerator i) u)
        (residueMap.mul (DyadicPrimeClassification69.two localized_integer_order) v) := by
  constructor
  · intro hx
    have h : residueMap.red x = residueMap.red (residueMap.mul (primeGenerator i) x) := by
      rw [residueMap.red_mul,generator_residue]
      exact (DyadicFiberPrimes.complement_fixes_kernel i _ hx).symm
    obtain ⟨v,hv⟩ := (DyadicPrimeClassification69.same_residue_iff localized_integer_order x _).mp h
    exact ⟨x,v,hv⟩
  · rintro ⟨u,v,rfl⟩
    unfold DyadicFiberDescent.coordinateKernel
    rw [residueMap.red_add,residueMap.red_mul,residueMap.red_mul,generator_residue]
    have h₂ : residueMap.red (DyadicPrimeClassification69.two localized_integer_order) =
      ((0,0),(0,0)) := DyadicPrimeClassification69.reduce_two _
    rw [h₂]
    generalize residueMap.red u = a
    generalize residueMap.red v = b
    cases i <;> simp [DyadicFiberPrimes.kernel,DyadicFiberPrimes.project,DyadicFiberPrimes.sum,
      DyadicFiberPrimes.product,DyadicFiberPrimes.axis,DyadicInert.residueAdd,DyadicInert.residueProduct]

theorem primes_above_two (P : LocalIntegers → Prop) :
    (DyadicFiberDescent.IsPrime residueMap P ∧ P (DyadicPrimeClassification69.two localized_integer_order)) ↔
    P = DyadicFiberDescent.coordinateKernel residueMap false ∨
    P = DyadicFiberDescent.coordinateKernel residueMap true :=
  DyadicPrimeClassification69.primes_above_two localized_integer_order P

theorem residue_fields :
    DyadicFiberDescent.coordinateKernel residueMap false ≠ DyadicFiberDescent.coordinateKernel residueMap true ∧
    ∀ i : Bool, ∀ r : DyadicFiberPrimes.F4, ∃ x : LocalIntegers,
      DyadicFiberPrimes.project i (residueMap.red x) = r :=
  DyadicPrimeClassification69.distinct_primes_with_residues localized_integer_order

end Reimann.DyadicArithmetic69
