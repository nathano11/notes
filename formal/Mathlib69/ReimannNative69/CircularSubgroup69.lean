import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Reimann.CircularSinnott69

/-! The conductor-69 circular numbers are generated inside the multiplicative
group of the ambient field. Pulling a group of circular numbers back along
the units of an integral order imposes integrality on the unit and its inverse. -/

namespace Reimann.CircularSubgroup69

open CircularFieldReduction69 CircularPolynomial69 CircularRealUnit69 CircularSinnott69

variable {R : Type} [Field R]

section
variable [CharZero R]

/-- Conductor-69 circular-number generators over the actual intersection. -/
def normGenerators (x : R) (hx : Primitive69 x) (K : R → Prop) : Set Rˣ :=
  {w | ∃ a : Fin 69, Nat.Coprime a.val 69 ∧
    (w : R) = normOperator x hx K (factor x a)}

def conductorNumbers (x : R) (hx : Primitive69 x) (K : R → Prop) : Subgroup Rˣ :=
  Subgroup.closure (normGenerators x hx K)

theorem conductorNumbers_le (x : R) (hx : Primitive69 x) (K : R → Prop) (D : Subgroup Rˣ) :
    conductorNumbers x hx K ≤ D ↔ normGenerators x hx K ⊆ D :=
  Subgroup.closure_le D

end

/-- For the ring of integers O and the full circular numbers D this is
the circular-unit group, realized inside the actual unit group of O. -/
def circularUnits (O : Subring R) (D : Subgroup Rˣ) : Subgroup Oˣ :=
  D.comap (Units.map O.subtype.toMonoidHom)

theorem circularUnits_mem (O : Subring R) (D : Subgroup Rˣ) (w : Oˣ) :
    w ∈ circularUnits O D ↔ Units.map O.subtype.toMonoidHom w ∈ D := Iff.rfl

def quadraticOrder (e : R) : Subring R := Subring.closure {e}

theorem quadraticOrder_le (e : R) (O : Subring R) :
    quadraticOrder e ≤ O ↔ e ∈ O := by
  rw [quadraticOrder, Subring.closure_le, Set.singleton_subset_iff]
  rfl

theorem quadraticOrder_mem (e : R) : e ∈ quadraticOrder e :=
  (quadraticOrder_le e _).mp le_rfl

theorem inverse_mem_order {e : R} (O : Subring R) (he : e ∈ O) : 25-e ∈ O :=
  O.sub_mem (natCast_mem O 25) he

def integralUnit {e : R} (O : Subring R) (he : e ∈ O) (hinv : e*(25-e) = 1) : Oˣ where
  val := ⟨e,he⟩
  inv := ⟨25-e,inverse_mem_order O he⟩
  val_inv := Subtype.ext hinv
  inv_val := Subtype.ext ((mul_comm _ _).trans hinv)

theorem integralUnit_value {e : R} (O : Subring R) (he : e ∈ O) (hinv : e*(25-e) = 1) :
    ((integralUnit O he hinv : O) : R) = e := rfl

theorem integralUnit_inverse_value {e : R} (O : Subring R) (he : e ∈ O) (hinv : e*(25-e) = 1) :
    (((integralUnit O he hinv)⁻¹).val : R) = 25-e := rfl

/-- A nonzero finite product in the field lifts to a product in a subgroup
of its multiplicative group once its factors lift. -/
theorem fold_units_mem {ι : Type} (D : Subgroup Rˣ) (f : ι → R) (ss : List ι)
    (hf : ∀ i ∈ ss, ∀ w : Rˣ, (w : R) = f i → w ∈ D)
    (w : Rˣ) (hw : (w : R) = ss.foldr (fun i z => f i * z) 1) : w ∈ D := by
  induction ss generalizing w with
  | nil =>
    have he : w = 1 := Units.ext hw
    exact he ▸ D.one_mem
  | cons i ss ih =>
    let t := ss.foldr (fun j z => f j * z) 1
    change (w : R) = f i * t at hw
    have hn : f i * t ≠ 0 := by rw [← hw]; exact w.ne_zero
    have hn' := mul_ne_zero_iff.mp hn
    let a := Units.mk0 (f i) hn'.1
    let b := Units.mk0 t hn'.2
    have ha := hf i List.mem_cons_self a rfl
    have hb := ih (fun j hj => hf j (List.mem_cons_of_mem i hj)) b rfl
    have h : w = a*b := Units.ext hw
    exact h ▸ D.mul_mem ha hb

section
variable [CharZero R]

theorem positive_mem_numbers (x : R) (hx : Primitive69 x) (K : R → Prop)
    (reps : List (Fin 69)) (hr : ∀ a ∈ reps, eta a.val = 1)
    (w : Rˣ) (hw : (w : R) =
      reps.foldr (fun a z => normOperator x hx K (factor x a) * z) 1) :
    w ∈ conductorNumbers x hx K := by
  apply fold_units_mem _ _ reps _ w hw
  intro i hi z hz
  exact Subgroup.subset_closure ⟨i, CircularRelativeGalois69.positive_unit ⟨i,hr i hi⟩, hz⟩

/-- A ring containing the positive unit automatically contains its integral
inverse. All conductor factors use the subgroup defined by the actual intersection. -/
theorem positive_and_inverse_in_subgroup (x u v : R) (hx : Primitive69 x)
    (hu : u^2 = -3) (hv : v^2 = -23) (c : Conjugation R) (hc : Compatible c u v)
    (O : Subring R) (D : Subgroup Rˣ) (hO : signedProduct x 1 ∈ O)
    (hD : normGenerators x hx (RealPart c u v) ⊆ D) :
    ∃ w : Oˣ, ((w : O) : R) = signedProduct x 1 ∧
      ((w⁻¹).val : R) = 25-signedProduct x 1 ∧
      w ∈ circularUnits O D ∧ w⁻¹ ∈ circularUnits O D := by
  obtain ⟨⟨ss,hs,he⟩,_,_,hi,_,_⟩ := real_circular_unit x u v hx hu hv c hc
  let w := integralUnit O hO hi
  let z := Units.map O.subtype.toMonoidHom w
  have hz : (z : R) = signedProduct x 1 := rfl
  have h := positive_mem_numbers x hx (RealPart c u v) ss hs z (hz.trans he)
  have hw : w ∈ circularUnits O D := (conductorNumbers_le _ _ _ _).mpr hD h
  exact ⟨w,rfl,rfl,hw,(circularUnits O D).inv_mem hw⟩

theorem positive_and_inverse_in_quadratic_order (x u v : R) (hx : Primitive69 x)
    (hu : u^2 = -3) (hv : v^2 = -23) (c : Conjugation R) (hc : Compatible c u v) :
    let O := quadraticOrder (signedProduct x 1)
    let D := conductorNumbers x hx (RealPart c u v)
    ∃ w : Oˣ, ((w : O) : R) = signedProduct x 1 ∧
      ((w⁻¹).val : R) = 25-signedProduct x 1 ∧
      w ∈ circularUnits O D ∧ w⁻¹ ∈ circularUnits O D :=
  positive_and_inverse_in_subgroup x u v hx hu hv c hc _ _ (quadraticOrder_mem _)
    Subgroup.subset_closure

end

open Polynomial

noncomputable def unitPolynomial : ℤ[X] := X^2 + (C (-25)*X + 1)

theorem unitPolynomial_tail_degree : (C (-25 : ℤ)*X + 1).natDegree ≤ 1 := by
  have h : (C (-25 : ℤ)*X).natDegree ≤ 1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le (-25 : ℤ) 1
  exact natDegree_add_le_of_le h (show (1 : ℤ[X]).natDegree ≤ 0 by simp)

theorem unitPolynomial_monic : unitPolynomial.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 2
  · exact natDegree_add_le_of_le (natDegree_X_pow_le 2) unitPolynomial_tail_degree
  · have h := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt unitPolynomial_tail_degree
        (by decide : 1 < 2))
    rw [unitPolynomial,coeff_add,coeff_X_pow_self,h,add_zero]

theorem integral_of_quadratic (e : R) (he : e^2-25*e+1=0) : IsIntegral ℤ e := by
  refine ⟨unitPolynomial,unitPolynomial_monic,?_⟩
  simpa [unitPolynomial, sub_eq_add_neg, neg_mul, add_assoc] using he

section
variable [CharZero R]

theorem positive_and_inverse_integral (x u v : R) (hx : Primitive69 x)
    (hu : u^2 = -3) (hv : v^2 = -23) (c : Conjugation R) (hc : Compatible c u v) :
    IsIntegral ℤ (signedProduct x 1) ∧ IsIntegral ℤ (25-signedProduct x 1) := by
  obtain ⟨_,_,_,_,he,hf⟩ := real_circular_unit x u v hx hu hv c hc
  exact ⟨integral_of_quadratic _ he,integral_of_quadratic _ hf⟩

/-- O may be the ring of integers of the real compositum inside R. Its
inclusion of real algebraic integers, and inclusion of norm generators in
the chosen circular numbers D, suffice to get actual units of O. -/
theorem positive_and_inverse_in_integers (x u v : R) (hx : Primitive69 x)
    (hu : u^2 = -3) (hv : v^2 = -23) (c : Conjugation R) (hc : Compatible c u v)
    (O : Subring R) (D : Subgroup Rˣ)
    (hO : ∀ z : R, RealPart c u v z → IsIntegral ℤ z → z ∈ O)
    (hD : normGenerators x hx (RealPart c u v) ⊆ D) :
    ∃ w : Oˣ, ((w : O) : R) = signedProduct x 1 ∧
      ((w⁻¹).val : R) = 25-signedProduct x 1 ∧
      w ∈ circularUnits O D ∧ w⁻¹ ∈ circularUnits O D := by
  obtain ⟨_,hr,_,_,he,_⟩ := real_circular_unit x u v hx hu hv c hc
  exact positive_and_inverse_in_subgroup x u v hx hu hv c hc O D
    (hO _ hr (integral_of_quadratic _ he)) hD

end

/-- The subring of the ambient field generated by the real algebraic integers
of the specified compositum. The next comparison identifies this presentation
with any specified integer ring having the usual carrier. -/
def realIntegerOrder (c : Conjugation R) (u v : R) : Subring R :=
  Subring.closure {z | RealPart c u v z ∧ IsIntegral ℤ z}

theorem realIntegerOrder_mem (c : Conjugation R) (u v z : R)
    (hr : RealPart c u v z) (hi : IsIntegral ℤ z) :
    z ∈ realIntegerOrder c u v :=
  Subring.subset_closure ⟨hr,hi⟩

theorem realIntegerOrder_eq_of_spec (c : Conjugation R) (u v : R) (O : Subring R)
    (hO : ∀ z : R, z ∈ O ↔ RealPart c u v z ∧ IsIntegral ℤ z) :
    realIntegerOrder c u v = O := by
  apply le_antisymm
  · apply Subring.closure_le.mpr
    intro z hz
    exact (hO z).mpr hz
  · intro z hz
    exact Subring.subset_closure ((hO z).mp hz)

variable [CharZero R]

theorem positive_and_inverse_in_real_integer_order (x u v : R) (hx : Primitive69 x)
    (hu : u^2 = -3) (hv : v^2 = -23) (c : Conjugation R) (hc : Compatible c u v)
    (D : Subgroup Rˣ) (hD : normGenerators x hx (RealPart c u v) ⊆ D) :
    let O := realIntegerOrder c u v
    ∃ w : Oˣ, ((w : O) : R) = signedProduct x 1 ∧
      ((w⁻¹).val : R) = 25-signedProduct x 1 ∧
      w ∈ circularUnits O D ∧ w⁻¹ ∈ circularUnits O D :=
  positive_and_inverse_in_integers x u v hx hu hv c hc _ D (realIntegerOrder_mem c u v) hD

end Reimann.CircularSubgroup69
