import Reimann.CircularRationalPeriod69
import Reimann.CircularQuadraticPower69
import Reimann.CircularGauss69
import Reimann.CircularKernel69

/-! Exclude 277th roots of both signed units in the rational quadratic field
by reducing primitive homogeneous coordinates at the two places over 1109. -/

namespace Reimann.CircularQuadraticNonpower69

open Lean.Grind CircularGauss69 CircularRational69 CircularRationalPeriod69

attribute [local instance] Ring.intCast

abbrev F := Fin 1109

def bitExponent : List Bool → Nat
  | [] => 0
  | b :: bs => (bitExponent bs + bitExponent bs) + (if b then 1 else 0)

def bitPower (v : F) : List Bool → F
  | [] => 1
  | b :: bs =>
    let w := bitPower v bs
    if b then w*w*v else w*w

theorem bitPower_correct (v : F) (bs : List Bool) : bitPower v bs = v^(bitExponent bs) := by
  induction bs with
  | nil => exact (Semiring.pow_zero v).symm
  | cons b bs ih =>
    cases b <;> simp only [bitPower, bitExponent, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, ih]
    · rw [Semiring.pow_add]
    · rw [Semiring.pow_succ, Semiring.pow_add]

def fermatDigits : List Bool :=
  [false,false,true,false,true,false,true,false,false,false,true]

theorem fermatExponent : bitExponent fermatDigits = 1108 := by decide +kernel

theorem fermat_table : ∀ v : F, bitPower v fermatDigits = if v = 0 then 0 else 1 := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 5000000 in
    decide +kernel

theorem fermat (v : F) : v^1108 = if v = 0 then 0 else 1 := by
  simpa only [bitPower_correct, fermatExponent] using fermat_table v

theorem prime_1109 : PrimeDivisor 1109 := by
  refine ⟨by decide, fun k hk => ?_⟩
  have bound := Nat.le_of_dvd (by decide : 0 < 1109) hk
  have check : ∀ i : Fin 1110, i.val ∣ 1109 → i.val = 1 ∨ i.val = 1109 := by
    set_option maxRecDepth 10000 in decide +kernel
  exact check ⟨k, by omega⟩ hk

theorem roots : (345 : F)^2 = 345+17 ∧ (765 : F)^2 = 765+17 := by decide +kernel

def residue (t : F) (w : CircularQuadratic69.Element) : F :=
  CircularQuadraticPower69.evaluateAt t w

theorem signed_fourth :
    (residue 345 CircularQuadratic69.epsilon)^4 = 725 ∧
    (residue 345 (CircularQuadratic69.conjugate CircularQuadratic69.epsilon))^4 = 361 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem fourth_power (v : F) : (v^277)^4 = v^1108 := by
  change (v^277)^4 = v^(((277+277)+277)+277)
  rw [Semiring.pow_add v ((277+277)+277) 277, Semiring.pow_add v (277+277) 277,
      Semiring.pow_add v 277 277]
  grind only

theorem denominator_zero (u d e : F) (he0 : e^4 ≠ 0) (he1 : e^4 ≠ 1)
    (hu : u^277 = d^277 * e) : d = 0 := by
  have h := congrArg (fun y : F => y^4) hu
  change (u^277)^4 = (d^277*e)^4 at h
  rw [CommSemiring.mul_pow, fourth_power, fourth_power, fermat u, fermat d] at h
  by_cases hd : d = 0
  · exact hd
  · simp only [hd, ite_false, Semiring.one_mul] at h
    by_cases hz : u = 0
    · simp only [hz, ite_true] at h
      exact False.elim (he0 h.symm)
    · simp only [hz, ite_false] at h
      exact False.elim (he1 h.symm)

theorem numerator_zero (u d e : F) (hd : d = 0) (h : u^277=d^277*e) : u = 0 := by
  have hh := congrArg (fun y : F => y^4) h
  change (u^277)^4 = (d^277*e)^4 at hh
  rw [CommSemiring.mul_pow, fourth_power, fourth_power, fermat u, fermat d, hd] at hh
  by_cases hu : u = 0
  · exact hu
  · simp only [hu, ite_false, ite_true, Semiring.zero_mul] at hh
    exact False.elim ((by decide : (1 : F) ≠ 0) hh)

theorem separate_coordinates (a b : F) (h : a+b*345=0) (k : a+b*765=0) :
    a=0 ∧ b=0 := by
  have hi : (235 : F)*(345-765) = 1 := by decide +kernel
  have hb : b=0 := by grind only
  exact ⟨by rw [hb] at h; grind only, hb⟩

theorem cast_zero_divides (z : Int) (h : (Int.cast z : F) = 0) : (1109 : Int) ∣ z :=
  Int.dvd_of_emod_eq_zero ((IsCharP.intCast_eq_zero_iff (α := F) 1109 z).mp h)

theorem primitive_coordinates (y : Element) :
    ∃ (d : Nat) (w : CircularQuadratic69.Element),
      ofIntegral ((d : Int), 0) * y = ofIntegral w ∧
      ¬ ((1109 : Int) ∣ (d : Int) ∧ (1109 : Int) ∣ w.1 ∧ (1109 : Int) ∣ w.2) := by
  obtain ⟨d, v, _, h, prim⟩ := exists_primitive_lift [y.a,y.b,1] (by simp)
  have ha := h 0
  have hb := h 1
  have hd := h 2
  change (d : Rat)*y.a = (v 0 : Rat) at ha
  change (d : Rat)*y.b = (v 1 : Rat) at hb
  change (d : Rat)*1 = (v 2 : Rat) at hd
  have dv : (d : Int) = v 2 := Rat.intCast_inj.mp (by rw [Rat.intCast_natCast, ← hd, Rat.mul_one])
  refine ⟨d, (v 0,v 1), ?_, ?_⟩
  · change times (ofIntegral ((d : Int), 0)) y = ofIntegral _
    apply ext_coordinates <;> simp only [times, ofIntegral, Rat.intCast_natCast] <;> grind only
  · rintro ⟨hD, hA, hB⟩
    obtain ⟨i, non⟩ := prim 1109 prime_1109
    apply non
    cases i with
    | zero => exact hA
    | succ i => cases i with
      | zero => exact hB
      | succ i => cases i with
        | zero => exact dv ▸ hD
        | succ j =>
          have hv := h (j+3)
          change (d : Rat)*0 = (v (j+3) : Rat) at hv
          have hz : v (j+3) = 0 := Rat.intCast_eq_zero_iff.mp (by rw [← hv, Rat.mul_zero])
          rw [hz]
          exact Int.dvd_zero _

theorem integral_injective {u v : CircularQuadratic69.Element} (h : ofIntegral u = ofIntegral v) : u = v := by
  exact Prod.ext (Rat.intCast_inj.mp (congrArg Element.a h)) (Rat.intCast_inj.mp (congrArg Element.b h))

theorem integral_product (u v : CircularQuadratic69.Element) :
    ofIntegral (CircularQuadratic69.product u v) = ofIntegral u * ofIntegral v := by
  change _ = times _ _
  apply ext_coordinates <;> simp only [ofIntegral, CircularQuadratic69.product, times,
    Rat.intCast_add, Rat.intCast_mul] <;> grind only

theorem integral_power (u : CircularQuadratic69.Element) (n : Nat) :
    ofIntegral (CircularQuadraticPower69.orderPower u n) = (ofIntegral u)^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [CircularQuadraticPower69.orderPower, integral_product, ih, Semiring.pow_succ]

theorem clear_power (y : Element) (d : Nat) (w e : CircularQuadratic69.Element)
    (h : ofIntegral ((d : Int),0) * y = ofIntegral w) (hy : y^277 = ofIntegral e) :
    CircularQuadraticPower69.orderPower w 277 =
      CircularQuadratic69.product (CircularQuadraticPower69.orderPower ((d : Int), 0) 277) e := by
  apply integral_injective
  rw [integral_product, integral_power, integral_power, ← h, CommSemiring.mul_pow, hy]

theorem residue_scalar (t : F) (d : Nat) : residue t ((d : Int),0) = Int.cast (d : Int) := by
  unfold residue CircularQuadraticPower69.evaluateAt
  simp only [Ring.intCast_zero, Semiring.zero_mul, Semiring.add_zero]

theorem specialization (t : F) (ht : t^2=t+17) (d : Nat) (w e : CircularQuadratic69.Element)
    (h : CircularQuadraticPower69.orderPower w 277 =
      CircularQuadratic69.product (CircularQuadraticPower69.orderPower ((d : Int),0) 277) e) :
    (residue t w)^277 = (Int.cast (d : Int) : F)^277 * residue t e := by
  have hh := congrArg (CircularQuadraticPower69.evaluateAt t) h
  rw [CircularQuadraticPower69.evaluateAt_product t ht,
      CircularQuadraticPower69.evaluateAt_power t ht, CircularQuadraticPower69.evaluateAt_power t ht] at hh
  change (residue t w)^277 = (residue t ((d : Int),0))^277 * residue t e at hh
  rw [residue_scalar] at hh
  exact hh

theorem local_obstruction (e : CircularQuadratic69.Element)
    (he0 : (residue 345 e)^4 ≠ 0) (he1 : (residue 345 e)^4 ≠ 1) (y : Element) :
    y^277 ≠ ofIntegral e := by
  intro hy
  obtain ⟨d,w,hw,primitive⟩ := primitive_coordinates y
  have clear := clear_power y d w e hw hy
  have h := specialization 345 roots.1 d w e clear
  have k := specialization 765 roots.2 d w e clear
  have hd := denominator_zero _ _ _ he0 he1 h
  have h1 := numerator_zero _ _ _ hd h
  have h2 := numerator_zero _ _ _ hd k
  obtain ⟨ha,hb⟩ := separate_coordinates (Int.cast w.1) (Int.cast w.2) h1 h2
  exact primitive ⟨cast_zero_divides _ hd, cast_zero_divides _ ha, cast_zero_divides _ hb⟩

theorem quadratic_field_nonpowers (y : Element) :
    y^277 ≠ ofIntegral CircularQuadratic69.epsilon ∧
    y^277 ≠ ofIntegral (CircularQuadratic69.conjugate CircularQuadratic69.epsilon) := by
  constructor
  · apply local_obstruction <;> rw [signed_fourth.1] <;> decide +kernel
  · apply local_obstruction <;> rw [signed_fourth.2] <;> decide +kernel

theorem signed_inverse :
    ofIntegral CircularQuadratic69.epsilon *
      ofIntegral (CircularQuadratic69.conjugate CircularQuadratic69.epsilon) = 1 := by
  rw [← integral_product, CircularQuadratic69.epsilon_norm_one]
  rfl

theorem degree276_field_obstruction (y : Element) :
    y^277 ≠ (ofIntegral CircularQuadratic69.epsilon)^276 ∧
    y^277 ≠ (ofIntegral (CircularQuadratic69.conjugate CircularQuadratic69.epsilon))^276 := by
  let e := ofIntegral CircularQuadratic69.epsilon
  let f := ofIntegral (CircularQuadratic69.conjugate CircularQuadratic69.epsilon)
  have h : e*f=1 := signed_inverse
  have k : f*e=1 := (CommSemiring.mul_comm ..).trans h
  exact ⟨fun hy => (quadratic_field_nonpowers (y*f)).2
    (CircularQuadraticPower69.one_more_power_of_inverse e f y 276 h hy),
    fun hy => (quadratic_field_nonpowers (y*e)).1
    (CircularQuadraticPower69.one_more_power_of_inverse f e y 276 k hy)⟩

theorem projected_periods : (725 : F)^277 = 1 ∧ (361 : F)^277 = 1 := by decide +kernel

theorem power_mod_277 (u : F) (hu : u^277 = 1) (n : Nat) : u^n = u^(n % 277) := by
  calc
    u^n = u^(277*(n/277) + n%277) := congrArg (fun k : Nat => u^k) (Nat.div_add_mod n 277).symm
    _ = u^(n%277) := by rw [Semiring.pow_add, ← CircularKernel69.power_of_power, hu, Semiring.one_pow, Semiring.one_mul]

theorem projected_orders : ∀ r : Fin 277, r.val ≠ 0 →
    ((725 : F)^r.val ≠ 0 ∧ (725 : F)^r.val ≠ 1) ∧
    ((361 : F)^r.val ≠ 0 ∧ (361 : F)^r.val ≠ 1) := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 5000000 in
    decide +kernel

theorem projections_of_nonmultiple (n : Nat) (hn : ¬277 ∣ n) :
    ((725 : F)^n ≠ 0 ∧ (725 : F)^n ≠ 1) ∧
    ((361 : F)^n ≠ 0 ∧ (361 : F)^n ≠ 1) := by
  rw [power_mod_277 _ projected_periods.1, power_mod_277 _ projected_periods.2]
  exact projected_orders ⟨n%277, Nat.mod_lt _ (by decide)⟩ (fun h => hn (Nat.dvd_of_mod_eq_zero h))

theorem project_fourth (e : CircularQuadratic69.Element) (n : Nat) :
    (residue 345 (CircularQuadraticPower69.orderPower e n))^4 = ((residue 345 e)^4)^n := by
  unfold residue
  rw [CircularQuadraticPower69.evaluateAt_power _ roots.1,
    CircularKernel69.power_of_power, CircularKernel69.power_of_power, Nat.mul_comm n 4]

theorem signed_nonmultiple (n : Nat) (hn : ¬277 ∣ n) (y : Element) :
    y^277 ≠ (ofIntegral CircularQuadratic69.epsilon)^n ∧
    y^277 ≠ (ofIntegral (CircularQuadratic69.conjugate CircularQuadratic69.epsilon))^n := by
  obtain ⟨hp, hm⟩ := projections_of_nonmultiple n hn
  rw [← integral_power, ← integral_power]
  constructor
  · apply local_obstruction <;> rw [project_fourth, signed_fourth.1]
    · exact hp.1
    · exact hp.2
  · apply local_obstruction <;> rw [project_fourth, signed_fourth.2]
    · exact hm.1
    · exact hm.2

theorem power_of_multiple (e : Element) (n : Nat) (hn : 277 ∣ n) :
    ∃ y : Element, y^277 = e^n := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨e^m, (CircularKernel69.power_of_power e m 277).trans (congrArg (fun k : Nat => e^k) (Nat.mul_comm ..))⟩

theorem signed_power_classes (n : Nat) :
    ((∃ y : Element, y^277 = (ofIntegral CircularQuadratic69.epsilon)^n) ↔ 277 ∣ n) ∧
    ((∃ y : Element, y^277 = (ofIntegral (CircularQuadratic69.conjugate CircularQuadratic69.epsilon))^n) ↔ 277 ∣ n) := by
  constructor
  · refine ⟨?_, power_of_multiple _ n⟩
    rintro ⟨y,hy⟩
    exact Classical.byContradiction (fun hn => (signed_nonmultiple n hn y).1 hy)
  · refine ⟨?_, power_of_multiple _ n⟩
    rintro ⟨y,hy⟩
    exact Classical.byContradiction (fun hn => (signed_nonmultiple n hn y).2 hy)

end Reimann.CircularQuadraticNonpower69
