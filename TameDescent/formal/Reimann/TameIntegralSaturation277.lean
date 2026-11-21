import Reimann.TameOrderFaithful277
import Reimann.TameTraceLattice277

namespace Reimann.TameIntegralSaturation277

open TameRationalField277 TameOrderFaithful277 TameArithmetic277
open TameBiquadratic277 TameTraceLattice277

/-- Integer coefficients are listed in ascending degree; the leading coefficient is one. -/
def monicValue (z : Biquad) (f : List Int) : Biquad :=
  f.foldr (fun (c : Int) tail => ba (bm z tail) (scalar (c : Rat))) (scalar 1)

def MonicIntegral (z : Biquad) : Prop := ∃ f : List Int, monicValue z f = scalar 0

/-- Product of the relative quadratic polynomial and its conjugate. -/
def monicCoefficients (v : OrderCoordinates) : List Int :=
  [absolute v, -4*(v.1.1*(relative v).1 + 3*v.1.2*(relative v).2),
   2*(relative v).1 + 4*(v.1.1^2 + 3*v.1.2^2), -4*v.1.1]

set_option maxHeartbeats 1200000 in
theorem quartic_vanishes (v : OrderCoordinates) :
    monicValue (rationalize v) (monicCoefficients v) = scalar 0 := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [monicValue, monicCoefficients, absolute, relative, List.foldr_cons, List.foldr_nil,
      rationalize, scalar, ba, bm, qa, qm, qs, Rat.intCast_add, Rat.intCast_mul,
      Rat.intCast_sub, Rat.intCast_neg, Int.pow_succ, Int.pow_zero] <;> grind

theorem order_integral (v : OrderCoordinates) : MonicIntegral (rationalize v) :=
  ⟨monicCoefficients v, quartic_vanishes v⟩

def dilate (d : Int) (z : Biquad) := bm (scalar (d : Rat)) z

theorem dilate_product (u v : Int) (x y : Biquad) :
    dilate (u*v) (bm x y) = bm (dilate u x) (dilate v y) := by
  unfold dilate
  rw [Rat.intCast_mul, ← (scalar_embedding _ _).2.2]
  simp only [mul_assoc]
  rw [← mul_assoc (scalar (v : Rat)) x y, mul_comm (scalar (v : Rat)) x, mul_assoc]

theorem rationalize_sum (v w : OrderCoordinates) :
    rationalize (componentAdd v w) = ba (rationalize v) (rationalize w) := by
  apply Prod.ext <;> apply Prod.ext <;> simp [rationalize, componentAdd, ba, qa]

theorem rationalize_product (v w : OrderCoordinates) :
    rationalize (product (-3) (-23) v w) = bm (rationalize v) (rationalize w) := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases w with ⟨⟨e,f⟩,⟨g,h⟩⟩
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [product, rationalize,bm,qa,qm,qs,Rat.intCast_add,Rat.intCast_mul,
       Rat.intCast_neg] <;> grind

theorem rationalize_scalar (a : Int) : rationalize (integerCoordinates a) = scalar (a : Rat) := rfl

def homogeneous (d : Int) (x : OrderCoordinates) : List Int → OrderCoordinates
  | [] => integerCoordinates 1
  | c :: cs => componentAdd (product (-3) (-23) x (homogeneous d x cs))
      (integerCoordinates (d^(cs.length+1)*c))

theorem homogeneous_value (d : Int) (x : OrderCoordinates) (z : Biquad)
    (hx : rationalize x = dilate d z) (f : List Int) :
    rationalize (homogeneous d x f) = dilate (d^f.length) (monicValue z f) := by
  induction f with
  | nil =>
    change scalar 1 = dilate (d^0) (scalar 1)
    simp [dilate,scalar,bm,qm,qa,qs] <;> grind
  | cons c cs ih =>
    change rationalize (componentAdd _ _) = dilate (d^(cs.length+1))
      (ba (bm z (monicValue z cs)) (scalar (c : Rat)))
    rw [rationalize_sum,rationalize_product,rationalize_scalar,ih,hx]
    unfold dilate at *
    rw [distributive, (scalar_embedding _ _).2.2, Rat.intCast_mul]
    congr 1
    rw [Int.pow_succ']
    exact (dilate_product d (d^cs.length) z (monicValue z cs)).symm

theorem homogeneous_residue (t : Int) (x : OrderCoordinates) (f : List Int) (i : Fin 4)
    (h : TameOrderPrimes277.red (homogeneous (277*t) x f) i = 0) :
    TameOrderPrimes277.red x i = 0 := by
  induction f with
  | nil =>
    change TameOrderPrimes277.red (TameOrderPrimes277.scalar 1) i = 0 at h
    rw [TameOrderPrimes277.red_scalar] at h
    exact False.elim ((by decide : (1 : TameFiber277.F) ≠ 0) h)
  | cons c cs ih =>
    let a := (277*t)^(cs.length+1)*c
    have ha : (277 : Int) ∣ a := ⟨t*((277*t)^cs.length*c), by dsimp [a]; rw [Int.pow_succ']; grind⟩
    have zero := (TameOrderPrimes277.contraction i a).mpr ha
    change TameOrderPrimes277.red (integerCoordinates a) i = 0 at zero
    change TameOrderPrimes277.red (componentAdd (product (-3) (-23) x _) (integerCoordinates a)) i = 0 at h
    rw [TameOrderPrimes277.red_add,TameOrderPrimes277.red_mul] at h
    change _ * _ + TameOrderPrimes277.red (integerCoordinates a) i = 0 at h
    rw [zero,Fin.add_zero] at h
    exact (TameFiber277.field_prime _ _ h).elim id ih

theorem rationalize_injective {u v : OrderCoordinates} (h : rationalize u = rationalize v) : u = v := by
  rcases u with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases v with ⟨⟨e,f⟩,⟨g,j⟩⟩
  simpa [rationalize] using h

theorem divide_numerator (t : Int) (v : OrderCoordinates) (z : Biquad)
    (hz : MonicIntegral z) (hv : rationalize v = dilate (277*t) z) :
    ∃ w : OrderCoordinates, rationalize v = dilate 277 (rationalize w) := by
  obtain ⟨f,hf⟩ := hz
  have h := homogeneous_value (277*t) v z hv f
  rw [hf] at h
  have h₀ : homogeneous (277*t) v f = integerCoordinates 0 := by
    apply rationalize_injective
    rw [h,rationalize_scalar]
    simp [dilate,scalar,bm,qa,qm,qs] <;> grind
  have hred : TameOrderPrimes277.red v = TameOrderPrimes277.red (integerCoordinates 0) := by
    funext i
    have zero : TameOrderPrimes277.red (integerCoordinates 0) i = 0 :=
      (TameOrderPrimes277.contraction i 0).mpr (Int.dvd_zero _)
    rw [zero]
    apply homogeneous_residue t v f i
    rwa [h₀]
  obtain ⟨w, he⟩ := TameOrderPrimes277.translate hred
  refine ⟨w, ?_⟩
  rw [he,rationalize_sum,rationalize_product,rationalize_scalar]
  change ba (scalar 0) (bm (rationalize w) (scalar 277)) = bm (scalar 277) (rationalize w)
  rw [mul_comm (rationalize w)]
  simp [ba,qa,scalar] <;> grind

theorem cancel_dilate {z w : Biquad} (h : dilate 277 z = dilate 277 w) : z = w := by
  simp only [dilate,TameTraceLattice277.scalar_mul_coords,Prod.mk.injEq] at h
  apply Prod.ext <;> apply Prod.ext <;> grind

theorem remove_denominator (z : Biquad) (hz : MonicIntegral z) (d : Nat) (hd : d > 0)
    (v : OrderCoordinates) (hv : rationalize v = dilate (d : Int) z) :
    ∃ k : Nat, ¬ (277 : Int) ∣ (k : Int) ∧ ∃ w : OrderCoordinates, rationalize w = dilate (k : Int) z := by
  induction d using Nat.strongRecOn generalizing v with
  | ind d ih =>
    by_cases h : (277 : Int) ∣ (d : Int)
    · let t := d/277
      have he : (d : Int) = 277*(t : Int) := by dsimp [t]; omega
      rw [he] at hv
      obtain ⟨w,hw⟩ := divide_numerator t v z hz hv
      have ht := TameTraceLattice277.scale_twice 277 (t : Int) z
      exact ih t (by dsimp [t]; omega) (by dsimp [t]; omega) w
        (cancel_dilate (hw.symm.trans (hv.trans ht.symm)))
    · exact ⟨d,h,v,hv⟩

theorem common_denominator (z : Biquad) :
    ∃ d : Nat, d > 0 ∧ ∃ v : OrderCoordinates, rationalize v = dilate (d : Int) z := by
  rcases z with ⟨⟨a,b⟩,⟨c,e⟩⟩
  let d := a.den*b.den*c.den*e.den
  have hd : d > 0 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos a.den_pos b.den_pos) c.den_pos) e.den_pos
  let v : OrderCoordinates :=
    ((a.num*(b.den : Int)*c.den*e.den, (a.den : Int)*b.num*c.den*e.den),
     ((a.den : Int)*b.den*c.num*e.den, (a.den : Int)*b.den*c.den*e.num))
  refine ⟨d,hd,v,?_⟩
  have ha := rational_numerator a
  have hb := rational_numerator b
  have hc := rational_numerator c
  have he := rational_numerator e
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [v,d,rationalize,dilate,scalar_mul_coords,Int.natCast_mul,Rat.intCast_mul] <;> grind

theorem in_order_iff (z : Biquad) : InOrder z ↔ ∃ v : OrderCoordinates, rationalize v = z := by
  constructor
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩
    exact ⟨((a,b),(c,d)), Prod.ext (Prod.ext ha.symm hb.symm) (Prod.ext hc.symm hd.symm)⟩
  · rintro ⟨v,rfl⟩
    exact ⟨⟨v.1.1,rfl⟩,⟨v.1.2,rfl⟩,⟨v.2.1,rfl⟩,⟨v.2.2,rfl⟩⟩

theorem integral_denominator (z : Biquad) (hz : MonicIntegral z) : Localized InOrder z := by
  obtain ⟨d,hd,v,hv⟩ := common_denominator z
  obtain ⟨k,hk,w,hw⟩ := remove_denominator z hz d hd v hv
  exact ⟨k,hk,(in_order_iff _).mpr ⟨w,hw⟩⟩

theorem nonmultiple_product {a b : Int} (ha : ¬ (277 : Int) ∣ a) (hb : ¬ (277 : Int) ∣ b) :
    ¬ (277 : Int) ∣ a*b := by
  intro h
  let P := TameOrderPrimes277.coordinateKernel 0
  have product_scalar : product (-3) (-23) (integerCoordinates a) (integerCoordinates b) =
      integerCoordinates (a*b) := by
    apply Prod.ext <;> apply Prod.ext <;> simp [product,integerCoordinates]
  have hp : P (product (-3) (-23) (integerCoordinates a) (integerCoordinates b)) := by
    rw [product_scalar]
    exact (TameOrderPrimes277.contraction 0 _).mpr h
  rcases (TameOrderPrimes277.coordinate_prime 0).prime hp with h' | h'
  · exact ha ((TameOrderPrimes277.contraction 0 _).mp h')
  · exact hb ((TameOrderPrimes277.contraction 0 _).mp h')

/-- The localization of all roots of monic integer polynomials agrees with that
of the explicit integer-coordinate order, without supplying an integral basis. -/
theorem integral_localization (z : Biquad) :
    Localized MonicIntegral z ↔ Localized InOrder z := by
  constructor
  · rintro ⟨s,hs,hz⟩
    obtain ⟨t,ht,h⟩ := integral_denominator _ hz
    rw [scale_twice] at h
    exact ⟨t*s,nonmultiple_product ht hs,h⟩
  · rintro ⟨s,hs,hz⟩
    obtain ⟨v,hv⟩ := (in_order_iff _).mp hz
    exact ⟨s,hs,hv ▸ order_integral v⟩

end Reimann.TameIntegralSaturation277
