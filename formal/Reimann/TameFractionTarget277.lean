import Reimann.TameFractionCompletion277

namespace Reimann.TameFractionTarget277

open TameLimit277 TameFractionCompletion277

/-- An injective realization of the inverse-limit integers in a field. -/
structure IntegralMap (K : Type) [Lean.Grind.Field K] where
  app : Integer277 → K
  zero : app (ofInt 0) = 0
  add : ∀ x y, app (TameLimit277.add x y) = app x + app y
  mul : ∀ x y, app (TameLimit277.mul x y) = app x * app y
  injective : ∀ {x y}, app x = app y → x = y

variable {K : Type} [Lean.Grind.Field K]

theorem denominator_nonzero (f : IntegralMap K) (x : Pair Integer277 (ofInt 0)) :
    f.app x.den ≠ 0 := fun h => x.nonzero (f.injective (h.trans f.zero.symm))

def pairValue (f : IntegralMap K) (x : Pair Integer277 (ofInt 0)) : K :=
  f.app x.num / f.app x.den

theorem cancel_denominator (f : IntegralMap K) (x : Pair Integer277 (ofInt 0)) :
    pairValue f x * f.app x.den = f.app x.num :=
  Lean.Grind.Field.div_mul_cancel (denominator_nonzero f x)

theorem div_eq_iff_cross (a b c d : K) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a*d = c*b := by
  have hab := Lean.Grind.Field.div_mul_cancel (x := a) hb
  have hcd := Lean.Grind.Field.div_mul_cancel (x := c) hd
  have hib := Lean.Grind.Field.mul_inv_cancel hb
  have hid := Lean.Grind.Field.mul_inv_cancel hd
  constructor
  · intro h
    calc
      a*d = (a/b*b)*d := by rw [hab]
      _ = (c/d*d)*b := by rw [h]; grind
      _ = c*b := by rw [hcd]
  · intro h
    calc
      a/b = (a*d)*(b⁻¹*d⁻¹) := by rw [Lean.Grind.Field.div_eq_mul_inv]; grind
      _ = (c*b)*(b⁻¹*d⁻¹) := congrArg (fun x : K => x*(b⁻¹*d⁻¹)) h
      _ = c/d := by rw [Lean.Grind.Field.div_eq_mul_inv]; grind

theorem pairValue_equal_iff (f : IntegralMap K) (a b : Pair Integer277 (ofInt 0)) :
    pairValue f a = pairValue f b ↔ Cross mul a b := by
  rw [pairValue, pairValue, div_eq_iff_cross _ _ _ _ (denominator_nonzero f a)
    (denominator_nonzero f b), ← f.mul, ← f.mul]
  exact ⟨fun h => f.injective h, congrArg f.app⟩

def evaluate (f : IntegralMap K) : AdicRatios → K :=
  Quot.lift (pairValue f) (fun a b h => (pairValue_equal_iff f a b).mpr h)

theorem evaluate_injective (f : IntegralMap K) (x y : AdicRatios)
    (h : evaluate f x = evaluate f y) : x = y := by
  induction x using Quot.ind with
  | mk a =>
    induction y using Quot.ind with
    | mk b => exact Quot.sound ((pairValue_equal_iff f a b).mp h)

theorem evaluate_surjective (f : IntegralMap K)
    (spans : ∀ z : K, ∃ a b : Integer277, b ≠ ofInt 0 ∧ f.app a / f.app b = z)
    (z : K) : ∃ q : AdicRatios, evaluate f q = z := by
  obtain ⟨a,b,hb,h⟩ := spans z
  exact ⟨Quot.mk _ ⟨a,b,hb⟩,h⟩

theorem evaluate_mul (f : IntegralMap K) (x y : AdicRatios) :
    evaluate f (ratioMul x y) = evaluate f x * evaluate f y := by
  induction x using Quot.ind with
  | mk a =>
    induction y using Quot.ind with
    | mk b =>
      change f.app (mul a.num b.num) / f.app (mul a.den b.den) =
        (f.app a.num / f.app a.den) * (f.app b.num / f.app b.den)
      simp only [f.mul,Lean.Grind.Field.div_eq_mul_inv,Lean.Grind.Field.inv_mul]
      grind

theorem evaluate_add (f : IntegralMap K) (x y : AdicRatios) :
    evaluate f (ratioAdd x y) = evaluate f x + evaluate f y := by
  induction x using Quot.ind with
  | mk a =>
    induction y using Quot.ind with
    | mk b =>
      change f.app (add (mul a.num b.den) (mul b.num a.den)) / f.app (mul a.den b.den) =
        f.app a.num / f.app a.den + f.app b.num / f.app b.den
      have ha := Lean.Grind.Field.mul_inv_cancel (denominator_nonzero f a)
      have hb := Lean.Grind.Field.mul_inv_cancel (denominator_nonzero f b)
      simp only [f.add,f.mul,Lean.Grind.Field.div_eq_mul_inv,Lean.Grind.Field.inv_mul]
      grind

def rationalPair (r : Rat) : Pair Integer277 (ofInt 0) :=
  ⟨ofInt r.num, ofInt (r.den : Int), fun h => r.den_nz (by
    have he := ofInt_injective h
    omega)⟩

def rational (r : Rat) : AdicRatios := Quot.mk _ (rationalPair r)

theorem evaluate_rational (f : IntegralMap K) (r : Rat) :
    evaluate f (rational r) = f.app (ofInt r.num) / f.app (ofInt (r.den : Int)) :=
  rfl

theorem rational_injective (p q : Rat) (h : rational p = rational q) : p = q := by
  have eq := (adic_fraction_equal_iff (rationalPair p) (rationalPair q)).mp h
  change mul (ofInt p.num) (ofInt (q.den : Int)) =
      mul (ofInt q.num) (ofInt (p.den : Int)) at eq
  rw [← ofInt_mul, ← ofInt_mul] at eq
  exact Rat.eq_iff_mul_eq_mul.mpr (ofInt_injective eq)

theorem den_not_zero (q : Rat) : (q.den : Int) ≠ 0 := by
  have h := q.den_nz
  omega

theorem presented_cross (q : Rat) (n d : Int) (hd : d ≠ 0) (h : q = Rat.divInt n d) :
    q.num * d = n * (q.den : Int) :=
  (Rat.divInt_eq_divInt_iff (den_not_zero q) hd).mp ((Rat.num_divInt_den q).trans h)

theorem rational_add (p q : Rat) : rational (p+q) = ratioAdd (rational p) (rational q) := by
  have hd : (p.den : Int)*(q.den : Int) ≠ 0 :=
    Int.mul_ne_zero (den_not_zero p) (den_not_zero q)
  have h := Rat.divInt_add_divInt p.num q.num (den_not_zero p) (den_not_zero q)
  rw [Rat.num_divInt_den p,Rat.num_divInt_den q] at h
  have eq := congrArg ofInt (presented_cross (p+q) _ _ hd h)
  apply (adic_fraction_equal_iff (rationalPair (p+q)) (plusPair (rationalPair p) (rationalPair q))).mpr
  simpa only [plusPair,rationalPair,← ofInt_mul,← ofInt_add] using eq

theorem rational_mul (p q : Rat) : rational (p*q) = ratioMul (rational p) (rational q) := by
  have hd : (p.den : Int)*(q.den : Int) ≠ 0 :=
    Int.mul_ne_zero (den_not_zero p) (den_not_zero q)
  have h := Rat.divInt_mul_divInt p.num q.num (d₁ := (p.den : Int)) (d₂ := (q.den : Int))
  rw [Rat.num_divInt_den p,Rat.num_divInt_den q] at h
  have eq := congrArg ofInt (presented_cross (p*q) _ _ hd h)
  apply (adic_fraction_equal_iff (rationalPair (p*q)) (timesPair (rationalPair p) (rationalPair q))).mpr
  simpa only [timesPair,rationalPair,← ofInt_mul] using eq

end Reimann.TameFractionTarget277
