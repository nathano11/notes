import Reimann.TameOrderCompletion277
import Reimann.TameAdicDomain277

namespace Reimann.TameFractionCompletion277

/-- Numerator and a nonzero denominator. -/
structure Pair (R : Type) (zero : R) where
  num : R
  den : R
  nonzero : den ≠ zero

def Cross {R : Type} {zero : R} (times : R → R → R) (x y : Pair R zero) : Prop :=
  times x.num y.den = times y.num x.den

/-- The quotient by cross multiplication. Cancellation below proves when
equality here is exactly the displayed cross multiplication condition. -/
def Fractions (R : Type) (zero : R) (times : R → R → R) := Quot (@Cross R zero times)

def mapPair {a : A} {b : B} (f : A → B) (reflect : ∀ x, f x = b → x = a)
    (x : Pair A a) : Pair B b :=
  ⟨f x.num, f x.den, fun h => x.nonzero (reflect _ h)⟩

theorem map_cross {a : A} {b : B} {s : A → A → A} {t : B → B → B}
    (f : A → B) (reflect : ∀ x, f x = b → x = a)
    (hm : ∀ x y, f (s x y) = t (f x) (f y)) (x y : Pair A a) (h : Cross s x y) :
    Cross t (mapPair f reflect x) (mapPair f reflect y) :=
  (hm _ _).symm.trans ((congrArg f h).trans (hm _ _))

def mapFractions {a : A} {b : B} {s : A → A → A} {t : B → B → B}
    (f : A → B) (reflect : ∀ x, f x = b → x = a)
    (hm : ∀ x y, f (s x y) = t (f x) (f y)) : Fractions A a s → Fractions B b t :=
  Quot.lift (fun x => Quot.mk _ (mapPair f reflect x))
    (fun x y h => Quot.sound (map_cross f reflect hm x y h))

theorem mapPair_inverse {a : A} {b : B} (f : A → B) (g : B → A)
    (hf : ∀ x, f x = b → x = a) (hg : ∀ x, g x = a → x = b)
    (h : ∀ x, g (f x) = x) (x : Pair A a) :
    mapPair g hg (mapPair f hf x) = x := by
  cases x
  simp [mapPair,h]

theorem mapFractions_inverse {a : A} {b : B} {s : A → A → A} {t : B → B → B}
    (f : A → B) (g : B → A) (hf : ∀ x, f x = b → x = a)
    (hg : ∀ x, g x = a → x = b) (fm : ∀ x y, f (s x y) = t (f x) (f y))
    (gm : ∀ x y, g (t x y) = s (g x) (g y)) (h : ∀ x, g (f x) = x)
    (z : Fractions A a s) :
    mapFractions g hg gm (mapFractions f hf fm z) = z := by
  induction z using Quot.ind with
  | mk x => exact congrArg (Quot.mk _) (mapPair_inverse f g hf hg h x)

theorem swap_factors (s : R → R → R) (assoc : ∀ x y z, s (s x y) z = s x (s y z))
    (comm : ∀ x y, s x y = s y x) (x y z : R) : s (s x y) z = s (s x z) y := by
  rw [assoc, comm y z, ← assoc]

theorem cross_trans {zero : R} (s : R → R → R)
    (assoc : ∀ x y z, s (s x y) z = s x (s y z)) (comm : ∀ x y, s x y = s y x)
    (cancel : ∀ d, d ≠ zero → ∀ x y, s x d = s y d → x=y)
    (x y z : Pair R zero) (hxy : Cross s x y) (hyz : Cross s y z) : Cross s x z := by
  apply cancel y.den y.nonzero
  calc
    s (s x.num z.den) y.den = s (s x.num y.den) z.den := swap_factors _ assoc comm _ _ _
    _ = s (s y.num x.den) z.den := congrArg (fun k => s k z.den) hxy
    _ = s (s y.num z.den) x.den := swap_factors _ assoc comm _ _ _
    _ = s (s z.num y.den) x.den := congrArg (fun k => s k x.den) hyz
    _ = s (s z.num x.den) y.den := swap_factors _ assoc comm _ _ _

theorem fraction_equal_iff {zero : R} (s : R → R → R)
    (assoc : ∀ x y z, s (s x y) z = s x (s y z)) (comm : ∀ x y, s x y = s y x)
    (cancel : ∀ d, d ≠ zero → ∀ x y, s x d = s y d → x=y)
    (x y : Pair R zero) :
    Quot.mk (Cross s) x = Quot.mk (Cross s) y ↔ Cross s x y := by
  let S : Setoid (Pair R zero) := ⟨Cross s,
    ⟨fun _ => rfl, fun h => Eq.symm h, cross_trans s assoc comm cancel _ _ _⟩⟩
  exact ⟨fun h => @Quotient.exact _ S _ _ h, Quot.sound⟩

theorem reflect_base (f : A → B) (g : B → A) (h : ∀ x, g (f x) = x)
    (a : A) (b : B) (hz : g b = a) (x : A) (hx : f x = b) : x = a :=
  (h x).symm.trans ((congrArg g hx).trans hz)

open Reimann.TameLimit277 Reimann.TameOrderCompletion277

/-- Nonzero-denominator fractions in the inverse-limit integers. -/
abbrev AdicRatios := Fractions Integer277 (ofInt 0) mul

variable {O : Type} (E : Evaluation O) (op : O → O → O)
    (hm : ∀ n a b, E.eval n (op a b) % modulus n = (E.eval n a * E.eval n b) % modulus n)

/-- The multiplication is the one induced on the order completion from op. -/
abbrev OrderRatios := Fractions (Completion E) (fromInteger E (ofInt 0))
    (onCompletion (multiplication E op hm))

def toAdicRatios : OrderRatios E op hm → AdicRatios :=
  mapFractions (toInteger E)
    (reflect_base _ _ (fromInteger_toInteger E) _ _ rfl)
    (toInteger_onCompletion (multiplication E op hm))

def fromAdicRatios : AdicRatios → OrderRatios E op hm :=
  mapFractions (fromInteger E)
    (reflect_base _ _ (toInteger_fromInteger E) _ _ (toInteger_fromInteger E _))
    (fromInteger_limitOp (multiplication E op hm))

theorem completion_fraction_roundtrips :
    (∀ x, fromAdicRatios E op hm (toAdicRatios E op hm x) = x) ∧
    (∀ y, toAdicRatios E op hm (fromAdicRatios E op hm y) = y) :=
  ⟨mapFractions_inverse (toInteger E) (fromInteger E) _ _ _ _ (fromInteger_toInteger E),
   mapFractions_inverse (fromInteger E) (toInteger E) _ _ _ _ (toInteger_fromInteger E)⟩

theorem adic_mul_comm (x y : Integer277) : mul x y = mul y x := by
  apply equal_of_residues
  intro n
  change (x.residue n*y.residue n)%_ = (y.residue n*x.residue n)%_
  rw [Int.mul_comm]

theorem adic_mul_assoc (x y z : Integer277) : mul (mul x y) z = mul x (mul y z) := by
  apply equal_of_residues
  intro n
  change ((x.residue n * y.residue n) % modulus n * z.residue n) % modulus n =
    (x.residue n * ((y.residue n * z.residue n) % modulus n)) % modulus n
  have hl := Int.mul_emod (x.residue n*y.residue n) (z.residue n) (modulus n)
  have hr := Int.mul_emod (x.residue n) (y.residue n*z.residue n) (modulus n)
  rw [z.canonical] at hl
  rw [x.canonical] at hr
  rw [← hl, ← hr, Int.mul_assoc]

def difference (x y : Integer277) : Integer277 :=
  ofCompatible (fun n => x.residue n - y.residue n) (by
    intro n
    obtain ⟨a,ha⟩ := step_difference x n
    obtain ⟨b,hb⟩ := step_difference y n
    exact ⟨a-b,by grind⟩)

theorem difference_zero (x y : Integer277) (h : difference x y = ofInt 0) : x = y := by
  apply equal_of_residues
  intro n
  have he := congrArg (fun z : Integer277 => z.residue n) h
  change (x.residue n-y.residue n)%modulus n = 0 % modulus n at he
  rw [Int.zero_emod] at he
  have hr := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr he
  simpa only [x.canonical, y.canonical] using hr

theorem difference_product_zero (d x y : Integer277) (h : mul x d = mul y d) :
    mul (difference x y) d = ofInt 0 := by
  apply equal_of_residues
  intro n
  have he := congrArg (fun z : Integer277 => z.residue n) h
  change (x.residue n*d.residue n)%modulus n = (y.residue n*d.residue n)%modulus n at he
  have hf := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he
  have hh := Int.mul_emod (x.residue n-y.residue n) (d.residue n) (modulus n)
  rw [d.canonical] at hh
  change ((x.residue n-y.residue n)%modulus n*d.residue n)%modulus n = 0%modulus n
  rw [← hh, Int.sub_mul, Int.zero_emod]
  exact hf

theorem adic_cancel (d : Integer277) (hd : d ≠ ofInt 0) (x y : Integer277)
    (h : mul x d = mul y d) : x = y := by
  have hz := difference_product_zero d x y h
  exact difference_zero x y ((TameAdicDomain277.no_zero_divisors _ d hz).resolve_right hd)

theorem adic_fraction_equal_iff (x y : Pair Integer277 (ofInt 0)) :
    Quot.mk (Cross mul) x = Quot.mk (Cross mul) y ↔ mul x.num y.den = mul y.num x.den :=
  fraction_equal_iff mul adic_mul_assoc adic_mul_comm adic_cancel x y

theorem order_fraction_equal_iff (x y : Pair (Completion E) (fromInteger E (ofInt 0))) :
    Quot.mk (Cross (onCompletion (multiplication E op hm))) x =
      Quot.mk (Cross (onCompletion (multiplication E op hm))) y ↔
    onCompletion (multiplication E op hm) x.num y.den =
      onCompletion (multiplication E op hm) y.num x.den := by
  constructor
  · intro h
    have he := congrArg (toAdicRatios E op hm) h
    let f := toInteger E
    have hz : ∀ x, f x = ofInt 0 → x = fromInteger E (ofInt 0) :=
      reflect_base _ _ (fromInteger_toInteger E) _ _ rfl
    have hmapped := (adic_fraction_equal_iff (mapPair f hz x) (mapPair f hz y)).mp he
    change mul (f x.num) (f y.den) = mul (f y.num) (f x.den) at hmapped
    have hx := toInteger_onCompletion (multiplication E op hm) x.num y.den
    have hy := toInteger_onCompletion (multiplication E op hm) y.num x.den
    have hi := congrArg (fromInteger E) (hx.trans (hmapped.trans hy.symm))
    simpa only [fromInteger_toInteger] using hi
  · intro h
    exact Quot.sound (r := Cross (onCompletion (multiplication E op hm))) h

theorem adic_four_factors (a b c d : Integer277) :
    mul (mul a b) (mul c d) = mul (mul a c) (mul b d) := by
  rw [adic_mul_assoc, ← adic_mul_assoc b c d, adic_mul_comm b c,
    adic_mul_assoc c b d, ← adic_mul_assoc]

theorem adic_add_mul (a b d : Integer277) :
    mul (add a b) d = add (mul a d) (mul b d) := by
  apply equal_of_residues
  intro n
  have hl := Int.mul_emod (a.residue n+b.residue n) (d.residue n) (modulus n)
  rw [d.canonical] at hl
  change ((a.residue n+b.residue n)%modulus n*d.residue n)%modulus n =
    ((a.residue n*d.residue n)%modulus n+(b.residue n*d.residue n)%modulus n)%modulus n
  rw [← hl, ← Int.add_emod, Int.add_mul]

def timesPair (a b : Pair Integer277 (ofInt 0)) : Pair Integer277 (ofInt 0) :=
  ⟨mul a.num b.num, mul a.den b.den, TameAdicDomain277.product_nonzero _ _ a.nonzero b.nonzero⟩

theorem times_cross (a a' b b' : Pair Integer277 (ofInt 0))
    (ha : Cross mul a a') (hb : Cross mul b b') :
    Cross mul (timesPair a b) (timesPair a' b') := by
  change mul a.num a'.den = mul a'.num a.den at ha
  change mul b.num b'.den = mul b'.num b.den at hb
  change mul (mul a.num b.num) (mul a'.den b'.den) =
    mul (mul a'.num b'.num) (mul a.den b.den)
  rw [adic_four_factors a.num b.num, adic_four_factors a'.num b'.num, ha,hb]

def plusPair (a b : Pair Integer277 (ofInt 0)) : Pair Integer277 (ofInt 0) :=
  ⟨add (mul a.num b.den) (mul b.num a.den), mul a.den b.den,
   TameAdicDomain277.product_nonzero _ _ a.nonzero b.nonzero⟩

theorem plus_cross (a a' b b' : Pair Integer277 (ofInt 0))
    (ha : Cross mul a a') (hb : Cross mul b b') :
    Cross mul (plusPair a b) (plusPair a' b') := by
  change mul a.num a'.den = mul a'.num a.den at ha
  change mul b.num b'.den = mul b'.num b.den at hb
  unfold Cross plusPair
  simp only [adic_add_mul]
  congr 1
  · rw [adic_four_factors a.num b.den, adic_four_factors a'.num b'.den,
      ha, adic_mul_comm b.den b'.den]
  · rw [adic_mul_comm a'.den b'.den, adic_mul_comm a.den b.den,
      adic_four_factors b.num a.den, adic_four_factors b'.num a'.den,
      hb, adic_mul_comm a.den a'.den]

def onRatios {R : Type} {zero : R} {s : R → R → R}
    (op' : Pair R zero → Pair R zero → Pair R zero)
    (hop : ∀ a a' b b', Cross s a a' → Cross s b b' → Cross s (op' a b) (op' a' b')) :
    Fractions R zero s → Fractions R zero s → Fractions R zero s :=
  Quot.lift (fun a => Quot.lift (fun b => Quot.mk _ (op' a b))
    (fun b b' h => Quot.sound (hop a a b b' rfl h)))
    (fun a a' h => by
      funext z
      induction z using Quot.ind with
      | mk b => exact Quot.sound (hop a a' b b h rfl))

def ratioMul : AdicRatios → AdicRatios → AdicRatios := onRatios timesPair times_cross

def ratioAdd : AdicRatios → AdicRatios → AdicRatios := onRatios plusPair plus_cross

theorem order_nonzero_product (a b : Completion E) (ha : a ≠ fromInteger E (ofInt 0))
    (hb : b ≠ fromInteger E (ofInt 0)) :
    onCompletion (multiplication E op hm) a b ≠ fromInteger E (ofInt 0) := by
  have reflect := reflect_base (toInteger E) (fromInteger E) (fromInteger_toInteger E)
    (fromInteger E (ofInt 0)) (ofInt 0) rfl
  intro h
  apply TameAdicDomain277.product_nonzero _ _ (fun h => ha (reflect a h)) (fun h => hb (reflect b h))
  exact (toInteger_onCompletion (multiplication E op hm) a b).symm.trans
    ((congrArg (toInteger E) h).trans (toInteger_fromInteger E _))

def orderTimesPair (a b : Pair (Completion E) (fromInteger E (ofInt 0))) :
    Pair (Completion E) (fromInteger E (ofInt 0)) :=
  ⟨onCompletion (multiplication E op hm) a.num b.num,
   onCompletion (multiplication E op hm) a.den b.den,
   order_nonzero_product E op hm _ _ a.nonzero b.nonzero⟩

theorem toAdicRatios_product (a b : Pair (Completion E) (fromInteger E (ofInt 0))) :
    toAdicRatios E op hm (Quot.mk _ (orderTimesPair E op hm a b)) =
    ratioMul (toAdicRatios E op hm (Quot.mk _ a)) (toAdicRatios E op hm (Quot.mk _ b)) := by
  apply congrArg (Quot.mk _)
  unfold mapPair timesPair orderTimesPair
  simp only [toInteger_onCompletion]
  rfl

variable (opAdd : O → O → O)
    (ha : ∀ n a b, E.eval n (opAdd a b) % modulus n = (E.eval n a + E.eval n b) % modulus n)

def orderPlusPair (a b : Pair (Completion E) (fromInteger E (ofInt 0))) :
    Pair (Completion E) (fromInteger E (ofInt 0)) :=
  let m := onCompletion (multiplication E op hm)
  ⟨onCompletion (addition E opAdd ha) (m a.num b.den) (m b.num a.den),
   m a.den b.den, order_nonzero_product E op hm _ _ a.nonzero b.nonzero⟩

theorem toAdicRatios_sum (a b : Pair (Completion E) (fromInteger E (ofInt 0))) :
    toAdicRatios E op hm (Quot.mk _ (orderPlusPair E op hm opAdd ha a b)) =
    ratioAdd (toAdicRatios E op hm (Quot.mk _ a)) (toAdicRatios E op hm (Quot.mk _ b)) := by
  apply congrArg (Quot.mk _)
  unfold mapPair plusPair orderPlusPair
  simp only [toInteger_onCompletion]
  rfl

end Reimann.TameFractionCompletion277
