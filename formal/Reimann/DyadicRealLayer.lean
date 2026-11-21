import Std

/-! The real dyadic cyclotomic recurrence over arbitrary commutative rings. -/

namespace Reimann.DyadicRealLayer

open Lean.Grind

/-- P₀(X)=X and Pₐ₊₁(X)=Pₐ(X)²−2. Evaluation makes sense universally. -/
def eval {R : Type u} [CommRing R] (x : R) : Nat → R
  | 0 => x
  | a+1 => eval x a * eval x a - 2

theorem compose_square_sub_two {R : Type u} [CommRing R] (a : Nat) (x : R) :
    eval (x*x-2) a = eval x (a+1) := by
  induction a with
  | zero => rfl
  | succ a ih => change eval (x*x-2) a * eval (x*x-2) a - 2 = _; rw [ih]; rfl

theorem square_power {R : Type u} [CommRing R] (z : R) (a : Nat) :
    z^(2^(a+1) : Nat) = z^(2^a : Nat)*z^(2^a : Nat) := by
  rw [Nat.pow_succ, Nat.mul_two, Semiring.pow_add]

theorem power_inverse {R : Type u} [CommRing R] {z t : R} (hinv : z*t=1) (a : Nat) :
    z^(2^a : Nat)*t^(2^a : Nat)=1 := by
  induction a with
  | zero => simpa [Semiring.pow_one] using hinv
  | succ a ih =>
    rw [square_power, square_power]
    calc
      _ = (z^(2^a : Nat)*t^(2^a : Nat))*(z^(2^a : Nat)*t^(2^a : Nat)) := by grind
      _ = _ := by rw [ih]; grind

theorem eval_trace {R : Type u} [CommRing R] {z t : R} (hinv : z*t=1) (a : Nat) :
    eval (z+t) a = z^(2^a : Nat)+t^(2^a : Nat) := by
  induction a with
  | zero => simp [eval, Semiring.pow_one]
  | succ a ih =>
    rw [eval, ih, square_power, square_power]
    have h := power_inverse hinv a
    grind

/-- The half-order relation for a primitive 2^(a+2)-th root gives the
equation of its real trace. The argument includes a=0. -/
theorem real_cyclotomic_root {R : Type u} [CommRing R] {z t : R} (a : Nat)
    (hinv : z*t=1) (hhalf : z^(2^(a+1) : Nat)= -1) : eval (z+t) a = 0 := by
  rw [eval_trace hinv]
  rw [square_power] at hhalf
  have h := power_inverse hinv a
  calc
    _ = (z^(2^a : Nat)*z^(2^a : Nat)+1)*t^(2^a : Nat) := by
      have h' := congrArg (fun v : R => z^(2^a : Nat)*v) h
      grind
    _ = _ := by rw [hhalf]; grind

/-- Universal characteristic-two reduction. In particular this applies to
polynomial rings and to nilpotent elements, with no finiteness assumption. -/
theorem characteristic_two_reduction {R : Type u} [CommRing R] (h2 : (2:R)=0)
    (a : Nat) (x : R) : eval x a = x^(2^a : Nat) := by
  induction a with
  | zero => simp [eval, Semiring.pow_one]
  | succ a ih => rw [eval, ih, square_power, h2]; grind

theorem positive_layer_constant (a : Nat) :
    eval (0:Int) (a+1) = (if a=0 then -2 else 2) := by
  induction a with
  | zero => decide
  | succ a ih =>
    change eval (0:Int) (a+1) * eval (0:Int) (a+1) - 2 = _
    rw [ih]
    split <;> simp

theorem constant_mod_four (a : Nat) : eval (0:Int) (a+1) % 4 = 2 := by
  rw [positive_layer_constant]; split <;> decide

theorem prime_contains_power_root {R : Type u} [CommRing R] (P : R → Prop)
    (hzero : P 0) (hprime : ∀ v w, P (v*w) → P v ∨ P w)
    (a : Nat) (x : R) (h : x^(2^a : Nat)=0) : P x := by
  have descend (k : Nat) : P (x^(2^k : Nat)) → P x := by
    induction k with
    | zero => simpa only [Nat.pow_zero, Semiring.pow_one] using (fun h : P x => h)
    | succ k ih =>
      intro h
      rw [square_power] at h
      exact ih ((hprime _ _ h).elim id id)
  exact descend a (h ▸ hzero)

/-- The class of the real generator lies in every prime of the fiber. -/
theorem prime_contains_generator {R : Type u} [CommRing R] (h2 : (2:R)=0)
    (P : R → Prop) (hzero : P 0) (hprime : ∀ v w, P (v*w) → P v ∨ P w)
    (a : Nat) (x : R) (hx : eval x a=0) : P x :=
  prime_contains_power_root P hzero hprime a x ((characteristic_two_reduction h2 a x).symm.trans hx)

attribute [local instance] Ring.intCast

/-- Low coefficients first. Tail value 0 evaluates an ordinary coefficient
list. Tail value 1 supplies an implicit monic leading coefficient. -/
def horner {R : Type u} [CommRing R] (x tail : R) : List Int → R
  | [] => tail
  | c::cs => IntCast.intCast c + x*horner x tail cs

/-- Add k times a bounded list of coefficients to the low slots. -/
def addScaled (k : Int) : List Int → List Int → List Int
  | [], ys => ys
  | _::_, [] => []
  | c::cs, d::ds => (k*c+d)::addScaled k cs ds

theorem length_addScaled (k : Int) (cs ds : List Int) : (addScaled k cs ds).length = ds.length := by
  induction cs generalizing ds with
  | nil => rfl
  | cons c cs ih => cases ds <;> simp [addScaled, ih]

theorem horner_addScaled {R : Type u} [CommRing R] (x b : R) (k : Int)
    (cs ds : List Int) (h : cs.length ≤ ds.length) :
    horner x b (addScaled k cs ds) = (k:R)*horner x 0 cs + horner x b ds := by
  induction cs generalizing ds with
  | nil => simp only [addScaled, horner]; grind
  | cons c cs ih =>
    cases ds with
    | nil => simp at h
    | cons d ds =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at h
      simp only [addScaled, horner, Ring.intCast_add, Ring.intCast_mul, ih ds h]
      grind

theorem explicit_leading_one {R : Type u} [CommRing R] (x : R) (cs : List Int) :
    horner x 0 (cs++[1]) = horner x 1 cs := by
  induction cs with
  | nil => simp [horner, Ring.intCast_one]; grind
  | cons c cs ih => simp [horner, ih]

/-- Multiply two monic polynomials, storing every coefficient below the
leading one. -/
def monicProduct : List Int → List Int → List Int
  | [], ds => ds
  | c::cs, ds => addScaled c (ds++[1]) (0::monicProduct cs ds)

theorem monicProduct_degree (cs ds : List Int) :
    (monicProduct cs ds).length = cs.length+ds.length := by
  induction cs with
  | nil => simp [monicProduct]
  | cons c cs ih => simp [monicProduct,length_addScaled,ih]; omega

theorem monicProduct_eval {R : Type u} [CommRing R] (x : R) (cs ds : List Int) :
    horner x 1 (monicProduct cs ds) = horner x 1 cs * horner x 1 ds := by
  induction cs with
  | nil => simp only [monicProduct, horner]; grind
  | cons c cs ih =>
    have h : (ds++[1]).length ≤ (0::monicProduct cs ds).length := by
      simp [monicProduct_degree]
    rw [monicProduct, horner_addScaled x 1 _ _ _ h, explicit_leading_one]
    simp only [horner, Ring.intCast_zero, ih]
    grind

/-- The coefficient vector below the leading one of Pₐ. -/
def lowCoefficients : Nat → List Int
  | 0 => [0]
  | a+1 => addScaled (-2) [1] (monicProduct (lowCoefficients a) (lowCoefficients a))

theorem monic_degree (a : Nat) : (lowCoefficients a).length = 2^a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [lowCoefficients,length_addScaled,monicProduct_degree,ih,Nat.pow_succ,Nat.mul_two]

/-- The explicit integral coefficient list, terminated by one, evaluates to
the recurrence in every commutative ring. -/
theorem monic_coefficients_eval {R : Type u} [CommRing R] (x : R) (a : Nat) :
    horner x 0 (lowCoefficients a++[1]) = eval x a := by
  rw [explicit_leading_one]
  induction a with
  | zero => simp only [lowCoefficients,horner,eval,Ring.intCast_zero]; grind
  | succ a ih =>
    have hp : 0 < 2^a := Nat.pow_pos (by decide)
    have hlen : ([(1:Int)]).length ≤ (monicProduct (lowCoefficients a) (lowCoefficients a)).length := by
      rw [monicProduct_degree,monic_degree]; change 1 ≤ 2^a+2^a; omega
    rw [lowCoefficients, horner_addScaled x 1 _ _ _ hlen, monicProduct_eval, ih, eval]
    simp only [horner,Ring.intCast_one,Ring.intCast_neg]
    grind

theorem addScaled_even {k : Int} (hk : 2 ∣ k) (cs ds : List Int)
    (hd : ∀ d ∈ ds, 2 ∣ d) : ∀ d ∈ addScaled k cs ds, 2 ∣ d := by
  induction cs generalizing ds with
  | nil => exact hd
  | cons c cs ih =>
    cases ds with
    | nil => simp [addScaled]
    | cons b bs =>
      intro d h
      rcases List.mem_cons.mp h with he | he
      · subst d
        exact Int.dvd_add (Int.dvd_mul_of_dvd_left hk) (hd _ (by simp))
      · exact ih bs (fun t ht => hd t (List.mem_cons_of_mem _ ht)) _ he

theorem monicProduct_even (cs ds : List Int) (hc : ∀ c ∈ cs, 2 ∣ c) (hd : ∀ d ∈ ds, 2 ∣ d) :
    ∀ t ∈ monicProduct cs ds, 2 ∣ t := by
  induction cs with
  | nil => exact hd
  | cons c cs ih =>
    apply addScaled_even (hc _ (by simp))
    intro t ht
    rcases List.mem_cons.mp ht with h | h
    · simp [h]
    · exact ih (fun v hv => hc v (List.mem_cons_of_mem _ hv)) t h

/-- Coefficientwise reduction is the single monomial X^(2^a). -/
theorem low_coefficients_even (a : Nat) : ∀ t ∈ lowCoefficients a, 2 ∣ t := by
  induction a with
  | zero => simp [lowCoefficients]
  | succ a ih =>
    exact addScaled_even (by decide : (2:Int) ∣ -2) _ _ (monicProduct_even _ _ ih ih)

/-- In a prime of a fiber adjoining x with Pₐ(x)=0, an expansion r+xq
is in the prime exactly when its constant coefficient is in the prime. -/
theorem prime_iff_constant {R : Type u} [CommRing R] (h2 : (2:R)=0)
    (P : R → Prop) (hzero : P 0) (hprime : ∀ v w, P (v*w) → P v ∨ P w)
    (hplus : ∀ v w, P v → P w → P (v+w)) (hneg : ∀ v, P v → P (-v))
    (habsorb : ∀ v w, P v → P (v*w)) (a : Nat) (x r q : R) (hx : eval x a=0) :
    P (r+x*q) ↔ P r := by
  have hp := habsorb x q (prime_contains_generator h2 P hzero hprime a x hx)
  constructor
  · intro h
    have e := hplus _ _ h (hneg _ hp)
    rwa [show r+x*q+ -(x*q)=r by grind] at e
  · intro h
    exact hplus _ _ h hp

/-- When every element admits a constant-plus-generator expansion, a prime
is the pullback of its contraction along the constant projection. The
generator relation and expansion are the only presentation inputs. -/
theorem prime_pullback {R : Type u} {B : Type v} [CommRing R] (h2 : (2:R)=0)
    (P : R → Prop) (hzero : P 0) (hprime : ∀ v w, P (v*w) → P v ∨ P w)
    (hplus : ∀ v w, P v → P w → P (v+w)) (hneg : ∀ v, P v → P (-v))
    (habsorb : ∀ v w, P v → P (v*w)) (a : Nat) (x : R) (hx : eval x a=0)
    (incl : B → R) (constant : R → B) (expand : ∀ y, ∃ q, y = incl (constant y)+x*q)
    (y : R) : P y ↔ P (incl (constant y)) := by
  obtain ⟨q, hq⟩ := expand y
  have h := prime_iff_constant h2 P hzero hprime hplus hneg habsorb a x (incl (constant y)) q hx
  rwa [← hq] at h

end Reimann.DyadicRealLayer
