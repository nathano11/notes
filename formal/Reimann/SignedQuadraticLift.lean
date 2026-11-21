import Std

/-! Constructive one-bit Weierstrass preparation for a distinguished quadratic.
Coefficients are indexed in the variable T, starting at the constant term.
The three corrections solve the product equation over F₂ without division by
anything except the previous precision. -/
namespace Reimann.SignedQuadraticLift

structure Stage where
  c0 : Int
  c1 : Int
  cofactor : Nat → Int

/-- Multiplication by T on an ascending coefficient sequence. -/
def delay (f : Nat → Int) : Nat → Int
  | 0 => 0
  | k+1 => f k

/-- Coefficients of (T²+c₁T+c₀)U. -/
def product (S : Stage) (k : Nat) : Int :=
  S.c0*S.cofactor k + S.c1*delay S.cofactor k + delay (delay S.cofactor) k

def Matches (m : Int) (f : Nat → Int) (S : Stage) : Prop :=
  ∀ k, m ∣ f k - product S k

def Distinguished (S : Stage) : Prop :=
  S.c0%2=0 ∧ S.c1%2=0 ∧ S.cofactor 0%2=1

def error (m : Int) (f : Nat → Int) (S : Stage) (k : Nat) : Int :=
  (f k - product S k) / m

def constantBit (e : Nat → Int) : Int := e 0 % 2

def linearBit (e u : Nat → Int) : Int := (e 1 - constantBit e * u 1) % 2

def cofactorBit (e u : Nat → Int) (k : Nat) : Int :=
  (e (k+2) - constantBit e * u (k+2) - linearBit e u * u (k+1)) % 2

def adjust (m a b : Int) (v : Nat → Int) (S : Stage) : Stage :=
  ⟨S.c0+m*a, S.c1+m*b, fun k => S.cofactor k+m*v k⟩

def lift (m : Int) (f : Nat → Int) (S : Stage) : Stage :=
  let e := error m f S
  adjust m (constantBit e) (linearBit e S.cofactor) (cofactorBit e S.cofactor) S

/-- Derivative of multiplication at (T²,U mod 2) in the three corrections. -/
def linearized (a b : Int) (u v : Nat → Int) (k : Nat) : Int :=
  a*u k + b*delay u k + delay (delay v) k

theorem delay_affine (m : Int) (u v : Nat → Int) :
    delay (fun k => u k+m*v k) = fun k => delay u k+m*delay v k := by
  funext k
  cases k <;> simp [delay]

/-- All the terms omitted by the mod-two derivative contain another factor two. -/
theorem linearization_error {m : Int} (hm : m%2=0) {S : Stage} (hd : Distinguished S)
    (a b : Int) (v : Nat → Int) (k : Nat) :
    2*m ∣ product (adjust m a b v S) k - product S k - m*linearized a b S.cofactor v k := by
  obtain ⟨p,hp⟩ := Int.dvd_iff_emod_eq_zero.mpr hd.1
  obtain ⟨q,hq⟩ := Int.dvd_iff_emod_eq_zero.mpr hd.2.1
  obtain ⟨z,hz⟩ := Int.dvd_iff_emod_eq_zero.mpr hm
  refine ⟨p*v k + q*delay v k + z*(a*v k + b*delay v k), ?_⟩
  simp only [product, adjust, linearized, delay_affine, hp, hq, hz]
  grind

theorem odd_pivot (x u : Int) (hu : u%2=1) : (2:Int) ∣ x-(x%2)*u := by
  rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.mul_emod, hu]
  simp

/-- At degree zero the leading unit is u₀. At degree one the same unit
fixes the other polynomial coefficient. Every subsequent degree fixes a
different cofactor digit. -/
theorem correction_solves (e u : Nat → Int) (hu : u 0%2=1) (k : Nat) :
    (2:Int) ∣ e k - linearized (constantBit e) (linearBit e u) u (cofactorBit e u) k := by
  cases k with
  | zero => simpa [linearized, delay, constantBit] using odd_pivot (e 0) _ hu
  | succ n =>
    cases n with
    | zero =>
      have h := odd_pivot (e 1 - constantBit e*u 1) _ hu
      simpa only [linearized, delay, linearBit, Int.add_zero, ← Int.sub_sub] using h
    | succ n =>
      have h : (2:Int) ∣ (e (n+2)-constantBit e*u (n+2)-linearBit e u*u (n+1)) -
          (e (n+2)-constantBit e*u (n+2)-linearBit e u*u (n+1))%2 := by omega
      simpa only [linearized, delay, cofactorBit, ← Int.sub_sub] using h

theorem error_exact {m : Int} {f : Nat → Int} {S : Stage} (h : Matches m f S) (k : Nat) :
    f k - product S k = m * error m f S k := by
  have hz := Int.dvd_iff_emod_eq_zero.mp (h k)
  have he := Int.emod_add_mul_ediv (f k-product S k) m
  simpa only [hz, Int.zero_add, error] using he.symm

theorem lift_matches {m : Int} {f : Nat → Int} {S : Stage}
    (hm : m%2=0) (hd : Distinguished S) (h : Matches m f S) :
    Matches (2*m) f (lift m f S) := by
  let e := error m f S
  let l := linearized (constantBit e) (linearBit e S.cofactor) S.cofactor (cofactorBit e S.cofactor)
  intro k
  obtain ⟨p,hp⟩ := correction_solves e S.cofactor hd.2.2 k
  obtain ⟨q,hq⟩ := linearization_error hm hd (constantBit e) (linearBit e S.cofactor)
    (cofactorBit e S.cofactor) k
  change e k - l k = 2*p at hp
  change product (lift m f S) k - product S k - m*l k = 2*m*q at hq
  have exactError : f k - product S k = m*e k := error_exact h k
  refine ⟨p-q, ?_⟩
  calc
    _ = (f k-product S k) - m*l k - (product (lift m f S) k-product S k-m*l k) := by omega
    _ = m*(e k-l k) - 2*m*q := by rw [exactError,hq]; grind
    _ = _ := by rw [hp]; grind

theorem lift_preserves {m : Int} {f : Nat → Int} {S : Stage} :
    (m ∣ (lift m f S).c0-S.c0) ∧ (m ∣ (lift m f S).c1-S.c1) ∧
      ∀ k, m ∣ (lift m f S).cofactor k-S.cofactor k := by
  let e := error m f S
  refine ⟨⟨constantBit e, ?_⟩,⟨linearBit e S.cofactor, ?_⟩,fun k => ⟨cofactorBit e S.cofactor k, ?_⟩⟩ <;>
    simp only [lift,adjust,e] <;> omega

theorem lift_distinguished {m : Int} {f : Nat → Int} {S : Stage}
    (hm : m%2=0) (hd : Distinguished S) : Distinguished (lift m f S) := by
  have preserve := lift_preserves (m:=m) (f:=f) (S:=S)
  have two := Int.dvd_iff_emod_eq_zero.mpr hm
  have p := Int.dvd_trans two preserve.1
  have q := Int.dvd_trans two preserve.2.1
  have z := Int.dvd_trans two (preserve.2.2 0)
  rcases hd with ⟨hp,hq,hz⟩
  unfold Distinguished
  omega

/-- Modulo two the monic factor is T², so the initial cofactor is the
coefficient sequence with its first two entries removed. -/
def initial (f : Nat → Int) : Stage := ⟨0,0,fun k => f (k+2)⟩

theorem initial_matches {f : Nat → Int} (h0 : f 0%2=0) (h1 : f 1%2=0) :
    Matches 2 f (initial f) := by
  intro k
  cases k with
  | zero => simpa [product, initial, delay, Int.dvd_iff_emod_eq_zero] using h0
  | succ n =>
    cases n with
    | zero => simpa [product, initial, delay, Int.dvd_iff_emod_eq_zero] using h1
    | succ n => simp [product, initial, delay]

theorem initial_distinguished {f : Nat → Int} (h2 : f 2%2=1) :
    Distinguished (initial f) := by
  simpa [Distinguished, initial] using h2

end Reimann.SignedQuadraticLift
