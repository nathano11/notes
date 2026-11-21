import Std

namespace Reimann.TameUnramified277

open Lean.Grind

variable {R S : Type} [CommRing R] [CommRing S]

/-- Divided difference of the two powers, with no division in the ring. -/
def factor (x y : R) : Nat → R
  | 0 => 0
  | n+1 => x^n + y*factor x y n

theorem power_difference (x y : R) (n : Nat) :
    (x-y)*factor x y n = x^n-y^n := by
  induction n with
  | zero => simp only [factor,Semiring.pow_zero]; grind
  | succ n ih =>
    rw [factor,Semiring.pow_succ,Semiring.pow_succ]
    grind

structure Reduction (R S : Type) [CommRing R] [CommRing S] where
  app : R → S
  zero : app 0 = 0
  one : app 1 = 1
  add : ∀ x y, app (x+y) = app x + app y
  mul : ∀ x y, app (x*y) = app x * app y

theorem map_power (f : Reduction R S) (x : R) (n : Nat) : f.app (x^n) = (f.app x)^n := by
  induction n with
  | zero => simpa only [Semiring.pow_zero] using f.one
  | succ n ih => rw [Semiring.pow_succ,Semiring.pow_succ,f.mul,ih]

attribute [local instance] Semiring.natCast

theorem diagonal_reduction (f : Reduction R S) (x y : R) (h : f.app x=f.app y) (n : Nat) :
    f.app (factor x y n)*f.app y = (n : S)*(f.app y)^n := by
  induction n with
  | zero => simp only [factor,f.zero,Semiring.pow_zero,Semiring.natCast_zero]; grind
  | succ n ih =>
    rw [factor,f.add,f.mul,map_power,h,Semiring.pow_succ,Semiring.natCast_succ]
    grind

/-- Reduction is injective on m-th roots of unity whenever m survives in the residue
ring and there are no zero divisors in the original ring. -/
theorem injective_on_power_roots (f : Reduction R S)
    (noZero : ∀ a b : R, a*b=0 → a=0 ∨ b=0) (m : Nat) (hm : (m : S) ≠ 0)
    (x y : R) (hx : x^m=1) (hy : y^m=1) (h : f.app x=f.app y) : x=y := by
  have hd := power_difference x y m
  rw [hx,hy] at hd
  have hz : (x-y)*factor x y m = 0 := by grind
  rcases noZero _ _ hz with xy | hf
  · grind
  · have he := diagonal_reduction f x y h m
    rw [hf,f.zero,← map_power,hy,f.one] at he
    exact False.elim (hm (by grind))

theorem inertia_fixes (f : Reduction R S) (g : Reduction R R)
    (noZero : ∀ a b : R, a*b=0 → a=0 ∨ b=0)
    (m : Nat) (hm : (m : S) ≠ 0)
    (inertia : ∀ a, f.app (g.app a) = f.app a) (x : R) (hx : x^m=1) :
    g.app x = x := by
  apply injective_on_power_roots f noZero m hm _ _ _ hx (inertia _)
  rw [← map_power,hx,g.one]

end Reimann.TameUnramified277
