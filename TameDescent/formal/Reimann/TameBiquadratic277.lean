import Reimann.TameSplitting277

namespace Reimann.TameBiquadratic277

open Lean.Grind

variable {R : Type} [CommRing R]

/-- The values of a + bX at +r and -r. -/
def pairEval (r : R) (v : R × R) : R × R :=
  (v.1 + r*v.2, v.1-r*v.2)

/-- d is an inverse of the derivative 2r. In particular r*d is one half. -/
def pairInterpolate (r d : R) (v : R × R) : R × R :=
  (r*d*(v.1+v.2), d*(v.1-v.2))

theorem interpolate_pairEval (r d : R) (hd : 2*r*d=1) (v : R × R) :
    pairInterpolate r d (pairEval r v) = v := by
  apply Prod.ext <;> simp only [pairInterpolate,pairEval] <;> grind

theorem pairEval_interpolate (r d : R) (hd : 2*r*d=1) (v : R × R) :
    pairEval r (pairInterpolate r d v) = v := by
  apply Prod.ext <;> simp only [pairInterpolate,pairEval] <;> grind

/-- Coefficients are indexed by 1, X, Y, XY. Values use ++, +-, -+, --. -/
abbrev Quad (S : Type) := (S × S) × (S × S)

def fourEval (x y : R) (v : Quad R) : Quad R :=
  let a := pairEval x v.1
  let b := pairEval x v.2
  (pairEval y (a.1,b.1), pairEval y (a.2,b.2))

def fourInterpolate (x dx y dy : R) (v : Quad R) : Quad R :=
  let a := pairInterpolate y dy v.1
  let b := pairInterpolate y dy v.2
  (pairInterpolate x dx (a.1,b.1), pairInterpolate x dx (a.2,b.2))

theorem interpolate_fourEval (x dx y dy : R) (hx : 2*x*dx=1) (hy : 2*y*dy=1)
    (v : Quad R) : fourInterpolate x dx y dy (fourEval x y v) = v := by
  simp [fourInterpolate,fourEval,interpolate_pairEval x dx hx,interpolate_pairEval y dy hy]

theorem fourEval_interpolate (x dx y dy : R) (hx : 2*x*dx=1) (hy : 2*y*dy=1)
    (v : Quad R) : fourEval x y (fourInterpolate x dx y dy v) = v := by
  simp [fourInterpolate,fourEval,pairEval_interpolate x dx hx,pairEval_interpolate y dy hy]

/-- Polynomial multiplication reduced by X²=A and Y²=B. -/
def product (A B : R) (s t : Quad R) : Quad R :=
  let ((a,b),(c,d)) := s
  let ((e,f),(g,h)) := t
  ((a*e+A*b*f+B*c*g+A*B*d*h, a*f+b*e+B*(c*h+d*g)),
   (a*g+c*e+A*(b*h+d*f), a*h+d*e+b*g+c*f))

def pointProduct (s t : Quad R) : Quad R :=
  ((s.1.1*t.1.1,s.1.2*t.1.2),(s.2.1*t.2.1,s.2.2*t.2.2))

theorem fourEval_product (A B x y : R) (hx : x*x=A) (hy : y*y=B)
    (s t : Quad R) :
    fourEval x y (product A B s t) = pointProduct (fourEval x y s) (fourEval x y t) := by
  subst A
  subst B
  apply Prod.ext <;> apply Prod.ext <;> simp only [fourEval,pairEval,product,pointProduct] <;> grind

def componentAdd (s t : Quad R) : Quad R :=
  ((s.1.1+t.1.1,s.1.2+t.1.2),(s.2.1+t.2.1,s.2.2+t.2.2))

theorem fourEval_add (x y : R) (s t : Quad R) :
    fourEval x y (componentAdd s t) = componentAdd (fourEval x y s) (fourEval x y t) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [fourEval,pairEval,componentAdd] <;> grind

theorem fourEval_scalar (x y a : R) :
    fourEval x y ((a,0),(0,0)) = ((a,a),(a,a)) := by
  simp only [fourEval,pairEval]
  apply Prod.ext <;> apply Prod.ext <;> grind

open Fin.IntCast

theorem cast_difference {m : Nat} [NeZero m] (a b : Int) (h : (m : Int) ∣ a-b) :
    (a : Fin m) = (b : Fin m) := by
  apply Fin.eq_of_val_eq
  rw [Lean.Grind.Fin.val_intCast,Lean.Grind.Fin.val_intCast]
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)]

abbrev Residue (n : Nat) := Fin (277^(n+1))

def liftedRoot (a x d : Int) (n : Nat) : Residue n :=
  ((TameSplitting277.liftPair a x d n).1 : Int)

def liftedInverse (a x d : Int) (n : Nat) : Residue n :=
  ((TameSplitting277.liftPair a x d n).2 : Int)

/-- A signed Hensel level supplies the exact equations in the residue ring. -/
theorem lifted_equations (a x d : Int) (n : Nat) (h : TameSplitting277.SignedLevel a x d n) :
    liftedRoot a x d n * liftedRoot a x d n = (a : Residue n) ∧
    2*liftedRoot a x d n*liftedInverse a x d n = 1 := by
  let u := (TameSplitting277.liftPair a x d n).1
  let v := (TameSplitting277.liftPair a x d n).2
  have hs : ((u^2 : Int) : Residue n) = (a : Residue n) :=
    cast_difference _ _ (by simpa [u] using h.positive)
  have hi : ((2*u*v : Int) : Residue n) = ((1 : Int) : Residue n) :=
    cast_difference _ _ (by simpa [u,v] using h.positiveSimple)
  rw [Ring.intCast_pow] at hs
  rw [Ring.intCast_mul,Ring.intCast_mul,Ring.intCast_one] at hi
  change (u : Residue n)*(u : Residue n) = (a : Residue n) ∧
    2*(u : Residue n)*(v : Residue n) = 1
  constructor
  · rw [← hs]
    grind
  · exact hi

/-- Additive and multiplicative coordinates with inverse maps and the given scalar action. -/
structure Splitting (S : Type) [CommRing S] (A B : S) where
  evaluate : Quad S → Quad S
  interpolate : Quad S → Quad S
  reconstruct : ∀ c, interpolate (evaluate c) = c
  realize : ∀ v, evaluate (interpolate v) = v
  mul : ∀ c d, evaluate (product A B c d) = pointProduct (evaluate c) (evaluate d)
  add : ∀ c d, evaluate (componentAdd c d) = componentAdd (evaluate c) (evaluate d)
  scalar : ∀ c, evaluate ((c,0),(0,0)) = ((c,c),(c,c))

def splittingOfRoots (A B x dx y dy : R) (hx : x*x=A) (hdx : 2*x*dx=1)
    (hy : y*y=B) (hdy : 2*y*dy=1) : Splitting R A B where
  evaluate := fourEval x y
  interpolate := fourInterpolate x dx y dy
  reconstruct := interpolate_fourEval x dx y dy hdx hdy
  realize := fourEval_interpolate x dx y dy hdx hdy
  mul := fourEval_product A B x y hx hy
  add := fourEval_add x y
  scalar := fourEval_scalar x y

/-- At each positive precision this is the four-factor algebra decomposition
of the coordinate presentation, preserving addition, products, and constants. -/
def finite_splitting277 (n : Nat) : Splitting (Residue n) (-3) (-23) := by
  obtain ⟨h,k⟩ := TameSplitting277.split_both_277 n
  obtain ⟨hx,hdx⟩ := lifted_equations _ _ _ _ h
  obtain ⟨hy,hdy⟩ := lifted_equations _ _ _ _ k
  exact splittingOfRoots _ _ _ _ _ _ hx hdx hy hdy

end Reimann.TameBiquadratic277
