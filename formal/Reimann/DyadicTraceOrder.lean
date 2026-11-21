import Reimann.Dyadic

/-! The integral quadratic tensor order in the basis (1,e,w,ew), where
e²=e−h and w²=w−k. The four entries of a matrix are used as coordinates
in that order. The trace is the trace of multiplication on this basis.
-/

namespace Reimann.DyadicTraceOrder

open Reimann.Dyadic

/-- Multiplication by e on both coefficients of 1,w. -/
def timesE (h : Int) (x : Matrix) : Matrix := ⟨-h*x.b,x.a+x.b,-h*x.d,x.c+x.d⟩

/-- Multiplication by w on both coefficients of 1,e. -/
def timesW (k : Int) (x : Matrix) : Matrix := ⟨-k*x.c,-k*x.d,x.a+x.c,x.b+x.d⟩

/-- The four columns for multiplication by x are x,ex,wx,wex. -/
def trace (h k : Int) (x : Matrix) : Int :=
  x.a+(timesE h x).b+(timesW k x).c+(timesW k (timesE h x)).d

theorem trace_formula (h k : Int) (x : Matrix) :
    trace h k x = 4*x.a+2*x.b+2*x.c+x.d := by
  simp only [trace,timesE,timesW]; grind

/-- Pairings against the four basis elements in basis order. -/
def pairings (h k : Int) (x : Matrix) : Matrix :=
  ⟨trace h k x,trace h k (timesE h x),trace h k (timesW k x),
    trace h k (timesW k (timesE h x))⟩

/-- Tr(1),Tr(e),Tr(e²) in the quadratic basis (1,e). -/
def quadraticGram (h : Int) : Matrix := ⟨2,1,1,1-2*h⟩

theorem quadratic_discriminant (h : Int) : det (quadraticGram h) = 1-4*h := by
  simp only [det,quadraticGram]; grind

/-- The Gram operator is left and right multiplication by the two
quadratic Gram matrices, with the e-index varying fastest. -/
theorem pairings_tensor (h k : Int) (x : Matrix) :
    pairings h k x = mul (mul (quadraticGram k) x) (quadraticGram h) := by
  simp only [pairings,trace_formula,timesE,timesW,quadraticGram,mul,Matrix.mk.injEq]
  grind

def minorThree (a b c d e f g h i : Int) : Int :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- Laplace expansion along the first row. -/
def detFour (x y z t : Matrix) : Int :=
  x.a*minorThree y.b y.c y.d z.b z.c z.d t.b t.c t.d -
  x.b*minorThree y.a y.c y.d z.a z.c z.d t.a t.c t.d +
  x.c*minorThree y.a y.b y.d z.a z.b z.d t.a t.b t.d -
  x.d*minorThree y.a y.b y.c z.a z.b z.c t.a t.b t.c

def discriminant (h k : Int) : Int :=
  detFour (pairings h k ⟨1,0,0,0⟩) (pairings h k ⟨0,1,0,0⟩)
    (pairings h k ⟨0,0,1,0⟩) (pairings h k ⟨0,0,0,1⟩)

theorem discriminant_formula (h k : Int) :
    discriminant h k = ((1-4*h)*(1-4*k))^2 := by
  simp only [discriminant,detFour,minorThree,pairings_tensor,quadraticGram,mul]
  grind

theorem parameter_discriminant (q d : Nat) (hq : q%8=3) (hd : d%16=7) :
    discriminant (((q+1)/4 : Nat) : Int) (((d+1)/4 : Nat) : Int) =
      ((q : Int)*(d : Int))^2 := by
  have eqQ : 1-4*((((q+1)/4 : Nat)) : Int) = -(q : Int) := by omega
  have eqD : 1-4*((((d+1)/4 : Nat)) : Int) = -(d : Int) := by omega
  rw [discriminant_formula,eqQ,eqD]
  grind

theorem discriminant_odd (h k : Int) : discriminant h k % 2 = 1 := by
  rw [discriminant_formula,Int.pow_succ _ 1,Int.pow_one]
  have he : (1-4*h)*(1-4*k) = 1+2*(-2*h-2*k+8*h*k) := by grind
  rw [he]
  let z := -2*h-2*k+8*h*k
  have hs : (1+2*z)*(1+2*z) = 1+2*(2*z+2*z*z) := by grind
  change ((1+2*z)*(1+2*z))%2=1
  rw [hs]
  omega

/-- Tensor of the two quadratic adjugates. -/
def recover (h k : Int) (x : Matrix) : Matrix :=
  mul (mul ⟨1-2*k,-1,-1,2⟩ x) ⟨1-2*h,-1,-1,2⟩

/-- Only one factor of each quadratic discriminant is needed to recover coordinates. -/
theorem recover_pairings (h k : Int) (x : Matrix) :
    recover h k (pairings h k x) = scale ((1-4*h)*(1-4*k)) x := by
  simp only [pairings_tensor,recover,quadraticGram,mul,scale,Matrix.mk.injEq]; grind

theorem recover_scale (h k s : Int) (x : Matrix) :
    recover h k (scale s x) = scale s (recover h k x) := by
  simp only [recover,mul,scale,Matrix.mk.injEq]; grind

theorem coordinates_divisible (s : Int) (x : Matrix) :
    entryDivisor s x ↔ ∃ y : Matrix, x = scale s y := by
  constructor
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩
    exact ⟨⟨a,b,c,d⟩,by cases x; simp_all [scale]⟩
  · rintro ⟨y,rfl⟩
    exact ⟨⟨y.a,rfl⟩,⟨y.b,rfl⟩,⟨y.c,rfl⟩,⟨y.d,rfl⟩⟩

theorem pairings_scale (h k s : Int) (x : Matrix) :
    pairings h k (scale s x) = scale s (pairings h k x) := by
  simp only [pairings_tensor,quadraticGram,mul,scale,Matrix.mk.injEq]; grind

/-- Multiplying every coordinate by an odd integer preserves divisibility
by every power of two. -/
theorem cancel_odd_scale (n : Nat) (v : Int) (x : Matrix) :
    entryDivisor (twoPower n) (scale (1+2*v) x) ↔ entryDivisor (twoPower n) x := by
  simp only [entryDivisor,scale,cancel_odd_factor]

/-- An element x/2^n has integral pairings with 1,e,w,ew exactly when
its four coefficients are integral. A single denominator works at every
precision, including n=0. -/
theorem trace_integral_iff (h k : Int) (n : Nat) (x : Matrix) :
    entryDivisor (twoPower n) (pairings h k x) ↔ entryDivisor (twoPower n) x := by
  constructor
  · intro hp
    obtain ⟨y,hy⟩ := (coordinates_divisible _ _).mp hp
    have he := congrArg (recover h k) hy
    rw [recover_pairings,recover_scale] at he
    have hs : (1-4*h)*(1-4*k) = 1+2*(-2*h-2*k+8*h*k) := by grind
    rw [hs] at he
    apply (cancel_odd_scale n (-2*h-2*k+8*h*k) x).mp
    exact (coordinates_divisible _ _).mpr ⟨_,he⟩
  · intro hx
    obtain ⟨y,rfl⟩ := (coordinates_divisible _ _).mp hx
    exact (coordinates_divisible _ _).mpr ⟨_,pairings_scale _ _ _ _⟩

/-- At (q,d)=(3,23) one has h=1,k=6 and discriminant 69². -/
theorem trace_order_3_23 :
    discriminant 1 6 = 4761 ∧ ∀ n x, entryDivisor (twoPower n) (pairings 1 6 x) ↔
      entryDivisor (twoPower n) x := by
  exact ⟨by decide, trace_integral_iff 1 6⟩

end Reimann.DyadicTraceOrder
