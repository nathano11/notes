import Reimann.TameTraceLattice277
import Reimann.DyadicFiberPrimes

/-! Monic equations and denominator descent in the rational field E₀. -/
namespace Reimann.DyadicIntegralCriterion69

open TameRationalField277

/-- Coefficients run from the constant term upwards. The omitted leading coefficient is one. -/
def monicAt (z : Biquad) : List Int → Biquad
  | [] => scalar 1
  | c :: cs => ba (bm z (monicAt z cs)) (scalar (c : Rat))

def IsIntegral (z : Biquad) : Prop := ∃ f : List Int, monicAt z f = scalar 0

def dilate (d : Int) (z : Biquad) : Biquad := bm (scalar (d : Rat)) z

theorem dilate_add (d : Int) (x y : Biquad) :
    dilate d (ba x y) = ba (dilate d x) (dilate d y) := distributive _ _ _

theorem dilate_scalar (d a : Int) : dilate d (scalar (a : Rat)) = scalar ((d*a : Int) : Rat) := by
  simp only [dilate, (scalar_embedding _ _).2.2, Rat.intCast_mul]

theorem dilate_product (u v : Int) (x y : Biquad) :
    dilate (u*v) (bm x y) = bm (dilate u x) (dilate v y) := by
  unfold dilate
  rw [Rat.intCast_mul, ← (scalar_embedding _ _).2.2]
  simp only [mul_assoc]
  rw [← mul_assoc (scalar (v : Rat)) x y, mul_comm (scalar (v : Rat)) x, mul_assoc]

theorem dilate_zero (u : Int) : dilate u (scalar 0) = scalar 0 := by
  simpa using dilate_scalar u 0

theorem cancel_double {x y : Biquad} (h : dilate 2 x = dilate 2 y) : x=y := by
  simp only [dilate,TameTraceLattice277.scalar_mul_coords,Prod.mk.injEq] at h
  apply Prod.ext <;> apply Prod.ext <;> grind

/-- Integer coordinates for a full lattice with a reduced fiber at two. -/
structure IntegralModel (O : Type) where
  embed : O → Biquad
  integer : Int → O
  sum : O → O → O
  product : O → O → O
  red : O → DyadicFiberPrimes.Fiber
  embed_int : ∀ a, embed (integer a) = scalar (a : Rat)
  embed_add : ∀ x y, embed (sum x y) = ba (embed x) (embed y)
  embed_mul : ∀ x y, embed (product x y) = bm (embed x) (embed y)
  red_one : red (integer 1) = ((1,0),(1,0))
  red_even_step : ∀ x y t, red (sum (product x y) (integer (2*t))) =
    DyadicFiberPrimes.product (red x) (red y)
  zero_red : ∀ x, embed x = scalar 0 → red x = ((0,0),(0,0))
  halve : ∀ x, red x = ((0,0),(0,0)) → ∃ y, embed x = dilate 2 (embed y)

/-- Integer numerator for d^deg(f) f(x/d) in the chosen lattice. -/
def homogenize {O : Type} (A : IntegralModel O) (d : Int) (x : O) : List Int → O
  | [] => A.integer 1
  | c :: cs => A.sum (A.product x (homogenize A d x cs)) (A.integer (d^(cs.length+1)*c))

theorem embed_homogenize {O : Type} (A : IntegralModel O) (d : Int) (x : O)
    (z : Biquad) (h : A.embed x = dilate d z) (f : List Int) :
    A.embed (homogenize A d x f) = dilate (d^f.length) (monicAt z f) := by
  induction f with
  | nil =>
    simp only [homogenize,monicAt,List.length_nil,Int.pow_zero,A.embed_int]
    exact (mul_one _).symm
  | cons c cs ih =>
    simp only [homogenize,monicAt,List.length_cons,A.embed_add,A.embed_mul,A.embed_int,ih,h,dilate_add]
    rw [dilate_scalar, ← dilate_product, Int.pow_succ', Int.mul_comm d (d^cs.length)]

/-- Each factor of the special fiber is a field. At even denominator,
a zero coordinate of the homogenized numerator forces the same coordinate of x to vanish. -/
theorem residue_of_homogenize {O : Type} (A : IntegralModel O) (t : Int) (x : O)
    (i : Bool) (f : List Int) :
    DyadicFiberPrimes.kernel i (A.red (homogenize A (2*t) x f)) → DyadicFiberPrimes.kernel i (A.red x) := by
  induction f with
  | nil => simp only [homogenize,A.red_one]; intro h; exact ((DyadicFiberPrimes.kernel_prime i).proper h).elim
  | cons c cs ih =>
    simp only [homogenize]
    have eq : (2*t)^(cs.length+1)*c = 2*(t*((2*t)^cs.length*c)) := by
      rw [Int.pow_succ']; grind
    rw [eq,A.red_even_step]
    intro h
    exact ((DyadicFiberPrimes.kernel_prime i).prime _ _ h).elim id ih

theorem even_numerator {O : Type} (A : IntegralModel O) (t : Int) (x : O) (z : Biquad)
    (hz : IsIntegral z) (hx : A.embed x = dilate (2*t) z) :
    ∃ y, A.embed x = dilate 2 (A.embed y) := by
  obtain ⟨f,hf⟩ := hz
  have he := embed_homogenize A (2*t) x z hx f
  rw [hf,dilate_zero] at he
  have hr := A.zero_red _ he
  have h (i : Bool) : DyadicFiberPrimes.kernel i (A.red x) :=
    residue_of_homogenize A t x i f (hr ▸ (DyadicFiberPrimes.kernel_prime i).zero)
  exact A.halve x (Prod.ext (h false) (h true))

/-- A positive common denominator can be chosen odd for every monic-integral field element. -/
theorem odd_denominator {O : Type} (A : IntegralModel O) (z : Biquad) (hz : IsIntegral z)
    (d : Nat) (hd : 0 < d) (x : O) (hx : A.embed x = dilate (d : Int) z) :
    ∃ k : Nat, k % 2 = 1 ∧ ∃ y, A.embed y = dilate (k : Int) z := by
  induction d using Nat.strongRecOn generalizing x with
  | ind d ih =>
    by_cases odd : d%2=1
    · exact ⟨d,odd,x,hx⟩
    · let t := d/2
      have he : (d : Int)=2*(t : Int) := by dsimp [t]; omega
      rw [he] at hx
      obtain ⟨y,hy⟩ := even_numerator A t x z hz hx
      have h₂ := TameTraceLattice277.scale_twice 2 (t : Int) z
      change dilate 2 (dilate (t : Int) z) = dilate (2*(t : Int)) z at h₂
      exact ih t (by dsimp [t]; omega) (by dsimp [t]; omega) y
        (cancel_double (hy.symm.trans (hx.trans h₂.symm)))

end Reimann.DyadicIntegralCriterion69
