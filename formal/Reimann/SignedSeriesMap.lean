import Reimann.DyadicSeriesProjection
import Reimann.SignedCyclicAction

/-! The low six bits of the full dyadic Cauchy product, and specialization
at the generator difference of the cyclic group of order 64. -/
namespace Reimann.SignedSeriesMap

open Reimann.DyadicLattice

abbrev Series := Reimann.DyadicSeriesProjection.Series

abbrev Coeffs := Nat → BitVec 6

def low (f : Series) : Coeffs := fun n => (f n).residue 5

/-- Cauchy multiplication after reduction of every coefficient modulo 64. -/
def cauchy (f g : Coeffs) (n : Nat) : BitVec 6 :=
  ((List.range (n+1)).map (fun j => f j * g (n-j))).foldr (·+·) 0

theorem low_sum (xs : List Scalar) :
    (xs.foldr add (natScalar 0)).residue 5 =
      (xs.map (fun a => a.residue 5)).foldr (·+·) 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (x.residue 5) + (xs.foldr add (natScalar 0)).residue 5 =
      x.residue 5 + (xs.map (fun a => a.residue 5)).foldr (·+·) 0
    rw [ih]

theorem low_convolution (f g : Series) :
    low (DyadicSeriesProjection.convolution f g) = cauchy (low f) (low g) := by
  funext n
  simp only [low, DyadicSeriesProjection.convolution, low_sum, List.map_map, cauchy]
  rfl

theorem cauchy_zero (f g : Coeffs) : cauchy f g 0 = f 0 * g 0 := by
  change f 0 * g 0 + 0 = _
  simp

theorem cauchy_succ (f g : Coeffs) (n : Nat) :
    cauchy f g (n+1) = f 0*g (n+1) + cauchy (fun k => f (k+1)) g n := by
  unfold cauchy
  rw [List.range_succ_eq_map (n := n+1)]
  simp [List.map_map, Function.comp_def]

abbrev Row := Fin 64 → BitVec 6

/-- Sum the first n coefficients against the supplied powers.
The bound is open: the coefficient at n is added in the successor step. -/
def partialAction (f : Coeffs) (power : Nat → Row) : Nat → Row
  | 0 => fun _ => 0
  | n+1 => fun i => partialAction f power n i + f n * power n i

theorem partial_add (f g : Coeffs) (p : Nat → Row) (n : Nat) (i : Fin 64) :
    partialAction (fun k => f k+g k) p n i = partialAction f p n i + partialAction g p n i := by
  induction n with
  | zero => simp [partialAction]
  | succ n ih => simp only [partialAction, ih, BitVec.add_mul]; ac_rfl

theorem partial_scale (c : BitVec 6) (f : Coeffs) (p : Nat → Row) (n : Nat) (i : Fin 64) :
    partialAction (fun k => c*f k) p n i = c * partialAction f p n i := by
  induction n with
  | zero => simp [partialAction]
  | succ n ih => simp [partialAction, ih, BitVec.mul_add, BitVec.mul_assoc]

/-- Multiplication of a coefficient sequence by T. -/
def delay (f : Coeffs) : Coeffs
  | 0 => 0
  | n+1 => f n

theorem partial_delay (f : Coeffs) (p : Nat → Row) (n : Nat) (i : Fin 64) :
    partialAction (delay f) p (n+1) i = partialAction f (fun k => p (k+1)) n i := by
  induction n with
  | zero => simp [partialAction, delay]
  | succ n ih => unfold partialAction; rw [ih]; rfl

theorem partial_difference (f : Coeffs) (p : Nat → Row) (n : Nat) (i : Fin 64) :
    partialAction f (fun k j => p k (j-1)-p k j) n i =
      partialAction f p n (i-1) - partialAction f p n i := by
  induction n with
  | zero => simp [partialAction]
  | succ n ih => simp only [partialAction, ih]; grind

theorem cauchy_decompose (f g : Coeffs) :
    cauchy f g = fun n => f 0*g n + delay (cauchy (fun k => f (k+1)) g) n := by
  funext n
  cases n with
  | zero => simp [cauchy_zero, delay]
  | succ n => exact cauchy_succ f g n

theorem fold_add_tail (xs : List (BitVec 6)) (b : BitVec 6) :
    xs.foldr (·+·) b = xs.foldr (·+·) 0 + b := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, BitVec.add_assoc]

theorem cauchy_right_succ (f g : Coeffs) (n : Nat) :
    cauchy f g (n+1) = cauchy f (fun k => g (k+1)) n + f (n+1)*g 0 := by
  unfold cauchy
  rw [List.range_succ (n := n+1), List.map_append, List.foldr_append]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.sub_self]
  have eqn : (List.range (n+1)).map (fun k => f k * g (n+1-k)) =
      (List.range (n+1)).map (fun k => f k * g (n-k+1)) := by
    apply List.map_congr_left
    intro k hk
    have h := List.mem_range.mp hk
    rw [show n+1-k = n-k+1 by omega]
  rw [eqn, fold_add_tail]
  simp

theorem cauchy_comm (f g : Coeffs) (n : Nat) : cauchy f g n = cauchy g f n := by
  induction n generalizing f g with
  | zero => simp [cauchy_zero, BitVec.mul_comm]
  | succ n ih =>
    rw [cauchy_succ f g, cauchy_right_succ g f, ih]
    grind

theorem zero_cauchy (g : Coeffs) (n : Nat) : cauchy (fun _ => 0) g n = 0 := by
  induction n with
  | zero => simp [cauchy_zero]
  | succ n ih => rw [cauchy_succ]; simpa using ih

/-- Exact coefficient sequence for a monic quadratic times a completely
unrestricted cofactor. This computes the usual full Cauchy product. -/
theorem tail_product_of_quadratic (c0 c1 : Scalar) (u : Series) :
    low (DyadicSeriesProjection.convolution (DyadicSeriesProjection.quadraticSeries c0 c1) u) =
    fun n => c0.residue 5 * low u n +
      (delay (fun k => c1.residue 5 * low u k + delay (low u) k)) n := by
  rw [low_convolution]
  funext n
  match n with
  | 0 => simp [cauchy_zero, low, DyadicSeriesProjection.quadraticSeries, delay]
  | 1 => simp [cauchy_zero, cauchy_succ, low, DyadicSeriesProjection.quadraticSeries, delay]
  | n+2 =>
    rw [cauchy_succ, cauchy_succ]
    have single : cauchy (fun k => low (DyadicSeriesProjection.quadraticSeries c0 c1) (k+1+1)) (low u) n = low u n := by
      cases n with
      | zero => simp [cauchy_zero, low, DyadicSeriesProjection.quadraticSeries, natScalar]
      | succ m =>
        rw [cauchy_succ]
        change 1 * low u (m+1) + cauchy (fun _ => 0) (low u) m = _
        rw [zero_cauchy (low u) m]; simp
    rw [single]
    rfl

/-- The missing endpoint of the delayed truncation vanishes because the
224th power is zero. The earlier powers obey the cyclic difference recurrence. -/
theorem truncated_delay (f : Coeffs) (p : Nat → Row)
    (hz : ∀ j, p 224 j = 0)
    (hstep : ∀ k j, p (k+1) j = p k (j-1) - p k j) (i : Fin 64) :
    partialAction (delay f) p 224 i =
      partialAction f p 224 (i-1) - partialAction f p 224 i := by
  have same : partialAction (delay f) p (224+1) i = partialAction (delay f) p 224 i := by
    change partialAction (delay f) p 224 i + delay f 224 * p 224 i = _
    rw [hz]; simp
  rw [← same, partial_delay]
  have step : (fun k => p (k+1)) = (fun k j => p k (j-1)-p k j) := by
    funext k j; exact hstep k j
  rw [step, partial_difference]

theorem two_predecessors (i : Fin 64) : (i-1)-1 = i-2 := by
  revert i
  decide

/-- Project the full quadratic times an arbitrary multiplier, with the
coefficient at the two preceding cyclic coordinates written explicitly. -/
theorem truncated_quadratic_product (c0 c1 : Scalar) (u : Series) (p : Nat → Row)
    (hz : ∀ j, p 224 j = 0) (hs : ∀ k j, p (k+1) j = p k (j-1) - p k j)
    (i : Fin 64) :
    partialAction (low (DyadicSeriesProjection.convolution
      (DyadicSeriesProjection.quadraticSeries c0 c1) u)) p 224 i =
      (1+c0.residue 5-c1.residue 5) * partialAction (low u) p 224 i +
      (c1.residue 5-2) * partialAction (low u) p 224 (i-1) +
      partialAction (low u) p 224 (i-2) := by
  rw [tail_product_of_quadratic, partial_add, partial_scale,
      truncated_delay _ p hz hs i]
  simp only [partial_add, partial_scale, truncated_delay _ p hz hs, two_predecessors]
  grind

theorem low_convolution_comm (f g : Series) :
    low (DyadicSeriesProjection.convolution f g) = low (DyadicSeriesProjection.convolution g f) := by
  rw [low_convolution, low_convolution]
  funext n; exact cauchy_comm _ _ _

/-- Multiplication by T in the full coefficient sequence over the dyadic integers. -/
def shiftSeries (f : Series) : Series
  | 0 => natScalar 0
  | n+1 => f n

theorem low_shift (f : Series) : low (shiftSeries f) = delay (low f) := by
  funext n
  cases n <;> rfl

theorem truncated_product_head (f g : Coeffs) (p : Nat → Row)
    (hz : ∀ j, p 224 j = 0) (hs : ∀ k j, p (k+1) j = p k (j-1) - p k j)
    (i : Fin 64) : partialAction (cauchy f g) p 224 i =
      f 0 * partialAction g p 224 i +
      (partialAction (cauchy (fun k => f (k+1)) g) p 224 (i-1) -
       partialAction (cauchy (fun k => f (k+1)) g) p 224 i) := by
  rw [cauchy_decompose f g, partial_add, partial_scale, truncated_delay _ p hz hs]

/-- Unroll the shifted cofactor recurrence to any depth with its exact remainder. -/
theorem telescoping (f : Coeffs) (p tail : Nat → Row)
    (h : ∀ k i, tail k i = f k * p k i + tail (k+1) i) (n : Nat) (i : Fin 64) :
    tail 0 i = partialAction f p n i + tail n i := by
  induction n with
  | zero => simp [partialAction]
  | succ n ih =>
    rw [ih, h n i, partialAction, BitVec.add_assoc]

/-- The action of a series with six-bit coefficients on an arbitrary cyclic row. -/
def action (f : Coeffs) (v : Row) : Row :=
  partialAction f (fun k => SignedCyclicAction.iterate k v) 224

/-- The projection from full dyadic power series, in the X-basis at X^64 = 1. -/
def evaluate (f : Series) : Row := action (low f) SignedCyclicAction.delta

theorem evaluate_low (f : Series) :
    evaluate f = partialAction (low f) (fun k => SignedCyclicAction.iterate k SignedCyclicAction.delta) 224 := rfl

theorem evaluate_add (f g : Series) (i : Fin 64) :
    evaluate (fun k => add (f k) (g k)) i = evaluate f i + evaluate g i :=
  partial_add (low f) (low g) _ _ i

theorem evaluate_scale (c : Scalar) (f : Series) (i : Fin 64) :
    evaluate (fun k => mul c (f k)) i = c.residue 5 * evaluate f i :=
  partial_scale (c.residue 5) (low f) _ _ i

theorem action_delay (f : Coeffs) (v : Row) :
    action (delay f) v = SignedCyclicAction.difference (action f v) := by
  funext i
  exact truncated_delay f _ (congrFun (SignedCyclicAction.iterate_224 v)) (fun _ _ => rfl) i

theorem evaluate_shift (f : Series) :
    evaluate (shiftSeries f) = SignedCyclicAction.difference (evaluate f) := by
  unfold evaluate
  rw [low_shift, action_delay]

/-- Every actual series cofactor gives the coordinate multiplier in the cyclic row.
No condition on its coefficients or on the quadratic is needed. -/
theorem evaluate_quadratic_product (c0 c1 : Scalar) (u : Series) (i : Fin 64) :
    evaluate (DyadicSeriesProjection.convolution (DyadicSeriesProjection.quadraticSeries c0 c1) u) i =
      (1+c0.residue 5-c1.residue 5)*evaluate u i +
      (c1.residue 5-2)*evaluate u (i-1) + evaluate u (i-2) :=
  truncated_quadratic_product c0 c1 u _ (congrFun (SignedCyclicAction.iterate_224 _)) (fun _ _ => rfl) i

theorem evaluate_quadratic_product_right (c0 c1 : Scalar) (u : Series) (i : Fin 64) :
    evaluate (DyadicSeriesProjection.convolution u (DyadicSeriesProjection.quadraticSeries c0 c1)) i =
      (1+c0.residue 5-c1.residue 5)*evaluate u i +
      (c1.residue 5-2)*evaluate u (i-1) + evaluate u (i-2) := by
  have h := evaluate_quadratic_product c0 c1 u i
  unfold evaluate at h ⊢
  rw [low_convolution_comm u]
  exact h

theorem iterate_difference (n : Nat) (v : Row) :
    SignedCyclicAction.iterate n (SignedCyclicAction.difference v) =
      SignedCyclicAction.iterate (n+1) v := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg SignedCyclicAction.difference ih

theorem action_product_head (f g : Coeffs) (v : Row) (i : Fin 64) :
    action (cauchy f g) v i = f 0 * action g v i +
      SignedCyclicAction.difference (action (cauchy (fun k => f (k+1)) g) v) i :=
  truncated_product_head f g _ (congrFun (SignedCyclicAction.iterate_224 v)) (fun _ _ => rfl) i

/-- Multiplication of arbitrary formal series acts by composition in the regular
representation of the finite cyclic group ring. -/
theorem action_cauchy (f g : Coeffs) (v : Row) :
    action (cauchy f g) v = action f (action g v) := by
  let rest (n : Nat) := action (cauchy (fun k => f (n+k)) g) v
  let tail (n : Nat) := SignedCyclicAction.iterate n (rest n)
  have peel (n : Nat) : rest n = fun i => f n * action g v i +
      SignedCyclicAction.difference (rest (n+1)) i := by
    have next : (fun k => f (n+(k+1))) = fun k => f (n+1+k) := by
      funext k; congr 1; omega
    funext i
    simpa only [rest, Nat.add_zero, next] using action_product_head (fun k => f (n+k)) g v i
  have step (n : Nat) (i : Fin 64) :
      tail n i = f n * SignedCyclicAction.iterate n (action g v) i + tail (n+1) i := by
    dsimp only [tail]
    rw [peel n, SignedCyclicAction.iterate_add, SignedCyclicAction.iterate_scale, iterate_difference]
  have start : tail 0 = action (cauchy f g) v := by
    simp [tail, rest, SignedCyclicAction.iterate]
  have stop : tail 224 = fun _ => 0 := SignedCyclicAction.iterate_224 _
  funext i
  have result := telescoping f (fun k => SignedCyclicAction.iterate k (action g v)) tail step 224 i
  rw [start, stop] at result
  exact result.trans (BitVec.add_zero (action f (action g v) i))

/-- Specialization carries the unrestricted full Cauchy product to the
action of the first projected power series on the row of the second. -/
theorem evaluate_convolution (f g : Series) :
    evaluate (DyadicSeriesProjection.convolution f g) = action (low f) (evaluate g) := by
  unfold evaluate
  rw [low_convolution, action_cauchy]

end Reimann.SignedSeriesMap
