import Reimann.CircularMonomial69

/-! Finite evaluation of rational coefficient sequences at a field element,
with explicit cutoffs for monic normalization and polynomial division. -/
namespace Reimann.CircularRelationEval69

open Lean.Grind Lean.Grind.Field.NormNum CircularGauss69 CircularMonomial69

def evalAt {R : Type} [Field R] (x : R) (p : Nat → Rat) (n : Nat) : R :=
  sumBelow (fun i => ofRat (p i) * x^i) n

def Vanishes {R : Type} [Field R] (x : R) (p : Nat → Rat) : Prop :=
  ∃ m, Bounded p m ∧ evalAt x p m = 0

theorem ofRat_zero {R : Type} [Field R] : (ofRat 0 : R) = 0 := by
  simp [ofRat, Ring.intCast_zero, Semiring.natCast_one, Field.div_eq_mul_inv,
    Field.inv_one, Semiring.mul_one]

theorem ofRat_one {R : Type} [Field R] : (ofRat 1 : R) = 1 := by
  simp [ofRat, Ring.intCast_one, Semiring.natCast_one, Field.div_eq_mul_inv,
    Field.inv_one, Semiring.mul_one]

theorem eval_succ {R : Type} [Field R] (x : R) (p : Nat → Rat) (n : Nat) :
    evalAt x p (n+1) = evalAt x p n + ofRat (p n) * x^n := rfl

theorem eval_extend {R : Type} [Field R] (x : R) (p : Nat → Rat) (m n : Nat)
    (hb : Bounded p m) (hmn : m ≤ n) : evalAt x p n = evalAt x p m := by
  induction n with
  | zero =>
    have e : m = 0 := by omega
    rw [e]
  | succ n ih =>
    by_cases e : m = n+1
    · rw [e]
    · rw [eval_succ, hb n (by omega), ofRat_zero, Semiring.zero_mul, Semiring.add_zero,
        ih (by omega)]

theorem eval_of_vanishes {R : Type} [Field R] (x : R) (p : Nat → Rat) (m : Nat)
    (hb : Bounded p m) (hp : Vanishes x p) : evalAt x p m = 0 := by
  obtain ⟨n, hn, hv⟩ := hp
  exact (eval_extend x p m (max m n) hb (Nat.le_max_left ..)).symm.trans
    ((eval_extend x p n (max m n) hn (Nat.le_max_right ..)).trans hv)

theorem eval_scale {R : Type} [Field R] [IsCharP R 0] (x : R) (a : Rat)
    (p : Nat → Rat) (m : Nat) :
    evalAt x (fun i => a * p i) m = ofRat a * evalAt x p m := by
  induction m with
  | zero => change 0 = _ * 0; rw [Semiring.mul_zero]
  | succ m ih => rw [eval_succ, eval_succ, ofRat_mul, ih]; grind only

theorem eval_sub {R : Type} [Field R] [IsCharP R 0] (x : R)
    (p q : Nat → Rat) (m : Nat) :
    evalAt x (fun i => p i - q i) m = evalAt x p m - evalAt x q m := by
  induction m with
  | zero => change 0 = 0 - 0; grind only
  | succ m ih => rw [eval_succ, eval_succ, eval_succ, ofRat_sub, ih]; grind only

theorem eval_zero_below {R : Type} [Field R] (x : R) (p : Nat → Rat) (m : Nat)
    (hz : ∀ k < m, p k = 0) : evalAt x p m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [eval_succ, hz m (by omega), ofRat_zero, Semiring.zero_mul, Semiring.add_zero]
    exact ih (fun k hk => hz k (by omega))

theorem shift_below (s : Nat) (a : Rat) (p : Nat → Rat) (k : Nat) (hk : k < s) :
    shift s a p k = 0 := by simp [shift, Nat.not_le.mpr hk]

theorem shift_at (s : Nat) (a : Rat) (p : Nat → Rat) (k : Nat) :
    shift s a p (s+k) = a * p k := by simp [shift]

theorem eval_shift {R : Type} [Field R] [IsCharP R 0] (x : R)
    (s : Nat) (a : Rat) (p : Nat → Rat) (m : Nat) :
    evalAt x (shift s a p) (s+m) = (ofRat a * x^s) * evalAt x p m := by
  induction m with
  | zero =>
    rw [Nat.add_zero, eval_zero_below x _ _ (shift_below s a p)]
    change 0 = _ * 0
    rw [Semiring.mul_zero]
  | succ m ih =>
    rw [Nat.add_succ, eval_succ, shift_at, ofRat_mul, eval_succ, ih, Semiring.pow_add]
    grind only

theorem bounded_shift (s : Nat) (a : Rat) (p : Nat → Rat) (m : Nat) (hp : Bounded p m) :
    Bounded (shift s a p) (s+m) := by
  intro k hk
  simp [shift, show s ≤ k by omega, hp (k-s) (by omega), Rat.mul_zero]

theorem vanishes_shift {R : Type} [Field R] [IsCharP R 0] (x : R) (p : Nat → Rat)
    (s : Nat) (a : Rat) (hp : Vanishes x p) : Vanishes x (shift s a p) := by
  obtain ⟨m, hb, he⟩ := hp
  exact ⟨s+m, bounded_shift s a p m hb, by rw [eval_shift, he, Semiring.mul_zero]⟩

theorem vanishes_sub {R : Type} [Field R] [IsCharP R 0] (x : R)
    (p q : Nat → Rat) (hp : Vanishes x p) (hq : Vanishes x q) :
    Vanishes x (fun i => p i - q i) := by
  obtain ⟨m, bm, em⟩ := hp
  obtain ⟨n, bn, en⟩ := hq
  refine ⟨max m n, ?_, ?_⟩
  · intro k hk
    change p k - q k = 0
    rw [bm k (Nat.le_trans (Nat.le_max_left ..) hk), bn k (Nat.le_trans (Nat.le_max_right ..) hk),
      Rat.sub_self]
  · rw [eval_sub, eval_extend x p m _ bm (Nat.le_max_left ..),
      eval_extend x q n _ bn (Nat.le_max_right ..), em, en]
    grind only

theorem vanishes_sub_shift {R : Type} [Field R] [IsCharP R 0] (x : R)
    (p D : Nat → Rat) (s : Nat) (a : Rat) (hp : Vanishes x p) (hD : Vanishes x D) :
    Vanishes x (fun i => p i - shift s a D i) :=
  vanishes_sub x p _ hp (vanishes_shift x D s a hD)

theorem last_nonzero (p : Nat → Rat) (m : Nat) (hb : Bounded p m) (hn : ∃ i, p i ≠ 0) :
    ∃ d, d < m ∧ p d ≠ 0 ∧ Bounded p (d+1) := by
  induction m with
  | zero =>
    obtain ⟨i, hi⟩ := hn
    exact False.elim (hi (hb i (Nat.zero_le i)))
  | succ m ih =>
    by_cases h : p m = 0
    · have hlow : Bounded p m := by
        intro k hk
        by_cases e : k = m
        · rw [e, h]
        · exact hb k (by omega)
      obtain ⟨d, hd, hnz, bd⟩ := ih hlow
      exact ⟨d, by omega, hnz, bd⟩
    · exact ⟨m, Nat.lt_succ_self _, h, hb⟩

theorem normalize_at_degree {R : Type} [Field R] [IsCharP R 0] (x : R)
    (p : Nat → Rat) (d : Nat) (hb : Bounded p (d+1))
    (hn : p d ≠ 0) (hp : Vanishes x p) :
    let q := fun i => (p d)⁻¹ * p i
    Bounded q (d+1) ∧ q d = 1 ∧ Vanishes x q := by
  let q := fun i => (p d)⁻¹ * p i
  have bq : Bounded q (d+1) := by
    intro i hi
    change (p d)⁻¹ * p i = 0
    rw [hb i hi, Rat.mul_zero]
  exact ⟨bq, Rat.inv_mul_cancel _ hn, d+1, bq, by
    rw [eval_scale, eval_of_vanishes x p _ hb hp, Semiring.mul_zero]⟩

theorem monic_of_vanishing {R : Type} [Field R] [IsCharP R 0] (x : R)
    (p : Nat → Rat) (m : Nat) (hb : Bounded p m) (hn : ∃ i, p i ≠ 0) (hp : Vanishes x p) :
    ∃ d < m, ∃ q : Nat → Rat, Bounded q (d+1) ∧ q d = 1 ∧ Vanishes x q := by
  obtain ⟨d, hd, hnz, bd⟩ := last_nonzero p m hb hn
  exact ⟨d, hd, _, normalize_at_degree x p d bd hnz hp⟩

theorem no_monic_constant {R : Type} [Field R] [IsCharP R 0] (x : R)
    (p : Nat → Rat) (hb : Bounded p 1) (hc : p 0 = 1) : ¬ Vanishes x p := by
  intro hp
  have h := eval_of_vanishes x p 1 hb hp
  change 0 + ofRat (p 0) * x^0 = 0 at h
  rw [hc, ofRat_one, Semiring.pow_zero, Semiring.mul_one] at h
  have h01 : (1 : R) = 0 := by grind only
  have hrat := (IsCharP.natCast_eq_zero_iff (α := R) 0 1).mp
  have hf := hrat (by simpa only [Semiring.natCast_one] using h01)
  omega

end Reimann.CircularRelationEval69
