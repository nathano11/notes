import Reimann.TameLimit277

namespace Reimann.TameCauchy277

open TameLimit277

/-- The Cauchy condition for all neighborhoods 277^(n+1) ℤ at zero. -/
def IsCauchy (s : Nat → Int) : Prop :=
  ∀ n, ∃ N, ∀ i ≥ N, ∀ j ≥ N, s i % modulus n = s j % modulus n

structure CauchySeq where
  term : Nat → Int
  cauchy : IsCauchy term

/-- A sequence eventually has each prescribed inverse-limit residue. -/
def Converges (s : Nat → Int) (x : Integer277) : Prop :=
  ∀ n, ∃ N, ∀ i ≥ N, s i % modulus n = x.residue n

/-- The difference of the two Cauchy sequences tends to zero. -/
def Same (s t : CauchySeq) : Prop :=
  ∀ n, ∃ N, ∀ i ≥ N, s.term i % modulus n = t.term i % modulus n

def Completion := Quot Same

theorem cauchy_of_converges {s : Nat → Int} {x : Integer277} (h : Converges s x) :
    IsCauchy s := by
  intro n
  obtain ⟨N,hs⟩ := h n
  exact ⟨N,fun i hi j hj => (hs i hi).trans (hs j hj).symm⟩

theorem converges_unique {s : Nat → Int} {x y : Integer277}
    (hx : Converges s x) (hy : Converges s y) : x = y := by
  apply equal_of_residues
  intro n
  obtain ⟨N,hN⟩ := hx n
  obtain ⟨M,hM⟩ := hy n
  exact (hN (max N M) (Nat.le_max_left _ _)).symm.trans (hM _ (Nat.le_max_right _ _))

noncomputable def stableIndex (s : CauchySeq) (n : Nat) : Nat :=
  Classical.choose (s.cauchy n)

noncomputable def stableResidue (s : CauchySeq) (n : Nat) : Int :=
  s.term (stableIndex s n) % modulus n

theorem eventual_residue (s : CauchySeq) (n i : Nat) (hi : stableIndex s n ≤ i) :
    s.term i % modulus n = stableResidue s n :=
  Classical.choose_spec (s.cauchy n) i hi (stableIndex s n) (Nat.le_refl _)

theorem stable_compatible (s : CauchySeq) (n : Nat) :
    stableResidue s (n+1) % modulus n = stableResidue s n := by
  let i := max (stableIndex s n) (stableIndex s (n+1))
  have hn : stableIndex s n ≤ i := Nat.le_max_left _ _
  have hnext : stableIndex s (n+1) ≤ i := Nat.le_max_right _ _
  rw [← eventual_residue s (n+1) i hnext, Int.emod_emod_of_dvd _ (modulus_step n),
    eventual_residue s n i hn]

/-- Recover each coordinate from the tail at that precision. -/
noncomputable def seqLimit (s : CauchySeq) : Integer277 where
  residue := stableResidue s
  canonical n := Int.emod_emod _ _
  compatible := stable_compatible s

theorem converges_limit (s : CauchySeq) : Converges s.term (seqLimit s) :=
  fun n => ⟨stableIndex s n, fun i hi => eventual_residue s n i hi⟩

theorem same_of_converges {s t : CauchySeq} {x : Integer277} (hs : Converges s.term x)
    (ht : Converges t.term x) : Same s t := by
  intro n
  obtain ⟨N,hN⟩ := hs n
  obtain ⟨M,hM⟩ := ht n
  refine ⟨max N M,fun i hi => (hN i ?_).trans (hM i ?_).symm⟩
  · exact Nat.le_trans (Nat.le_max_left _ _) hi
  · exact Nat.le_trans (Nat.le_max_right _ _) hi

theorem transfer_converges {s t : CauchySeq} {x : Integer277} (hst : Same s t)
    (ht : Converges t.term x) : Converges s.term x := by
  intro n
  obtain ⟨N,hN⟩ := hst n
  obtain ⟨M,hM⟩ := ht n
  refine ⟨max N M,fun i hi => (hN i ?_).trans (hM i ?_)⟩
  · exact Nat.le_trans (Nat.le_max_left _ _) hi
  · exact Nat.le_trans (Nat.le_max_right _ _) hi

theorem same_iff_limit (s t : CauchySeq) : Same s t ↔ seqLimit s = seqLimit t := by
  constructor
  · intro h
    exact converges_unique (converges_limit s) (transfer_converges h (converges_limit t))
  · intro h
    exact same_of_converges (h ▸ converges_limit s) (converges_limit t)

noncomputable def toInteger : Completion → Integer277 :=
  Quot.lift seqLimit (fun s t => (same_iff_limit s t).mp)

theorem canonical_converges (x : Integer277) : Converges x.residue x :=
  fun n => ⟨n,fun _ hi => reduce x hi⟩

def canonicalSeq (x : Integer277) : CauchySeq :=
  ⟨x.residue,cauchy_of_converges (canonical_converges x)⟩

def ofInteger (x : Integer277) : Completion := Quot.mk _ (canonicalSeq x)

theorem toInteger_ofInteger (x : Integer277) : toInteger (ofInteger x) = x :=
  converges_unique (converges_limit (canonicalSeq x)) (canonical_converges x)

theorem ofInteger_toInteger (X : Completion) : ofInteger (toInteger X) = X := by
  induction X using Quot.ind with
  | mk s =>
    exact Quot.sound (same_of_converges (canonical_converges (seqLimit s)) (converges_limit s))

def constantSeq (a : Int) : CauchySeq :=
  ⟨fun _ => a,fun _ => ⟨0, fun _ _ _ _ => rfl⟩⟩

def constant (a : Int) : Completion := Quot.mk _ (constantSeq a)

theorem toInteger_constant (a : Int) : toInteger (constant a) = ofInt a :=
  converges_unique (converges_limit (constantSeq a)) (fun _ => ⟨0,fun _ _ => rfl⟩)

/-- An integer operation computed independently at every residue precision. -/
structure ResidueOperation where
  onInt : Int → Int → Int
  onLimit : Integer277 → Integer277 → Integer277
  reduce_op : ∀ n a b, onInt a b % modulus n =
    onInt (a % modulus n) (b % modulus n) % modulus n
  eval_op : ∀ n x y, (onLimit x y).residue n =
    onInt (x.residue n) (y.residue n) % modulus n

theorem converges_pointwise (B : ResidueOperation) {s t : Nat → Int} {x y : Integer277}
    (hs : Converges s x) (ht : Converges t y) :
    Converges (fun i => B.onInt (s i) (t i)) (B.onLimit x y) := by
  intro n
  obtain ⟨N,hN⟩ := hs n
  obtain ⟨M,hM⟩ := ht n
  refine ⟨max N M,fun i hi => ?_⟩
  rw [B.reduce_op, hN i (Nat.le_trans (Nat.le_max_left _ _) hi),
    hM i (Nat.le_trans (Nat.le_max_right _ _) hi), B.eval_op]

def pointwise (B : ResidueOperation) (s t : CauchySeq) : CauchySeq where
  term i := B.onInt (s.term i) (t.term i)
  cauchy := cauchy_of_converges (converges_pointwise B (converges_limit s) (converges_limit t))

theorem pointwise_limit (B : ResidueOperation) (s t : CauchySeq) :
    seqLimit (pointwise B s t) = B.onLimit (seqLimit s) (seqLimit t) :=
  converges_unique (converges_limit (pointwise B s t))
    (converges_pointwise B (converges_limit s) (converges_limit t))

theorem pointwise_respects (B : ResidueOperation) {s s' t t' : CauchySeq}
    (hs : Same s s') (ht : Same t t') : Same (pointwise B s t) (pointwise B s' t') := by
  apply (same_iff_limit _ _).mpr
  rw [pointwise_limit,pointwise_limit,(same_iff_limit _ _).mp hs,(same_iff_limit _ _).mp ht]

def onCompletion (B : ResidueOperation) : Completion → Completion → Completion :=
  Quot.lift (fun s => Quot.lift (fun t => Quot.mk _ (pointwise B s t))
    (fun _ _ ht => Quot.sound (pointwise_respects B (fun _ => ⟨0,fun _ _ => rfl⟩) ht)))
    (fun s s' hs => by
      funext T
      induction T using Quot.ind with
      | mk t => exact Quot.sound (pointwise_respects B hs (fun _ => ⟨0,fun _ _ => rfl⟩)))

theorem toInteger_onCompletion (B : ResidueOperation) (X Y : Completion) :
    toInteger (onCompletion B X Y) = B.onLimit (toInteger X) (toInteger Y) := by
  induction X using Quot.ind with
  | mk s =>
    induction Y using Quot.ind with
    | mk t => exact pointwise_limit B s t

def addition : ResidueOperation where
  onInt := (· + ·)
  onLimit := add
  reduce_op _ _ _ := Int.add_emod _ _ _
  eval_op _ _ _ := rfl

def multiplication : ResidueOperation where
  onInt := (· * ·)
  onLimit := mul
  reduce_op _ _ _ := Int.mul_emod _ _ _
  eval_op _ _ _ := rfl

theorem toInteger_add (x y : Completion) :
    toInteger (onCompletion addition x y) = add (toInteger x) (toInteger y) :=
  toInteger_onCompletion addition x y

theorem toInteger_mul (x y : Completion) :
    toInteger (onCompletion multiplication x y) = mul (toInteger x) (toInteger y) :=
  toInteger_onCompletion multiplication x y

theorem residue_eq_iff_dvd (a b : Int) (n : Nat) :
    a % modulus n = b % modulus n ↔ modulus n ∣ a-b :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.trans Int.dvd_iff_emod_eq_zero.symm

/-- Express the same Cauchy test at every natural exponent, including zero. -/
theorem cauchy_divisibility_iff (s : Nat → Int) : IsCauchy s ↔
    ∀ k : Nat, ∃ N, ∀ i ≥ N, ∀ j ≥ N, (277 : Int)^k ∣ s i - s j := by
  constructor
  · intro h k
    cases k with
    | zero => exact ⟨0,fun _ _ _ _ => by simp⟩
    | succ k =>
      obtain ⟨N,hN⟩ := h k
      exact ⟨N,fun i hi j hj => (residue_eq_iff_dvd _ _ k).mp (hN i hi j hj)⟩
  · intro h n
    obtain ⟨N,hN⟩ := h (n+1)
    exact ⟨N,fun i hi j hj => (residue_eq_iff_dvd _ _ n).mpr (hN i hi j hj)⟩

theorem same_divisibility_iff (s t : CauchySeq) : Same s t ↔
    ∀ k : Nat, ∃ N, ∀ i ≥ N, (277 : Int)^k ∣ s.term i - t.term i := by
  constructor
  · intro h k
    cases k with
    | zero => exact ⟨0,fun _ _ => by simp⟩
    | succ k =>
      obtain ⟨N,hN⟩ := h k
      exact ⟨N,fun i hi => (residue_eq_iff_dvd _ _ k).mp (hN i hi)⟩
  · intro h n
    obtain ⟨N,hN⟩ := h (n+1)
    exact ⟨N,fun i hi => (residue_eq_iff_dvd _ _ n).mpr (hN i hi)⟩

theorem constants_dense (X : Completion) (n : Nat) :
    ∃ a : Int, ∀ k ≤ n, (toInteger (constant a)).residue k = (toInteger X).residue k := by
  refine ⟨(toInteger X).residue n,fun k hk => ?_⟩
  rw [toInteger_constant]
  exact reduce (toInteger X) hk

def AdicCauchy (s : Nat → Integer277) : Prop :=
  ∀ n, ∃ N, ∀ i ≥ N, ∀ j ≥ N, (s i).residue n = (s j).residue n

def AdicConverges (s : Nat → Integer277) (x : Integer277) : Prop :=
  ∀ n, ∃ N, ∀ i ≥ N, (s i).residue n = x.residue n

theorem diagonal_isCauchy {s : Nat → Integer277} (h : AdicCauchy s) :
    IsCauchy (fun i => (s i).residue i) := by
  intro n
  obtain ⟨N,hN⟩ := h n
  refine ⟨max n N,fun i hi j hj => ?_⟩
  have hni := Nat.le_trans (Nat.le_max_left n N) hi
  have hnj := Nat.le_trans (Nat.le_max_left n N) hj
  rw [reduce (s i) hni,reduce (s j) hnj]
  exact hN i (Nat.le_trans (Nat.le_max_right _ _) hi) j (Nat.le_trans (Nat.le_max_right _ _) hj)

theorem diagonal_converges_iff (s : Nat → Integer277) (x : Integer277) :
    Converges (fun i => (s i).residue i) x ↔ AdicConverges s x := by
  constructor
  · intro h n
    obtain ⟨N,hN⟩ := h n
    refine ⟨max n N,fun i hi => ?_⟩
    rw [← reduce (s i) (Nat.le_trans (Nat.le_max_left n N) hi)]
    exact hN i (Nat.le_trans (Nat.le_max_right _ _) hi)
  · intro h n
    obtain ⟨N,hN⟩ := h n
    refine ⟨max n N,fun i hi => ?_⟩
    rw [reduce (s i) (Nat.le_trans (Nat.le_max_left n N) hi)]
    exact hN i (Nat.le_trans (Nat.le_max_right _ _) hi)

/-- Every Cauchy sequence in the completed integer ring has a unique limit. -/
theorem complete_and_separated (s : Nat → Integer277) (h : AdicCauchy s) :
    ∃ x : Integer277, AdicConverges s x ∧ ∀ y, AdicConverges s y → x = y := by
  let d : CauchySeq := ⟨fun i => (s i).residue i, diagonal_isCauchy h⟩
  have hd := converges_limit d
  exact ⟨seqLimit d, (diagonal_converges_iff s _).mp hd,
    fun y hy => converges_unique hd ((diagonal_converges_iff s y).mpr hy)⟩

/-- The ordinary Cauchy sequence completion of ℤ at 277 has inverse maps
to the ring of compatible residues. Arithmetic is taken termwise in ℤ. -/
theorem cauchy_integer_realization :
    (∀ x : Integer277, toInteger (ofInteger x) = x) ∧
    (∀ X : Completion, ofInteger (toInteger X) = X) ∧
    (∀ a : Int, toInteger (constant a) = ofInt a) ∧
    (∀ x y, toInteger (onCompletion addition x y) = add (toInteger x) (toInteger y)) ∧
    (∀ x y, toInteger (onCompletion multiplication x y) = mul (toInteger x) (toInteger y)) :=
  ⟨toInteger_ofInteger,ofInteger_toInteger,toInteger_constant,toInteger_add,toInteger_mul⟩

end Reimann.TameCauchy277
