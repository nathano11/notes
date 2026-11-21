import Reimann.TameLimit277

namespace Reimann.TameOrderCompletion277

open Reimann.TameLimit277

/-- Compatible residue evaluations with integer constants at every level. -/
structure Evaluation (O : Type) where
  eval : Nat → O → Int
  integral : Int → O
  compatible : ∀ n a, modulus n ∣ eval (n+1) a - eval n a
  constants : ∀ n z, modulus n ∣ eval n (integral z) - z

/-- An approximation at each level, coherent from one precision to the next. -/
structure Approximant (E : Evaluation O) where
  term : Nat → O
  coherent : ∀ n, modulus n ∣ E.eval (n+1) (term (n+1)) - E.eval n (term n)

def sameResidues (E : Evaluation O) (x y : Approximant E) : Prop :=
  ∀ n, E.eval n (x.term n) % modulus n = E.eval n (y.term n) % modulus n

/-- The inverse limit of the finite quotients by equality under evaluation. -/
def Completion (E : Evaluation O) := Quot (sameResidues E)

def toInteger (E : Evaluation O) : Completion E → Integer277 :=
  Quot.lift (fun x : Approximant E =>
    ofCompatible (fun n => E.eval n (x.term n)) x.coherent)
    (fun _ _ he => equal_of_residues he)

/-- Lift a compatible system using the integer residue at each level.
The correction terms from the chosen constant representatives disappear modulo
the smaller modulus by the divisibility of consecutive moduli. -/
def liftIntegral (E : Evaluation O) (x : Integer277) : Approximant E where
  term n := E.integral (x.residue n)
  coherent n := by
    obtain ⟨a,ha⟩ := Int.dvd_trans (modulus_step n) (E.constants (n+1) (x.residue (n+1)))
    obtain ⟨b,hb⟩ := E.constants n (x.residue n)
    obtain ⟨d,hd⟩ := step_difference x n
    exact ⟨a-b+d, by grind⟩

def fromInteger (E : Evaluation O) (x : Integer277) : Completion E :=
  Quot.mk _ (liftIntegral E x)

theorem constants_mod (E : Evaluation O) (n : Nat) (z : Int) :
    E.eval n (E.integral z) % modulus n = z % modulus n :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd (E.constants n z))

theorem toInteger_fromInteger (E : Evaluation O) (x : Integer277) :
    toInteger E (fromInteger E x) = x := by
  apply equal_of_residues
  intro n
  exact (constants_mod E n (x.residue n)).trans (x.canonical n)

theorem fromInteger_toInteger (E : Evaluation O) (X : Completion E) :
    fromInteger E (toInteger E X) = X := by
  induction X using Quot.ind with
  | mk x =>
    apply Quot.sound
    intro n
    exact (constants_mod E n (E.eval n (x.term n) % modulus n)).trans (Int.emod_emod _ _)

/-- The canonical image of the order before completion. -/
def ofOrder (E : Evaluation O) (a : O) : Completion E :=
  Quot.mk _ ⟨fun _ => a, fun n => E.compatible n a⟩

/-- Integer constants approximate every completed point at each prescribed precision. -/
theorem integer_constants_dense (E : Evaluation O) (X : Completion E) (n : Nat) :
    ∃ z : Int, (toInteger E (ofOrder E (E.integral z))).residue n = (toInteger E X).residue n :=
  ⟨(toInteger E X).residue n, (constants_mod E n _).trans ((toInteger E X).canonical n)⟩

theorem approximate_through (E : Evaluation O) (X : Completion E) (n : Nat) :
    ∃ z : Int, ∀ k ≤ n,
      (toInteger E (ofOrder E (E.integral z))).residue k = (toInteger E X).residue k := by
  obtain ⟨z,hz⟩ := integer_constants_dense E X n
  refine ⟨z,fun k hk => ?_⟩
  exact (reduce (toInteger E (ofOrder E (E.integral z))) hk).symm.trans
    ((congrArg (· % modulus k) hz).trans (reduce (toInteger E X) hk))

theorem coherent_of_residues (E : Evaluation O) (s : Nat → O) (z : Integer277)
    (hs : ∀ n, E.eval n (s n) % modulus n = z.residue n) :
    ∀ n, modulus n ∣ E.eval (n+1) (s (n+1)) - E.eval n (s n) := by
  intro n
  apply Int.dvd_of_emod_eq_zero
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  rw [← Int.emod_emod_of_dvd _ (modulus_step n), hs (n+1), hs n, z.compatible]

/-- A binary operation on the order whose residues are evaluated by a fixed
integer operation. The hypotheses are coordinate identities only. -/
structure BinaryOperation (E : Evaluation O) where
  op : O → O → O
  scalar : Int → Int → Int
  limitOp : Integer277 → Integer277 → Integer277
  eval_op : ∀ n a b, E.eval n (op a b) % modulus n =
    scalar (E.eval n a % modulus n) (E.eval n b % modulus n) % modulus n
  eval_limit : ∀ n a b, (limitOp a b).residue n =
    scalar (a.residue n) (b.residue n) % modulus n

def pointwise {E : Evaluation O} (B : BinaryOperation E) (x y : Approximant E) :
    Approximant E where
  term n := B.op (x.term n) (y.term n)
  coherent := coherent_of_residues E _ (B.limitOp (toInteger E (Quot.mk _ x))
    (toInteger E (Quot.mk _ y))) (fun n => (B.eval_op n _ _).trans
      (B.eval_limit n (toInteger E (Quot.mk _ x)) (toInteger E (Quot.mk _ y))).symm)

theorem pointwise_respects {E : Evaluation O} (B : BinaryOperation E)
    {x x' y y' : Approximant E} (hx : sameResidues E x x') (hy : sameResidues E y y') :
    sameResidues E (pointwise B x y) (pointwise B x' y') := by
  intro n
  change E.eval n (B.op (x.term n) (y.term n)) % modulus n =
    E.eval n (B.op (x'.term n) (y'.term n)) % modulus n
  rw [B.eval_op, B.eval_op, hx n, hy n]

/-- The pointwise operation on approximants descends to their quotient. -/
def onCompletion {E : Evaluation O} (B : BinaryOperation E) :
    Completion E → Completion E → Completion E :=
  Quot.lift (fun x => Quot.lift
    (fun y => Quot.mk _ (pointwise B x y))
    (fun _ _ hy => Quot.sound (pointwise_respects B (fun _ => rfl) hy)))
    (fun x x' hx => by
      funext Y
      induction Y using Quot.ind with
      | mk y => exact Quot.sound (pointwise_respects B hx (fun _ => rfl)))

theorem toInteger_onCompletion {E : Evaluation O} (B : BinaryOperation E)
    (X Y : Completion E) :
    toInteger E (onCompletion B X Y) = B.limitOp (toInteger E X) (toInteger E Y) := by
  induction X using Quot.ind with
  | mk x =>
    induction Y using Quot.ind with
    | mk y =>
      apply equal_of_residues
      intro n
      exact (B.eval_op n _ _).trans
        (B.eval_limit n (toInteger E (Quot.mk _ x)) (toInteger E (Quot.mk _ y))).symm

def addition (E : Evaluation O) (op : O → O → O)
    (h : ∀ n a b, E.eval n (op a b) % modulus n =
      (E.eval n a + E.eval n b) % modulus n) : BinaryOperation E where
  op := op
  scalar := (· + ·)
  limitOp := add
  eval_op n a b := (h n a b).trans (Int.add_emod _ _ _)
  eval_limit _ _ _ := rfl

def multiplication (E : Evaluation O) (op : O → O → O)
    (h : ∀ n a b, E.eval n (op a b) % modulus n =
      (E.eval n a * E.eval n b) % modulus n) : BinaryOperation E where
  op := op
  scalar := (· * ·)
  limitOp := mul
  eval_op n a b := (h n a b).trans (Int.mul_emod _ _ _)
  eval_limit _ _ _ := rfl

theorem fromInteger_limitOp {E : Evaluation O} (B : BinaryOperation E)
    (a b : Integer277) :
    fromInteger E (B.limitOp a b) = onCompletion B (fromInteger E a) (fromInteger E b) := by
  have h := toInteger_onCompletion B (fromInteger E a) (fromInteger E b)
  rw [toInteger_fromInteger,toInteger_fromInteger] at h
  rw [← h, fromInteger_toInteger]

end Reimann.TameOrderCompletion277
