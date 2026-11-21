import Mathlib.NumberTheory.Padics.RingHoms
import Reimann.TameLimit277
import Reimann.TameLocalOrders277

namespace Reimann.TamePadicInteger277

open TameLimit277

/-- Mathlib indexes residues by the exponent; the project starts at exponent one. -/
def exponentResidue (x : Integer277) : Nat → Int
  | 0 => 0
  | n + 1 => x.residue n

theorem exponentResidue_step (x : Integer277) (i : Nat) :
    (277 : Int) ^ i ∣ exponentResidue x (i+1) - exponentResidue x i := by
  cases i with
  | zero => simp [exponentResidue]
  | succ n => exact step_difference x n

theorem modulus_natCast (n : Nat) : ((277 ^ (n+1) : Nat) : Int) = modulus n := by
  simp [modulus]

theorem cast_truncation_difference (a b n : Nat) (hab : a ≤ b)
    (h : 277 ^ (n+1) ∣ b-a) : modulus n ∣ (b : Int) - (a : Int) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨(k : Int), ?_⟩
  rw [← modulus_natCast, ← Int.ofNat_sub hab, hk, Int.natCast_mul]

theorem prime277 : Nat.Prime 277 := by decide +kernel

local instance fact277 : Fact (Nat.Prime 277) := ⟨prime277⟩

/-- The actual p-adic integer represented by the canonical integer lifts. -/
noncomputable def realize (x : Integer277) : ℤ_[277] :=
  PadicInt.ofIntSeq (exponentResidue x)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ 277 (exponentResidue_step x))

theorem realize_reduction (x : Integer277) (n : Nat) :
    PadicInt.toZModPow (n+1) (realize x) =
      (x.residue n : ZMod (277 ^ (n+1))) :=
  PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (exponentResidue x) 277
    (exponentResidue_step x) (n+1)

/-- The truncations of a standard p-adic integer give compatible integer lifts. -/
theorem approximation_step (z : ℤ_[277]) (n : Nat) :
    modulus n ∣ (z.appr (n+2) : Int) - (z.appr (n+1) : Int) :=
  cast_truncation_difference _ _ n (PadicInt.appr_mono z (Nat.le_succ _))
    (PadicInt.dvd_appr_sub_appr z (n+1) (n+2) (Nat.le_succ _))

noncomputable def read (z : ℤ_[277]) : Integer277 :=
  ofCompatible (fun n => (z.appr (n+1) : Int)) (approximation_step z)

theorem read_residue (z : ℤ_[277]) (n : Nat) :
    (read z).residue n = (z.appr (n+1) : Int) := by
  change (z.appr (n+1) : Int) % modulus n = _
  apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
  rw [← modulus_natCast]
  exact Int.ofNat_lt.mpr (PadicInt.appr_lt z _)

theorem read_reduction (z : ℤ_[277]) (n : Nat) :
    ((read z).residue n : ZMod (277 ^ (n+1))) = PadicInt.toZModPow (n+1) z := by
  rw [read_residue, Int.cast_natCast]
  rfl

theorem ext_positive_reductions {v w : ℤ_[277]}
    (h : ∀ n : Nat, PadicInt.toZModPow (n+1) v = PadicInt.toZModPow (n+1) w) : v = w := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (277 ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n => exact h n

theorem realize_read (z : ℤ_[277]) : realize (read z) = z :=
  ext_positive_reductions (fun n => (realize_reduction _ n).trans (read_reduction z n))

theorem cast_residue_iff (x y : Integer277) (n : Nat) :
    (x.residue n : ZMod (277 ^ (n+1))) = (y.residue n : ZMod (277 ^ (n+1))) ↔
      x.residue n = y.residue n := by
  simpa only [modulus_natCast, x.canonical, y.canonical] using
    (ZMod.intCast_eq_intCast_iff' (x.residue n) (y.residue n) (277 ^ (n+1)))

theorem realize_injective : Function.Injective realize := by
  intro x y he
  apply equal_of_residues
  intro n
  have hr := congrArg (PadicInt.toZModPow (n+1)) he
  rw [realize_reduction, realize_reduction] at hr
  exact (cast_residue_iff x y n).mp hr

/-- A standard closed p-adic ball at positive integral depth is one residue class. -/
theorem norm_sub_le_iff_residue (x y : Integer277) (n : Nat) :
    ‖realize x - realize y‖ ≤ ((277 : Nat) : ℝ) ^ (-(↑(n+1) : ℤ)) ↔
      x.residue n = y.residue n := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, sub_eq_zero, realize_reduction, realize_reduction, cast_residue_iff]

/-- The open unit ball tests the residue used to label the four primes. -/
theorem norm_sub_lt_one_iff_first_residue (x y : Integer277) :
    ‖realize x - realize y‖ < 1 ↔ x.residue 0 = y.residue 0 := by
  have h : ‖realize x - realize y‖ ≤ ((277 : Nat) : ℝ) ^ (-1 : ℤ) ↔
      ‖realize x - realize y‖ < 1 := by
    simpa only [neg_add_cancel, zpow_zero] using
      (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (realize x - realize y) (-1))
  exact h.symm.trans (norm_sub_le_iff_residue x y 0)

theorem read_realize (x : Integer277) : read (realize x) = x :=
  realize_injective (realize_read _)

noncomputable def integerEquiv : Integer277 ≃ ℤ_[277] where
  toFun := realize
  invFun := read
  left_inv := read_realize
  right_inv := realize_read

/-- Casting a canonical residue to its finite ring discards the chosen representative. -/
theorem cast_remainder (a : Int) (n : Nat) :
    ((a % modulus n : Int) : ZMod (277 ^ (n+1))) = (a : ZMod (277 ^ (n+1))) := by
  rw [← modulus_natCast]
  exact ZMod.intCast_mod a _

theorem realize_add (x y : Integer277) :
    realize (TameLimit277.add x y) = realize x + realize y := by
  apply ext_positive_reductions
  intro n
  rw [map_add, realize_reduction, realize_reduction, realize_reduction]
  change (((x.residue n + y.residue n) % modulus n : Int) : ZMod (277 ^ (n+1))) = _
  rw [cast_remainder, Int.cast_add]

theorem realize_mul (x y : Integer277) :
    realize (TameLimit277.mul x y) = realize x * realize y := by
  apply ext_positive_reductions
  intro n
  rw [map_mul, realize_reduction, realize_reduction, realize_reduction]
  change (((x.residue n * y.residue n) % modulus n : Int) : ZMod (277 ^ (n+1))) = _
  rw [cast_remainder, Int.cast_mul]

theorem realize_neg (x : Integer277) :
    realize (TameLimit277.neg x) = -realize x := by
  apply ext_positive_reductions
  intro n
  rw [map_neg, realize_reduction, realize_reduction]
  change (((-x.residue n) % modulus n : Int) : ZMod (277 ^ (n+1))) = _
  rw [cast_remainder, Int.cast_neg]

theorem realize_ofInt (a : Int) : realize (ofInt a) = (a : ℤ_[277]) := by
  apply ext_positive_reductions
  intro n
  rw [map_intCast, realize_reduction]
  exact cast_remainder a n

scoped instance integerAdd : Add Integer277 := ⟨TameLimit277.add⟩
scoped instance integerMul : Mul Integer277 := ⟨TameLimit277.mul⟩

/-- The ring equivalence on the project's own residue-wise operations. -/
noncomputable def integerRingEquiv : Integer277 ≃+* ℤ_[277] where
  toEquiv := integerEquiv
  map_add' := realize_add
  map_mul' := realize_mul

open TameLocalOrders277 TameOrderCompletion277

/-- Evaluate an element completed at the ordinary powers of one signed prime. -/
noncomputable def orderToPadic (sx sy : Bool) (z : PrimeCompletion sx sy) : ℤ_[277] :=
  realize (toInteger (evaluation sx sy) (fromPrime sx sy z))

/-- Recover a prime-adic approximant using the standard p-adic integer's residues. -/
noncomputable def padicToOrder (sx sy : Bool) (z : ℤ_[277]) : PrimeCompletion sx sy :=
  toPrime sx sy (fromInteger (evaluation sx sy) (read z))

theorem padicToOrder_orderToPadic (sx sy : Bool) (z : PrimeCompletion sx sy) :
    padicToOrder sx sy (orderToPadic sx sy z) = z := by
  unfold padicToOrder orderToPadic
  rw [read_realize]
  exact (four_integral_completions sx sy).1 z

theorem orderToPadic_padicToOrder (sx sy : Bool) (z : ℤ_[277]) :
    orderToPadic sx sy (padicToOrder sx sy z) = z := by
  unfold padicToOrder orderToPadic
  rw [(four_integral_completions sx sy).2, realize_read]

/-- Each of the four completed polynomial orders is the standard p-adic integer ring. -/
noncomputable def integralCompletionEquiv (sx sy : Bool) : PrimeCompletion sx sy ≃ ℤ_[277] where
  toFun := orderToPadic sx sy
  invFun := padicToOrder sx sy
  left_inv := padicToOrder_orderToPadic sx sy
  right_inv := orderToPadic_padicToOrder sx sy

theorem orderToPadic_reduction (sx sy : Bool) (z : PrimeCompletion sx sy) (n : Nat) :
    PadicInt.toZModPow (n+1) (orderToPadic sx sy z) =
      ((toInteger (evaluation sx sy) (fromPrime sx sy z)).residue n : ZMod (277 ^ (n+1))) :=
  realize_reduction _ n

/-- Carry a pointwise operation on approximants across equality modulo ideal powers. -/
def primeOperation (sx sy : Bool) (B : BinaryOperation (evaluation sx sy))
    (x y : PrimeCompletion sx sy) : PrimeCompletion sx sy :=
  toPrime sx sy (onCompletion B (fromPrime sx sy x) (fromPrime sx sy y))

theorem primeOperation_coordinates (sx sy : Bool) (B : BinaryOperation (evaluation sx sy))
    (x y : PrimeCompletion sx sy) :
    toInteger (evaluation sx sy) (fromPrime sx sy (primeOperation sx sy B x y)) =
      B.limitOp (toInteger (evaluation sx sy) (fromPrime sx sy x))
        (toInteger (evaluation sx sy) (fromPrime sx sy y)) := by
  unfold primeOperation
  rw [(same_completions sx sy).2, toInteger_onCompletion]

theorem orderToPadic_add (sx sy : Bool) (x y : PrimeCompletion sx sy) :
    orderToPadic sx sy (primeOperation sx sy (completedAdd sx sy) x y) =
      orderToPadic sx sy x + orderToPadic sx sy y :=
  (congrArg realize (primeOperation_coordinates sx sy (completedAdd sx sy) x y)).trans
    (realize_add _ _)

theorem orderToPadic_mul (sx sy : Bool) (x y : PrimeCompletion sx sy) :
    orderToPadic sx sy (primeOperation sx sy (completedMul sx sy) x y) =
      orderToPadic sx sy x * orderToPadic sx sy y :=
  (congrArg realize (primeOperation_coordinates sx sy (completedMul sx sy) x y)).trans
    (realize_mul _ _)

scoped instance primeAdd (sx sy : Bool) : Add (PrimeCompletion sx sy) :=
  ⟨primeOperation sx sy (completedAdd sx sy)⟩

scoped instance primeMul (sx sy : Bool) : Mul (PrimeCompletion sx sy) :=
  ⟨primeOperation sx sy (completedMul sx sy)⟩

/-- The four comparisons preserve the original order operations on approximants. -/
noncomputable def integralCompletionRingEquiv (sx sy : Bool) :
    PrimeCompletion sx sy ≃+* ℤ_[277] where
  toEquiv := integralCompletionEquiv sx sy
  map_add' := orderToPadic_add sx sy
  map_mul' := orderToPadic_mul sx sy

end Reimann.TamePadicInteger277
