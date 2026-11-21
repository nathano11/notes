import Reimann.TameArithmetic277
import Reimann.TameOrderCompletion277
import Reimann.TamePrimePowers277
import Reimann.TameOrderPrimes277

namespace Reimann.TameLocalOrders277

open Reimann.TameArithmetic277 Reimann.TameOrderCompletion277 Reimann.TameLimit277
open Reimann.TameBiquadratic277 Reimann.TameOrderReduction277 Fin.IntCast Lean.Grind

/-- Evaluation of the integral polynomial order at one fixed pair of signs. -/
def evaluation (sx sy : Bool) : Evaluation OrderCoordinates where
  eval := branchEval sx sy
  integral := integerCoordinates
  compatible := branchEval_compatible sx sy
  constants n z := by rw [branchEval_integer]; simp

theorem coordinate_product (sx sy : Bool) {S : Type} [CommRing S] (u v : Quad S) :
    coordinate sx sy (pointProduct u v) = coordinate sx sy u*coordinate sx sy v := by
  cases sx <;> cases sy <;> rfl

theorem evaluation_product (sx sy : Bool) (n : Nat) (u v : OrderCoordinates) :
    branchEval sx sy n (product (-3) (-23) u v) % modulus n =
      (branchEval sx sy n u * branchEval sx sy n v) % modulus n := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  apply (cast_eq_iff n _ _).mp
  rw [Ring.intCast_mul, ← bridge, ← bridge, ← bridge, reduce_product,
    (finite_splitting277 n).mul, coordinate_product]

theorem evaluation_sum (sx sy : Bool) (n : Nat) (u v : OrderCoordinates) :
    branchEval sx sy n (componentAdd u v) =
      branchEval sx sy n u + branchEval sx sy n v := by
  unfold branchEval componentAdd evalAt
  grind

def completedAdd (sx sy : Bool) : BinaryOperation (evaluation sx sy) :=
  addition _ componentAdd (fun n u v => congrArg (fun z => z % modulus n)
    (evaluation_sum sx sy n u v))

def completedMul (sx sy : Bool) : BinaryOperation (evaluation sx sy) :=
  multiplication _ (product (-3) (-23)) (evaluation_product sx sy)

/-- On the explicit integral polynomial order, each of the four evaluation
filtrations has completion Z_277, with its original pointwise operations. -/
theorem four_evaluation_completions (sx sy : Bool) :
    (∀ x, toInteger (evaluation sx sy) (fromInteger (evaluation sx sy) x) = x) ∧
    (∀ X, fromInteger (evaluation sx sy) (toInteger (evaluation sx sy) X) = X) ∧
    (∀ X Y, toInteger (evaluation sx sy) (onCompletion (completedAdd sx sy) X Y) =
       add (toInteger (evaluation sx sy) X) (toInteger (evaluation sx sy) Y)) ∧
    (∀ X Y, toInteger (evaluation sx sy) (onCompletion (completedMul sx sy) X Y) =
       mul (toInteger (evaluation sx sy) X) (toInteger (evaluation sx sy) Y)) :=
  ⟨toInteger_fromInteger _, fromInteger_toInteger _,
    toInteger_onCompletion (completedAdd sx sy), toInteger_onCompletion (completedMul sx sy)⟩

def branchIndex (sx sy : Bool) : Fin 4 :=
  if sx then (if sy then 3 else 2) else (if sy then 1 else 0)

theorem branchIndex_bijective :
    (∀ i : Fin 4, ∃ s t : Bool, branchIndex s t = i) ∧
    (∀ s t s' t', branchIndex s t = branchIndex s' t' → s = s' ∧ t = t') := by
  decide +kernel

theorem branch_prime (sx sy : Bool) (v : OrderCoordinates) :
    TameOrderPrimes277.coordinateKernel (branchIndex sx sy) v ↔
      TamePrimePowers277.primePlace sx sy v := by
  have h : TameOrderPrimes277.red v (branchIndex sx sy) =
      coordinate sx sy ((finite_splitting277 0).evaluate (reduce 0 v)) := by
    cases sx <;> cases sy <;> rfl
  change TameOrderPrimes277.red v (branchIndex sx sy) = 0 ↔
    (277 : Int) ∣ branchEval sx sy 0 v
  rw [h, bridge]
  change ((branchEval sx sy 0 v : Int) : Residue 0) = ((0 : Int) : Residue 0) ↔ _
  rw [cast_eq_iff]
  simp

theorem all_order_primes (P : OrderCoordinates → Prop) :
    (TameOrderPrimes277.OrderPrime P ∧ P (integerCoordinates 277)) ↔
      ∃ s t : Bool, P = TamePrimePowers277.primePlace s t ∧
        ∀ s' t', P = TamePrimePowers277.primePlace s' t' → s = s' ∧ t = t' := by
  have eqp (s t : Bool) : TameOrderPrimes277.coordinateKernel (branchIndex s t) =
      TamePrimePowers277.primePlace s t := funext (fun v => propext (branch_prime s t v))
  constructor
  · intro hp
    obtain ⟨i,hi,hu⟩ := (TameOrderPrimes277.four_primes_above_277 P).mp hp
    obtain ⟨s,t,he⟩ := branchIndex_bijective.1 i
    subst i
    refine ⟨s,t,hi.trans (eqp s t),?_⟩
    intro s' t' h'
    exact branchIndex_bijective.2 _ _ _ _ (hu _ (h'.trans (eqp s' t').symm)).symm
  · rintro ⟨s,t,rfl,_⟩
    rw [← eqp]
    exact ⟨TameOrderPrimes277.coordinate_prime _,TameOrderPrimes277.coordinate_above _⟩

def difference (v w : OrderCoordinates) : OrderCoordinates :=
  componentAdd v (scale (-1) w)

theorem evaluation_difference (sx sy : Bool) (n : Nat) (v w : OrderCoordinates) :
    branchEval sx sy n (difference v w) = branchEval sx sy n v - branchEval sx sy n w := by
  unfold difference branchEval componentAdd scale evalAt
  grind

theorem equal_mod_prime_power (sx sy : Bool) (n : Nat) (v w : OrderCoordinates) :
    TamePrimePowers277.primePower sx sy (n+1) (difference v w) ↔
      branchEval sx sy n v % modulus n = branchEval sx sy n w % modulus n := by
  rw [TamePrimePowers277.prime_power_iff, evaluation_difference]
  exact Int.dvd_iff_emod_eq_zero.trans Int.emod_eq_emod_iff_emod_sub_eq_zero.symm

theorem coherent_mod_prime_power (sx sy : Bool) (n : Nat) (v w : OrderCoordinates) :
    TamePrimePowers277.primePower sx sy (n+1) (difference v w) ↔
      modulus n ∣ branchEval sx sy (n+1) v-branchEval sx sy n w := by
  rw [TamePrimePowers277.prime_power_iff, evaluation_difference]
  obtain ⟨e,he⟩ := branchEval_compatible sx sy n v
  change _ ↔ (277 : Int)^(n+1) ∣ _
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a+e, by grind⟩
  · rintro ⟨a,ha⟩
    exact ⟨a-e, by grind⟩

/-- A sequence of elements of the integral order, compatible modulo the
ordinary powers of its specified prime ideal. -/
structure PrimePath (sx sy : Bool) where
  term : Nat → OrderCoordinates
  coherent : ∀ n, TamePrimePowers277.primePower sx sy (n+1) (difference (term (n+1)) (term n))

def PrimeCompletion (sx sy : Bool) := Quot (fun x y : PrimePath sx sy =>
  ∀ n, TamePrimePowers277.primePower sx sy (n+1) (difference (x.term n) (y.term n)))

def fromPrime (sx sy : Bool) : PrimeCompletion sx sy → Completion (evaluation sx sy) :=
  Quot.lift (fun x : PrimePath sx sy =>
    Quot.mk _ (⟨x.term, fun n => (coherent_mod_prime_power sx sy n _ _).mp
      (x.coherent n)⟩ : Approximant (evaluation sx sy)))
    (fun x y h => Quot.sound (fun n => (equal_mod_prime_power sx sy n (x.term n) (y.term n)).mp (h n)))

def toPrime (sx sy : Bool) : Completion (evaluation sx sy) → PrimeCompletion sx sy :=
  Quot.lift (fun x : Approximant (evaluation sx sy) =>
    Quot.mk _ (⟨x.term, fun n => (coherent_mod_prime_power sx sy n _ _).mpr
      (x.coherent n)⟩ : PrimePath sx sy))
    (fun x y h => Quot.sound (fun n => (equal_mod_prime_power sx sy n (x.term n) (y.term n)).mpr (h n)))

theorem same_completions (sx sy : Bool) :
    (∀ z, toPrime sx sy (fromPrime sx sy z) = z) ∧
    (∀ w, fromPrime sx sy (toPrime sx sy w) = w) := by
  constructor <;> intro x <;> induction x using Quot.ind <;> rfl

/-- For each signed prime, the completion defined directly by ordinary ideal
powers has mutually inverse maps to the inverse-limit ring of 277-adic integers.
All prime ideals of the polynomial order above 277 occur in all_order_primes. -/
theorem four_integral_completions (sx sy : Bool) :
    (∀ z : PrimeCompletion sx sy,
      toPrime sx sy (fromInteger (evaluation sx sy)
        (toInteger (evaluation sx sy) (fromPrime sx sy z))) = z) ∧
    (∀ a : Integer277, toInteger (evaluation sx sy) (fromPrime sx sy
      (toPrime sx sy (fromInteger (evaluation sx sy) a))) = a) := by
  constructor
  · intro z
    rw [fromInteger_toInteger, (same_completions sx sy).1]
  · intro a
    rw [(same_completions sx sy).2, toInteger_fromInteger]

end Reimann.TameLocalOrders277
