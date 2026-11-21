import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

namespace Reimann.TameCyclotomicRoots277

open Polynomial

variable (F : Type*) [Field F] [CharZero F] [IsAlgClosed F] (m : ℕ) [NeZero m]

theorem separable_power_equation : (X^m-C (1:F)).Separable :=
  separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr (NeZero.ne m)) one_ne_zero

theorem root_count : (nthRoots m (1:F)).card = m := by
  change (X^m-C (1:F)).roots.card = m
  rw [← (IsAlgClosed.splits (X^m-C (1:F))).natDegree_eq_card_roots,
    natDegree_X_pow_sub_C]

theorem unity_card : Nat.card (rootsOfUnity m F) = m := by
  classical
  let t := nthRoots m (1:F)
  have he : {x // x ∈ t} ≃ ↥t.toFinset :=
    Equiv.subtypeEquivRight (fun x => Multiset.mem_toFinset.symm)
  calc
    Nat.card (rootsOfUnity m F) = Nat.card {x // x ∈ t} := Nat.card_congr (rootsOfUnityEquivNthRoots F m)
    _ = Nat.card ↥t.toFinset := Nat.card_congr he
    _ = t.toFinset.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
    _ = t.card := Multiset.toFinset_card_of_nodup (nodup_roots (separable_power_equation F m))
    _ = m := root_count F m

theorem enough : HasEnoughRootsOfUnity F m :=
  HasEnoughRootsOfUnity.of_card_le (unity_card F m).ge

end Reimann.TameCyclotomicRoots277
