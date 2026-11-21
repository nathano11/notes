import Reimann.Cubic

namespace Reimann.TameExample

/-- Fundamental-discriminant arithmetic for the two real quadratic subfields. -/
theorem discriminants :
    3*107 = 321 ∧ 3*503 = 1509 ∧ 321 % 4 = 1 ∧ 1509 % 4 = 1 ∧
    17^2 < 321 ∧ 321 < 18^2 ∧ 38^2 < 1509 ∧ 1509 < 39^2 := by decide +kernel

/-- Complete successor cycles, each starting at its lexicographically least pair. -/
def states321 : List (List Cubic.ReducedPair) := [
  [(2,17),(16,17),(6,15),(16,15)],
  [(4,15),(8,17),(12,15),(20,9),(10,11),(24,9)],
  [(4,17),(24,15),(10,9),(20,11),(12,9),(8,15)]]

def states1509 : List (List Cubic.ReducedPair) := [
  [(2,37),(70,37),(6,33),(70,33)],
  [(10,33),(14,37),(30,33),(26,27),(34,25),(42,9)],
  [(10,37),(42,33),(34,9),(26,25),(30,27),(14,33)]]

/-- Every displayed transition is the actual reduction recurrence, including
    each closing transition. The three cycles have no state in common. -/
theorem cycles321 :
    states321.map List.length = [4,6,6] ∧ states321.flatten.Nodup ∧
    states321.all (fun xs => xs.map (Cubic.successor 321 17) == xs.drop 1 ++ xs.take 1) = true ∧
    states321.flatten.all (Cubic.isReduced 321 17) = true ∧
    Cubic.reducedCount 321 17 = 16 := by decide +kernel

theorem cycles1509 :
    states1509.map List.length = [4,6,6] ∧ states1509.flatten.Nodup ∧
    states1509.all (fun xs => xs.map (Cubic.successor 1509 38) == xs.drop 1 ++ xs.take 1) = true ∧
    states1509.flatten.all (Cubic.isReduced 1509 38) = true ∧
    Cubic.reducedCount 1509 38 = 16 := by decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Bounded membership check independent of the reducedCount algorithm. -/
theorem box321 : ∀ Q : Fin 35, ∀ P : Fin 18,
    Cubic.isReduced 321 17 (Q.val,P.val) = true ↔ (Q.val,P.val) ∈ states321.flatten := by
  decide +kernel

theorem box1509 : ∀ Q : Fin 77, ∀ P : Fin 39,
    Cubic.isReduced 1509 38 (Q.val,P.val) = true ↔ (Q.val,P.val) ∈ states1509.flatten := by
  decide +kernel

/-- The defining inequalities put every reduced state inside the search box. -/
theorem reduced_box_bounds (D h Q P : Nat) (hr : Cubic.isReduced D h (Q,P) = true) :
    Q < 2*h+1 ∧ P < h+1 := by
  simp only [Cubic.isReduced, decide_eq_true_eq] at hr
  omega

theorem complete321 (Q P : Nat) :
    Cubic.isReduced 321 17 (Q,P) = true ↔ (Q,P) ∈ states321.flatten := by
  constructor
  · intro hr
    obtain ⟨hq,hp⟩ := reduced_box_bounds _ _ _ _ hr
    exact (box321 ⟨Q,hq⟩ ⟨P,hp⟩).mp hr
  · intro hm
    exact List.all_eq_true.mp cycles321.2.2.2.1 _ hm

theorem complete1509 (Q P : Nat) :
    Cubic.isReduced 1509 38 (Q,P) = true ↔ (Q,P) ∈ states1509.flatten := by
  constructor
  · intro hr
    obtain ⟨hq,hp⟩ := reduced_box_bounds _ _ _ _ hr
    exact (box1509 ⟨Q,hq⟩ ⟨P,hp⟩).mp hr
  · intro hm
    exact List.all_eq_true.mp cycles1509.2.2.2.1 _ hm

theorem square_mod_three (x : Int) : x^2 % 3 ≠ 2 := by
  have h : x%3 = 0 ∨ x%3 = 1 ∨ x%3 = 2 := by omega
  rw [Int.pow_succ, Int.pow_one, Int.mul_emod]
  rcases h with h | h | h <;> rw [h] <;> decide

/-- No element (x+y√D)/2 can have norm -1 when 3 divides D. -/
theorem negative_norm_obstruction (D x y : Int) (hD : 3 ∣ D) :
    x^2-D*y^2 ≠ -4 := by
  intro he
  obtain ⟨d,hd⟩ := hD
  have ht : x^2 = -4+3*(d*y^2) := by rw [hd] at he; grind
  have hmod := congrArg (fun n : Int => n%3) ht
  apply square_mod_three x
  simpa using hmod

theorem no_negative_units (x y : Int) :
    x^2-321*y^2 ≠ -4 ∧ x^2-1509*y^2 ≠ -4 :=
  ⟨negative_norm_obstruction _ x y ⟨107,rfl⟩,
   negative_norm_obstruction _ x y ⟨503,rfl⟩⟩

/-- Primality expressed by the complete positive-divisor criterion. -/
theorem prime_factors (k : Nat) :
    ((k ∣ 107) → k = 1 ∨ k = 107) ∧ ((k ∣ 503) → k = 1 ∨ k = 503) := by
  have h107 : ∀ j : Fin 108, j.val ∣ 107 → j.val = 1 ∨ j.val = 107 := by decide +kernel
  have h503 : ∀ j : Fin 504, j.val ∣ 503 → j.val = 1 ∨ j.val = 503 := by decide +kernel
  constructor
  · intro hk
    have hb := Nat.le_of_dvd (by decide : 0 < 107) hk
    exact h107 ⟨k, by omega⟩ hk
  · intro hk
    have hb := Nat.le_of_dvd (by decide : 0 < 503) hk
    exact h503 ⟨k, by omega⟩ hk

end Reimann.TameExample
