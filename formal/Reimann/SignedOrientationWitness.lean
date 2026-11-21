import Reimann.DyadicMahler69
import Reimann.SignedTowerRows

/-! Integral coefficients at the first quotient that distinguishes the two
choices of generator for the distributions of conductors 69 and 2893. -/
namespace Reimann.SignedOrientationWitness

open SignedGammaTower DyadicGammaDistribution69 SignedTowerRows

/-- Inverting the exponent leaves every coordinate at layers zero and one fixed. -/
theorem low_layers (n : Nat) (hn : n < 2) (j : Fin (2^n)) :
    exponent n j.val = j.val := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> revert j <;> decide

/-- At layer two the positive argument at exponent one is 13 for the inverse
generator and 5 for the forward generator. -/
theorem order_four_arguments :
    exponent 2 1 = 3 ∧ (representative 2 1, representative 2 3) = (13,5) := by decide

/-- Push an integral row down through d successive cyclic quotients. -/
def push (n : Nat) : Nat → (Nat → Int) → Nat → Int
  | 0, row, j => row j
  | d+1, row, j => push (n+1) d row j + push (n+1) d row (j+2^n)

theorem push_eq (w : Nat → Nat → Int) (hw : Compatible w) (n d : Nat)
    (row : Nat → Int) (top : ∀ k < 2^(n+d), w (n+d) k = row k)
    (j : Nat) (hj : j < 2^n) : w n j = push n d row j := by
  induction d generalizing n j with
  | zero => exact top j hj
  | succ d ih =>
    have top' : ∀ k < 2^((n+1)+d), w ((n+1)+d) k = row k := by
      simpa only [show (n+1)+d = n+(d+1) by omega] using top
    have upper : 2^(n+1) = 2^n*2 := Nat.pow_succ ..
    rw [hw n j hj, push]
    rw [ih (n+1) top' j (by omega), ih (n+1) top' (j+2^n) (by omega)]

theorem conductor69_order_four (j : Fin 4) :
    gammaRow 2 j.val = ([0,-1,4,1] : List Int)[j.val]! := by
  calc
    _ = push 2 2 (fun k => ((List.range 16).map (gammaRow 4))[k]!) j.val := by
      apply push_eq gammaRow (fun n k _ => gamma_row_refines n k) 2 2 _ _ j.val j.isLt
      intro k hk
      have h : k < 16 := hk
      simp [h]
    _ = _ := by rw [DyadicMahler69.level_four_row]; revert j; decide

theorem conductor2893_order_four (j : Fin 4) :
    weight 2 j.val = ([25,2,-1,-18] : List Int)[j.val]! := by
  calc
    _ = push 2 4 (fun k => SignedMeasure256.row[k]!) j.val := by
      exact push_eq weight weight_compatible 2 4 _ (fun k hk => weight_six ⟨k,hk⟩) _ j.isLt
    _ = _ := by revert j; decide

/-- Compare h=1 with its inverted coordinate over the integers. -/
theorem first_orientation_witness :
    (gammaRow 2 1, gammaRow 2 (exponent 2 1)) = (-1,1) ∧
    (weight 2 1, weight 2 (exponent 2 1)) = (2,-18) := by
  rw [order_four_arguments.1]
  exact ⟨Prod.ext (conductor69_order_four 1) (conductor69_order_four 3),
    Prod.ext (conductor2893_order_four 1) (conductor2893_order_four 3)⟩

/-- In the order-four group ring the first distinguishing coefficient
precisions are modulo four for conductor 69 and modulo eight for 2893. -/
theorem first_distinguishing_bits :
    let a := gammaRow 2 1
    let b := gammaRow 2 (exponent 2 1)
    let c := weight 2 1
    let d := weight 2 (exponent 2 1)
    a%2 = b%2 ∧ a%4 ≠ b%4 ∧ c%4 = d%4 ∧ c%8 ≠ d%8 := by
  obtain ⟨h69,h2893⟩ := first_orientation_witness
  obtain ⟨a,b⟩ := Prod.mk.inj h69
  obtain ⟨c,d⟩ := Prod.mk.inj h2893
  dsimp only
  rw [a,b,c,d]
  decide

end Reimann.SignedOrientationWitness
