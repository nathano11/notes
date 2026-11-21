import Reimann.SignedStickelberger
import Reimann.SignedTowerMeasure
import Reimann.SignedGammaTower
import Reimann.SignedCompletedAction

/-! Exact compatibility of dyadic rows in inverse-generator coordinates. -/
namespace Reimann.SignedTowerRows

open Reimann.SignedProjection

/-- A parent coefficient is the sum of the two coefficients of its lifts. -/
def Compatible (w : Nat → Nat → Int) : Prop :=
  ∀ n j, j < 2^n → w n j = w (n+1) j + w (n+1) (j+2^n)

/-- Push a row of order 2^n to the coordinate i of the order-64 quotient. -/
def massAt (w : Nat → Nat → Int) (n : Nat) (i : Fin 64) : Int :=
  total (fun j => if j%64=i.val then w n j else 0) (2^n)

theorem mass_step (w : Nat → Nat → Int) (h : Compatible w) (n : Nat) (hn : 6 ≤ n) (i : Fin 64) :
    massAt w (n+1) i = massAt w n i := by
  have hd : 64 ∣ 2^n := Nat.pow_dvd_pow 2 hn
  have hmod (k : Nat) : (2^n+k)%64 = k%64 := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]; simp
  unfold massAt
  rw [show 2^(n+1) = 2^n + 2^n by rw [Nat.pow_succ]; omega, total_append]
  let f (j : Nat) : Int := if j%64=i.val then w (n+1) j else 0
  let g (j : Nat) : Int := if j%64=i.val then w (n+1) (j+2^n) else 0
  have child : (fun j : Nat => if (2^n+j)%64=i.val then w (n+1) (2^n+j) else 0) = g := by
    funext j
    dsimp only [g]
    rw [hmod, Nat.add_comm (2^n) j]
  rw [child]
  change total f (2^n) + total g (2^n) = _
  have comb := total_affine f g 1 1 (2^n)
  simp only [Int.one_mul] at comb
  rw [← comb]
  apply SignedStickelberger.total_congr_below
  intro j hj
  dsimp [f, g]
  by_cases b : j%64=i.val <;> simp [b, h n j hj]

theorem total_point (w : Nat → Int) (k n : Nat) :
    total (fun j => if j=k then w j else 0) n = if k<n then w k else 0 := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [total, ih]
    by_cases hn : n=k
    · subst n; simp
    · by_cases h : k<n <;> simp [h, hn, show (k<n+1) ↔ (k<n) by omega]

theorem mass_six (w : Nat → Nat → Int) (i : Fin 64) : massAt w 6 i = w 6 i.val := by
  unfold massAt
  change total _ 64 = _
  calc
    _ = total (fun j : Nat => if j=i.val then w 6 j else 0) 64 := by
      apply SignedStickelberger.total_congr_below
      intro j hj
      rw [Nat.mod_eq_of_lt hj]
    _ = _ := by rw [total_point, if_pos i.isLt]

theorem mass_at_all_levels (w : Nat → Nat → Int) (h : Compatible w) (j : Nat) (i : Fin 64) :
    massAt w (6+j) i = w 6 i.val := by
  induction j with
  | zero => exact mass_six w i
  | succ j ih => exact (mass_step w h (6+j) (by omega) i).trans ih

/-- The normalized first moment in the inverse-generator fibre j at layer n. -/
def weight (n j : Nat) : Int :=
  SignedTowerMeasure.coefficient (n+2) (SignedGammaTower.representative n j)

theorem weight_compatible : Compatible weight := by
  intro n j _
  have split := SignedGammaTower.sibling_fibres n j
  dsimp only at split
  have h := SignedTowerMeasure.coefficient_refine (n+2) (SignedGammaTower.representative n j)
  unfold weight
  rcases split with ⟨a,b⟩ | ⟨a,b⟩
  · rw [a,b]; exact h
  · rw [a,b,Int.add_comm]; exact h

theorem weight_six (i : Fin 64) : weight 6 i.val = SignedMeasure256.row[i.val]! := by
  unfold weight
  rw [SignedGammaTower.level256_representative i]
  exact SignedTowerMeasure.level256_coefficient i

/-- The certified row is the image of every higher arithmetic layer. -/
theorem push_to_checked_row (d : Nat) (i : Fin 64) :
    massAt weight (6+d) i = SignedMeasure256.row[i.val]! :=
  (mass_at_all_levels weight weight_compatible d i).trans (weight_six i)

/-- Embed any integer distribution coefficientwise into the completed dyadic group ring. -/
def asTower (w : Nat → Nat → Int) (h : Compatible w) : SignedCompletedAction.Tower where
  coeff n i := SignedCompletedAction.integer (w n i.val)
  compatible {n} i := by
    change SignedCompletedAction.integer (w n i.val) =
      DyadicLattice.add (SignedCompletedAction.integer (w (n+1) i.val))
        (SignedCompletedAction.integer (w (n+1) (i.val+2^n)))
    rw [h n i.val i.isLt, SignedCompletedAction.integer_add]

/-- The explicit, compatible half-normalized conductor-2893 Stickelberger element. -/
def normalized_tower : SignedCompletedAction.Tower := asTower weight weight_compatible

theorem tower_coordinate (i : Fin 64) : SignedCompletedAction.coordinate normalized_tower i =
    BitVec.ofInt 6 SignedMeasure256.row[i.val]! := by
  change BitVec.ofInt 6 (weight 6 i.val) = _
  rw [weight_six i]

end Reimann.SignedTowerRows
