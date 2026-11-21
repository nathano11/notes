import Reimann.SignedTaylorScalar
import Reimann.SignedTowerRows
import Reimann.SignedPascalAction

/-! Recover the finite cyclic coefficients of a compatible integer measure
from its canonical Taylor series by interchanging two finite sums. -/
namespace Reimann.SignedCanonicalProjection

/-- A finite sum of coefficients in Z/64, accumulated in ascending order. -/
def bitSum (f : Nat → BitVec 6) : Nat → BitVec 6
  | 0 => 0
  | n+1 => bitSum f n + f n

theorem bits_total (f : Nat → Int) (m : Nat) :
    BitVec.ofInt 6 (SignedProjection.total f m) = bitSum (fun j => BitVec.ofInt 6 (f j)) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [SignedProjection.total, BitVec.ofInt_add, ih, bitSum]

theorem bitSum_add (f g : Nat → BitVec 6) (m : Nat) :
    bitSum (fun k => f k + g k) m = bitSum f m + bitSum g m := by
  induction m with
  | zero => simp [bitSum]
  | succ m ih => simp only [bitSum, ih]; ac_rfl

theorem bitSum_scale (a : BitVec 6) (f : Nat → BitVec 6) (m : Nat) :
    bitSum (fun k => a*f k) m = a*bitSum f m := by
  induction m with
  | zero => simp [bitSum]
  | succ m ih => simp [bitSum, ih, BitVec.mul_add]

theorem bitSum_zero (m : Nat) : bitSum (fun _ => 0) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bitSum, ih]; rfl

/-- Exchange two finite sums in the coefficient ring. -/
theorem bitSum_interchange (f : Nat → Nat → BitVec 6) (l m : Nat) :
    bitSum (fun k => bitSum (fun j => f k j) m) l =
      bitSum (fun j => bitSum (fun k => f k j) l) m := by
  induction l with
  | zero => simpa only [bitSum] using (bitSum_zero m).symm
  | succ l ih => simp only [bitSum, ih, bitSum_add]

theorem bitSum_congr (f g : Nat → BitVec 6) (m : Nat) (h : ∀ k<m, f k = g k) :
    bitSum f m = bitSum g m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bitSum, bitSum, ih (fun k hk => h k (by omega)), h m (by omega)]

theorem bitSum_scale_right (a : BitVec 6) (f : Nat → BitVec 6) (m : Nat) :
    bitSum (fun k => f k*a) m = bitSum f m*a := by
  induction m with
  | zero => simp [bitSum]
  | succ m ih => rw [bitSum, ih, bitSum, BitVec.add_mul]

/-- Taylor moments on one finite level evaluated against test powers give
the sum of the evaluations of the individual binomial rows. -/
theorem moment_interchange (w : Nat → Int) (b : Nat → Nat → Nat) (p : Nat → BitVec 6)
    (m l : Nat) :
    bitSum (fun k => BitVec.ofInt 6 (SignedProjection.total (fun j => w j*(b j k : Int)) m)*p k) l =
      bitSum (fun j => BitVec.ofInt 6 (w j)*bitSum (fun k => BitVec.ofNat 6 (b j k)*p k) l) m := by
  calc
    _ = bitSum (fun k => bitSum (fun j =>
        BitVec.ofInt 6 (w j)*BitVec.ofNat 6 (b j k)*p k) m) l := by
      apply bitSum_congr
      intro k _
      rw [bits_total, ← bitSum_scale_right]
      apply bitSum_congr
      intro j _
      rw [BitVec.ofInt_mul]
      rfl
    _ = _ := (bitSum_interchange _ l m).trans (by
      apply bitSum_congr
      intro j _
      rw [← bitSum_scale]
      apply bitSum_congr
      intro k _
      exact BitVec.mul_assoc ..)

/-- A delta in the cyclic coordinate retains exactly one residue class. -/
theorem indicator_total (w : Nat → Int) (m : Nat) (i : Fin 64) :
    bitSum (fun j => BitVec.ofInt 6 (w j) * (if j%64=i.val then 1 else 0)) m =
      BitVec.ofInt 6 (SignedProjection.total (fun j => if j%64=i.val then w j else 0) m) := by
  rw [bits_total]
  apply bitSum_congr
  intro j _
  by_cases h : j%64=i.val <;> simp [h]

/-- The six-bit Taylor coefficients evaluated against a Pascal action with
cyclic character j ↦ X^j recover the mass of the corresponding order-64 fibre. -/
theorem canonical_moment_projection (w : Nat → Nat → Int) (hc : SignedTowerRows.Compatible w)
    (i : Fin 64) (p : Nat → BitVec 6)
    (pascal : ∀ j : Nat, bitSum (fun k => BitVec.ofNat 6 (CoinvariantSupport.binomial j k)*p k) 224 =
      if j%64=i.val then 1 else 0) :
    bitSum (fun k => ((SignedTaylorScalar.coefficient w hc k).residue 5) * p k) 224 =
      BitVec.ofInt 6 (w 6 i.val) := by
  calc
    _ = bitSum (fun k => BitVec.ofInt 6 (SignedTaylor.taylorAt w 13 k) * p k) 224 := by
      apply bitSum_congr
      intro k hk
      rw [SignedTaylorScalar.jet_at_thirteen w hc k hk]
    _ = bitSum (fun j => BitVec.ofInt 6 (w 13 j)*
        bitSum (fun k => BitVec.ofNat 6 (CoinvariantSupport.binomial j k)*p k) 224) (2^13) :=
      moment_interchange (w 13) CoinvariantSupport.binomial p (2^13) 224
    _ = bitSum (fun j => BitVec.ofInt 6 (w 13 j)*(if j%64=i.val then 1 else 0)) (2^13) :=
      bitSum_congr _ _ _ (fun j _ => congrArg (BitVec.ofInt 6 (w 13 j) * ·) (pascal j))
    _ = BitVec.ofInt 6 (SignedTowerRows.massAt w 13 i) := indicator_total _ _ i
    _ = _ := congrArg (BitVec.ofInt 6) (SignedTowerRows.mass_at_all_levels w hc 7 i)

theorem partial_action_sum (f : SignedSeriesMap.Coeffs) (p : Nat → SignedSeriesMap.Row)
    (m : Nat) (i : Fin 64) :
    SignedSeriesMap.partialAction f p m i = bitSum (fun j => f j * p j i) m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (fun x => x + f m * p m i) ih

/-- Projection of the fully constructed 2-adic coefficient sequence is the
original measure at cyclic order 64, for any compatible integer distribution. -/
theorem evaluate_canonical (w : Nat → Nat → Int) (hc : SignedTowerRows.Compatible w) :
    SignedSeriesMap.evaluate (SignedTaylorScalar.coefficient w hc) =
      fun i : Fin 64 => BitVec.ofInt 6 (w 6 i.val) := by
  funext i
  rw [SignedSeriesMap.evaluate_low, partial_action_sum]
  apply canonical_moment_projection w hc i
  intro j
  have h := SignedPascalAction.binomial_action j i
  rwa [partial_action_sum] at h

/-- The canonical analytic series of the conductor-2893 signed distribution
specializes to the independently checked 64-entry character row. -/
theorem arithmetic_projection (i : Fin 64) :
    SignedSeriesMap.evaluate
        (SignedTaylorScalar.coefficient SignedTowerRows.weight SignedTowerRows.weight_compatible) i =
      BitVec.ofInt 6 (SignedMeasure256.row[i.val]?.getD 0) := by
  rw [evaluate_canonical]
  change BitVec.ofInt 6 (SignedTowerRows.weight 6 i.val) = _
  rw [SignedTowerRows.weight_six]
  have hi : i.val < SignedMeasure256.row.length := by rw [SignedMeasure256.row_length]; exact i.isLt
  simp [hi]

end Reimann.SignedCanonicalProjection
