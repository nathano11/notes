import Reimann.SignedTaylorScalar
import Reimann.SignedTowerRows
import Reimann.SignedRowDescent

/-! The initial odd coefficient of the canonical series constructed from
the full conductor-2893 normalized distribution, in T = X - 1. -/
namespace Reimann.SignedAnalyticDegree

open Reimann.SignedTowerRows (weight weight_compatible)
open Reimann.SignedRowDescent (orderFour translated)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
/-- Compute all four normalized masses at modulus 16 from the integral
moment definition. They coincide with the independent pushdown of the
certified level-256 row. -/
theorem order_four_weights : ∀ j : Fin 4, weight 2 j.val = orderFour[j.val]! := by
  decide +kernel

/-- All four coefficients of the finite row H(1+T) by the integral binomial transform. -/
theorem taylor_at_two (k : Fin 4) : SignedTaylor.taylorAt weight 2 k.val = translated[k.val]! := by
  change SignedProjection.total (fun j : Nat => weight 2 j*(CoinvariantSupport.binomial j k.val : Int)) 4 = _
  calc
    _ = SignedProjection.total (fun j : Nat => orderFour[j]!*(CoinvariantSupport.binomial j k.val : Int)) 4 := by
      apply SignedStickelberger.total_congr_below
      intro j hj
      have h := order_four_weights ⟨j,hj⟩
      change weight 2 j = orderFour[j]! at h
      rw [h]
    _ = _ := by revert k; decide

/-- The four low coefficient bits of the all-level measure's coherent series. -/
theorem canonical_low_word (k : Fin 4) :
    (SignedTaylorScalar.coefficient weight weight_compatible k.val).residue 0 =
      BitVec.ofInt 1 translated[k.val]! := by
  rw [SignedTaylorScalar.coefficient_at_level weight weight_compatible 1 0 2 k.val
      (by decide) k.isLt, taylor_at_two]

theorem canonical_initial_parity :
    let a := fun k : Nat => (((SignedTaylorScalar.coefficient weight weight_compatible k).residue 0).toNat : Int)
    (∀ i < 2, a i % 2 = 0) ∧ a 2 % 2 = 1 := by
  apply SignedRowDescent.first_odd_coefficient
  intro j
  rw [canonical_low_word j]
  revert j
  decide

/-- Coefficient formulation of μ=0 and λ=2 for the normalized conductor-2893
series: the constant and linear coefficients are even, and the quadratic
coefficient is odd. The arithmetic tower and all three words are constructed. -/
theorem mu_zero_lambda_two :
    let f := SignedTaylorScalar.coefficient weight weight_compatible
    (∀ i, i < 2 → (f i).residue 0 = 0) ∧ (f 2).residue 0 = 1 := by
  obtain ⟨lo,hi⟩ := canonical_initial_parity
  have zeroBit : ∀ b : BitVec 1, (b.toNat:Int)%2=0 → b=0 := by decide
  have oneBit : ∀ b : BitVec 1, (b.toNat:Int)%2=1 → b=1 := by decide
  exact ⟨fun i h => zeroBit _ (lo i h), oneBit _ hi⟩

end Reimann.SignedAnalyticDegree
