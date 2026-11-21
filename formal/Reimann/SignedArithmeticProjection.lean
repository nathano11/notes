import Reimann.SignedCoefficients
import Reimann.SignedCyclicFactor
import Reimann.SignedTowerRows
import Reimann.SignedCanonicalProjection
import Reimann.SignedAnalyticDegree
import Reimann.SignedAnalyticPreparation
import Reimann.SignedSeriesUnit
import Reimann.SignedResidueRoots
import Reimann.SignedAdicProduct

/-! Specialize a factorization at the infinite level to the certified
conductor-2893 row. Residues are taken only after forming the factorization. -/
namespace Reimann.SignedArithmeticProjection

open Reimann.DyadicLattice

/-- Least representative of the six coefficient bits used by the cyclic certificate. -/
def representative (c : Scalar) : Int := (c.residue 5).toNat

theorem representative_bits (c : Scalar) : BitVec.ofInt 6 (representative c) = c.residue 5 := by
  change BitVec.ofNat 6 (c.residue 5).toNat = c.residue 5
  simp

theorem representative_even (c : Scalar) (h : c.residue 0 = 0) : representative c % 2 = 0 := by
  have low := (c.reduce (i:=0) (j:=5) (by decide)).trans h
  exact (by decide : ∀ x : BitVec 6, x.setWidth 1=0 → (x.toNat:Int)%2=0) _ low

theorem finite_factor_of_coordinates (c0 c1 : Scalar) (u : Fin 64 → BitVec 6)
    (h : ∀ i : Fin 64, BitVec.ofInt 6 SignedMeasure256.row[i.val]! =
      (1+c0.residue 5-c1.residue 5)*u i + (c1.residue 5-2)*u (i-1) + u (i-2)) :
    SignedPreparation.CyclicFactor (representative c0) (representative c1) SignedMeasure256.row := by
  apply SignedCyclicFactor.coordinates_to_factor _ _ _ (by decide) u
  intro i
  have idx : SignedMeasure256.row[i.val]?.getD 0 = SignedMeasure256.row[i.val]! :=
    (by decide : ∀ j : Fin 64, SignedMeasure256.row[j.val]?.getD 0 = SignedMeasure256.row[j.val]!) i
  have castSub (x y : Int) : BitVec.ofInt 6 (x-y) = BitVec.ofInt 6 x - BitVec.ofInt 6 y := by
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
    grind
  simpa only [idx, castSub, BitVec.ofInt_add, representative_bits,
    show BitVec.ofInt 6 1 = 1 by decide, show BitVec.ofInt 6 2 = 2 by decide] using h i

/-- A cofactor in the entire completed group ring specializes to a cofactor for the certified row. -/
theorem finite_factor_of_tower_factor (c0 c1 : Scalar) (u : SignedCompletedAction.Tower)
    (h : SignedTowerRows.normalized_tower = SignedCompletedAction.quadraticAction c0 c1 u) :
    SignedPreparation.CyclicFactor (representative c0) (representative c1) SignedMeasure256.row := by
  apply finite_factor_of_coordinates c0 c1 (SignedCompletedAction.coordinate u)
  intro i
  rw [← SignedTowerRows.tower_coordinate i, h, SignedCompletedAction.project_quadratic]

theorem coefficient_bits {c0 c1 : Scalar} (h0 : c0.residue 0=0) (h1 : c1.residue 0=0)
    (h : SignedPreparation.CyclicFactor (representative c0) (representative c1) SignedMeasure256.row) :
    c0.residue 5=40 ∧ c1.residue 5=18 := by
  obtain ⟨ha,hb⟩ := SignedCoefficients.coefficients_of_cyclic_factor
    (representative_even c0 h0) (representative_even c1 h1) h
  exact ⟨(by decide : ∀ x : BitVec 6, (x.toNat:Int)%64=40 → x=40) _ ha,
         (by decide : ∀ x : BitVec 6, (x.toNat:Int)%64=18 → x=18) _ hb⟩

theorem coefficients_of_tower_factor {c0 c1 : Scalar} (h0 : c0.residue 0=0) (h1 : c1.residue 0=0)
    (u : SignedCompletedAction.Tower)
    (factor : SignedTowerRows.normalized_tower = SignedCompletedAction.quadraticAction c0 c1 u) :
    c0.residue 5=40 ∧ c1.residue 5=18 :=
  coefficient_bits h0 h1 (finite_factor_of_tower_factor c0 c1 u factor)

abbrev analyticSeries : DyadicSeriesProjection.Series :=
  SignedTaylorScalar.coefficient SignedTowerRows.weight SignedTowerRows.weight_compatible

theorem finite_factor_of_analytic_factor (c0 c1 : Scalar) (u : DyadicSeriesProjection.Series)
    (factor : analyticSeries = DyadicSeriesProjection.convolution (DyadicSeriesProjection.quadraticSeries c0 c1) u) :
    SignedPreparation.CyclicFactor (representative c0) (representative c1) SignedMeasure256.row := by
  apply finite_factor_of_coordinates c0 c1 (SignedSeriesMap.evaluate u)
  intro i
  have he : SignedSeriesMap.evaluate analyticSeries i = BitVec.ofInt 6 SignedMeasure256.row[i.val]! := by
    unfold analyticSeries
    rw [SignedCanonicalProjection.evaluate_canonical]
    exact congrArg (BitVec.ofInt 6) (SignedTowerRows.weight_six i)
  rw [← he, factor, SignedSeriesMap.evaluate_quadratic_product]

theorem coefficients_of_analytic_factor {c0 c1 : Scalar} (h0 : c0.residue 0=0) (h1 : c1.residue 0=0)
    (u : DyadicSeriesProjection.Series)
    (factor : analyticSeries = DyadicSeriesProjection.convolution (DyadicSeriesProjection.quadraticSeries c0 c1) u) :
    c0.residue 5=40 ∧ c1.residue 5=18 :=
  coefficient_bits h0 h1 (finite_factor_of_analytic_factor c0 c1 u factor)

theorem analytic_preparation :
    (SignedAnalyticPreparation.constant analyticSeries).residue 0=0 ∧
    (SignedAnalyticPreparation.linear analyticSeries).residue 0=0 ∧
    (SignedAnalyticPreparation.cofactor analyticSeries 0).residue 0=1 ∧
    analyticSeries = DyadicSeriesProjection.convolution
      (DyadicSeriesProjection.quadraticSeries (SignedAnalyticPreparation.constant analyticSeries)
        (SignedAnalyticPreparation.linear analyticSeries)) (SignedAnalyticPreparation.cofactor analyticSeries) := by
  obtain ⟨low, high⟩ := SignedAnalyticDegree.canonical_initial_parity
  exact SignedAnalyticPreparation.prepared analyticSeries (low 0 (by decide)) (low 1 (by decide)) high

/-- Six bits of both coefficients of the explicitly constructed distinguished quadratic. -/
theorem analytic_coefficient_bits :
    (SignedAnalyticPreparation.constant analyticSeries).residue 5=40 ∧
    (SignedAnalyticPreparation.linear analyticSeries).residue 5=18 := by
  obtain ⟨h0,h1,_,factor⟩ := analytic_preparation
  exact coefficients_of_analytic_factor h0 h1 _ factor

/-- The analytic series and its constructed quadratic generate the same full-series ideal. -/
theorem analytic_mutual_divisibility :
    let q := DyadicSeriesProjection.quadraticSeries (SignedAnalyticPreparation.constant analyticSeries)
      (SignedAnalyticPreparation.linear analyticSeries)
    let u := SignedAnalyticPreparation.cofactor analyticSeries
    analyticSeries = DyadicSeriesProjection.convolution q u ∧
      ∃ v, DyadicSeriesProjection.convolution u v = SignedSeriesUnit.one ∧
        DyadicSeriesProjection.convolution v u = SignedSeriesUnit.one ∧
        q = DyadicSeriesProjection.convolution v analyticSeries := by
  dsimp only
  obtain ⟨_,_,hu,fac⟩ := analytic_preparation
  obtain ⟨v,hv,hv'⟩ := SignedSeriesUnit.two_sided_inverse _ hu
  refine ⟨fac,v,hv,hv',?_⟩
  have undo (f q u v : DyadicSeriesProjection.Series) (h : f = DyadicSeriesProjection.convolution q u)
      (inv : DyadicSeriesProjection.convolution v u = SignedSeriesUnit.one) :
      q = DyadicSeriesProjection.convolution v f := by
    rw [h, SignedSeriesUnit.convolution_comm q u, ← SignedSeriesUnit.convolution_assoc, inv,
      SignedSeriesUnit.one_product]
  exact undo _ _ _ _ fac hv'

/-- A single pair of coherent roots factors the constructed analytic quadratic at every argument. -/
theorem analytic_linear_factors :
    let c0 := SignedAnalyticPreparation.constant analyticSeries
    let c1 := SignedAnalyticPreparation.linear analyticSeries
    ∃ r s : Scalar, r.residue 2 = 4 ∧ s.residue 2 = 2 ∧ ∀ x,
      SignedResidueRoots.quadraticValue c0 c1 x = mul (add x (neg r)) (add x (neg s)) := by
  obtain ⟨h0,h1⟩ := analytic_coefficient_bits
  exact SignedResidueRoots.ordinary_factorization _ _ h0 h1

theorem analytic_labelled_roots :
    let c0 := SignedAnalyticPreparation.constant analyticSeries
    let c1 := SignedAnalyticPreparation.linear analyticSeries
    ∃ r s : Scalar, r.residue 2 = 4 ∧ s.residue 2 = 2 ∧ r ≠ s ∧
      SignedResidueRoots.quadraticValue c0 c1 r = natScalar 0 ∧
      SignedResidueRoots.quadraticValue c0 c1 s = natScalar 0 := by
  obtain ⟨h0,h1⟩ := analytic_coefficient_bits
  exact SignedResidueRoots.labelled_zeros _ _ h0 h1

set_option maxRecDepth 8192 in
/-- Every proper positive trial divisor greater than one is excluded for both primes. -/
theorem mizusawa_prime_pair :
    (∀ d : Fin 11, 2 ≤ d.val → 11 % d.val ≠ 0) ∧
    (∀ d : Fin 263, 2 ≤ d.val → 263 % d.val ≠ 0) ∧
    11 % 8 = 3 ∧ 263 % 16 = 7 ∧ 11*263 = 2893 := by decide

/-- A square witness puts this pair in the residue branch of the example on p. 134. -/
theorem mizusawa_residue_branch :
    11*263 < 5000 ∧ 96^2 % 263 = 11 ∧ (40:Nat) % 4 = 0 ∧ (18:Nat) % 4 = 2 := by decide

/-- Exact finite valuations attained by the product of the two cleared signed samples
of the constructed quadratic, over all positive odd weights. -/
theorem analytic_product_valuation_spectrum (n : Nat) :
    let c0 := SignedAnalyticPreparation.constant analyticSeries
    let c1 := SignedAnalyticPreparation.linear analyticSeries
    (∃ r, r%2 = 1 ∧ SignedAdicProduct.valuationAt (SignedAdicProduct.product c0 c1 r) n) ↔
      n = 8 ∨ 11 ≤ n := by
  obtain ⟨h0,h1⟩ := analytic_coefficient_bits
  exact SignedAdicProduct.product_valuation_spectrum _ _ h0 h1 n

end Reimann.SignedArithmeticProjection
