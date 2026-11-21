import Reimann.SignedArithmeticProjection
import Reimann.DyadicMahler69
import Reimann.SignedCommonNormalization
import Reimann.SignedNormalizationPrecision

/-! Equality of normalized finite rows in the forward-generator coordinates
determines the full series constructed from their binomial moments. -/
namespace Reimann.SignedNormalizationComparison

open Reimann.DyadicLattice
open Reimann.SignedTowerRows (Compatible)

theorem taylor_residue_of_rows (u v : Nat → Nat → Int) (n k p : Nat)
    (h : ∀ j, j<2^n → BitVec.ofInt p (u n j)=BitVec.ofInt p (v n j)) :
    BitVec.ofInt p (SignedTaylor.taylorAt u n k) = BitVec.ofInt p (SignedTaylor.taylorAt v n k) := by
  have partialSum (a : Nat) (ha : a≤2^n) :
      BitVec.ofInt p (SignedProjection.total (fun j => u n j*(CoinvariantSupport.binomial j k:Int)) a) =
      BitVec.ofInt p (SignedProjection.total (fun j => v n j*(CoinvariantSupport.binomial j k:Int)) a) := by
    induction a with
    | zero => rfl
    | succ a ih =>
      simp only [SignedProjection.total, BitVec.ofInt_add, BitVec.ofInt_mul, ih (by omega), h a (by omega)]
  exact partialSum _ (Nat.le_refl _)

/-- At each requested precision it suffices to match normalized coefficient rows
at arbitrarily deep levels. Both systems use the same group exponents. -/
theorem series_eq_of_cofinal_rows (u v : Nat → Nat → Int) (hu : Compatible u) (hv : Compatible v)
    (matchRows : ∀ p depth : Nat, ∃ n, depth≤n ∧ ∀ j, j<2^n →
      BitVec.ofInt (p+1) (u n j)=BitVec.ofInt (p+1) (v n j)) :
    SignedTaylorScalar.coefficient u hu = SignedTaylorScalar.coefficient v hv := by
  funext k
  apply scalar_ext
  intro p
  obtain ⟨n,hn,rows⟩ := matchRows p (k+(p+1))
  rw [SignedTaylorScalar.coefficient_at_level u hu k p n k hn (SignedTaylor.degree_bound k),
      SignedTaylorScalar.coefficient_at_level v hv k p n k hn (SignedTaylor.degree_bound k)]
  exact taylor_residue_of_rows u v n k (p+1) rows

/-- For every requested precision and minimum depth, a compatible integral candidate
has the cleared numerator's residues on an entire inverse-exponent row.
At group order 2^n the dyadic conductor is 2^(n+2). -/
def NumeratorAgreement (m s : Nat) (w num : Nat → Nat → Int) : Prop :=
  ∀ p depth : Nat, ∃ n, depth≤n ∧ ∀ j, j<2^n →
    (2^((n+2)+s)*(m:Int)*w n j) % (2:Int)^((p+1)+(n+2)+s) =
    num n j % (2:Int)^((p+1)+(n+2)+s)

theorem bits_of_equal_remainders (p : Nat) (x y : Int)
    (h : x % (2:Int)^p = y % (2:Int)^p) : BitVec.ofInt p x = BitVec.ofInt p y := by
  apply BitVec.eq_of_toNat_eq
  simpa only [BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int] using congrArg Int.toNat h

/-- Numerator precision includes the exact dyadic denominator at the chosen
level. The odd conductor introduces no additional loss. -/
theorem series_eq_of_numerator_comparisons (m s : Nat) (hm : m%2=1)
    (w v num : Nat → Nat → Int) (hw : Compatible w) (hv : Compatible v)
    (exactNum : ∀ n j, num n j = 2^((n+2)+s)*(m:Int)*v n j)
    (agreement : NumeratorAgreement m s w num) :
    SignedTaylorScalar.coefficient w hw = SignedTaylorScalar.coefficient v hv := by
  apply series_eq_of_cofinal_rows w v hw hv
  intro p depth
  obtain ⟨n,hn,rows⟩ := agreement p depth
  refine ⟨n,hn,?_⟩
  intro j hj
  have eqn := rows j hj
  rw [exactNum] at eqn
  apply bits_of_equal_remainders
  exact (SignedNormalizationPrecision.scaled_residue_iff m (n+2) s (p+1) _ _ hm).mp eqn

theorem clearing_scale (d s m : Nat) (c : Int) :
    (2:Int)^s * ((2^d*m:Nat):Int)*c = (2:Int)^(d+s)*(m:Int)*c := by
  simp only [Int.natCast_mul, Int.natCast_pow, Int.pow_add]
  ac_rfl

/-- Integer raw first-power numerator in the fibre of the forward group exponent j. -/
def raw2893 (n j : Nat) : Int :=
  SignedBernoulliPairing.rawFibre SignedCommonNormalization.character2893
    (SignedGammaTower.representative n j) (2^(n+2)) 2893

/-- Cleared literal Bernoulli numerator in the same generator convention at conductor 69. -/
def literal69 (n j : Nat) : Int :=
  SignedBernoulliPairing.literalFibre DyadicZeroValues.chi276
    (SignedGammaTower.representative n j) (2^(n+2)) 69

theorem series_eq_2893_of_raw_rows (w : Nat → Nat → Int) (hw : Compatible w)
    (agreement : NumeratorAgreement 2893 1 w raw2893) :
    SignedTaylorScalar.coefficient w hw = SignedArithmeticProjection.analyticSeries := by
  apply series_eq_of_numerator_comparisons 2893 1 (by decide) w SignedTowerRows.weight raw2893
    hw SignedTowerRows.weight_compatible _ agreement
  intro n j
  exact (SignedCommonNormalization.gamma_normalization_2893 n j).1.trans
    (clearing_scale (n+2) 1 2893 _)

theorem series_eq_69_of_literal_rows (w : Nat → Nat → Int) (hw : Compatible w)
    (agreement : NumeratorAgreement 69 2 w literal69) :
    SignedTaylorScalar.coefficient w hw = DyadicMahler69.series := by
  apply series_eq_of_numerator_comparisons 69 2 (by decide) w DyadicGammaDistribution69.gammaRow literal69
    hw (fun n j _ => DyadicGammaDistribution69.gamma_row_refines n j) _ agreement
  intro n j
  exact (SignedCommonNormalization.gamma_normalization_69 n j).2.trans
    (clearing_scale (n+2) 2 69 _)

/-- A compatible integral realization of the field measure permits full-series comparison. -/
theorem characteristic_bits_of_raw_rows (w : Nat → Nat → Int) (hw : Compatible w)
    (agreement : NumeratorAgreement 2893 1 w raw2893) (c0 c1 : Scalar)
    (h0 : c0.residue 0=0) (h1 : c1.residue 0=0) (u : DyadicSeriesProjection.Series)
    (factor : SignedTaylorScalar.coefficient w hw =
      DyadicSeriesProjection.convolution (DyadicSeriesProjection.quadraticSeries c0 c1) u) :
    c0.residue 5=40 ∧ c1.residue 5=18 :=
  SignedArithmeticProjection.coefficients_of_analytic_factor h0 h1 u
    ((series_eq_2893_of_raw_rows w hw agreement).symm.trans factor)

/-- For coefficient z at one actual order-64 coordinate the two integer numerator
tests require respectively fifteen and sixteen bits. -/
theorem level256_numerators_iff (j : Fin 64) (z : Int) :
    let c := SignedTowerRows.weight 6 j.val
    let literal := SignedBernoulliPairing.literalFibre SignedCommonNormalization.character2893
      (SignedGammaTower.representative 6 j.val) 256 2893
    ((2*256*2893*z)%32768 = (raw2893 6 j.val)%32768 ↔ z%64=c%64) ∧
      ((4*256*2893*z)%65536 = literal%65536 ↔ z%64=c%64) := by
  dsimp only
  obtain ⟨hr,hl⟩ := SignedCommonNormalization.gamma_normalization_2893 6 j.val
  change raw2893 6 j.val = 2*256*2893*SignedTowerRows.weight 6 j.val at hr
  change SignedBernoulliPairing.literalFibre _ _ 256 2893 = 4*256*2893*SignedTowerRows.weight 6 j.val at hl
  rw [hr,hl]
  exact ⟨SignedNormalizationPrecision.scaled_residue_iff 2893 8 1 6 _ _ (by decide),
    SignedNormalizationPrecision.scaled_residue_iff 2893 8 2 6 _ _ (by decide)⟩

/-- Only the modulus-256 character row is needed to compare the six-bit projections. -/
theorem projected_row_of_raw256 (f : DyadicSeriesProjection.Series)
    (rows : ∀ j : Fin 64, (2*256*2893*((SignedSeriesMap.evaluate f j).toNat:Int))%32768 =
      (raw2893 6 j.val)%32768) (i : Fin 64) :
    SignedSeriesMap.evaluate f i = BitVec.ofInt 6 SignedMeasure256.row[i.val]! := by
  have hr := (level256_numerators_iff i ((SignedSeriesMap.evaluate f i).toNat:Int)).1.mp (rows i)
  have hb := bits_of_equal_remainders 6 _ _ hr
  rw [SignedTowerRows.weight_six i] at hb
  change BitVec.ofNat 6 (SignedSeriesMap.evaluate f i).toNat = _ at hb
  simpa using hb

/-- One projected arithmetic comparison and one field ideal inclusion suffice for
the characteristic residues. No equality of all levels is assumed. -/
theorem characteristic_bits_at_256 (f : DyadicSeriesProjection.Series)
    (rows : ∀ j : Fin 64, (2*256*2893*((SignedSeriesMap.evaluate f j).toNat:Int))%32768 =
      (raw2893 6 j.val)%32768) (c0 c1 : Scalar) (h0 : c0.residue 0=0) (h1 : c1.residue 0=0)
    (u : DyadicSeriesProjection.Series)
    (factor : f = DyadicSeriesProjection.convolution (DyadicSeriesProjection.quadraticSeries c0 c1) u) :
    c0.residue 5=40 ∧ c1.residue 5=18 := by
  apply SignedArithmeticProjection.coefficient_bits h0 h1
  apply SignedArithmeticProjection.finite_factor_of_coordinates c0 c1 (SignedSeriesMap.evaluate u)
  intro i
  rw [← projected_row_of_raw256 f rows i, factor, SignedSeriesMap.evaluate_quadratic_product]

end Reimann.SignedNormalizationComparison
