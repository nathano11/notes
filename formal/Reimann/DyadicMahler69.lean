import Reimann.SignedTaylorScalar
import Reimann.DyadicGammaDistribution69

/-! The integral power series obtained from the inverse-exponent conductor-69
rows via X = 1+T. Its k-th coefficient is the coherent limit of the finite
binomial moments Σ_j w_a(j) choose(j,k). -/

namespace Reimann.DyadicMahler69

open Reimann.DyadicGammaDistribution69 Reimann.DyadicSeriesProjection
open Reimann.DyadicStickelberger69 Reimann.DyadicHalfPrecision Reimann.DyadicLattice

/-- The honest coefficientwise inverse limit of the signed progression rows. -/
def series : Series :=
  Reimann.SignedTaylorScalar.coefficient gammaRow (fun n j _ => gamma_row_refines n j)

/-- Every coefficient is determined modulo 2^(i+1) at any level n meeting
the displayed bound. This holds simultaneously for all k < 2^(s+1). -/
theorem series_at_level (s i n k : Nat) (hn : s+(i+1) ≤ n) (hk : k < 2^(s+1)) :
    (series k).residue i = BitVec.ofInt (i+1) (Reimann.SignedTaylor.taylorAt gammaRow n k) :=
  Reimann.SignedTaylorScalar.coefficient_at_level _ _ s i n k hn hk

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The inverse-exponent row modulo 64 as sixteen ordinary integers. -/
theorem level_four_row : (List.range 16).map (gammaRow 4) =
    [2,-3,3,4,2,-1,-1,-1,-4,0,0,-3,0,3,2,1] := by decide

/-- Ordinary integer Taylor moments for degrees zero through three. -/
theorem level_four_taylor :
    let M := Reimann.SignedTaylor.taylorAt gammaRow 4
    (M 0, M 1, M 2, M 3) = (4,22,225,1269) := by decide

theorem first_four_residues :
    ((series 0).residue 2, (series 1).residue 2, (series 2).residue 2, (series 3).residue 2) =
      (4,6,1,5) := by
  obtain ⟨h0,h⟩ := Prod.mk.inj level_four_taylor
  obtain ⟨h1,h⟩ := Prod.mk.inj h
  obtain ⟨h2,h3⟩ := Prod.mk.inj h
  rw [series_at_level 1 2 4 0 (by decide) (by decide),
      series_at_level 1 2 4 1 (by decide) (by decide),
      series_at_level 1 2 4 2 (by decide) (by decide),
      series_at_level 1 2 4 3 (by decide) (by decide),h0,h1,h2,h3]
  decide

theorem canonical_half_row : evaluate series = halfRow := by
  obtain ⟨h0,h⟩ := Prod.mk.inj first_four_residues
  obtain ⟨h1,h⟩ := Prod.mk.inj h
  obtain ⟨h2,h3⟩ := Prod.mk.inj h
  unfold evaluate
  rw [h0,h1,h2,h3,half_row_exact]
  decide

/-- The doubled canonical series gives the literal Bernoulli row at conductor
552 modulo 16 for every truncation retaining at least four terms. -/
theorem canonical_unhalved_row (j : Nat) :
    partialDouble series (j+4) = literalRow16 :=
  (half_row_iff_unhalved series j).mp canonical_half_row

/-- The finite-row test has been discharged for the actual progression series.
The remaining algebraic input here is the equality of the full principal ideals. -/
theorem lattice_order_of_canonical_series (c0 c1 : Scalar)
    (hideal : ∃ u v : Series, quadraticSeries c0 c1 = convolution u series ∧
      series = convolution v (quadraticSeries c0 c1)) (r a : Nat) :
    ∃ encode : Quot (Reimann.DyadicOrder.latticeCoset c0 c1 r a) → Fin (2^(2*a+1)),
    ∃ decode : Fin (2^(2*a+1)) → Quot (Reimann.DyadicOrder.latticeCoset c0 c1 r a),
      (∀ x, decode (encode x) = x) ∧ (∀ i, encode (decode i) = i) :=
  lattice_order_of_unhalved c0 c1 series hideal (canonical_unhalved_row 0) r a

end Reimann.DyadicMahler69
