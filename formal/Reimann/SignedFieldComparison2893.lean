import Reimann.SignedStickelbergerCandidate

/-! Characteristic coefficients of the forward operator and the literal
Stickelberger candidate for the conductor-2893 tower. -/
namespace Reimann.SignedFieldComparison2893

open Reimann.DyadicLattice
open Reimann.DyadicSeriesProjection (Series convolution quadraticSeries)
open Reimann.SignedStickelbergerCandidate (series2893)

theorem candidate_cofactor :
    let f := SignedArithmeticProjection.analyticSeries
    series2893 = convolution
      (quadraticSeries (SignedAnalyticPreparation.constant f) (SignedAnalyticPreparation.linear f))
      (SignedAnalyticPreparation.cofactor f) := by
  rw [SignedStickelbergerCandidate.series2893_eq]
  exact SignedArithmeticProjection.analytic_preparation.2.2.2

theorem transport_divisibility (theta phi q u v : Series)
    (comparison : theta=convolution phi v) (ideal : phi=convolution q u) :
    theta=convolution q (convolution u v) := by
  rw [comparison,ideal,SignedSeriesUnit.convolution_assoc]

/-- One inclusion in each comparison suffices. The literal candidate supplies
all 64 fifteen-bit raw numerator congruences independently of the field polynomial. -/
theorem characteristic_bits (phi : Series) (c0 c1 : Scalar) (h0 : c0.residue 0=0)
    (h1 : c1.residue 0=0) (u v : Series)
    (comparison : series2893=convolution phi v)
    (ideal : phi=convolution (quadraticSeries c0 c1) u) :
    c0.residue 5=40 ∧ c1.residue 5=18 :=
  SignedNormalizationComparison.characteristic_bits_at_256 series2893
    SignedStickelbergerCandidate.raw_congruences_256 c0 c1 h0 h1 _
    (transport_divisibility _ _ _ _ _ comparison ideal)

/-- In a cyclic basis (b,Tb), if T²b has coordinates (s,t), the
characteristic polynomial of T is X²−tX−s. -/
theorem cyclic_word {n : Nat} (s t x : BitVec n) :
    x*(x-t) - ((0:BitVec n)-s)*((0:BitVec n)-1) = x*x-t*x-s := by grind

/-- Evaluate a monic quadratic on b, with T b the second basis vector. -/
theorem annihilator_on_generator {n : Nat} (s t c0 c1 : BitVec n) :
    (s+c0,t+c1)=(0,0) ↔ c0= -s ∧ c1= -t := by
  constructor
  · intro h
    obtain ⟨ha,hb⟩ := Prod.mk.inj h
    grind
  · rintro ⟨rfl,rfl⟩
    grind

theorem quadratic_of_cyclic_annihilation (s t : Scalar)
    (ann : ∀ n, let f := SignedArithmeticProjection.analyticSeries
      (s.residue n + (SignedAnalyticPreparation.constant f).residue n,
       t.residue n + (SignedAnalyticPreparation.linear f).residue n)=(0,0)) :
    SignedAnalyticPreparation.constant SignedArithmeticProjection.analyticSeries = neg s ∧
    SignedAnalyticPreparation.linear SignedArithmeticProjection.analyticSeries = neg t := by
  exact ⟨scalar_ext (fun n => ((annihilator_on_generator _ _ _ _).mp (ann n)).1),
    scalar_ext (fun n => ((annihilator_on_generator _ _ _ _).mp (ann n)).2)⟩

/-- If Q(T)b=0 in a free cyclic rank-two lattice in the basis (b,Tb),
the literal candidate is a multiple of det(XI−T) with the constructed cofactor. -/
theorem ideal_of_cyclic_annihilation (s t : Scalar)
    (ann : ∀ n, let f := SignedArithmeticProjection.analyticSeries
      (s.residue n + (SignedAnalyticPreparation.constant f).residue n,
       t.residue n + (SignedAnalyticPreparation.linear f).residue n)=(0,0)) :
    series2893 = convolution (quadraticSeries (neg s) (neg t))
      (SignedAnalyticPreparation.cofactor SignedArithmeticProjection.analyticSeries) := by
  obtain ⟨h0,h1⟩ := quadratic_of_cyclic_annihilation s t ann
  simpa only [h0,h1] using candidate_cofactor

end Reimann.SignedFieldComparison2893
