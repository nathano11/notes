import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Reimann2893.SignedNativeScalar2893
import Reimann.SignedStickelbergerCandidate
import Reimann.DyadicOneSided69

/-! The inverse-power character series in the standard Iwasawa power series ring,
with transport of genuine multiplication and principal-ideal divisibility. -/
namespace Reimann.SignedNativeSeries2893

open SignedNativeScalar2893
open DyadicSeriesProjection (Series)
open DyadicLattice

noncomputable def readSeries (f : PowerSeries ℤ_[2]) : Series :=
  fun n => read (PowerSeries.coeff n f)

noncomputable def realizeSeries (f : Series) : PowerSeries ℤ_[2] :=
  PowerSeries.mk (fun n => realize (f n))

theorem read_realize_series (f : Series) : readSeries (realizeSeries f) = f := by
  funext n
  simp [readSeries,realizeSeries,read_realize]

theorem realize_read_series (f : PowerSeries ℤ_[2]) : realizeSeries (readSeries f) = f := by
  ext n
  simp [readSeries,realizeSeries,realize_read]

theorem range_list_sum (v : Nat → ℤ_[2]) (m : Nat) :
    ∑ j ∈ Finset.range m, v j = ((List.range m).map v).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

theorem read_list_sum (l : List ℤ_[2]) :
    read l.sum = (l.map read).foldr add (natScalar 0) := by
  induction l with
  | nil => exact read_nat 0
  | cons x xs ih =>
    simp only [List.sum_cons,List.map_cons,List.foldr_cons, read_add,ih]

theorem readSeries_mul (f g : PowerSeries ℤ_[2]) :
    readSeries (f*g) = DyadicSeriesProjection.convolution (readSeries f) (readSeries g) := by
  funext n
  change read (PowerSeries.coeff n (f*g)) = _
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g),
    range_list_sum, read_list_sum, List.map_map]
  simp only [Function.comp_def,read_mul,readSeries,DyadicSeriesProjection.convolution]

noncomputable def candidate : PowerSeries ℤ_[2] :=
  realizeSeries SignedStickelbergerCandidate.series2893

noncomputable def candidate69 : PowerSeries ℤ_[2] :=
  realizeSeries SignedStickelbergerCandidate.series69

theorem read_candidate : readSeries candidate = SignedStickelbergerCandidate.series2893 :=
  read_realize_series _

theorem read_candidate69 : readSeries candidate69 = DyadicMahler69.series :=
  (read_realize_series _).trans SignedStickelbergerCandidate.series69_eq

/-- The monic polynomial C0+C1 X+X² viewed in the standard power series ring. -/
noncomputable def quadratic (c0 c1 : ℤ_[2]) : PowerSeries ℤ_[2] :=
  PowerSeries.C c0 + PowerSeries.C c1 * PowerSeries.X^1 + PowerSeries.X^2

theorem read_quadratic (c0 c1 : ℤ_[2]) :
    readSeries (quadratic c0 c1) = DyadicSeriesProjection.quadraticSeries (read c0) (read c1) := by
  funext n
  change read (PowerSeries.coeff n (quadratic c0 c1)) = _
  simp only [quadratic,map_add,PowerSeries.coeff_C,PowerSeries.coeff_C_mul_X_pow,PowerSeries.coeff_X_pow]
  cases n with
  | zero => simp [DyadicSeriesProjection.quadraticSeries]
  | succ n =>
    cases n with
    | zero => simp [DyadicSeriesProjection.quadraticSeries]
    | succ n =>
      cases n with
      | zero => simpa [DyadicSeriesProjection.quadraticSeries] using read_nat 1
      | succ n => simpa [DyadicSeriesProjection.quadraticSeries] using read_nat 0

theorem read_even (z : ℤ_[2]) (h : PadicInt.toZModPow 1 z=0) : (read z).residue 0=0 := by
  apply word_ext
  rw [read_reduction]
  change PadicInt.toZModPow 1 z=(0:ZMod (2^1))
  exact h

theorem readSeries_injective : Function.Injective readSeries := by
  intro f g h
  simpa only [realize_read_series] using congrArg realizeSeries h

/-- Quadratic obtained by integral preparation of the complete signed character sum. -/
noncomputable def preparedQuadratic : PowerSeries ℤ_[2] :=
  quadratic (realize (SignedAnalyticPreparation.constant SignedArithmeticProjection.analyticSeries))
    (realize (SignedAnalyticPreparation.linear SignedArithmeticProjection.analyticSeries))

theorem read_prepared :
    readSeries preparedQuadratic = DyadicSeriesProjection.quadraticSeries
      (SignedAnalyticPreparation.constant SignedArithmeticProjection.analyticSeries)
      (SignedAnalyticPreparation.linear SignedArithmeticProjection.analyticSeries) := by
  rw [preparedQuadratic,read_quadratic,read_realize,read_realize]

/-- The equality of native ideals for the analytically prepared quadratic is unconditional. -/
theorem prepared_principal_ideal :
    Ideal.span {candidate} = Ideal.span {preparedQuadratic} := by
  obtain ⟨h, v, _, _, h'⟩ := SignedArithmeticProjection.analytic_mutual_divisibility
  have hc : readSeries candidate = SignedArithmeticProjection.analyticSeries :=
    read_candidate.trans SignedStickelbergerCandidate.series2893_eq
  apply le_antisymm <;> apply Ideal.span_singleton_le_span_singleton.mpr
  · refine ⟨realizeSeries (SignedAnalyticPreparation.cofactor SignedArithmeticProjection.analyticSeries),?_⟩
    apply readSeries_injective
    rw [hc,readSeries_mul,read_prepared,read_realize_series]
    exact h
  · refine ⟨realizeSeries v,?_⟩
    apply readSeries_injective
    rw [mul_comm candidate,readSeries_mul,read_realize_series,hc,read_prepared]
    exact h'

/-- The conductor-69 owner can transport a native monic principal inclusion
to the already checked weight-one criterion. -/
theorem conductor69_samples_of_native_membership (c0 c1 : ℤ_[2])
    (belongs : quadratic c0 c1 ∈ Ideal.span {candidate69}) :
    DyadicOrder.WeightOneSamples (read c0) (read c1) := by
  obtain ⟨u,hu⟩ := Ideal.mem_span_singleton.mp belongs
  rw [mul_comm candidate69] at hu
  have fac := congrArg readSeries hu
  rw [read_quadratic,readSeries_mul,read_candidate69] at fac
  exact DyadicOneSided69.samples_of_forward_divisibility ⟨_,fac⟩

/-- Membership of the actual normalized Stickelberger candidate in a native
quadratic ideal supplies the finite characteristic bits in the same native ring. -/
theorem characteristic_bits_of_principal_inclusion (c0 c1 : ℤ_[2])
    (h0 : PadicInt.toZModPow 1 c0=0) (h1 : PadicInt.toZModPow 1 c1=0)
    (belongs : candidate ∈ Ideal.span {quadratic c0 c1}) :
    PadicInt.toZModPow 6 c0=40 ∧ PadicInt.toZModPow 6 c1=18 := by
  obtain ⟨u,hu⟩ := Ideal.mem_span_singleton.mp belongs
  have fac := congrArg readSeries hu
  rw [read_candidate,readSeries_mul,read_quadratic] at fac
  obtain ⟨hc,hl⟩ := SignedNormalizationComparison.characteristic_bits_at_256
    SignedStickelbergerCandidate.series2893 SignedStickelbergerCandidate.raw_congruences_256
    (read c0) (read c1) (read_even c0 h0) (read_even c1 h1) (readSeries u) fac
  change PadicInt.toZModPow (5+1) c0=40 ∧ PadicInt.toZModPow (5+1) c1=18
  rw [← read_reduction,← read_reduction,hc,hl]
  decide

end Reimann.SignedNativeSeries2893
