import Reimann.SignedNormalizationComparison
import Reimann.SignedOrientationWitness

/-! Project the full finite signed character sums to inverse-power coordinates
and take the integral half-normalization before passing to a series. -/
namespace Reimann.SignedStickelbergerCandidate

open SignedProjection (total)
open SignedGammaTower (representative)
open SignedBernoulliPairing (rawTerm literalTerm)

theorem selected_cell (f : Nat → Int) (t k : Nat) :
    total (fun i => if i=t then f i else 0) k = if t<k then f t else 0 := by
  induction k with
  | zero => simp [total]
  | succ k ih =>
    rw [total, ih]
    by_cases he : k=t
    · subst k
      simp
    · by_cases h : t<k
      · simp [h,he,show t<k+1 by omega]
      · simp [h,he,show ¬t<k+1 by omega]

theorem residue_block (f : Nat → Int) (t D k : Nat) (ht : t<D) :
    total (fun i => if (D*k+i)%D=t then f (D*k+i) else 0) D = f (D*k+t) := by
  calc
    _ = total (fun i => if i=t then f (D*k+i) else 0) D := by
      apply SignedStickelberger.total_congr_below
      intro i hi
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    _ = _ := by simp [selected_cell, ht]

theorem project_one_residue (f : Nat → Int) (t D m : Nat) (ht : t<D) :
    total (fun a => if a%D=t then f a else 0) (D*m) =
      total (fun k => f (D*k+t)) m := by
  induction m with
  | zero => simp [total]
  | succ m ih =>
    rw [Nat.mul_succ, SignedProjection.total_append, ih, residue_block f t D m ht, total]

theorem reverse_sum (f : Nat → Int) (m : Nat) :
    total (fun k => f (m-1-k)) m = total f m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change total (fun k => f (m-k)) (m+1) = total f m + f m
    have cut := SignedProjection.total_append (fun k => f (m-k)) 1 m
    rw [Nat.add_comm 1 m] at cut
    rw [cut]
    have tail : total (fun k => f (m-(1+k))) m = total f m := by
      apply Eq.trans _ ih
      apply SignedStickelberger.total_congr_below
      intro k _
      congr 1 <;> omega
    rw [tail]
    simp [total, Int.add_comm]

theorem reflection_index (D m t k : Nat) (ht : t≤D) (hk : k<m) :
    D*(m-1-k)+(D-t) = D*m-(t+D*k) := by
  have e : D*((m-1-k)+(k+1)) = D*m := by rw [show (m-1-k)+(k+1)=m by omega]
  rw [Nat.mul_add, Nat.mul_succ] at e
  omega

theorem total_sum (f g : Nat → Int) (m : Nat) :
    total (fun a => f a + g a) m = total f m + total g m := by
  simpa using SignedProjection.total_affine f g 1 1 m

/-- Project an integer group-ring numerator to the class represented by ±t.
The sums run over the complete residue interval of the ambient conductor. -/
def projectedNumerator (f : Nat → Int) (t D m : Nat) : Int :=
  total (fun a => (if a%D=t then f a else 0) + (if a%D=D-t then f a else 0)) (D*m)

/-- Group the full residue interval by the positive class and its negative.
The reflected lifts enumerate the second class in reverse order. -/
theorem full_sum_as_pairs (f : Nat → Int) (t D m : Nat) (hi : 0<t) (ht : t<D) :
    projectedNumerator f t D m =
      total (fun k => f (t+D*k) + f (D*m-(t+D*k))) m := by
  rw [projectedNumerator, total_sum,
    project_one_residue f t D m ht, project_one_residue f (D-t) D m (by omega)]
  rw [← reverse_sum (fun k => f (D*k+(D-t))) m, ← total_sum]
  apply SignedStickelberger.total_congr_below
  intro k hk
  rw [reflection_index D m t k (by omega) hk, Nat.add_comm (D*k) t]

theorem inverse_representative_pos (n j : Nat) : 0 < representative n j := by
  have h := SignedGammaTower.positive_residue n j
  omega

/-- The raw first-moment sum divided by its exact integer denominator. -/
def rawRow (g : Nat → Int) (m n j : Nat) : Int :=
  let D := 2^(n+2)
  projectedNumerator (rawTerm g) (representative n j) D m / (2*((D*m : Nat):Int))

/-- The centered Bernoulli sum divided by the denominator for the half-normalized series. -/
def centeredRow (g : Nat → Int) (m n j : Nat) : Int :=
  let D := 2^(n+2)
  projectedNumerator (literalTerm g (D*m)) (representative n j) D m / (4*((D*m : Nat):Int))

theorem raw_sum_2893 (n j : Nat) :
    projectedNumerator (rawTerm SignedCommonNormalization.character2893) (representative n j) (2^(n+2)) 2893 =
      2*((2^(n+2)*2893 : Nat):Int)*SignedTowerRows.weight n j := by
  rw [full_sum_as_pairs _ _ _ _ (inverse_representative_pos n j) (SignedGammaTower.representative_lt n j)]
  exact (SignedCommonNormalization.gamma_normalization_2893 n j).1

theorem centered_sum_69 (n j : Nat) :
    let D := 2^(n+2)
    projectedNumerator (literalTerm DyadicZeroValues.chi276 (D*69)) (representative n j) D 69 =
      4*((D*69 : Nat):Int)*DyadicGammaDistribution69.gammaRow n j := by
  dsimp only
  rw [full_sum_as_pairs _ _ _ _ (inverse_representative_pos n j) (SignedGammaTower.representative_lt n j)]
  exact (SignedCommonNormalization.gamma_normalization_69 n j).2

theorem raw_row_2893 (n j : Nat) :
    rawRow SignedCommonNormalization.character2893 2893 n j = SignedTowerRows.weight n j := by
  dsimp only [rawRow]
  rw [raw_sum_2893]
  have hd : (0:Nat)<2^(n+2)*2893 := Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
  have h : (0:Int) < ((2^(n+2)*2893 : Nat):Int) := by exact_mod_cast hd
  exact Int.mul_ediv_cancel_left _ (by omega)

theorem centered_row_69 (n j : Nat) :
    centeredRow DyadicZeroValues.chi276 69 n j = DyadicGammaDistribution69.gammaRow n j := by
  dsimp only [centeredRow]
  rw [centered_sum_69]
  have hd : (0:Nat)<2^(n+2)*69 := Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
  have h : (0:Int) < ((2^(n+2)*69 : Nat):Int) := by exact_mod_cast hd
  exact Int.mul_ediv_cancel_left _ (by omega)

theorem raw_compatible : SignedTowerRows.Compatible (rawRow SignedCommonNormalization.character2893 2893) := by
  intro n j hj
  simpa only [raw_row_2893] using
    (show SignedTowerRows.weight n j = _ from SignedTowerRows.weight_compatible n j hj)

theorem centered_compatible : SignedTowerRows.Compatible (centeredRow DyadicZeroValues.chi276 69) := by
  intro n j _
  simp only [centered_row_69]
  exact DyadicGammaDistribution69.gamma_row_refines n j

def series2893 : DyadicSeriesProjection.Series :=
  SignedTaylorScalar.coefficient (rawRow SignedCommonNormalization.character2893 2893) raw_compatible

def series69 : DyadicSeriesProjection.Series :=
  SignedTaylorScalar.coefficient (centeredRow DyadicZeroValues.chi276 69) centered_compatible

theorem series2893_eq : series2893 = SignedArithmeticProjection.analyticSeries := by
  apply SignedNormalizationComparison.series_eq_of_cofinal_rows
  intro p depth
  exact ⟨depth,Nat.le_refl _,fun j _ => congrArg (BitVec.ofInt (p+1)) (raw_row_2893 depth j)⟩

theorem series69_eq : series69 = DyadicMahler69.series := by
  apply SignedNormalizationComparison.series_eq_of_cofinal_rows
  intro p depth
  exact ⟨depth,Nat.le_refl _,fun j _ => congrArg (BitVec.ofInt (p+1)) (centered_row_69 depth j)⟩

theorem orientation_check :
    (representative 2 1, representative 2 3)=(13,5) ∧
    (rawRow SignedCommonNormalization.character2893 2893 2 1,
      rawRow SignedCommonNormalization.character2893 2893 2 3)=(2,-18) ∧
    (centeredRow DyadicZeroValues.chi276 69 2 1,centeredRow DyadicZeroValues.chi276 69 2 3)=(-1,1) := by
  obtain ⟨h69,h2893⟩ := SignedOrientationWitness.first_orientation_witness
  rw [SignedOrientationWitness.order_four_arguments.1] at h69 h2893
  exact ⟨SignedOrientationWitness.order_four_arguments.2,
    by simpa only [raw_row_2893] using h2893, by simpa only [centered_row_69] using h69⟩

theorem evaluated_residue_256 (j : Fin 64) :
    ((SignedSeriesMap.evaluate series2893 j).toNat:Int)%64 = SignedTowerRows.weight 6 j.val %64 := by
  have hv := congrFun (SignedCanonicalProjection.evaluate_canonical _ raw_compatible) j
  change SignedSeriesMap.evaluate series2893 j =
    BitVec.ofInt 6 (rawRow SignedCommonNormalization.character2893 2893 6 j.val) at hv
  rw [hv, raw_row_2893, BitVec.toNat_ofInt]
  change (((SignedTowerRows.weight 6 j.val %64).toNat:Int)%64) = _
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide : (64:Int)≠0)), Int.emod_emod]

theorem centered_congruences_256 (j : Fin 64) :
    (4*256*2893*((SignedSeriesMap.evaluate series2893 j).toNat:Int))%65536 =
      (SignedBernoulliPairing.literalFibre SignedCommonNormalization.character2893
        (representative 6 j.val) 256 2893)%65536 :=
  (SignedNormalizationComparison.level256_numerators_iff j _).2.mpr (evaluated_residue_256 j)

theorem coprime_of_trial (a p : Nat) (hp : 1<p) (hr : a%p≠0)
    (trial : ∀ d : Fin p, 2≤d.val → p%d.val≠0) : Nat.Coprime a p := by
  let d := Nat.gcd a p
  have ht : d ∣ p := Nat.gcd_dvd_right a p
  have ha : d ∣ a := Nat.gcd_dvd_left a p
  have hle : d≤p := Nat.le_of_dvd (by omega) ht
  have hn : d≠p := by
    intro he
    exact hr (Nat.mod_eq_zero_of_dvd (he ▸ ha))
  have hd : d≠0 := by intro he; rw [he] at ht; simp at ht; omega
  have hc := trial ⟨d,by omega⟩
  have hm := Nat.mod_eq_zero_of_dvd ht
  change d=1
  by_cases h : d=1
  · exact h
  · exact False.elim (hc (by change 2≤d; omega) hm)

/-- The zero extension of the signed conductor-2893 character vanishes at every
nonunit of the full conductor, at every dyadic layer. -/
theorem zero_off_units (a n : Nat) (bad : ¬ Nat.Coprime a (2^(n+2)*2893)) :
    SignedCommonNormalization.character2893 a=0 := by
  by_cases h2 : a%2=0
  · have h1 : a%4≠1 := by omega
    have h3 : a%4≠3 := by omega
    simp [SignedCommonNormalization.character2893, SignedStickelberger.signFour,h1,h3]
  by_cases h11 : a%11=0
  · simp [SignedCommonNormalization.character2893,SignedMeasure256.character,Dyadic.quadSymbol,h11]
  by_cases h263 : a%263=0
  · simp [SignedCommonNormalization.character2893,SignedMeasure256.character,Dyadic.quadSymbol,h263]
  apply False.elim (bad ?_)
  rw [show (2893:Nat)=11*263 by decide, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  exact ⟨Nat.gcd_pow_right_of_gcd_eq_one (coprime_of_trial a 2 (by decide) h2 (by decide)),
    coprime_of_trial a 11 (by decide) h11 SignedArithmeticProjection.mizusawa_prime_pair.1,
    coprime_of_trial a 263 (by decide) h263 SignedArithmeticProjection.mizusawa_prime_pair.2.1⟩

/-- Restriction to the cyclotomic units indexing the finite Galois group leaves the
original raw Stickelberger numerator unchanged. -/
theorem unit_supported_sum (n j : Nat) :
    let D := 2^(n+2)
    let g := SignedCommonNormalization.character2893
    projectedNumerator (fun a => if Nat.Coprime a (D*2893) then rawTerm g a else 0)
        (representative n j) D 2893 =
      projectedNumerator (rawTerm g) (representative n j) D 2893 := by
  dsimp only
  apply congrArg (fun f => projectedNumerator f _ _ _)
  funext a
  by_cases h : Nat.Coprime a (2^(n+2)*2893)
  · simp [h]
  · simp [h, rawTerm, zero_off_units a n h]

/-- All 64 raw congruences for the series constructed from the full finite character sums. -/
theorem raw_congruences_256 (j : Fin 64) :
    (2*256*2893*((SignedSeriesMap.evaluate series2893 j).toNat:Int))%32768 =
      (SignedNormalizationComparison.raw2893 6 j.val)%32768 :=
  (SignedNormalizationComparison.level256_numerators_iff j _).1.mpr (evaluated_residue_256 j)

end Reimann.SignedStickelbergerCandidate
