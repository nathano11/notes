import Reimann.SignedBernoulliPairing
import Reimann.SignedTowerRows
import Reimann.DyadicGammaDistribution69

/-! Both conventions for signed numerators in the conductor-2893 and conductor-69
distributions, on every positive fibre and at common inverse powers of five. -/
namespace Reimann.SignedCommonNormalization

/-- The even conductor-2893 character twisted by the odd character modulo four. -/
def character2893 (a : Nat) : Int :=
  SignedMeasure256.character a * SignedStickelberger.signFour a

theorem lift_bound {D m t k : Nat} (ht : t < D) (hk : k < m) :
    t + D*k ≤ D*m := by
  have h := Nat.mul_le_mul_left D (show k+1 ≤ m by omega)
  rw [Nat.mul_succ] at h
  omega

theorem positive_lift {D t : Nat} (hD : D%4=0) (ht : t%4=1) (k : Nat) :
    (t+D*k)%4=1 := by
  rw [Nat.add_mod, Nat.mul_mod, hD, ht]
  simp

theorem negative_reflection {D m a : Nat} (hD : D%4=0) (ha : a ≤ D*m) (hp : a%4=1) :
    (D*m-a)%4=3 := by
  have h : (D*m)%4=0 := by rw [Nat.mul_mod, hD]; simp
  omega

theorem character2893_positive {a : Nat} (hp : a%4=1) :
    character2893 a = SignedMeasure256.character a := by
  simp [character2893, SignedStickelberger.signFour, hp]

theorem character2893_opposite (n a : Nat) (ha : a ≤ 2^(n+2)*2893) (hp : a%4=1) :
    character2893 (2^(n+2)*2893-a) = -character2893 a := by
  have hD := Nat.mod_eq_zero_of_dvd (SignedGammaTower.four_dvd_modulus n)
  have hn := negative_reflection hD ha hp
  rw [character2893_positive hp]
  simp [character2893, SignedStickelberger.signFour, hn, SignedTowerMeasure.level_reflection (n+2) a ha]

theorem character69_positive {a : Nat} (hp : a%4=1) :
    DyadicZeroValues.chi276 a = DyadicDistribution69.psi a := by
  simp [DyadicZeroValues.chi276, DyadicDistribution69.psi, hp]

theorem character69_opposite (D a : Nat) (hD : D%4=0) (ha : a ≤ D*69) (hp : a%4=1) :
    DyadicZeroValues.chi276 (D*69-a) = -DyadicZeroValues.chi276 a := by
  have hn := negative_reflection hD ha hp
  rw [character69_positive hp]
  simp only [DyadicZeroValues.chi276, hn]
  change -DyadicDistribution69.psi (D*69-a) = -DyadicDistribution69.psi a
  exact congrArg Neg.neg (by
    simpa only [Nat.mul_comm 69 D] using
      (DyadicDistribution69.psi_reflected D a (by simpa only [Nat.mul_comm 69 D] using ha)))

open SignedBernoulliPairing

/-- At conductor 2893 both cleared numerators describe the same integral coefficient. -/
theorem positive_fibre_2893 (n t : Nat) (ht : t < 2^(n+2)) (hp : t%4=1) :
    let D := 2^(n+2)
    let c := SignedTowerMeasure.coefficient (n+2) t
    rawFibre character2893 t D 2893 = 2*((D*2893 : Nat):Int)*c ∧
    literalFibre character2893 t D 2893 = 4*((D*2893 : Nat):Int)*c := by
  have hD := Nat.mod_eq_zero_of_dvd (SignedGammaTower.four_dvd_modulus n)
  apply fibre_normalization character2893 (SignedTowerMeasure.fibre (n+2) t)
  · exact fun _ hk => lift_bound ht hk
  · exact fun k _ => character2893_positive (positive_lift hD hp k)
  · exact fun k hk => character2893_opposite n _ (lift_bound ht hk) (positive_lift hD hp k)
  · exact SignedTowerMeasure.mass_zero _ _
  · exact SignedTowerMeasure.coefficient_exact _ _

/-- The centered Bernoulli numerator at conductor 2893, cleared by 4M. -/
theorem literal_bernoulli_2893 (n t : Nat) (ht : t < 2^(n+2)) (hp : t%4=1) :
    literalFibre character2893 t (2^(n+2)) 2893 =
      4*((2^(n+2)*2893 : Nat):Int)*SignedTowerMeasure.coefficient (n+2) t :=
  (positive_fibre_2893 n t ht hp).2

/-- At conductor 69 both cleared numerators describe the same integral coefficient. -/
theorem positive_fibre_69 (n t : Nat) (hD : 2^n%4=0) (ht : t < 2^n) (hp : t%4=1) :
    let D := 2^n
    let c := DyadicDistribution69.coefficient n t
    rawFibre DyadicZeroValues.chi276 t D 69 = 2*((D*69 : Nat):Int)*c ∧
    literalFibre DyadicZeroValues.chi276 t D 69 = 4*((D*69 : Nat):Int)*c := by
  apply fibre_normalization DyadicZeroValues.chi276 (DyadicDistribution69.fibre n t)
  · exact fun _ hk => lift_bound ht hk
  · exact fun k _ => character69_positive (positive_lift hD hp k)
  · exact fun k hk => character69_opposite _ _ hD (lift_bound ht hk) (positive_lift hD hp k)
  · exact (DyadicDistribution69.all_fibre_moments n t).1
  · exact DyadicDistribution69.coefficient_exact n t

/-- The raw first-power Stickelberger numerator at conductor 69, cleared by 2M. -/
theorem literal_stickelberger_69 (n t : Nat) (hD : 2^n%4=0) (ht : t < 2^n) (hp : t%4=1) :
    rawFibre DyadicZeroValues.chi276 t (2^n) 69 =
      2*((2^n*69 : Nat):Int)*DyadicDistribution69.coefficient n t :=
  (positive_fibre_69 n t hD ht hp).1

/-- Forward power j of the generator indexes the inverse residue in the 2893 tower. -/
theorem gamma_normalization_2893 (n j : Nat) :
    let t := SignedGammaTower.representative n j
    let D := 2^(n+2)
    let c := SignedTowerRows.weight n j
    rawFibre character2893 t D 2893 = 2*((D*2893 : Nat):Int)*c ∧
    literalFibre character2893 t D 2893 = 4*((D*2893 : Nat):Int)*c :=
  positive_fibre_2893 n _ (SignedGammaTower.representative_lt n j) (SignedGammaTower.positive_residue n j)

/-- The same inverse residue indexes the two conductor-69 numerators. -/
theorem gamma_normalization_69 (n j : Nat) :
    let t := SignedGammaTower.representative n j
    let D := 2^(n+2)
    let c := DyadicGammaDistribution69.gammaRow n j
    rawFibre DyadicZeroValues.chi276 t D 69 = 2*((D*69 : Nat):Int)*c ∧
    literalFibre DyadicZeroValues.chi276 t D 69 = 4*((D*69 : Nat):Int)*c :=
  positive_fibre_69 (n+2) _ (Nat.mod_eq_zero_of_dvd (SignedGammaTower.four_dvd_modulus n))
    (SignedGammaTower.representative_lt n j) (SignedGammaTower.positive_residue n j)

/-- The common raw fibre is the literal sum of the previously checked Stickelberger terms. -/
theorem raw_fibre_eq_stickelberger_2893 (n t : Nat) :
    let D := 2^(n+2)
    rawFibre character2893 t D 2893 =
      SignedProjection.total (fun k => SignedStickelberger.term (t+D*k) +
        SignedStickelberger.term (D*2893-(t+D*k))) 2893 := by
  simp only [rawFibre, rawPair, rawTerm, character2893, SignedStickelberger.term, Int.mul_assoc]

/-- The common centered fibre is the literal conductor-69 sum in arithmetic coordinates. -/
theorem literal_fibre_eq_bernoulli_69 (n t : Nat) :
    literalFibre DyadicZeroValues.chi276 t (2^n) 69 =
      SignedProjection.total (DyadicDistribution69.signedFibreTerm n t) 69 := by
  apply congrArg (fun f => SignedProjection.total f 69)
  funext k
  simp only [literalPair, literalTerm, DyadicDistribution69.signedFibreTerm,
    DyadicDistribution69.signedBernoulliTerm, Nat.mul_comm 69 (2^n)]

end Reimann.SignedCommonNormalization
