import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.FieldSimp
import Reimann.SignedStickelbergerCandidate

/-! Finite Fourier interpolation at the inverse powers of the forward generator 5.
The working modulus is the full modulus of the row. -/
namespace Reimann.SignedFiniteInterpolation2893

open SignedGammaTower (representative signedRepresentative)
open SignedStickelbergerCandidate (projectedNumerator)
open SignedBernoulliPairing (literalTerm)

variable {K : Type*} [Field K]

/-- The two indicator functions of a row at the odd residue of a lift. -/
def signedMask (K : Type*) [Field K] (n j a : Nat) : K :=
  (if signedRepresentative n false j = a % 2^(n+2) then 1 else 0) +
  (if signedRepresentative n true j = a % 2^(n+2) then 1 else 0)

theorem cast_total (f : Nat → Int) (M : Nat) :
    (SignedProjection.total f M : K) = ∑ a ∈ Finset.range M, (f a : K) := by
  induction M with
  | zero => simp [SignedProjection.total]
  | succ M ih => simp only [SignedProjection.total, Int.cast_add, Finset.sum_range_succ, ih]

theorem cast_projected (f : Nat → Int) (n j m : Nat) :
    (projectedNumerator f (representative n j) (2^(n+2)) m : K) =
    ∑ a ∈ Finset.range (2^(n+2)*m), (f a : K) * signedMask K n j a := by
  rw [projectedNumerator, cast_total]
  apply Finset.sum_congr rfl
  intro a _
  simp only [signedMask, SignedGammaTower.signedRepresentative, Bool.false_eq_true,
    ↓reduceIte, Int.cast_add, mul_add]
  congr 1 <;> split <;> rename_i h <;> simp [h, eq_comm]

theorem character_signed_inverse (n j : Nat) (b : Bool)
    (θ : DirichletCharacter K (2^(n+2))) (even : θ.Even) :
    θ 5 ^ j = (θ (signedRepresentative n b j : ZMod (2^(n+2))))⁻¹ := by
  have modular : (5 : ZMod (2^(n+2)))^j * (representative n j : ZMod (2^(n+2))) = 1 := by
    have h := congrArg (fun x : Nat => (x : ZMod (2^(n+2)))) (SignedGammaTower.representative_is_inverse n j)
    simpa only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h
  have val : θ 5 ^ j * θ (representative n j : ZMod (2^(n+2))) = 1 := by
    simpa only [map_pow, map_mul, map_one] using congrArg θ modular
  have hp := eq_inv_of_mul_eq_one_left val
  cases b with
  | false => exact hp
  | true =>
    change θ 5 ^ j = (θ ((2^(n+2)-representative n j : Nat) : ZMod (2^(n+2))))⁻¹
    rw [Nat.cast_sub (SignedGammaTower.representative_lt n j).le, ZMod.natCast_self,
      zero_sub, even.eval_neg]
    exact hp

theorem character_partition (n a : Nat) (odd : a%2=1)
    (θ : DirichletCharacter K (2^(n+2))) (even : θ.Even) :
    (∑ j : Fin (2^n), signedMask K n j a * θ 5 ^ j.val) = (θ a)⁻¹ := by
  have h2 : 2 ∣ 2^(n+2) := dvd_trans (by decide : 2 ∣ 4) (SignedGammaTower.four_dvd_modulus n)
  obtain ⟨b,t,ht⟩ := SignedGammaTower.signed_unique_class n (a % 2^(n+2))
    (Nat.mod_lt _ (by positivity)) (by rwa [Nat.mod_mod_of_dvd _ h2])
  have hc (s : Bool) (j : Fin (2^n)) :
      signedRepresentative n s j = a % 2^(n+2) ↔ s=b ∧ j=t := by
    simpa only [Nat.mod_eq_of_lt j.isLt, Fin.ext_iff] using ht s j.val
  have residue := (hc b t).2 ⟨rfl,rfl⟩
  have value := character_signed_inverse n t b θ even
  rw [residue,ZMod.natCast_mod] at value
  rw [Finset.sum_eq_single t]
  · have mask : signedMask K n t a = 1 := by
      simp only [signedMask, hc]
      cases b <;> simp
    simpa [mask] using value
  · intro j _ hj
    simp [signedMask, hc, hj]
  · simp

theorem fourier_projected (n m : Nat) (f : Nat → Int) (evenZero : ∀ a, a%2=0 → f a=0)
    (θ : DirichletCharacter K (2^(n+2))) (even : θ.Even) :
    (∑ j : Fin (2^n), (projectedNumerator f (representative n j) (2^(n+2)) m : K) * θ 5 ^ j.val) =
      ∑ a ∈ Finset.range (2^(n+2)*m), (f a : K) * (θ a)⁻¹ := by
  simp only [cast_projected, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum]
  by_cases h : a%2=0
  · simp [evenZero a h]
  · rw [character_partition n a (by omega) θ even]

/-- Generalized first Bernoulli sum at the stated modulus, with B₁(x) = x − 1/2. -/
noncomputable def firstBernoulli (M : Nat) (w : Nat → K) : K :=
  ∑ a ∈ Finset.range M, w a * ((a:K)/(M:K) - 1/2)

/-- Fourier value of an integer row in the coordinate of the forward generator. -/
def fourier (n : Nat) (c : Nat → Int) (θ : DirichletCharacter K (2^(n+2))) : K :=
  ∑ j : Fin (2^n), (c j : K) * θ 5 ^ j.val

variable [CharZero K]

theorem fourier_of_centered (n m : Nat) (hm : 0<m) (g c : Nat → Int)
    (evenZero : ∀ a, a%2=0 → g a=0)
    (rows : ∀ j, projectedNumerator (literalTerm g (2^(n+2)*m)) (representative n j)
      (2^(n+2)) m = 4*((2^(n+2)*m : Nat):Int)*c j)
    (θ : DirichletCharacter K (2^(n+2))) (even : θ.Even) :
    fourier n c θ = -firstBernoulli (2^(n+2)*m) (fun a => (g a : K) * (θ a)⁻¹) / 2 := by
  let M := 2^(n+2)*m
  have hM : (M:K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos (by positivity) hm))
  have raw := fourier_projected n m (literalTerm g M)
    (fun a ha => by simp [literalTerm,evenZero a ha]) θ even
  have left : (4*(M:K)) * fourier n c θ =
      ∑ a ∈ Finset.range M, ((M:K)-2*(a:K))*(g a : K)*(θ a)⁻¹ := by
    calc
      _ = ∑ j : Fin (2^n), (projectedNumerator (literalTerm g M) (representative n j) (2^(n+2)) m : K) * θ 5 ^ j.val := by
        rw [fourier,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [rows]
        push_cast
        simp only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
      _ = _ := by simpa only [literalTerm, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
            Int.cast_ofNat] using raw
  have right : ∑ a ∈ Finset.range M, ((M:K)-2*(a:K))*(g a : K)*(θ a)⁻¹ =
      (-2*(M:K))*firstBernoulli M (fun a => (g a:K)*(θ a)⁻¹) := by
    rw [firstBernoulli,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    generalize (θ a)⁻¹ = v
    field_simp
    ring
  change fourier n c θ = -firstBernoulli M _ / 2
  have h := left.trans right
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4:K) ≠ 0) hM)
  rw [h]
  ring

theorem fourier_bernoulli_2893 (n : Nat) (θ : DirichletCharacter K (2^(n+2))) (even : θ.Even) :
    fourier n (SignedStickelbergerCandidate.rawRow SignedCommonNormalization.character2893 2893 n) θ =
      -firstBernoulli (2^(n+2)*2893) (fun a => (SignedCommonNormalization.character2893 a : K)*θ⁻¹ a) / 2 := by
  simp only [MulChar.inv_apply_eq_inv']
  apply fourier_of_centered n 2893 (by decide)
  · intro a ha
    have h1 : a%4≠1 := by omega
    have h3 : a%4≠3 := by omega
    simp [SignedCommonNormalization.character2893,SignedStickelberger.signFour,h1,h3]
  · intro j
    rw [SignedStickelbergerCandidate.raw_row_2893, SignedStickelbergerCandidate.full_sum_as_pairs
      _ _ _ _ (SignedStickelbergerCandidate.inverse_representative_pos n j) (SignedGammaTower.representative_lt n j)]
    exact (SignedCommonNormalization.gamma_normalization_2893 n j).2
  · exact even

theorem fourier_bernoulli_69 (n : Nat) (θ : DirichletCharacter K (2^(n+2))) (even : θ.Even) :
    fourier n (SignedStickelbergerCandidate.centeredRow DyadicZeroValues.chi276 69 n) θ =
      -firstBernoulli (2^(n+2)*69) (fun a => (DyadicZeroValues.chi276 a : K)*θ⁻¹ a) / 2 := by
  simp only [MulChar.inv_apply_eq_inv']
  apply fourier_of_centered n 69 (by decide)
  · intro a ha
    have h : a%4=0 ∨ a%4=2 := by omega
    rcases h with h|h <;> simp [DyadicZeroValues.chi276,h]
  · intro j
    rw [SignedStickelbergerCandidate.centered_row_69]
    exact SignedStickelbergerCandidate.centered_sum_69 n j
  · exact even

end Reimann.SignedFiniteInterpolation2893
