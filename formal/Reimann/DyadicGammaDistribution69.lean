import Reimann.SignedGammaTower
import Reimann.DyadicProgression69

/-!
At layer a the coefficient of γ^h in the signed conductor-69 distribution
uses the positive residue t satisfying 5^h t = 1 modulo 2^(a+2). Here γ
acts by 5. The arithmetic representatives are numbered by t=1+4j, while
the group-ring coordinates use h modulo 2^a.
-/

namespace Reimann.DyadicGammaDistribution69

open Reimann.DyadicDistribution69
open Reimann.SignedGammaTower

/-- Convert a group-ring exponent h to the arithmetic row index j=(t-1)/4. -/
def angularIndex (a : Nat) (h : Fin (2^a)) : Fin (2^a) :=
  ⟨representative a h.val / 4, by
    have hx := representative_lt a h.val
    rw [Nat.pow_add] at hx
    omega⟩

theorem angular_representative (a : Nat) (h : Fin (2^a)) :
    1+4*(angularIndex a h).val = representative a h.val := by
  have hx := positive_residue a h.val
  change 1+4*(representative a h.val / 4) = representative a h.val
  omega

/-- The coefficient of γ^h is read at t ≡ 5^(-h) in the positive angular fibre. -/
def gammaRow (a h : Nat) : Int := coefficient (a+2) (representative a h)

/-- Pushforward along γ ↦ γ from layer a+1 to a adds the two exponent lifts. -/
theorem gamma_row_refines (a h : Nat) :
    gammaRow a h = gammaRow (a+1) h + gammaRow (a+1) (h+2^a) := by
  obtain H | H := sibling_fibres a h
  · unfold gammaRow
    rw [H.1,H.2]
    exact coefficient_refines _ _
  · unfold gammaRow
    rw [H.1,H.2, Int.add_comm]
    exact coefficient_refines _ _

theorem gamma_row_period (a h : Nat) : gammaRow a (h%2^a) = gammaRow a h := by
  unfold gammaRow
  rw [(representative_injective_mod a _ h).mpr (Nat.mod_mod ..)]

theorem angular_is_inverse (a : Nat) (h : Fin (2^a)) :
    (5^h.val*(1+4*(angularIndex a h).val)) % 2^(a+2) = 1 := by
  rw [angular_representative]
  exact representative_is_inverse _ _

theorem angular_injective (a : Nat) (h k : Fin (2^a))
    (he : angularIndex a h = angularIndex a k) : h = k := by
  have hx := angular_representative a h
  rw [he, angular_representative] at hx
  apply Fin.ext
  simpa only [Nat.mod_eq_of_lt h.isLt, Nat.mod_eq_of_lt k.isLt] using
    (representative_injective_mod a h.val k.val).mp hx.symm

theorem angular_surjective (a : Nat) (j : Fin (2^a)) : ∃ h, angularIndex a h = j := by
  have hpos : (1+4*j.val)%4 = 1 := by omega
  obtain ⟨h,hh⟩ := positive_class a (1+4*j.val) hpos
  have hlt : 1+4*j.val < 2^(a+2) := by rw [Nat.pow_add]; have hj := j.isLt; omega
  have hx := (hh h.val).mpr (Nat.mod_eq_of_lt h.isLt)
  rw [Nat.mod_eq_of_lt hlt, ←angular_representative a h] at hx
  exact ⟨h,Fin.ext (by omega)⟩

/-- The unique exponent of the inverse of 1+4j. -/
noncomputable def exponentIndex (a : Nat) (j : Fin (2^a)) : Fin (2^a) :=
  Classical.choose (angular_surjective a j)

theorem angular_after_exponent (a : Nat) (j : Fin (2^a)) :
    angularIndex a (exponentIndex a j) = j := Classical.choose_spec (angular_surjective a j)

theorem exponent_after_angular (a : Nat) (h : Fin (2^a)) :
    exponentIndex a (angularIndex a h) = h :=
  angular_injective a _ _ (angular_after_exponent a _)

/-- Reduction from exponents (or angular indices) at layer a+1 to layer a. -/
def reduceIndex (a : Nat) (h : Fin (2^(a+1))) : Fin (2^a) :=
  ⟨h.val%2^a, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

theorem angular_reduction (a : Nat) (h : Fin (2^(a+1))) :
    angularIndex a (reduceIndex a h) = reduceIndex a (angularIndex (a+1) h) := by
  apply Fin.ext
  have he : representative a (h.val%2^a) = representative a h.val :=
    (representative_injective_mod _ _ _).mpr (Nat.mod_mod ..)
  change representative a (h.val%2^a) / 4 = representative (a+1) h.val / 4 % 2^a
  rw [he, ←representative_reduce a h.val, Nat.pow_add 2 a 2]
  exact Nat.mod_mul_left_div_self _ _ _

theorem exponent_reduction (a : Nat) (j : Fin (2^(a+1))) :
    exponentIndex a (reduceIndex a j) = reduceIndex a (exponentIndex (a+1) j) := by
  apply angular_injective
  rw [angular_after_exponent, angular_reduction, angular_after_exponent]

theorem row_in_angular_coordinates (a : Nat) (h : Fin (2^a)) :
    gammaRow a h.val = positiveRow a (angularIndex a h) := by
  unfold gammaRow positiveRow
  rw [angular_representative]

/-- At conductor eight the identity is represented by 1, and γ by 5. -/
theorem level_one_marks :
    (representative 1 0, representative 1 1) = (1, 5) ∧
    (gammaRow 1 0, gammaRow 1 1) = (4,0) := by
  exact ⟨by decide, Reimann.DyadicProgression69.depth_three_coefficients⟩

theorem exponent_add (a i j : Nat) :
    exponent a (i+j) = (exponent a i + exponent a j) % 2^a := by
  apply Int.ofNat_inj.mp
  rw [exponent_cast, Int.natCast_emod, Int.natCast_add, Int.natCast_add,
    exponent_cast a i, exponent_cast a j, ← Int.add_emod]
  congr 1
  omega

/-- Addition of group exponents is multiplication of their inverse representatives. -/
theorem representative_product (a i j : Nat) :
    representative a (i+j) = (representative a i * representative a j) % 2^(a+2) := by
  unfold representative
  rw [Nat.mul_mod_mod, Nat.mod_mul_mod, ←Nat.pow_add, forward_power_iff,
    Nat.mod_eq_of_lt (exponent_lt _ _), exponent_add]

/-- At every exponent in every finite cyclic quotient, the stored coefficient
is the literal half-normalized signed Bernoulli coefficient. -/
theorem group_row_bernoulli (a h : Nat) :
    Reimann.SignedProjection.total (signedFibreTerm (a+2) (representative a h)) 69 =
      4*((2^(a+2) : Nat) : Int)*69*gammaRow a h :=
  literal_bernoulli_row _ _ (Nat.mod_eq_zero_of_dvd (four_dvd_modulus a))
    (representative_lt a h) (positive_residue a h)

end Reimann.DyadicGammaDistribution69
