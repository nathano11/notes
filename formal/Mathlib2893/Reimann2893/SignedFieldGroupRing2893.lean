import Reimann.SignedStickelbergerCandidate
import Reimann2893.SignedForwardGenerator2893
import Mathlib.Algebra.MonoidAlgebra.Defs

/-! Push the full signed conductor sum into the group ring of the constructed
field automorphisms. Each odd residue selects the inverse of its dyadic angular
class. The two residues of opposite sign select the same field automorphism. -/
namespace Reimann.SignedFieldGroupRing2893

open SignedFieldLayers2893 (Layer forward)
open SignedGammaTower SignedStickelbergerCandidate SignedBernoulliPairing

abbrev Aut (n : ℕ) := Layer n ≃+* Layer n

theorem residue_lt (n a : ℕ) : a % 2^(n+2) < 2^(n+2) :=
  Nat.mod_lt _ (by positivity)

theorem odd_residue (n a : ℕ) (ha : a%2=1) : a % 2^(n+2) % 2 = 1 := by
  rwa [Nat.mod_mod_of_dvd _ (dvd_trans (by decide : 2 ∣ 4) (four_dvd_modulus n))]

noncomputable def inverseIndex (n a : ℕ) (ha : a%2=1) : Fin (2^n) :=
  (signed_unique_class n _ (residue_lt n a) (odd_residue n a ha)).choose_spec.choose

theorem index_iff (n a : ℕ) (ha : a%2=1) (j : Fin (2^n)) :
    inverseIndex n a ha = j ↔ a%2^(n+2) = representative n j.val ∨
      a%2^(n+2) = 2^(n+2) - representative n j.val := by
  let h := signed_unique_class n _ (residue_lt n a) (odd_residue n a ha)
  have spec := h.choose_spec.choose_spec
  change h.choose_spec.choose = j ↔ _
  constructor
  · intro hj
    have index : j.val % 2^n = h.choose_spec.choose.val := by rw [Nat.mod_eq_of_lt j.isLt,hj]
    cases hs : h.choose
    · exact Or.inl ((spec false j.val).mpr ⟨hs.symm,index⟩).symm
    · exact Or.inr ((spec true j.val).mpr ⟨hs.symm,index⟩).symm
  · rintro (plus|minus)
    · have eqn := ((spec false j.val).mp (by simpa [signedRepresentative] using plus.symm)).2
      exact Fin.ext (by simpa [Nat.mod_eq_of_lt j.isLt] using eqn.symm)
    · have eqn := ((spec true j.val).mp (by simpa [signedRepresentative] using minus.symm)).2
      exact Fin.ext (by simpa [Nat.mod_eq_of_lt j.isLt] using eqn.symm)

theorem powers_injective (n : ℕ) :
    Function.Injective (fun j : Fin (2^n) => (forward n)^j.val) := by
  intro i j h
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := forward n) _ _ h
  · change i.val < orderOf (forward n)
    rw [SignedForwardGenerator2893.forward_order]
    exact i.isLt
  · change j.val < orderOf (forward n)
    rw [SignedForwardGenerator2893.forward_order]
    exact j.isLt

abbrev weight (a : ℕ) : ℤ := rawTerm SignedCommonNormalization.character2893 a

noncomputable def summand (n a : ℕ) : MonoidAlgebra ℤ (Aut n) :=
  if ha : a%2=1 then MonoidAlgebra.single ((forward n)^(inverseIndex n a ha).val) (weight a) else 0

theorem summand_coefficient (n a : ℕ) (j : Fin (2^n)) :
    (summand n a).coeff ((forward n)^j.val) =
      (if a%2^(n+2) = representative n j.val then weight a else 0) +
      (if a%2^(n+2) = 2^(n+2)-representative n j.val then weight a else 0) := by
  classical
  by_cases ha : a%2=1
  · rw [summand, dite_eq_left ha, MonoidAlgebra.coeff_single, Finsupp.single_apply, (powers_injective n).eq_iff,
      index_iff]
    have hpos := positive_residue n j.val
    have hlt := representative_lt n j.val
    have hd := Nat.mod_eq_zero_of_dvd (four_dvd_modulus n)
    split_ifs <;> omega
  · have bad : ¬a.Coprime (2^(n+2)*2893) := by
      intro h
      have h2 := h.of_dvd_right (dvd_trans (dvd_trans (by decide : 2∣4) (four_dvd_modulus n))
        (Nat.dvd_mul_right _ _))
      obtain ⟨k,hk⟩ := Nat.coprime_two_right.mp h2
      omega
    have hz : weight a = 0 := by simp [weight,rawTerm,zero_off_units a n bad]
    simp [summand,ha,hz]

noncomputable def fullNumerator (n : ℕ) : MonoidAlgebra ℤ (Aut n) :=
  ∑ a ∈ Finset.range (2^(n+2)*2893), summand n a

theorem range_total (f : ℕ → ℤ) (m : ℕ) :
    ∑ a ∈ Finset.range m, f a = SignedProjection.total f m := by
  induction m with
  | zero => simp [SignedProjection.total]
  | succ m ih => rw [Finset.sum_range_succ,ih,SignedProjection.total]

/-- The coefficient at the actual forward field automorphism's jth power
is the full integral multiple of the jth row in the constructed distribution. -/
theorem projected_group_numerator (n : ℕ) (j : Fin (2^n)) :
    (fullNumerator n).coeff ((forward n)^j.val) =
    2*((2^(n+2)*2893 : ℕ):ℤ)*SignedTowerRows.weight n j.val := by
  classical
  rw [fullNumerator, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [summand_coefficient]
  rw [range_total]
  exact raw_sum_2893 n j.val

noncomputable def level (n : ℕ) : MonoidAlgebra ℤ (Aut n) :=
  ∑ j : Fin (2^n), MonoidAlgebra.single ((forward n)^j.val)
    (rawRow SignedCommonNormalization.character2893 2893 n j.val)

theorem level_coefficient (n : ℕ) (j : Fin (2^n)) :
    (level n).coeff ((forward n)^j.val) = SignedTowerRows.weight n j.val := by
  classical
  simp [level,MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,MonoidAlgebra.coeff_single,
    Finsupp.single_apply,(powers_injective n).eq_iff,raw_row_2893]

/-- Equality in the integral group ring, including every automorphism outside
the relative cyclic subgroup. The quotient by the raw denominator is integral. -/
theorem field_group_ring_normalization (n : ℕ) :
    fullNumerator n = (2*((2^(n+2)*2893 : ℕ):ℤ)) • level n := by
  classical
  apply MonoidAlgebra.ext
  ext σ
  by_cases image : ∃ j : Fin (2^n), (forward n)^j.val = σ
  · obtain ⟨j,rfl⟩ := image
    rw [projected_group_numerator,MonoidAlgebra.coeff_smul_apply,level_coefficient]
    rfl
  · have outside : ∀ j : Fin (2^n), (forward n)^j.val ≠ σ := by simpa using image
    have zeroTerm (a : ℕ) : (summand n a).coeff σ = 0 := by
      by_cases ha : a%2=1
      · simp [summand,ha,MonoidAlgebra.coeff_single,outside]
      · simp [summand,ha]
    rw [MonoidAlgebra.coeff_smul_apply]
    simp [fullNumerator,level,MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_single,outside,zeroTerm]

/-- In the actual field group ring, the forward element and its inverse
already have different coefficients at the first distinguishing layer. -/
theorem field_orientation_witness :
    (representative 2 1, representative 2 3) = (13,5) ∧
    ((level 2).coeff (forward 2), (level 2).coeff ((forward 2)^3)) = (2,-18) := by
  obtain ⟨hr,h,_⟩ := orientation_check
  refine ⟨hr,?_⟩
  have h1 := level_coefficient 2 (1 : Fin (2^2))
  have h3 := level_coefficient 2 (3 : Fin (2^2))
  change (level 2).coeff ((forward 2)^1) = SignedTowerRows.weight 2 1 at h1
  change (level 2).coeff ((forward 2)^3) = SignedTowerRows.weight 2 3 at h3
  rw [pow_one] at h1
  rw [h1,h3]
  simpa only [raw_row_2893] using h

end Reimann.SignedFieldGroupRing2893
