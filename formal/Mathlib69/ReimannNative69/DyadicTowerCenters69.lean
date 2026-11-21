import ReimannNative69.DyadicBottomPrime69
import ReimannNative69.DyadicNormalTower69

/-! One pair of upper primes and its compatible labeled contractions at all real,
cyclotomic, and finite normal stages of the dyadic tower. -/
namespace Reimann.DyadicTowerCenters69

open DyadicNativePrime69 DyadicIntegerPrime69 DyadicBottomPrime69 DyadicNormalTower69

structure Labels {K : Type*} [Field K] (P Q : Ideal (integerRing K)) (u : integerRing K) : Prop where
  left_maximal : P.IsMaximal
  right_maximal : Q.IsMaximal
  left_two : (2 : integerRing K) ∈ P
  right_two : (2 : integerRing K) ∈ Q
  left_root : u ∈ P
  right_root : 1-u ∈ Q
  right_nonzero : u ∉ Q

theorem labels_distinct {K : Type*} [Field K] {P Q : Ideal (integerRing K)} {u : integerRing K}
    (h : Labels P Q u) : P≠Q := fun he => h.right_nonzero (he ▸ h.left_root)

/-- Restrict the same two upper ideals and the actual integral generator to a subfield. -/
def contractsAt {K : Type*} [Field K] (P Q : Ideal (integerRing K)) (u : integerRing K)
    (S : Subfield K) : Prop :=
  ∃ z : integerRing S, integersMap S.subtype z=u ∧
    Labels (contraction (integersMap S.subtype) P) (contraction (integersMap S.subtype) Q) z

theorem contract_labels {K : Type*} [Field K] {P Q : Ideal (integerRing K)} {u : integerRing K}
    (h : Labels P Q u) (S : Subfield K) (hu : u.val∈S) : contractsAt P Q u S := by
  obtain ⟨z,hz⟩ := integral_norm_descends S.subtype Subtype.val_injective u ⟨⟨u.val,hu⟩,rfl⟩
  refine ⟨z,hz,maximal_integer_contraction _ P h.left_maximal,maximal_integer_contraction _ Q h.right_maximal,
    ?_,?_,?_,?_,?_⟩
  · simpa only [mem_contraction,map_ofNat] using h.left_two
  · simpa only [mem_contraction,map_ofNat] using h.right_two
  · simpa only [mem_contraction,hz] using h.left_root
  · simpa only [mem_contraction,map_sub,map_one,hz] using h.right_root
  · simpa only [mem_contraction,hz] using h.right_nonzero

/-- Fix one pair of primes in the upper field. Their restrictions remain distinct
and dyadic at every Eₐ and every intermediate field over it, including Eₐ(μ₂∞)
and every finite normal stage. The choices are simultaneous for all a. -/
theorem all_real_layer_centers (Ω : Type*) [Field Ω] [CharZero Ω] (x y : Ω) (ζ : ℕ → Ω)
    (hy : y^2 = -23) :
    ∃ u : integerRing Ω, u.val=(1+y)/2 ∧ ∃ P Q : Ideal (integerRing Ω), Labels P Q u ∧
      ∀ a, contractsAt P Q u (realLayer Ω x y (ζ a)).toSubfield ∧
        ∀ S : IntermediateField (realLayer Ω x y (ζ a)) Ω, contractsAt P Q u S.toSubfield := by
  obtain ⟨u,hu,P,Q,hP,hQ,h2P,h2Q,hzP,hoQ,hnQ,_⟩ := two_primes_at_sqrt_neg23 y hy
  have lab : Labels P Q u := ⟨hP,hQ,h2P,h2Q,hzP,hoQ,hnQ⟩
  refine ⟨u,hu,P,Q,lab,fun a => ?_⟩
  have he : y∈realLayer Ω x y (ζ a) :=
    IntermediateField.subset_adjoin ℚ _ (by simp)
  have uw : u.val∈realLayer Ω x y (ζ a) := by
    rw [hu]
    exact div_mem (add_mem (one_mem _) he) ((realLayer Ω x y (ζ a)).natCast_mem 2)
  refine ⟨contract_labels lab _ uw,fun S => contract_labels lab _ ?_⟩
  exact S.algebraMap_mem (⟨u.val,uw⟩ : realLayer Ω x y (ζ a))

end Reimann.DyadicTowerCenters69
