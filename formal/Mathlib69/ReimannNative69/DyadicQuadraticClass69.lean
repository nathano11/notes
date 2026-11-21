import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! Explicit field and ideal relations for the bottom imaginary quadratic field. -/
namespace Reimann.DyadicQuadraticClass69

open scoped NumberField

abbrev Order := QuadraticAlgebra ℤ (-69) 0
abbrev Field69 := QuadraticAlgebra ℚ (-69) 0

instance rat_discriminant_nonsquare : Fact (¬ IsSquare (QuadraticAlgebra.discr (-69 : ℚ) 0)) :=
  ⟨by
    rintro ⟨t, ht⟩
    norm_num [QuadraticAlgebra.discr] at ht
    nlinarith [sq_nonneg t]⟩

instance number_field : NumberField Field69 where

theorem fundamental_discriminant : Int.IsFundamentalDiscr (QuadraticAlgebra.discr (-69 : ℤ) 0) := by
  change Int.IsFundamentalDiscr (4 * (-69 : ℤ))
  apply Int.isFundamentalDiscr_four_mul.mpr
  refine ⟨?_, Or.inr (by decide)⟩
  rw [← Int.squarefree_natAbs]
  change Squarefree (3 * 23 : ℕ)
  apply (Nat.squarefree_mul (by decide : Nat.Coprime 3 23)).mpr
  exact ⟨(by decide : Nat.Prime 3).prime.squarefree, (by decide : Nat.Prime 23).prime.squarefree⟩

/-- The coordinate order is the full ring of integers of the quadratic field. -/
noncomputable def ring_of_integers : Order ≃ₐ[ℤ] 𝓞 Field69 :=
  QuadraticAlgebra.Int.algEquivIntegralClosure fundamental_discriminant

/-- The image of the actual quadratic generator in the full ring of integers. -/
noncomputable def s : 𝓞 Field69 := ring_of_integers QuadraticAlgebra.omega

theorem s_squared : s ^ 2 = -69 := by
  have h : (QuadraticAlgebra.omega : Order) ^ 2 = -69 := by
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    norm_num
  change ring_of_integers QuadraticAlgebra.omega ^ 2 = -69
  rw [← map_pow, h, map_neg]
  exact congrArg Neg.neg (map_natCast ring_of_integers 69)

/-- Two ideals with coprime first generators retain their common second
generator on multiplication. -/
theorem common_generator_product {A : Type*} [CommRing A] (m n x : A) (h : IsCoprime m n) :
    (Ideal.span {m, x} : Ideal A) * Ideal.span {n, x} = Ideal.span {m * n, x} := by
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hx : x ∈ (Ideal.span {m * n, x} : Ideal A) := Ideal.subset_span (by simp)
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mul_mem_left _ _ hx
    · exact Ideal.mul_mem_right _ _ hx
    · exact Ideal.mul_mem_left _ _ hx
  · let I : Ideal A := Ideal.span {m * n, m * x, x * n, x * x}
    have hm : m * x ∈ I := Ideal.subset_span (by simp)
    have hn : x * n ∈ I := Ideal.subset_span (by simp)
    obtain ⟨a, b, hab⟩ := h
    have hx : x ∈ I := by
      have e : x = a * (m * x) + b * (x * n) := calc
        x = (a * m + b * n) * x := by rw [hab, one_mul]
        _ = _ := by ring
      rw [e]
      exact I.add_mem (I.mul_mem_left _ hm) (I.mul_mem_left _ hn)
    apply Ideal.span_le.mpr
    intro z hz
    rcases (show z = m * n ∨ z = x by simpa using hz) with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact hx

/-- The ideal (m,s-r) of the full integer ring. -/
noncomputable def primeIdeal (m r : ℤ) : Ideal (𝓞 Field69) :=
  Ideal.span {(m : 𝓞 Field69), s - (r : 𝓞 Field69)}

theorem primeIdeal_shift (m r t : ℤ) : primeIdeal m (r + m * t) = primeIdeal m r := by
  unfold primeIdeal
  push_cast
  rw [show s - ((r : 𝓞 Field69) + m * t) = (s - r) - m * t by ring,
    Ideal.span_pair_sub_left_mul]

theorem primeIdeal_mul_of_coprime (m n r : ℤ) (h : IsCoprime m n) :
    primeIdeal m r * primeIdeal n r = primeIdeal (m * n) r := by
  unfold primeIdeal
  rw [Int.cast_mul]
  exact common_generator_product _ _ _ (h.map (Int.castRingHom (𝓞 Field69)))

theorem primeIdeal_norm_generator (r : ℤ) :
    primeIdeal (69 + r ^ 2) r = Ideal.span {s - (r : 𝓞 Field69)} := by
  unfold primeIdeal
  have fact : ((69 + r ^ 2 : ℤ) : 𝓞 Field69) = (-(s + r)) * (s - r) := calc
    _ = -(s ^ 2) + (r : 𝓞 Field69) ^ 2 := by rw [s_squared]; push_cast; ring
    _ = _ := by ring
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rcases (show z = ((69 + r ^ 2 : ℤ) : 𝓞 Field69) ∨ z = s - r by simpa using hz) with rfl | rfl
    · rw [fact]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)
  · exact Ideal.span_mono (by intro z h; simp_all)

/-- The principal ideal of s−1 factors at 2, 5 and 7. -/
theorem factor_minus_one :
    primeIdeal 2 1 * primeIdeal 5 1 * primeIdeal 7 1 = Ideal.span {s - 1} := by
  rw [primeIdeal_mul_of_coprime 2 5 1 ⟨-2, 1, by decide⟩,
    primeIdeal_mul_of_coprime (2 * 5) 7 1 ⟨-2, 3, by decide⟩]
  simpa using primeIdeal_norm_generator 1

/-- The principal ideal of s+6 involves the conjugate prime at 5. -/
theorem factor_plus_six :
    primeIdeal 3 0 * primeIdeal 5 (-1) * primeIdeal 7 1 = Ideal.span {s + 6} := by
  have a := primeIdeal_shift 3 0 (-2)
  have b := primeIdeal_shift 5 (-1) (-1)
  have c := primeIdeal_shift 7 1 (-1)
  norm_num only [Int.reduceMul, Int.reduceAdd] at a b c
  rw [← a, ← b, ← c, primeIdeal_mul_of_coprime 3 5 (-6) ⟨2, -1, by decide⟩,
    primeIdeal_mul_of_coprime (3 * 5) 7 (-6) ⟨1, -2, by decide⟩]
  simpa only [Int.reducePow, Int.reduceAdd, Int.reduceMul, Int.cast_neg, Int.cast_ofNat,
    sub_neg_eq_add] using primeIdeal_norm_generator (-6)

/-- A pair of complementary residue generators gives the rational
principal ideal when their product is mk and m,k are coprime. -/
theorem complementary_generators {A : Type*} [CommRing A] (m x y k : A)
    (product : x * y = m * k) (coprime : IsCoprime m k) :
    (Ideal.span {m, x} : Ideal A) * Ideal.span {m, y} = Ideal.span {m} := by
  rw [Ideal.span_pair_mul_span_pair, product]
  let I : Ideal A := Ideal.span {m * m, m * y, x * m, m * k}
  have hm : m ∈ (Ideal.span {m} : Ideal A) := Ideal.subset_span (by simp)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_left _ _ hm
    · exact Ideal.mul_mem_right _ _ hm
    · exact Ideal.mul_mem_left _ _ hm
    · exact Ideal.mul_mem_right _ _ hm
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    have h₁ : m * m ∈ I := Ideal.subset_span (by simp)
    have h₂ : m * k ∈ I := Ideal.subset_span (by simp)
    obtain ⟨a, b, h⟩ := coprime
    have e : m = a * (m * m) + b * (m * k) := calc
      m = (a * m + b * k) * m := by rw [h, one_mul]
      _ = _ := by ring
    exact e ▸ I.add_mem (I.mul_mem_left _ h₁) (I.mul_mem_left _ h₂)

theorem primeIdeal_conjugate (m r k : ℤ) (hk : m * k = -69 - r ^ 2) (coprime : IsCoprime m k) :
    primeIdeal m r * primeIdeal m (-r) = Ideal.span {(m : 𝓞 Field69)} := by
  unfold primeIdeal
  rw [Int.cast_neg, sub_neg_eq_add]
  apply complementary_generators _ _ _ (k : 𝓞 Field69) _ (coprime.map (Int.castRingHom _))
  calc
    _ = s ^ 2 - (r : 𝓞 Field69) ^ 2 := by ring
    _ = ((m * k : ℤ) : 𝓞 Field69) := by rw [s_squared, hk]; push_cast; ring
    _ = _ := Int.cast_mul m k

theorem ramified_two_square : primeIdeal 2 1 ^ 2 = Ideal.span {(2 : 𝓞 Field69)} := by
  have h := primeIdeal_shift 2 (-1) 1
  norm_num only [Int.reduceMul, Int.reduceAdd] at h
  simpa only [pow_two, Int.cast_ofNat, ← h] using
    primeIdeal_conjugate 2 1 (-35) (by decide) ⟨18, 1, by decide⟩

theorem ramified_three_square : primeIdeal 3 0 ^ 2 = Ideal.span {(3 : 𝓞 Field69)} := by
  simpa only [pow_two, Int.cast_ofNat, neg_zero] using
    primeIdeal_conjugate 3 0 (-23) (by decide) ⟨8, 1, by decide⟩

theorem conjugate_five_product : primeIdeal 5 1 * primeIdeal 5 (-1) = Ideal.span {(5 : 𝓞 Field69)} := by
  exact primeIdeal_conjugate 5 1 (-14) (by decide) ⟨3, 1, by decide⟩

end Reimann.DyadicQuadraticClass69
