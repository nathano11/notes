import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Reimann.CircularRealUnit69
import Reimann.CircularConjugateRadicals69
import ReimannNative69.CommonAmbient69
import ReimannNative69.CommonRootPowers69

/-! Inversion on a root of unity preserves rational polynomial relations.
The proof averages a rational scalar product over its finite cyclic orbit. -/
namespace Reimann.CommonConjugation69

open Polynomial

variable {K : Type} [Field K] [Algebra ℚ K]

noncomputable def pairing (f : K →ₗ[ℚ] ℚ) (x : K) (n : ℕ) (a b : K) : ℚ :=
  ∑ i ∈ Finset.range n, f (x^i * a) * f (x^i * b)

theorem range_rotate {A : Type} [AddCancelCommMonoid A] (g : ℕ → A) (n : ℕ) (hn : g n = g 0) :
    (∑ i ∈ Finset.range n, g (i+1)) = ∑ i ∈ Finset.range n, g i := by
  have h₁ := Finset.sum_range_succ g n
  have h₂ := Finset.sum_range_succ' g n
  rw [hn] at h₁
  exact add_right_cancel (h₂.symm.trans h₁)

theorem pairing_zero_left (f : K →ₗ[ℚ] ℚ) (x : K) (n : ℕ) (b : K) :
    pairing f x n 0 b = 0 := by simp [pairing]

theorem pairing_zero_right (f : K →ₗ[ℚ] ℚ) (x : K) (n : ℕ) (a : K) :
    pairing f x n a 0 = 0 := by simp [pairing]

theorem pairing_add_left (f : K →ₗ[ℚ] ℚ) (x : K) (n : ℕ) (a b c : K) :
    pairing f x n (a+b) c = pairing f x n a c + pairing f x n b c := by
  simp [pairing, mul_add, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (f : K →ₗ[ℚ] ℚ) (x : K) (n : ℕ) (a b c : K) :
    pairing f x n a (b+c) = pairing f x n a b + pairing f x n a c := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_scalar (f : K →ₗ[ℚ] ℚ) (x : K) (n : ℕ) (q : ℚ) (a b : K) :
    pairing f x n (algebraMap ℚ K q * a) b = pairing f x n a (algebraMap ℚ K q * b) := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm (x^i) _ a, mul_left_comm (x^i) _ b,
    ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]
  simp [mul_left_comm, mul_assoc]

theorem pairing_shift (f : K →ₗ[ℚ] ℚ) {x : K} {n : ℕ} (hx : x^n = 1)
    (hn : n ≠ 0) (a b : K) :
    pairing f x n (x*a) b = pairing f x n a (x⁻¹*b) := by
  have hnz : x ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hx
    exact zero_ne_one hx
  let g (i : ℕ) := f (x^i*a) * f (x^i*(x⁻¹*b))
  have hp : g n = g 0 := by simp [g, hx]
  calc
    pairing f x n (x*a) b = ∑ i ∈ Finset.range n, g (i+1) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [g, pow_succ, mul_assoc, hnz]
    _ = _ := range_rotate g n hp

theorem pairing_power (f : K →ₗ[ℚ] ℚ) {x : K} {n : ℕ} (hx : x^n = 1)
    (hn : n ≠ 0) (d : ℕ) (a b : K) :
    pairing f x n (x^d*a) b = pairing f x n a (x⁻¹^d*b) := by
  induction d generalizing b with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', mul_assoc, pairing_shift f hx hn, ih, pow_succ, mul_assoc]

theorem pairing_polynomial (f : K →ₗ[ℚ] ℚ) {x : K} {n : ℕ} (hx : x^n = 1)
    (hn : n ≠ 0) (p : ℚ[X]) (a b : K) :
    pairing f x n (p.eval₂ (algebraMap ℚ K) x * a) b =
      pairing f x n a (p.eval₂ (algebraMap ℚ K) x⁻¹ * b) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add, add_mul, pairing_add_left, pairing_add_right, hp, hq]
  | monomial d q =>
    simp only [eval₂_monomial, mul_assoc]
    rw [pairing_scalar, pairing_power f hx hn, mul_left_comm]

theorem pairing_diagonal_zero (f : K →ₗ[ℚ] ℚ) (x : K) {n : ℕ} (hn : n ≠ 0)
    (a : K) (h : pairing f x n a a = 0) : f a = 0 := by
  unfold pairing at h
  have h₀ := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.range n) => mul_self_nonneg (f (x^i*a)))).mp h
    0 (Finset.mem_range.mpr (Nat.pos_of_ne_zero hn))
  simpa using h₀

theorem reciprocal_coordinate (f : K →ₗ[ℚ] ℚ) {x : K} {n : ℕ} (hx : x^n = 1)
    (hn : n ≠ 0) (p : ℚ[X]) (hp : p.eval₂ (algebraMap ℚ K) x = 0) :
    f (p.eval₂ (algebraMap ℚ K) x⁻¹) = 0 := by
  apply pairing_diagonal_zero f x hn
  have h := pairing_polynomial f hx hn p (p.eval₂ (algebraMap ℚ K) x⁻¹) 1
  simpa only [hp, zero_mul, mul_one, pairing_zero_left] using h.symm

theorem reciprocal_relation {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (p : ℚ[X]) (hp : p.eval₂ (algebraMap ℚ K) x = 0) :
    p.eval₂ (algebraMap ℚ K) x⁻¹ = 0 := by
  let B := Module.Basis.ofVectorSpace ℚ K
  apply B.forall_coord_eq_zero_iff.mp
  exact fun i => reciprocal_coordinate (B.coord i) hx hn p hp

noncomputable def evaluation (x : K) : ℚ[X] →+* K :=
  eval₂RingHom (algebraMap ℚ K) x

theorem reciprocal_equal {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    {p q : ℚ[X]} (h : evaluation x p = evaluation x q) :
    evaluation x⁻¹ p = evaluation x⁻¹ q := by
  have hz : evaluation x (p-q) = 0 := by rw [map_sub, h, sub_self]
  have hrev : evaluation x⁻¹ (p-q) = 0 := reciprocal_relation hx hn (p-q) hz
  simpa only [map_sub, sub_eq_zero] using hrev

noncomputable def reverseValue (x : K) (gen : Function.Surjective (evaluation x)) (a : K) : K :=
  evaluation x⁻¹ (gen a).choose

theorem reverse_evaluation {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (gen : Function.Surjective (evaluation x)) (p : ℚ[X]) :
    reverseValue x gen (evaluation x p) = evaluation x⁻¹ p :=
  reciprocal_equal hx hn (gen _).choose_spec

noncomputable def reverseHom {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (gen : Function.Surjective (evaluation x)) : K →+* K where
  toFun := reverseValue x gen
  map_zero' := by simpa only [map_zero] using reverse_evaluation hx hn gen 0
  map_one' := by simpa only [map_one] using reverse_evaluation hx hn gen 1
  map_add' a b := by
    obtain ⟨p, rfl⟩ := gen a
    obtain ⟨q, rfl⟩ := gen b
    rw [← map_add, reverse_evaluation hx hn gen, map_add, reverse_evaluation hx hn gen,
      reverse_evaluation hx hn gen]
  map_mul' a b := by
    obtain ⟨p, rfl⟩ := gen a
    obtain ⟨q, rfl⟩ := gen b
    rw [← map_mul, reverse_evaluation hx hn gen, map_mul, reverse_evaluation hx hn gen,
      reverse_evaluation hx hn gen]

theorem reverse_generator {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (gen : Function.Surjective (evaluation x)) :
    reverseHom hx hn gen x = x⁻¹ := by
  change reverseValue x gen x = x⁻¹
  simpa only [evaluation, coe_eval₂RingHom, eval₂_X] using reverse_evaluation hx hn gen X

theorem reverse_constant {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (gen : Function.Surjective (evaluation x)) (q : ℚ) :
    reverseHom hx hn gen (algebraMap ℚ K q) = algebraMap ℚ K q := by
  change reverseValue x gen _ = _
  simpa only [evaluation, coe_eval₂RingHom, eval₂_C] using reverse_evaluation hx hn gen (C q)

theorem reverse_on_inverse_evaluation {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (gen : Function.Surjective (evaluation x)) (p : ℚ[X]) :
    reverseHom hx hn gen (evaluation x⁻¹ p) = evaluation x p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial i q =>
    simp only [evaluation, coe_eval₂RingHom, eval₂_monomial, map_mul, map_pow, map_inv₀,
      reverse_constant, reverse_generator, inv_inv]

theorem reverse_involutive {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (gen : Function.Surjective (evaluation x)) : Function.Involutive (reverseHom hx hn gen) := by
  intro a
  obtain ⟨p, rfl⟩ := gen a
  change reverseHom hx hn gen (reverseValue x gen _) = evaluation x p
  rw [reverse_evaluation hx hn gen, reverse_on_inverse_evaluation]

noncomputable def cyclotomicConjugation {x : K} {n : ℕ} (hx : x^n = 1) (hn : n ≠ 0)
    (gen : Function.Surjective (evaluation x)) : CircularRealUnit69.Conjugation K where
  app := reverseHom hx hn gen
  involutive := reverse_involutive hx hn gen
  rat q := by
    change reverseHom hx hn gen ((q.num : K) / (q.den : K)) = _
    rw [map_div₀, map_intCast, map_natCast]
  add := map_add _
  sub := map_sub _
  mul := map_mul _
  inv := map_inv₀ _

section Concrete

open CommonAmbient69

theorem rational_generation : Function.Surjective (evaluation root) := by
  rw [evaluation, ← rationalEvaluation_eq]
  exact rational_polynomial_surjective

noncomputable def conjugation : CircularRealUnit69.Conjugation CommonAmbient69.K :=
  cyclotomicConjugation root_pow_19113 (by decide) rational_generation

theorem conjugate_root : conjugation.app root = root⁻¹ :=
  reverse_generator root_pow_19113 (by decide) rational_generation

theorem conjugate_x : conjugation.app x = x⁻¹ := by
  rw [← root_pow_277, CircularRealUnit69.map_power, conjugate_root, inv_pow]

theorem conjugate_z : conjugation.app z = z⁻¹ := by
  rw [← root_pow_69, CircularRealUnit69.map_power, conjugate_root, inv_pow]

theorem conjugate_roots (w : CommonAmbient69.K) (hw : w^277 = 1) :
    conjugation.app w = w⁻¹ :=
  CommonRootPowers69.inverts_all_roots conjugation z_order z_nontrivial conjugate_z w hw

theorem compatible : CircularRealUnit69.Compatible conjugation
    (CircularRadicals69.radical3 x) (CircularRadicals69.radical23 x) :=
  CircularConjugateRadicals69.compatible_of_root_inverse x x_primitive.order69
    conjugation conjugate_x conjugate_roots

end Concrete
end Reimann.CommonConjugation69
