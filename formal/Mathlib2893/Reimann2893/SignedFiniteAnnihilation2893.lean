import Reimann2893.SignedCyclicCriterion2893
import Reimann2893.SignedRationalCharacteristic2893
import Reimann2893.SignedClassScalars2893

/-! A uniform bound for the order of every coordinate of the quadratic
residual kills that residual upon rationalization. -/
namespace Reimann.SignedFiniteAnnihilation2893

open scoped TensorProduct Polynomial
open Polynomial SignedRationalCharacteristic2893

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M]

def delta (g : M ≃ₗ[ℤ_[2]] M) (b : M) : M := g b - b

noncomputable def residual (g : M ≃ₗ[ℤ_[2]] M) (c0 c1 : ℤ_[2]) (b : M) : M :=
  delta g (delta g b) + c1 • delta g b + c0 • b

noncomputable def oneTensor : M →ₗ[ℤ_[2]] Space M :=
  TensorProduct.mk ℤ_[2] ℚ_[2] M 1

theorem torsion_tmul (y : M) (s : ℕ) (kill : (2^s : ℕ) • y = 0) :
    oneTensor y = 0 := by
  have hz : (2^s : ℕ) • oneTensor y = 0 := by
    rw [← map_nsmul, kill, map_zero]
  have hq : ((2^s : ℕ) : ℚ_[2]) • oneTensor y = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hz
  exact (smul_eq_zero.mp hq).resolve_left (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide)))

theorem augmentation_oneTensor (g : M ≃ₗ[ℤ_[2]] M) (b : M) :
    augmentation M g (oneTensor b) = oneTensor (delta g b) := by
  rw [delta, map_sub]
  rfl

theorem oneTensor_smul (c : ℤ_[2]) (b : M) :
    oneTensor (c • b) = (c : ℚ_[2]) • oneTensor b := by
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul ℚ_[2] c (oneTensor b)).symm

theorem rational_relation (g : M ≃ₗ[ℤ_[2]] M) (c0 c1 : ℤ_[2]) (b : M)
    (s : ℕ) (kill : (2^s : ℕ) • residual g c0 c1 b = 0) :
    augmentation M g (augmentation M g (oneTensor b)) +
      (c1 : ℚ_[2]) • augmentation M g (oneTensor b) +
      (c0 : ℚ_[2]) • oneTensor b = 0 := by
  simpa only [residual, map_add, oneTensor_smul, augmentation_oneTensor] using
    torsion_tmul (residual g c0 c1 b) s kill

variable {G : ℕ → Type*} [∀ n, CommGroup (G n)] (N : ∀ n, G (n+1) →* G n)

theorem torsion_of_coordinates (y : Additive (SignedNormLimit2893.coherent N)) (s : ℕ)
    (kill : ∀ n, (SignedNormLimit2893.projection N n y.toMul)^(2^s) = 1) :
    (2^s : ℕ) • y = 0 := by
  change y.toMul ^ (2^s) = 1
  exact Subtype.ext (funext kill)

variable [Module ℤ_[2] (Additive (SignedNormLimit2893.coherent N))]
variable [FiniteDimensional ℚ_[2] (Space (Additive (SignedNormLimit2893.coherent N)))]

theorem ideal_from_finite_coordinates
    (g : Additive (SignedNormLimit2893.coherent N) ≃ₗ[ℤ_[2]] Additive (SignedNormLimit2893.coherent N))
    (b : Additive (SignedNormLimit2893.coherent N))
    (B : Module.Basis (Fin 2) ℚ_[2] (Space (Additive (SignedNormLimit2893.coherent N))))
    (base : B 0 = oneTensor b)
    (first : augmentation _ g (B 0) = B 1)
    (s : ℕ) (kill : ∀ n, (SignedNormLimit2893.projection N n
      (residual g SignedCyclicCriterion2893.constant SignedCyclicCriterion2893.linear b).toMul)^(2^s) = 1) :
    ∃ c0 c1 : ℤ_[2], characteristic _ g = C (c0 : ℚ_[2]) + C (c1 : ℚ_[2])*X + X^2 ∧
      SignedNativeSeries2893.candidate ∈ Ideal.span {SignedNativeSeries2893.quadratic c0 c1} := by
  apply SignedCyclicCriterion2893.ideal_from_generator (augmentation _ g) B first
  rw [base]
  exact rational_relation g _ _ b s (torsion_of_coordinates N _ s kill)

section PrimaryClasses

open SignedClassScalars2893

variable {H : Type*} [CommGroup H]

def localDelta (σ : H ≃* H) (x : H) : H := σ x / x

def localResidual (σ : H ≃* H) (x : H) (r0 r1 : ℕ) : H :=
  localDelta σ (localDelta σ x) * (localDelta σ x)^r1 * x^r0

theorem localDelta_exponent (σ : H ≃* H) (x : H) (d : ℕ) (hx : x^d = 1) :
    (localDelta σ x)^d = 1 := by
  rw [localDelta, div_pow, ← map_pow, hx, map_one, div_one]

variable (A : ℕ → Type*) [∀ n, CommGroup (A n)]
variable (ν : ∀ n, Primary (A (n+1)) →* Primary (A n))
variable (σ : ∀ n, Primary (A n) ≃* Primary (A n))
variable (hν : ∀ n x, ν n (σ (n+1) x) = σ n (ν n x))

theorem delta_coordinate (b : Additive (ClassLimit A ν)) (n : ℕ) :
    (delta (limitForwardLinear A ν σ hν) b).toMul.val n = localDelta (σ n) (b.toMul.val n) := rfl

theorem residual_coordinate (b : Additive (ClassLimit A ν)) (c0 c1 : ℤ_[2]) (n k : ℕ)
    (hx : (b.toMul.val n)^(2^k) = 1) :
    (residual (limitForwardLinear A ν σ hν) c0 c1 b).toMul.val n =
      localResidual (σ n) (b.toMul.val n) (c0.appr k) (c1.appr k) := by
  let g := limitForwardLinear A ν σ hν
  change (delta g (delta g b)).toMul.val n * (c1 • delta g b).toMul.val n *
    (c0 • b).toMul.val n = _
  have hd : ((delta g b).toMul.val n)^(2^k) = 1 := localDelta_exponent (σ n) _ _ hx
  rw [scalar_at_level A ν c0 b n k hx, scalar_at_level A ν c1 (delta g b) n k hd]
  rfl

variable [FiniteDimensional ℚ_[2] (Space (Additive (ClassLimit A ν)))]

theorem ideal_from_local_powers (b : Additive (ClassLimit A ν))
    (B : Module.Basis (Fin 2) ℚ_[2] (Space (Additive (ClassLimit A ν))))
    (base : B 0 = oneTensor b)
    (first : augmentation _ (limitForwardLinear A ν σ hν) (B 0) = B 1)
    (k : ℕ → ℕ) (orders : ∀ n, (b.toMul.val n)^(2^(k n)) = 1)
    (s : ℕ) (kill : ∀ n, (localResidual (σ n) (b.toMul.val n)
      (SignedCyclicCriterion2893.constant.appr (k n))
      (SignedCyclicCriterion2893.linear.appr (k n)))^(2^s) = 1) :
    ∃ c0 c1 : ℤ_[2], characteristic _ (limitForwardLinear A ν σ hν) =
        C (c0 : ℚ_[2]) + C (c1 : ℚ_[2])*X + X^2 ∧
      SignedNativeSeries2893.candidate ∈ Ideal.span {SignedNativeSeries2893.quadratic c0 c1} := by
  apply ideal_from_finite_coordinates (G := fun n => Primary (A n)) ν _ b B base first s
  intro n
  change ((residual _ _ _ b).toMul.val n)^(2^s) = 1
  rw [residual_coordinate A ν σ hν b _ _ n (k n) (orders n)]
  exact kill n

end PrimaryClasses
end Reimann.SignedFiniteAnnihilation2893

namespace Reimann.SignedFiniteAnnihilation2893
open scoped TensorProduct
variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M]

theorem oneTensor_zero_iff (y : M) :
    oneTensor y = 0 ↔ ∃ s : ℕ, (2^s : ℕ) • y = 0 := by
  constructor
  · intro ht
    change (TensorProduct.mk ℤ_[2] ℚ_[2] M 1) y = 0 at ht
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[2])
      (TensorProduct.mk ℤ_[2] ℚ_[2] M 1)).mp ht
    have hne : a.val ≠ 0 := nonZeroDivisors.coe_ne_zero a
    let u := PadicInt.unitCoeff hne
    have hfactor : a.val = (u : ℤ_[2]) * (2 : ℤ_[2]) ^ a.val.valuation := by
      simpa only [Nat.cast_ofNat] using PadicInt.unitCoeff_spec hne
    have hu : (u : ℤ_[2]) • (((2 : ℤ_[2])^a.val.valuation) • y) = 0 := by
      rw [← mul_smul, ← hfactor]
      exact ha
    refine ⟨a.val.valuation, ?_⟩
    have hpow : ((2 : ℤ_[2]) ^ a.val.valuation) • y = 0 := by
      calc
        _ = (↑(u⁻¹) : ℤ_[2]) • ((u : ℤ_[2]) • (((2 : ℤ_[2])^a.val.valuation) • y)) := by
          rw [← mul_smul, Units.inv_mul, one_smul]
        _ = 0 := by rw [hu, smul_zero]
    simpa only [← Nat.cast_smul_eq_nsmul ℤ_[2], Nat.cast_pow, Nat.cast_ofNat] using hpow
  · rintro ⟨s, hs⟩
    exact torsion_tmul y s hs

variable {G : ℕ → Type*} [∀ n, CommGroup (G n)] (N : ∀ n, G (n+1) →* G n)
variable [Module ℤ_[2] (Additive (SignedNormLimit2893.coherent N))]

theorem oneTensor_zero_iff_coordinates (y : Additive (SignedNormLimit2893.coherent N)) :
    oneTensor y = 0 ↔ ∃ s : ℕ, ∀ n, (SignedNormLimit2893.projection N n y.toMul)^(2^s) = 1 := by
  rw [oneTensor_zero_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, fun n => congrArg (fun z : Additive (SignedNormLimit2893.coherent N) => z.toMul.val n) hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, torsion_of_coordinates N y s hs⟩

theorem rational_relation_iff_coordinates
    (g : Additive (SignedNormLimit2893.coherent N) ≃ₗ[ℤ_[2]] Additive (SignedNormLimit2893.coherent N))
    (c0 c1 : ℤ_[2]) (b : Additive (SignedNormLimit2893.coherent N)) :
    SignedRationalCharacteristic2893.augmentation _ g
        (SignedRationalCharacteristic2893.augmentation _ g (oneTensor b)) +
      (c1 : ℚ_[2]) • SignedRationalCharacteristic2893.augmentation _ g (oneTensor b) +
      (c0 : ℚ_[2]) • oneTensor b = 0 ↔
    ∃ s : ℕ, ∀ n, (SignedNormLimit2893.projection N n (residual g c0 c1 b).toMul)^(2^s) = 1 := by
  rw [← oneTensor_zero_iff_coordinates]
  simp only [residual, map_add, oneTensor_smul, augmentation_oneTensor]

end Reimann.SignedFiniteAnnihilation2893
