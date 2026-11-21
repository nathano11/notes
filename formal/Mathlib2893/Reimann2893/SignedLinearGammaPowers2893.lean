import Reimann2893.SignedAdicAction2893
import Reimann2893.SignedClassScalars2893
import Reimann2893.SignedRationalCharacteristic2893

/-! Exponentiation of the forward automorphism by a dyadic integer on the class
limit. Since three is a dyadic unit, the rationalized forward automorphism has
a compatible sequence of cube roots. -/
namespace Reimann.SignedLinearGammaPowers2893

open SignedAdicAction2893 (iterate)
open SignedClassScalars2893 (Primary ClassLimit limitForwardLinear)
open SignedRationalCharacteristic2893 (Space forward)

theorem three_isUnit : IsUnit (3 : ℤ_[2]) := by
  apply PadicInt.isUnit_iff.mpr
  exact (PadicInt.norm_natCast_eq_one_iff (n:=3)).mpr (by decide)

noncomputable def thirdExponent (j : ℕ) : ℤ_[2] :=
  ((↑(three_isUnit.unit⁻¹) : ℤ_[2]))^j

theorem third_step (j : ℕ) : 3 * thirdExponent (j+1) = thirdExponent j := by
  have inverse : (3 : ℤ_[2]) * ↑three_isUnit.unit⁻¹ = 1 := by
    simpa only [three_isUnit.unit_spec] using three_isUnit.unit.mul_inv
  unfold thirdExponent
  rw [pow_succ',←mul_assoc,inverse,one_mul]

universe u
variable (A : ℕ → Type u) [∀ n, CommGroup (A n)]
variable (N : ∀ n, Primary (A (n+1)) →* Primary (A n))
variable (σ : ∀ n, Primary (A n) ≃* Primary (A n))
variable (comm : ∀ n x, N n (σ (n+1) x) = σ n (N n x))
variable (period : ∀ n x, iterate (σ n) (2^n) x = x)

local notation "L" => Additive (ClassLimit A N)

/-- The lift of the forward generator to exponent z, linear over the scalar
multiplication on the actual norm-coherent primary classes. -/
noncomputable def linearPower (z : ℤ_[2]) : L ≃ₗ[ℤ_[2]] L :=
  limitForwardLinear A N
    (fun n => iterate (σ n) (SignedAdicAction2893.exponent (SignedNativeScalar2893.read z) n))
    (SignedAdicAction2893.exponent_compatible N σ comm period (SignedNativeScalar2893.read z))

theorem linearPower_apply (z : ℤ_[2]) (x : L) :
    (linearPower A N σ comm period z x).toMul =
    SignedAdicAction2893.act N σ comm period (SignedNativeScalar2893.read z) x.toMul := rfl

theorem linearPower_one :
    linearPower A N σ comm period 1 = limitForwardLinear A N σ comm := by
  apply LinearEquiv.ext
  intro x
  change SignedAdicAction2893.act N σ comm period (SignedNativeScalar2893.read 1) x.toMul = _
  have h := SignedNativeScalar2893.read_nat 1
  rw [Nat.cast_one] at h
  rw [h]
  exact SignedAdicAction2893.act_one N σ comm period x.toMul

theorem linearPower_add (z w : ℤ_[2]) :
    linearPower A N σ comm period (z+w) =
      linearPower A N σ comm period w * linearPower A N σ comm period z := by
  apply LinearEquiv.ext
  intro x
  change SignedAdicAction2893.act N σ comm period (SignedNativeScalar2893.read (z+w)) x.toMul = _
  rw [SignedNativeScalar2893.read_add]
  exact SignedAdicAction2893.act_add N σ comm period _ _ x.toMul

theorem linearPower_zero : linearPower A N σ comm period 0 = 1 := by
  have h := linearPower_add A N σ comm period 0 0
  rw [zero_add] at h
  exact (mul_right_cancel (show (1 : L ≃ₗ[ℤ_[2]] L) * linearPower A N σ comm period 0 =
    linearPower A N σ comm period 0 * linearPower A N σ comm period 0 by simpa only [one_mul] using h)).symm

theorem linearPower_nat_mul (k : ℕ) (z : ℤ_[2]) :
    linearPower A N σ comm period ((k:ℤ_[2])*z) = (linearPower A N σ comm period z)^k := by
  induction k with
  | zero => simp [linearPower_zero]
  | succ k ih => rw [Nat.cast_succ,add_mul,one_mul,linearPower_add,ih,pow_succ']

/-- Successive dyadic thirds of the forward generator on the rationalization. -/
noncomputable def rationalCube (j : ℕ) : Space L ≃ₗ[ℚ_[2]] Space L :=
  (linearPower A N σ comm period (thirdExponent j)).baseChange ℤ_[2] ℚ_[2] L L

theorem rationalCube_zero : (rationalCube A N σ comm period 0).toLinearMap =
    forward L (limitForwardLinear A N σ comm) := by
  simp only [rationalCube, thirdExponent, pow_zero, linearPower_one,LinearEquiv.coe_baseChange,forward]

theorem rationalCube_step (j : ℕ) :
    rationalCube A N σ comm period (j+1) ^ 3 = rationalCube A N σ comm period j := by
  unfold rationalCube
  rw [←LinearEquiv.baseChange_pow,←linearPower_nat_mul]
  rw [show ((3:ℕ):ℤ_[2]) = (3:ℤ_[2]) by norm_num,third_step]

include period in
theorem exists_cube_tower :
    ∃ G : ℕ → Module.End ℚ_[2] (Space L),
      G 0 = forward L (limitForwardLinear A N σ comm) ∧
      (∀ j, G (j+1)^3 = G j) ∧ ∀ j, IsUnit (G j) := by
  let E := rationalCube A N σ comm period
  refine ⟨fun j => (E j).toLinearMap,rationalCube_zero A N σ comm period,?_,?_⟩
  · intro j
    have h := congrArg LinearEquiv.toLinearMap (rationalCube_step A N σ comm period j)
    simpa only [pow_succ, pow_zero, one_mul, LinearEquiv.coe_toLinearMap_mul] using h
  · intro j
    refine ⟨⟨(E j).toLinearMap,(E j).symm.toLinearMap,?_,?_⟩,rfl⟩
    · exact LinearMap.ext (fun x => (E j).apply_symm_apply x)
    · exact LinearMap.ext (fun x => (E j).symm_apply_apply x)

end Reimann.SignedLinearGammaPowers2893
