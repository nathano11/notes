import Reimann277.StrictArtinInput
import Reimann277.CyclotomicTame

namespace Reimann.TameStrictReciprocity277

open TameArtin277 TameCyclotomicLocal277 TameStrictArtin277 TameIdealAction277
open TameCyclotomicUnits277

local instance prime277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- The coefficient action on forward ideal arguments is the inverse cyclotomic twist. -/
def Twisted {r n : ℕ} (η : SClassGroup r n →* Target n) : Prop :=
  ∀ g a, (η (onClass r n g a)).toAdd =
    (finiteTwist r n g : ZMod (277^(n+1))) * (η a).toAdd

theorem forward_class_residue {r n : ℕ} {η : SClassGroup r n →* Target n}
    (hη : Twisted η) (s : Bool × Bool) (g : Local)
    (hg : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 → asAut g z = z^5)
    (a : SClassGroup r n) :
    modPrime n (η (onClass r n (restriction s g) a)).toAdd =
      111^r * modPrime n (η a).toAdd := by
  rw [hη,map_mul,TameCyclotomicTame277.restricted_scalar_power r n s g hg]

theorem inverse_residue_powers (r : ℕ) : (5 : ZMod 277)^r * 111^r = 1 := by
  rw [← mul_pow,show (5 : ZMod 277)*111 = 1 from by decide +kernel,one_pow]

/-- Pullback acts by precomposition with the inverse automorphism of ideal classes. -/
theorem pullback_class_residue {r n : ℕ} {η : SClassGroup r n →* Target n}
    (hη : Twisted η) (s : Bool × Bool) (g : Local)
    (hg : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 → asAut g z = z^5)
    (a : SClassGroup r n) :
    modPrime n (η ((onClass r n (restriction s g)).symm a)).toAdd =
      5^r * modPrime n (η a).toAdd := by
  have h := forward_class_residue hη s g hg ((onClass r n (restriction s g)).symm a)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h,← mul_assoc,inverse_residue_powers,one_mul]

end Reimann.TameStrictReciprocity277
