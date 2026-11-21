import Reimann277.CyclotomicLocal
import Reimann277.CyclotomicUnits

namespace Reimann.TameCyclotomicTame277

open TameCyclotomicLocal277 TameCyclotomicUnits277

local instance fact277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- Reduction retains the action of the same Galois element modulo 277. -/
theorem reduce_cyclotomic (n : Nat) (g : Global) :
    Units.map (modPrime n).toMonoidHom (finiteCyclotomic n g) = finiteCyclotomic 0 g := by
  apply Units.ext
  exact PadicInt.cast_toZModPow 1 (n+1) (by omega) (cyclotomic g : ℤ_[277])

theorem reduce_twist (r n : Nat) (g : Global) :
    modPrime n (finiteTwist r n g : ZMod (277^(n+1))) =
      ((finiteCyclotomic 0 g ^ (-(r:ℤ)) : Scalars 0) : ZMod 277) := by
  have he : Units.map (modPrime n).toMonoidHom (finiteTwist r n g) =
      finiteCyclotomic 0 g ^ (-(r:ℤ)) := by
    rw [finiteTwist_apply,map_zpow,reduce_cyclotomic]
  exact congrArg (fun u : (ZMod 277)ˣ => (u:ZMod 277)) he

theorem restricted_five (s : Bool × Bool) (g : Local)
    (hg : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 → asAut g z = z^5) :
    (finiteCyclotomic 0 (restriction s g) : ZMod 277) = 5 := by
  apply finiteCyclotomic_value_of_action
  have hv : (5 : ZMod 277).val = 5 := by decide +kernel
  rw [hv]
  exact restriction_root_action s 0 5 g hg

/-- At every depth, reduction of the inverse twist uses the same base 111. -/
theorem restricted_scalar_power (r n : Nat) (s : Bool × Bool) (g : Local)
    (hg : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 → asAut g z = z^5) :
    modPrime n (finiteTwist r n (restriction s g) : ZMod (277^(n+1))) = 111 ^ r := by
  rw [reduce_twist]
  exact inverse_scalar_power r _ (restricted_five s g hg)

theorem restricted_weight_one (n : Nat) (s : Bool × Bool) (g : Local)
    (hg : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 → asAut g z = z^5) :
    modPrime n (finiteTwist 1 n (restriction s g) : ZMod (277^(n+1))) = 111 := by
  rw [restricted_scalar_power 1 n s g hg, pow_one]

theorem restricted_twist_nontrivial (r n : Nat) (hr : ¬276 ∣ r) (s : Bool × Bool) (g : Local)
    (hg : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 → asAut g z = z^5) :
    modPrime n (finiteTwist r n (restriction s g) : ZMod (277^(n+1))) ≠ 1 := by
  rw [reduce_twist]
  exact inverse_five_ne_one r hr _ (restricted_five s g hg)

theorem restricted_unit_difference (r n : Nat) (hr : ¬276 ∣ r) (s : Bool × Bool) (g : Local)
    (hg : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 → asAut g z = z^5) :
    IsUnit ((finiteTwist r n (restriction s g) : ZMod (277^(n+1))) - 1) ∧
      ¬ (277 : ℤ) ∣ (((finiteTwist r n (restriction s g) : ZMod (277^(n+1))).val : ℤ) - 1) := by
  have h := restricted_twist_nontrivial r n hr s g hg
  exact ⟨unit_difference n _ h,int_difference_nondivisible n _ h⟩

end Reimann.TameCyclotomicTame277
