import Reimann277.CyclotomicLocal
import Reimann277.Inertia

namespace Reimann.TameCyclotomicInertia277

open TameBiquadraticField277 TameCyclotomicLocal277 TameInertia277

/-- Inertia at residue characteristic different from 277 acts trivially on
the finite cyclotomic character at every positive coefficient depth. -/
theorem finiteCyclotomic_inertia (P : Ideal (Integers (AlgebraicClosure Biquadratic)))
    (hP : P.IsMaximal) (hp : (277 : Integers (AlgebraicClosure Biquadratic)) ∉ P)
    {g : Global} (hg : g ∈ inertia (K := Biquadratic) P) (n : Nat) :
    finiteCyclotomic n g = 1 := by
  apply Units.ext
  change (finiteCyclotomic n g : ZMod (277^(n+1))) = 1
  apply finiteCyclotomic_value_of_action
  intro z hz
  have hgt : 1 < (277 : Nat)^(n+1) := one_lt_pow₀ (by decide) (Nat.succ_ne_zero n)
  rw [ZMod.val_one'' hgt.ne',pow_one]
  exact fixes_power_root P hP hp hg n hz

theorem inertia_le_kernel (P : Ideal (Integers (AlgebraicClosure Biquadratic)))
    (hP : P.IsMaximal) (hp : (277 : Integers (AlgebraicClosure Biquadratic)) ∉ P) (r n : Nat) :
    inertia (K := Biquadratic) P ≤ globalKernel r n := by
  intro g hg
  change finiteCyclotomic n (show Global from g) ^ (-(r : ℤ)) = 1
  rw [finiteCyclotomic_inertia P hP hp (g := (show Global from g)) hg n, one_zpow]

end Reimann.TameCyclotomicInertia277
