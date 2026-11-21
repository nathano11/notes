import Reimann277.StrictArtinInput
import Reimann277.StrictLocal

namespace Reimann.TameStrictArtin277

open TameRestriction TameStrictLocal277 TameCyclotomicLocal277 TameArtin277

/-- Conditional only on class reciprocity once a continuous finite cocycle is given.
The two conditions on the left spell out unramifiedness away from 277 and
principality on each of the four local groups at 277, including conjugates. -/
theorem strict_class_character (r n : ℕ) (hr : ¬276 ∣ r) (e : ClassReciprocity r n)
    {c : Global → ℤ} (hc : Crossed (data (tameWitness r n hr)) c)
    (hcont : Continuous (fun g : Global => (c g : ZMod (277^(n+1))))) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), modulus n ∣ c x.val) ∧
      TameStrictInterface.Strict (places (tameWitness r n hr)) c) ↔
      ∃! η : SClassGroup r n →* Target n,
        ∀ x : globalKernel r n, η (toClassGroup e x) = kernelCharacter hc hcont x :=
  strict_class_character_of_witness (tameWitness r n hr) e hc hcont

end Reimann.TameStrictArtin277
