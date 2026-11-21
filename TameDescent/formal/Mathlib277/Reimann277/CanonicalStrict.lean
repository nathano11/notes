import Reimann277.CanonicalDecomposition
import Reimann277.StrictReciprocity

namespace Reimann.TameStrictReciprocity277

open TameArtin277 TameCyclotomicLocal277 TameStrictLocal277 TameStrictArtin277
open TameArithmeticSymbol277 TameRestriction
open TameCanonicalDecomposition277 TameFinitePlaces277 TameBiquadraticField277

theorem strict_at_canonical_places {r n : ℕ} (w : Witness r n) {c : Global → ℤ}
    (hc : Crossed (data w) c) : TameStrictInterface.Strict (places w) c ↔
      ∀ (v : Above Biquadratic) (g : Global) (y : completionKernel r n v),
        modulus n ∣ c (conjugatedAt r n v g y).val := by
  rw [strict_iff_split w hc]
  constructor
  · intro h v g y
    exact h _ ((atPlaces_iff_canonical r n _).mpr ⟨v,g,y,rfl⟩)
  · intro h x hx
    obtain ⟨v,g,y,rfl⟩ := (atPlaces_iff_canonical r n x).mp hx
    exact h v g y

theorem canonical_strict_class_character (r n : ℕ) (hr : ¬276 ∣ r) (a : Input r n)
    {c : Global → ℤ} (hc : Crossed (data (tameWitness r n hr)) c)
    (hcont : Continuous (fun g : Global => (c g : ZMod (277^(n+1))))) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), modulus n ∣ c x.val) ∧
      ∀ (v : Above Biquadratic) (g : Global) (y : completionKernel r n v),
        modulus n ∣ c (conjugatedAt r n v g y).val) ↔
      ∃! η : SClassGroup r n →* Target n, Twisted η ∧
        ∀ x : globalKernel r n, η (toClassGroup (reciprocity a) x) = kernelCharacter hc hcont x := by
  rw [← strict_at_canonical_places (tameWitness r n hr) hc]
  exact strict_class_character_of_symbol r n hr a hc hcont

end Reimann.TameStrictReciprocity277
