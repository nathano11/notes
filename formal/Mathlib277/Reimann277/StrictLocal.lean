import Reimann277.TameGaloisLift
import Reimann277.StrictLocalInput

namespace Reimann.TameStrictLocal277

open TameCyclotomicLocal277 TameRestriction

/-- One automorphism of the local algebraic closure works at every labeled place. -/
noncomputable def tameWitness (r n : ℕ) (hr : ¬276 ∣ r) : Witness r n where
  generator := TameGaloisLift277.localFive
  nontrivial s := (TameGaloisLift277.localFive_unit_difference r n hr s).2

theorem tameWitness_generator (r n : ℕ) (hr : ¬276 ∣ r) :
    (tameWitness r n hr).generator = TameGaloisLift277.localFive := rfl

theorem arithmetic_strict_iff_split (r n : ℕ) (hr : ¬276 ∣ r) {c : Global → ℤ}
    (hc : Crossed (data (tameWitness r n hr)) c) :
    TameStrictInterface.Strict (places (tameWitness r n hr)) c ↔
      ∀ x : globalKernel r n, x ∈ atPlaces r n → modulus n ∣ c x.val :=
  strict_iff_split (tameWitness r n hr) hc

end Reimann.TameStrictLocal277
