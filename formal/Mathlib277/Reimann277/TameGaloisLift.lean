import Reimann277.CyclotomicTame
import Reimann277.TameGenerator
import Reimann.TameAdicDomain277

namespace Reimann.TameGaloisLift277

open TameCyclotomicLocal277 TameCyclotomicTame277

local instance fact277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- Integer representative in [0,277^(n+1)) of the scalar on the (-r)-twist. -/
noncomputable def scalarValue (r n : Nat) (g : Global) : ℤ :=
  (finiteTwist r n g : ZMod (277^(n+1))).val

/-- Choose the local automorphism once, before choosing the place, weight or depth. -/
noncomputable def localFive : Local :=
  Classical.choose TameGenerator277.exists_local_five

theorem localFive_root_action : ∀ z : AlgebraicClosure ℚ_[277], z^277 = 1 →
    asAut localFive z = z^5 :=
  Classical.choose_spec TameGenerator277.exists_local_five

theorem localFive_scalar (r n : Nat) (s : Bool × Bool) :
    TameCyclotomicUnits277.modPrime n
      (finiteTwist r n (restriction s localFive) : ZMod (277^(n+1))) = 111 ^ r :=
  restricted_scalar_power r n s localFive localFive_root_action

theorem localFive_unit_difference (r n : Nat) (hr : ¬276 ∣ r) (s : Bool × Bool) :
    IsUnit ((finiteTwist r n (restriction s localFive) : ZMod (277^(n+1))) - 1) ∧
      ¬ (277 : ℤ) ∣ scalarValue r n (restriction s localFive) - 1 :=
  restricted_unit_difference r n hr s localFive localFive_root_action

theorem uniform_local_scalar :
    ∃ g : Local, ∀ (r n : Nat) (s : Bool × Bool),
      TameCyclotomicUnits277.modPrime n
        (finiteTwist r n (restriction s g) : ZMod (277^(n+1))) = 111 ^ r :=
  ⟨localFive,localFive_scalar⟩

theorem weight_one_local_lift :
    ∃ g : Local, ∀ (n : Nat) (s : Bool × Bool),
      TameCyclotomicUnits277.modPrime n
        (finiteTwist 1 n (restriction s g) : ZMod (277^(n+1))) = 111 :=
  ⟨localFive,fun n s => restricted_weight_one n s localFive localFive_root_action⟩

/-- One actual absolute local automorphism supplies the required inverse-twist
unit difference at all four signed places. -/
theorem uniform_local_lift :
    ∃ g : Local, ∀ (r n : Nat), ¬276 ∣ r → ∀ s : Bool × Bool,
      IsUnit ((finiteTwist r n (restriction s g) : ZMod (277^(n+1))) - 1) ∧
      ¬ (277 : ℤ) ∣ scalarValue r n (restriction s g) - 1 :=
  ⟨localFive,localFive_unit_difference⟩

theorem simultaneous_local_lift (r n : Nat) (hr : ¬276 ∣ r) :
    ∃ g : Local, ∀ s : Bool × Bool,
      IsUnit ((finiteTwist r n (restriction s g) : ZMod (277^(n+1))) - 1) ∧
      ¬ (277 : ℤ) ∣ scalarValue r n (restriction s g) - 1 := by
  obtain ⟨g,hg⟩ := uniform_local_lift
  exact ⟨g,hg r n hr⟩

theorem simultaneous_local_bezout (r n : Nat) (hr : ¬276 ∣ r) :
    ∃ g : Local, ∀ s : Bool × Bool, ∃ i j : ℤ,
      (scalarValue r n (restriction s g)-1)*i + (277 : ℤ)^(n+1)*j = 1 := by
  obtain ⟨g,hg⟩ := simultaneous_local_lift r n hr
  exact ⟨g,fun s => TameAdicDomain277.unit_at_all_depths _ (hg s).2 (n+1)⟩

/-- A global tame lift is obtained using either sign for each generator. -/
theorem global_bezout (r n : Nat) (hr : ¬276 ∣ r) :
    ∃ g : Global, ∃ i j : ℤ, (scalarValue r n g-1)*i + (277 : ℤ)^(n+1)*j = 1 := by
  obtain ⟨g,hg⟩ := simultaneous_local_bezout r n hr
  exact ⟨restriction (false,false) g,hg (false,false)⟩

end Reimann.TameGaloisLift277
