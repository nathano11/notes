import Reimann277.IdealAction
import Reimann277.StrictLocalInput

namespace Reimann.TameStrictArtin277

open TameRestriction TameStrictLocal277 TameCyclotomicLocal277 TameArtin277

abbrev Target (n : ℕ) := Multiplicative (ZMod (277^(n+1)))

theorem residue_eq_of_difference {n : ℕ} {a b : ℤ} (h : modulus n ∣ a-b) :
    (a : ZMod (277^(n+1))) = (b : ZMod (277^(n+1))) := by
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a-b) (277^(n+1))).mpr h
  rwa [Int.cast_sub,sub_eq_zero] at hz

theorem residue_additive {r n : ℕ} {w : Witness r n} {c : Global → ℤ}
    (hc : Crossed (data w) c) (x y : globalKernel r n) :
    (c ((x*y : globalKernel r n) : Global) : ZMod (277^(n+1))) =
      (c x.val : ZMod (277^(n+1))) + (c y.val : ZMod (277^(n+1))) := by
  rw [← Int.cast_add]
  exact residue_eq_of_difference (crossed_kernel_left hc x.property y.val)

theorem residue_one {r n : ℕ} {w : Witness r n} {c : Global → ℤ}
    (hc : Crossed (data w) c) : (c 1 : ZMod (277^(n+1))) = 0 := by
  have h : (c 1 : ZMod (277^(n+1))) = (c 1 : ZMod (277^(n+1))) + (c 1 : ZMod (277^(n+1))) := by
    simpa using residue_additive hc (1 : globalKernel r n) 1
  exact add_left_cancel (a := (c 1 : ZMod (277^(n+1)))) ((add_zero _).trans h).symm

/-- Restriction is an ordinary continuous character on the kernel of the twist. -/
noncomputable def kernelCharacter {r n : ℕ} {w : Witness r n} {c : Global → ℤ}
    (hc : Crossed (data w) c) (hcont : Continuous (fun g : Global => (c g : ZMod (277^(n+1))))) :
    globalKernel r n →ₜ* Target n where
  toFun x := Multiplicative.ofAdd (c x.val : ZMod (277^(n+1)))
  map_one' := congrArg Multiplicative.ofAdd (residue_one hc)
  map_mul' x y := congrArg Multiplicative.ofAdd (residue_additive hc x y)
  continuous_toFun := hcont.comp continuous_subtype_val

theorem kernelCharacter_one_iff {r n : ℕ} {w : Witness r n} {c : Global → ℤ}
    (hc : Crossed (data w) c) (hcont) (x : globalKernel r n) :
    kernelCharacter hc hcont x = 1 ↔ modulus n ∣ c x.val :=
  ZMod.intCast_zmod_eq_zero_iff_dvd _ _

theorem kernelCharacter_twist {r n : ℕ} {w : Witness r n} {c : Global → ℤ}
    (hc : Crossed (data w) c) (hcont) (g : Global) (x : globalKernel r n) :
    (kernelCharacter hc hcont (TameIdealAction277.conjugateKernel g x)).toAdd =
      (finiteTwist r n g : ZMod (277^(n+1))) * (kernelCharacter hc hcont x).toAdd := by
  have h := residue_eq_of_difference ((restrictCharacter hc).equivariant g x.property)
  change (c (g*x.val*g⁻¹) : ZMod (277^(n+1))) = ((scalar r n g * c x.val : ℤ) : ZMod (277^(n+1))) at h
  rw [Int.cast_mul,scalar_cast] at h
  exact h

theorem ideal_character_twist {r n : ℕ} {w : Witness r n} {c : Global → ℤ}
    (hc : Crossed (data w) c) (hcont) (e : ClassReciprocity r n)
    (he : TameIdealAction277.ArtinEquivariant e) (η : SClassGroup r n →* Target n)
    (hη : ∀ x, η (toClassGroup e x) = kernelCharacter hc hcont x)
    (g : Global) (a : SClassGroup r n) :
    (η (TameIdealAction277.onClass r n g a)).toAdd =
      (finiteTwist r n g : ZMod (277^(n+1))) * (η a).toAdd := by
  obtain ⟨x,rfl⟩ := toClassGroup_surjective e a
  rw [← he,hη,hη]
  exact kernelCharacter_twist hc hcont g x

/-- Conditional only on class reciprocity once a continuous finite cocycle is given.
The two conditions on the left spell out unramifiedness away from 277 and
principality on each of the four local groups at 277, including conjugates. -/
theorem strict_class_character_of_witness {r n : ℕ} (w : Witness r n) (e : ClassReciprocity r n)
    {c : Global → ℤ} (hc : Crossed (data w) c)
    (hcont : Continuous (fun g : Global => (c g : ZMod (277^(n+1))))) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), modulus n ∣ c x.val) ∧
      TameStrictInterface.Strict (places w) c) ↔
      ∃! η : SClassGroup r n →* Target n,
        ∀ x : globalKernel r n, η (toClassGroup e x) = kernelCharacter hc hcont x := by
  rw [← class_character_descent e (kernelCharacter hc hcont), strict_iff_split w hc]
  constructor
  · rintro ⟨ha,hs⟩
    exact ⟨fun x hx => (kernelCharacter_one_iff hc hcont x).mpr (ha x hx),
      fun x hx => (kernelCharacter_one_iff hc hcont x).mpr (hs x hx)⟩
  · rintro ⟨ha,hs⟩
    exact ⟨fun x hx => (kernelCharacter_one_iff hc hcont x).mp (ha x hx),
      fun x hx => (kernelCharacter_one_iff hc hcont x).mp (hs x hx)⟩

end Reimann.TameStrictArtin277
