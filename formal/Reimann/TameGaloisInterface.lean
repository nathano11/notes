import Reimann.TameContinuity
import Reimann.TameStrictInterface

namespace Reimann.TameGaloisInterface

open Reimann.Transfer Reimann.TameRestriction Reimann.TameContinuity

/-- Continuity of scalar residues on the kernel with its subspace topology. -/
def ContinuousOnKernel (τ : Topology G) (N : G → Prop) (f : Subtype N → Int) : Prop :=
  ∀ V : Int → Prop, RelativeOpen τ N (fun x => V (f x))

/-- Pulling any scalar function back along a continuous map to a discrete
class group gives a continuous character whenever the functions agree pointwise. -/
theorem pullback_continuous {τ : Topology G} {N : G → Prop} {π : Subtype N → B}
    (hπ : ∀ V : B → Prop, RelativeOpen τ N (fun x => V (π x)))
    {f : Subtype N → Int} {φ : B → Int} (h : ∀ x, f x = φ (π x)) :
    ContinuousOnKernel τ N f := by
  intro V
  have he : (fun x => V (f x)) = (fun x => V (φ (π x))) := by
    funext x
    rw [h x]
  rw [he]
  exact hπ (fun b => V (φ b))

open Reimann.TameStrictInterface

variable {G B : Type} {P : GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} {L : Places T} {H : GroupLaw B}

/-- Exact data to construct in the number field. The kernel test quantifies
only over continuous upstairs homomorphisms annihilating the local kernels. -/
structure ContinuousArtinInput (τ : Topology G) (L : Places T) (H : GroupLaw B) where
  quotient : TameClassField.ArtinQuotient (kernelGroup T) H
  discreteQuotient : ∀ V : B → Prop, RelativeOpen τ T.kernel
    (fun x => V (quotient.proj.app x))
  action : G → B → B
  conjugation : ∀ g (x : Subtype T.kernel),
    quotient.proj.app ⟨conjugate P g x.val,T.conj_in g x.property⟩ =
      action g (quotient.proj.app x)
  split : ∀ x, LocalKernel L x → quotient.proj.app x = H.zero
  reciprocityKernel : ∀ χ : Hom (kernelGroup T) (TameClassField.residueGroup m),
    ContinuousOnKernel τ T.kernel (fun x => (χ.app x).val) →
    (∀ x, LocalKernel L x → χ.app x = (TameClassField.residueGroup m).zero) →
    TameClassField.KillsKernel quotient χ

def artin {τ : Topology G} (A : ContinuousArtinInput τ L H) : ArtinData L H where
  quotient := A.quotient
  action := A.action
  conjugation := A.conjugation
  local_zero := A.split
  admissible χ := ContinuousOnKernel τ T.kernel (fun x => (χ.app x).val)
  pullback_admissible := by
    intro ψ χ h
    exact pullback_continuous (φ := fun b => (ψ.app b).val) A.discreteQuotient
      (fun x => congrArg Subtype.val (h x))
  kernel_test := A.reciprocityKernel

/-- The predicate selecting the source quotient is exactly continuity of the
original crossed homomorphism, including any principal correction. -/
theorem admissible_iff_continuous {τ : Topology G} (A : ContinuousArtinInput τ L H)
    (top : GroupTopology P τ)
    (hscalar : Continuous τ (discrete Int) (fun g => T.scalar g % m))
    {c : G → Int} (hc : Crossed T c) :
    (artin A).admissible (characterHom (restrictCharacter hc)) ↔
      Continuous τ (discrete Int) (fun g => c g % m) :=
  (crossed_continuous_iff_restriction top hscalar hc).symm

/-- Continuous strict finite-coefficient classes and equivariant class
characters correspond by explicit inverse maps, with the Artin data displayed. -/
theorem continuous_strict_class_correspondence {τ : Topology G}
    (A : ContinuousArtinInput τ L H) (top : GroupTopology P τ)
    (hscalar : Continuous τ (discrete Int) (fun g => T.scalar g % m)) :
    (∀ {c : G → Int} (hc : Crossed T c),
      (artin A).admissible (characterHom (restrictCharacter hc)) ↔
        Continuous τ (discrete Int) (fun g => c g % m)) ∧
    (∀ z : StrictClass (artin A),
      fromClassCharacter (artin A) (toClassCharacter (artin A) z) = z) ∧
    (∀ f : ClassCharacter (artin A),
      toClassCharacter (artin A) (fromClassCharacter (artin A) f) = f) :=
  ⟨fun hc => admissible_iff_continuous A top hscalar hc,
    strict_class_character_roundtrips (artin A)⟩

end Reimann.TameGaloisInterface
