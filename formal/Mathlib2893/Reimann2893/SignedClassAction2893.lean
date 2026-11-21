import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.GroupTheory.Torsion

/-! The covariant action on the ideal class group and its two-primary subgroup.
The input is a field automorphism, with its action on the ring of integers
induced by the integral-closure construction. -/
namespace Reimann.SignedClassAction2893

open NumberField
open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [Field L]

/-- Transport of ideal classes through the induced isomorphism of integer rings. -/
noncomputable def transport (e : K ≃+* L) : ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 L) :=
  ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e)

/-- The chosen direction sends an integral ideal to its image under the automorphism. -/
theorem transport_mk0 [NumberField K] [NumberField L] (e : K ≃+* L) (I : (Ideal (𝓞 K))⁰) :
    transport e (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.val.map (RingOfIntegers.mapRingEquiv e),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.property)⟩ :=
  ClassGroup.mulEquiv_mk0 (RingOfIntegers.mapRingEquiv e) I

/-- The two-primary subgroup of ideal classes of the ring of integers. -/
abbrev twoClasses (F : Type*) [Field F] :=
  ↥(CommGroup.primaryComponent (ClassGroup (𝓞 F)) 2)

/-- Every homomorphism preserves the condition of being killed by a power of two. -/
theorem map_mem_two {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H)
    {x : G} (h : x ∈ CommGroup.primaryComponent G 2) :
    f x ∈ CommGroup.primaryComponent H 2 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← map_pow, hn, map_one]⟩

/-- Restrict the actual class group isomorphism to the two-primary class groups. -/
noncomputable def primaryTransport (e : K ≃+* L) : twoClasses K ≃* twoClasses L where
  toFun x := ⟨transport e x.val, map_mem_two (transport e).toMonoidHom x.property⟩
  invFun y := ⟨(transport e).symm y.val, map_mem_two (transport e).symm.toMonoidHom y.property⟩
  left_inv x := Subtype.ext ((transport e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((transport e).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext ((transport e).map_mul x.val y.val)

/-- On field automorphisms these are the forward maps on the full and two-primary class groups. -/
noncomputable abbrev forward (g : K ≃+* K) := transport g

noncomputable abbrev primaryForward (g : K ≃+* K) := primaryTransport g

theorem forward_on_classes (g : K ≃+* K) (x : twoClasses K) :
    (primaryForward g x).val = forward g x.val := rfl

theorem transport_identity (x : ClassGroup (𝓞 K)) : transport (RingEquiv.refl K) x = x := by
  have e : (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)).toRingHom = RingHom.id (𝓞 K) :=
    RingHom.ext fun _ => rfl
  change ClassGroup.map (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)).toRingHom
    (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)).injective x = x
  simp only [e, ClassGroup.map_id]

/-- Composition in the fields is carried to composition in their class groups
in the same order. -/
theorem transport_trans {F : Type*} [Field F] (e : K ≃+* L) (f : L ≃+* F)
    (x : ClassGroup (𝓞 K)) :
    transport (e.trans f) x = transport f (transport e x) := by
  have h : (RingOfIntegers.mapRingEquiv (e.trans f)).toRingHom =
      (RingOfIntegers.mapRingEquiv f).toRingHom.comp (RingOfIntegers.mapRingEquiv e).toRingHom :=
    RingHom.ext fun _ => rfl
  change ClassGroup.map (RingOfIntegers.mapRingEquiv (e.trans f)).toRingHom
    (RingOfIntegers.mapRingEquiv (e.trans f)).injective x =
    ClassGroup.map (RingOfIntegers.mapRingEquiv f).toRingHom (RingOfIntegers.mapRingEquiv f).injective
      (ClassGroup.map (RingOfIntegers.mapRingEquiv e).toRingHom (RingOfIntegers.mapRingEquiv e).injective x)
  simp only [h]
  exact (ClassGroup.map_map _ (RingOfIntegers.mapRingEquiv e).injective _
    (RingOfIntegers.mapRingEquiv f).injective x).symm

theorem primaryForward_trans (g h : K ≃+* K) (x : twoClasses K) :
    primaryForward (g.trans h) x = primaryForward h (primaryForward g x) :=
  Subtype.ext (transport_trans g h x.val)

/-- The full automorphism group of the field acts on the two-primary ideal classes. -/
noncomputable def primaryAction (F : Type*) [Field F] :
    (F ≃+* F) →* (twoClasses F ≃* twoClasses F) where
  toFun := primaryForward
  map_one' := MulEquiv.ext fun x => Subtype.ext (transport_identity x.val)
  map_mul' g h := MulEquiv.ext fun x => primaryForward_trans h g x

/-- In a finite cyclotomic layer any proven period of the field generator
is also a period of its action on the two-primary class group. -/
theorem primaryForward_period (g : K ≃+* K) (d : ℕ) (hd : g ^ d = 1) :
    primaryForward g ^ d = 1 := by
  change primaryAction K g ^ d = 1
  rw [← map_pow, hd, map_one]

end Reimann.SignedClassAction2893
