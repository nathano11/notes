import Reimann277.ArithmeticSymbol
import Reimann277.StrictArtin
import Reimann277.ClassOrientation
import Reimann277.ResidueCharacter

namespace Reimann.TameStrictReciprocity277

open TameArtin277 TameCyclotomicLocal277 TameStrictLocal277 TameStrictArtin277
open TameArithmeticSymbol277 TameIdealAction277 TameRestriction TameResidueCharacter277

theorem strict_class_character_of_symbol (r n : ℕ) (hr : ¬276 ∣ r) (a : Input r n)
    {c : Global → ℤ} (hc : Crossed (data (tameWitness r n hr)) c)
    (hcont : Continuous (fun g : Global => (c g : ZMod (277^(n+1))))) :
    ((∀ x ∈ TameInertia277.away (globalKernel r n), modulus n ∣ c x.val) ∧
      TameStrictInterface.Strict (places (tameWitness r n hr)) c) ↔
      ∃! η : SClassGroup r n →* Target n, Twisted η ∧
        ∀ x : globalKernel r n, η (toClassGroup (reciprocity a) x) = kernelCharacter hc hcont x := by
  let e := reciprocity a
  rw [strict_class_character r n hr e hc hcont]
  constructor
  · rintro ⟨η,hη,hu⟩
    exact ⟨η, ⟨ideal_character_twist hc hcont e (reciprocity_equivariant a) η hη,hη⟩,
      fun θ hθ => hu θ hθ.2⟩
  · rintro ⟨η,hη,hu⟩
    refine ⟨η,hη.2,?_⟩
    intro θ hθ
    exact hu θ ⟨ideal_character_twist hc hcont e (reciprocity_equivariant a) θ hθ,hθ⟩

/-- Equality of the descended characters is equality of cohomology classes. -/
theorem characters_equal_iff_principal {r n : ℕ} {w : Witness r n}
    {c d : Global → ℤ} (hc : Crossed (data w) c) (hd : Crossed (data w) d)
    (cc cd) (e : ClassReciprocity r n) (η θ : SClassGroup r n →* Target n)
    (hη : ∀ x, η (toClassGroup e x) = kernelCharacter hc cc x)
    (hθ : ∀ x, θ (toClassGroup e x) = kernelCharacter hd cd x) :
    η = θ ↔ ∃ b : ℤ, ∀ g, modulus n ∣ c g-d g-(scalar r n g-1)*b := by
  refine Iff.trans ?_ (restrictions_equal_iff_principal hc hd)
  constructor
  · rintro rfl x
    exact congrArg Multiplicative.toAdd ((hη x).symm.trans (hθ x))
  · intro h
    apply MonoidHom.ext
    intro y
    obtain ⟨x,rfl⟩ := toClassGroup_surjective e y
    rw [hη,hθ]
    exact congrArg Multiplicative.ofAdd (h x)

noncomputable def pullback {r n : ℕ} (w : Witness r n) (e : ClassReciprocity r n)
    (he : ArtinEquivariant e) (η : SClassGroup r n →* Target n) (hη : Twisted η) :
    ResidueCharacter (data w) where
  value x := (η (toClassGroup e ⟨x.val,x.property⟩)).toAdd
  additive {x y} hx hy := congrArg Multiplicative.toAdd
    ((η.comp (toClassGroup e)).map_mul ⟨x,hx⟩ ⟨y,hy⟩)
  equivariant g {x} hx := by
    change (η (toClassGroup e (conjugateKernel g ⟨x,hx⟩))).toAdd =
      (scalar r n g : ZMod (277^(n+1))) * _
    rw [he,hη,scalar_cast]

noncomputable def lift {r n : ℕ} (w : Witness r n) (e : ClassReciprocity r n)
    (he : ArtinEquivariant e) (η : SClassGroup r n →* Target n) (hη : Twisted η) : Global → ℤ :=
  extend (realize (pullback w e he η hη))

theorem lift_crossed {r n : ℕ} (w : Witness r n) (e : ClassReciprocity r n)
    (he : ArtinEquivariant e) (η : SClassGroup r n →* Target n) (hη : Twisted η) :
    Crossed (data w) (lift w e he η hη) :=
  extend_crossed_residue _

theorem lift_at_kernel {r n : ℕ} (w : Witness r n) (e : ClassReciprocity r n)
    (he : ArtinEquivariant e) (η : SClassGroup r n →* Target n) (hη : Twisted η)
    (x : globalKernel r n) :
    (lift w e he η hη x.val : ZMod (277^(n+1))) = (η (toClassGroup e x)).toAdd :=
  extend_at_kernel (pullback w e he η hη) x

noncomputable def commutatorMap {r n : ℕ} (w : Witness r n) (g : Global) : globalKernel r n :=
  ⟨_, (data w).comm_in g⟩

theorem commutatorMap_continuous {r n : ℕ} (w : Witness r n) : Continuous (commutatorMap w) := by
  apply Continuous.subtype_mk
  let t : Global := restriction (false,false) w.generator
  change Continuous (fun g : Global => ((t*g)*t⁻¹)*g⁻¹)
  have ht : Continuous (fun _ : Global => t) := continuous_const
  have htinv : Continuous (fun _ : Global => t⁻¹) := continuous_const
  exact ((ht.mul continuous_id).mul htinv).mul continuous_id.inv

theorem lift_continuous {r n : ℕ} (w : Witness r n) (e : ClassReciprocity r n)
    (he : ArtinEquivariant e) (η : SClassGroup r n →* Target n) (hη : Twisted η) :
    Continuous (fun g => (lift w e he η hη g : ZMod (277^(n+1)))) := by
  have h : Continuous (fun x : globalKernel r n => (η (toClassGroup e x)).toAdd) := by
    apply continuous_def.mpr
    intro V _
    exact class_projection_open_preimage e ((fun c => (η c).toAdd) ⁻¹' V)
  have hformula : (fun g => (lift w e he η hη g : ZMod (277^(n+1)))) =
      fun g => ((data w).inverse : ZMod (277^(n+1))) *
        (η (toClassGroup e (commutatorMap w g))).toAdd := funext (extend_formula (pullback w e he η hη))
  rw [hformula]
  exact continuous_const.mul (h.comp (commutatorMap_continuous w))

theorem lift_at_relations {r n : ℕ} (w : Witness r n) (e : ClassReciprocity r n)
    (he : ArtinEquivariant e) (η : SClassGroup r n →* Target n) (hη : Twisted η)
    (x : globalKernel r n) (hx : x ∈ localRelations r n) : modulus n ∣ lift w e he η hη x.val := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [lift_at_kernel]
  have h : project r n x = 1 := TameSplitQuotient277.project_local _ hx
  change (η (e (project r n x))).toAdd = 0
  rw [h,map_one,map_one]
  rfl

/-- Every character on the inverse-twisted ideal-class line has a strict continuous
cocycle representative. The same primitive measures equality of representatives globally. -/
theorem twisted_character_has_representative (r n : ℕ) (hr : ¬276 ∣ r)
    (a : Input r n) (η : SClassGroup r n →* Target n) (hη : Twisted η) :
    ∃ c : Global → ℤ, Crossed (data (tameWitness r n hr)) c ∧
      Continuous (fun g : Global => (c g : ZMod (277^(n+1)))) ∧
      (∀ x ∈ TameInertia277.away (globalKernel r n), modulus n ∣ c x.val) ∧
      TameStrictInterface.Strict (places (tameWitness r n hr)) c ∧
      ∀ x : globalKernel r n, (c x.val : ZMod (277^(n+1))) = (η (toClassGroup (reciprocity a) x)).toAdd := by
  let w := tameWitness r n hr
  let e := reciprocity a
  have he : ArtinEquivariant e := reciprocity_equivariant a
  refine ⟨lift w e he η hη,lift_crossed w e he η hη,lift_continuous w e he η hη,?_,?_,lift_at_kernel w e he η hη⟩
  · exact fun x hx => lift_at_relations w e he η hη x (Or.inl hx)
  · exact (strict_iff_split w (lift_crossed w e he η hη)).mpr
      (fun x hx => lift_at_relations w e he η hη x (Or.inr hx))

end Reimann.TameStrictReciprocity277
