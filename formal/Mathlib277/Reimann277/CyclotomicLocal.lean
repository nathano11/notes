import Reimann277.AbsoluteDecomposition
import Reimann277.CyclotomicReduction
import Reimann277.CyclotomicRoots
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.ZPow
import Mathlib.Topology.Instances.ZMod

namespace Reimann.TameCyclotomicLocal277

open TameBiquadraticField277 TamePadicEmbeddings277
open scoped Topology

local instance fact277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

abbrev Scalars (n : Nat) := (ZMod (277^(n+1)))ˣ

/-- The absolute cyclotomic character, with the Krull topology on its source. -/
noncomputable def fieldCharacter (K : Type*) [Field K] :
    Field.absoluteGaloisGroup K →ₜ* ℤ_[277]ˣ where
  toMonoidHom := (cyclotomicCharacter (AlgebraicClosure K) 277).comp
    (MulSemiringAction.toRingAut (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K))
  continuous_toFun := cyclotomicCharacter.continuous 277 K (AlgebraicClosure K)

noncomputable def cyclotomic : Global →ₜ* ℤ_[277]ˣ := fieldCharacter Biquadratic

theorem enough_roots (i : Nat) : HasEnoughRootsOfUnity (AlgebraicClosure Biquadratic) (277^i) :=
  TameCyclotomicRoots277.enough _ _

noncomputable def reducedCharacter (K : Type*) [Field K] (n : Nat) :
    Field.absoluteGaloisGroup K →ₜ* Scalars n where
  toMonoidHom := (Units.map (PadicInt.toZModPow (n+1) : ℤ_[277] →+* ZMod (277^(n+1))).toMonoidHom).comp
    (fieldCharacter K).toMonoidHom
  continuous_toFun := Continuous.of_coeHom_comp
    ((continuous_reduction (n+1)).comp (Units.continuous_val.comp (fieldCharacter K).continuous))

noncomputable def finiteCyclotomic (n : Nat) : Global →ₜ* Scalars n := reducedCharacter Biquadratic n

noncomputable def localFiniteCyclotomic (n : Nat) : Local →ₜ* Scalars n := reducedCharacter ℚ_[277] n

theorem field_root_action (K : Type*) [Field K] [CharZero K] (n : Nat)
    (g : Field.absoluteGaloisGroup K) (z : AlgebraicClosure K) (hz : z^277^(n+1) = 1) :
    asAut g z = z ^ ((reducedCharacter K n g : ZMod (277^(n+1))).val) := by
  letI (i : Nat) : HasEnoughRootsOfUnity (AlgebraicClosure K) (277^i) :=
    TameCyclotomicRoots277.enough _ _
  exact cyclotomicCharacter.spec 277
    (MulSemiringAction.toRingAut (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) _ g) z hz

theorem root_action (n : Nat) (g : Global) (z : AlgebraicClosure Biquadratic)
    (hz : z ^ 277^(n+1) = 1) :
    asAut g z = z ^ ((finiteCyclotomic n g : ZMod (277^(n+1))).val) :=
  field_root_action Biquadratic n g z hz

/-- A primitive root recovers the finite character from the power action. -/
theorem finiteCyclotomic_value_of_action (n : Nat) (g : Global) (a : ZMod (277^(n+1)))
    (h : ∀ z : AlgebraicClosure Biquadratic, z^277^(n+1) = 1 → asAut g z = z^a.val) :
    (finiteCyclotomic n g : ZMod (277^(n+1))) = a := by
  letI : HasEnoughRootsOfUnity (AlgebraicClosure Biquadratic) (277^(n+1)) := enough_roots _
  obtain ⟨z,hz⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure Biquadratic) (277^(n+1))
  apply ZMod.val_injective
  apply hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  exact (root_action n g z hz.pow_eq_one).symm.trans (h z hz.pow_eq_one)

/-- At depth n+1, the action on the (-r)-twist is the inverse r-th power. -/
noncomputable def finiteTwist (r n : Nat) : Global →ₜ* Scalars n where
  toFun g := finiteCyclotomic n g ^ (-(r : ℤ))
  map_one' := by simp
  map_mul' g h := by rw [map_mul,mul_zpow]
  continuous_toFun := (finiteCyclotomic n).continuous.zpow _

theorem finiteTwist_apply (r n : Nat) (g : Global) :
    finiteTwist r n g = finiteCyclotomic n g ^ (-(r : ℤ)) := rfl

noncomputable def globalKernel (r n : Nat) : Subgroup Global := (finiteTwist r n).toMonoidHom.ker

theorem mem_globalKernel_iff (r n : Nat) (g : Global) :
    g ∈ globalKernel r n ↔ finiteCyclotomic n g ^ (-(r : ℤ)) = 1 := Iff.rfl

instance globalKernelNormal (r n : Nat) : (globalKernel r n).Normal :=
  MonoidHom.normal_ker _

theorem globalKernel_open (r n : Nat) : IsOpen (globalKernel r n : Set Global) :=
  (isOpen_discrete ({1} : Set (Scalars n))).preimage (finiteTwist r n).continuous

theorem globalKernel_closed (r n : Nat) : IsClosed (globalKernel r n : Set Global) :=
  (isClosed_singleton (X := Scalars n) (x := 1)).preimage (finiteTwist r n).continuous

noncomputable def cutField (r n : Nat) : IntermediateField Biquadratic (AlgebraicClosure Biquadratic) :=
  IntermediateField.fixedField (globalKernel r n)

theorem cutField_fixing (r n : Nat) : (cutField r n).fixingSubgroup = globalKernel r n := by
  let H : ClosedSubgroup (AlgebraicClosure Biquadratic ≃ₐ[Biquadratic] AlgebraicClosure Biquadratic) :=
    ⟨globalKernel r n,globalKernel_closed r n⟩
  exact InfiniteGalois.fixingSubgroup_fixedField H

theorem cutField_finite_galois (r n : Nat) :
    FiniteDimensional Biquadratic (cutField r n) ∧ IsGalois Biquadratic (cutField r n) := by
  apply (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (cutField r n)).mp
  rw [cutField_fixing]
  exact ⟨globalKernel_open r n,globalKernelNormal r n⟩

theorem cutField_isAlgClosure (r n : Nat) :
    IsAlgClosure (cutField r n) (AlgebraicClosure Biquadratic) :=
  ⟨inferInstance,Algebra.IsAlgebraic.tower_top (K := Biquadratic) _⟩

/-- Model the Galois group of the cut field in the existing ambient closure. -/
noncomputable def kernelAutEquiv (r n : Nat) :
    globalKernel r n ≃*
      (AlgebraicClosure Biquadratic ≃ₐ[cutField r n] AlgebraicClosure Biquadratic) := by
  let e : globalKernel r n ≃* (cutField r n).fixingSubgroup := {
    toFun g := ⟨asAut g.val, by rw [cutField_fixing]; exact g.property⟩
    invFun g := ⟨g.val, by rw [← cutField_fixing]; exact g.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact e.trans (cutField r n).fixingSubgroupEquiv

theorem kernelAutEquiv_apply (r n : Nat) (g : globalKernel r n)
    (z : AlgebraicClosure Biquadratic) : kernelAutEquiv r n g z = asAut g.val z := rfl

/-- Transport to mathlib's chosen algebraic closure over the cut field. -/
noncomputable def kernelAbsoluteEquiv (r n : Nat) :
    globalKernel r n ≃* Field.absoluteGaloisGroup (cutField r n) :=
  letI := cutField_isAlgClosure r n
  (kernelAutEquiv r n).trans
    (IsAlgClosure.equiv (cutField r n) (AlgebraicClosure Biquadratic)
      (AlgebraicClosure (cutField r n))).autCongr

theorem restriction_finiteCyclotomic (s : Bool × Bool) (n : Nat) (g : Local) :
    finiteCyclotomic n (restriction s g) = localFiniteCyclotomic n g := by
  apply Units.ext
  apply finiteCyclotomic_value_of_action
  exact restriction_root_action s n _ g (field_root_action ℚ_[277] n g)

theorem local_twist_value (r n : Nat) (s : Bool × Bool) (g : Local) :
    finiteTwist r n (restriction s g) = localFiniteCyclotomic n g ^ (-(r : ℤ)) := by
  rw [finiteTwist_apply,restriction_finiteCyclotomic]

noncomputable def localKernel (r n : Nat) (s : Bool × Bool) : Subgroup Local :=
  (globalKernel r n).comap (restriction s).toMonoidHom

theorem mem_localKernel_iff (r n : Nat) (s : Bool × Bool) (x : Local) :
    x ∈ localKernel r n s ↔ finiteTwist r n (restriction s x) = 1 := Iff.rfl

theorem localKernel_open (r n : Nat) (s : Bool × Bool) :
    IsOpen (localKernel r n s : Set Local) :=
  (globalKernel_open r n).preimage (restriction s).continuous

theorem localKernel_intrinsic (r n : Nat) (s : Bool × Bool) (x : Local) :
    x ∈ localKernel r n s ↔ localFiniteCyclotomic n x ^ (-(r : ℤ)) = 1 := by
  rw [mem_localKernel_iff,local_twist_value]

theorem localKernel_same (r n : Nat) (s t : Bool × Bool) :
    localKernel r n s = localKernel r n t := by
  ext x
  rw [localKernel_intrinsic,localKernel_intrinsic]

noncomputable def upstairsRestriction (r n : Nat) (s : Bool × Bool) :
    localKernel r n s →ₜ* globalKernel r n where
  toMonoidHom := ((restriction s).toMonoidHom.comp (localKernel r n s).subtype).codRestrict _
    (fun x => x.property)
  continuous_toFun := ((restriction s).continuous.comp continuous_subtype_val).subtype_mk _

theorem upstairsRestriction_value (r n : Nat) (s : Bool × Bool) (x : localKernel r n s) :
    (upstairsRestriction r n s x : Global) = restriction s x.val := rfl

/-- Include all global conjugates of each chosen lift of a bottom place. -/
noncomputable def conjugatedRestriction (r n : Nat) (s : Bool × Bool) (a : Global) :
    localKernel r n s →ₜ* globalKernel r n where
  toFun x := ⟨a * restriction s x.val * a⁻¹,
    (globalKernelNormal r n).conj_mem _ x.property a⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change a * restriction s (x.val * y.val) * a⁻¹ =
      (a * restriction s x.val * a⁻¹) * (a * restriction s y.val * a⁻¹)
    simp [mul_assoc]
  continuous_toFun := ((continuous_const.mul ((restriction s).continuous.comp continuous_subtype_val)).mul
    continuous_const).subtype_mk _

theorem conjugatedRestriction_value (r n : Nat) (s : Bool × Bool) (a : Global)
    (x : localKernel r n s) :
    (conjugatedRestriction r n s a x : Global) = a * restriction s x.val * a⁻¹ := rfl

def atPlaces (r n : Nat) : Set (globalKernel r n) :=
  {x | ∃ (s : Bool × Bool) (a : Global) (y : localKernel r n s), x = conjugatedRestriction r n s a y}

theorem mem_atPlaces_iff (r n : Nat) (x : globalKernel r n) :
    x ∈ atPlaces r n ↔ ∃ (s : Bool × Bool) (a : Global) (y : localKernel r n s),
      x = conjugatedRestriction r n s a y := Iff.rfl

end Reimann.TameCyclotomicLocal277
