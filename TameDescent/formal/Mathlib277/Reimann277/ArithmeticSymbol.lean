import Reimann277.IdealAction
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.SetTheory.Cardinal.NatCard

namespace Reimann.TameArithmeticSymbol277

open scoped nonZeroDivisors
open TameArtin277 TameIdealArtin277 TameIdealAction277 TameCyclotomicLocal277

/-- A maximal ideal of a localization extends to the integral overring after
contraction, provided the contraction is maximal and contains the kernel.
The chosen prime of the overring avoids the inverted element. -/
theorem prolongation_of_integral {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.IsIntegral A C] (a : A) [IsLocalization.Away a B]
    (J : Ideal B) (hm : J.IsMaximal) (hc : (J.under A).IsMaximal)
    (hk : RingHom.ker (algebraMap A C) ≤ J.under A) :
    ∃ P : Ideal C, P.IsMaximal ∧ algebraMap A C a ∉ P ∧ P.under A = J.under A := by
  letI := hc
  obtain ⟨P,hP,he⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (J.under A) hk
  refine ⟨P,hP,?_,he⟩
  intro h
  have hs : a ∈ J.under A := he ▸ (show a ∈ P.under A from h)
  exact hm.ne_top (J.eq_top_of_isUnit_mem hs (IsLocalization.Away.algebraMap_isUnit (S := B) a))

/-- Inverting an element leaves the residue field at a surviving maximal
contraction unchanged. The equivalence is the map induced by localization. -/
noncomputable def localizedResidueEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) [IsLocalization.Away a B] (J : Ideal B) [J.IsPrime] (hc : (J.under A).IsMaximal) :
    (A ⧸ J.under A) ≃+* (B ⧸ J) :=
  RingEquiv.ofBijective (Ideal.quotientMap J (algebraMap A B) le_rfl)
    ⟨Ideal.quotientMap_injective, IsLocalization.surjective_quotientMap_of_maximal_of_localization
      (Submonoid.powers a) B hc⟩

theorem localizedResidueEquiv_mk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) [IsLocalization.Away a B] (J : Ideal B) [J.IsPrime] (hc : (J.under A).IsMaximal)
    (x : A) : localizedResidueEquiv a J hc (Ideal.Quotient.mk (J.under A) x) =
      Ideal.Quotient.mk J (algebraMap A B x) := rfl

abbrev ClosureIntegers := TameInertia277.Integers Closure

def integralInclusion (r n : ℕ) : CutIntegers r n →+* ClosureIntegers :=
  algebraMap (CutIntegers r n) (NumberField.RingOfIntegers Closure)

theorem integralInclusion_injective (r n : ℕ) : Function.Injective (integralInclusion r n) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  exact NumberField.RingOfIntegers.ker_algebraMap_eq_bot (cutField r n) Closure

local instance localizedDedekind (r n : ℕ) : IsDedekindDomain (SIntegers r n) :=
  IsLocalization.isDedekindDomain (CutIntegers r n)
    (TameLocalClass277.powers_277_regular (cutField r n)) (SIntegers r n)

abbrev IntegralIdeals (r n : ℕ) := (Ideal (SIntegers r n))⁰

def contracted {r n : ℕ} (J : IntegralIdeals r n) : Ideal (CutIntegers r n) :=
  J.val.under (CutIntegers r n)

theorem contracted_ne_zero {r n : ℕ} (J : IntegralIdeals r n) : contracted J ≠ 0 :=
  TameLocalClass277.under_ne_zero (Submonoid.powers (277 : CutIntegers r n))
    (SIntegers r n) (mem_nonZeroDivisors_iff_ne_zero.mp J.property)

theorem contracted_maximal {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal) :
    (contracted J).IsMaximal := by
  letI := hJ
  letI : (contracted J).IsPrime := Ideal.comap_isPrime _ _
  exact Ring.HasFiniteQuotients.maximalOfPrime (contracted_ne_zero J)

theorem residue_finite {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal) :
    Finite (SIntegers r n ⧸ J.val) := by
  letI := hJ
  letI : Finite (CutIntegers r n ⧸ J.val.under (CutIntegers r n)) :=
    Ring.HasFiniteQuotients.finiteQuotient (contracted_ne_zero J)
  let e := localizedResidueEquiv (277 : CutIntegers r n) J.val (contracted_maximal J hJ)
  exact Finite.of_surjective e e.surjective

noncomputable def residueSize {r n : ℕ} (J : IntegralIdeals r n) : ℕ :=
  Nat.card (SIntegers r n ⧸ J.val)

theorem residueSize_contracted {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal) :
    residueSize J = Nat.card (CutIntegers r n ⧸ contracted J) := by
  letI := hJ
  exact Nat.card_congr
    (localizedResidueEquiv (277 : CutIntegers r n) J.val (contracted_maximal J hJ)).symm.toEquiv

theorem residueSize_gt_one {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal) :
    1 < residueSize J := by
  letI := hJ
  letI := residue_finite J hJ
  exact Finite.one_lt_card

/-- The absolute prime and the localized prime have the same contraction to the
integers of the twist field. The residue characteristic is different from 277. -/
structure Prolongs {r n : ℕ} (J : IntegralIdeals r n) (P : Ideal ClosureIntegers) : Prop where
  maximal : P.IsMaximal
  away : (277 : ClosureIntegers) ∉ P
  contraction : P.comap (integralInclusion r n) = contracted J

theorem contracted_away {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal) :
    (277 : CutIntegers r n) ∉ contracted J := by
  intro h
  exact hJ.ne_top (J.val.eq_top_of_isUnit_mem h
    (IsLocalization.Away.algebraMap_isUnit (S := SIntegers r n) (277 : CutIntegers r n)))

/-- Lying over for the integral extension of integer rings gives a prolongation
of every finite prime of the localized ring. -/
theorem exists_prolongation {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal) :
    ∃ P, Prolongs J P := by
  have hker : RingHom.ker (integralInclusion r n) ≤ contracted J :=
    ((RingHom.injective_iff_ker_eq_bot _).mp (integralInclusion_injective r n)).le.trans bot_le
  obtain ⟨P,hm,ha,hc⟩ := prolongation_of_integral (C := NumberField.RingOfIntegers Closure)
    (277 : CutIntegers r n) J.val hJ (contracted_maximal J hJ) hker
  have h277 : integralInclusion r n (277 : CutIntegers r n) = (277 : ClosureIntegers) :=
    map_ofNat _ _
  exact ⟨P,hm,fun h => ha (h277.symm ▸ h),hc⟩

def FrobeniusAt {r n : ℕ} (J : IntegralIdeals r n) (P : Ideal ClosureIntegers)
    (x : globalKernel r n) : Prop :=
  TameInertia277.FrobeniusResidue P (residueSize J) (asAut x.val)

/-- The forward residue equation puts its lift in the decomposition subgroup. -/
theorem frobenius_stabilizes {r n : ℕ} {J : IntegralIdeals r n} (hJ : J.val.IsMaximal)
    {P : Ideal ClosureIntegers} (hP : Prolongs J P) {x : globalKernel r n}
    (hx : FrobeniusAt J P x) (z : ClosureIntegers) :
    TameInertia277.act (asAut x.val) z ∈ P ↔ z ∈ P :=
  TameInertia277.frobenius_preserves_ideal P hP.maximal.isPrime (residueSize J)
    (Nat.zero_lt_one.trans (residueSize_gt_one J hJ)) (asAut x.val) hx z

theorem project_frobenius_independent {r n : ℕ} {J : IntegralIdeals r n}
    {P : Ideal ClosureIntegers} (hp : Prolongs J P) (x y : globalKernel r n)
    (hx : FrobeniusAt J P x) (hy : FrobeniusAt J P y) : project r n x = project r n y :=
  TameInertia277.frobenius_lifts_equal (globalKernel r n) (project r n).toMonoidHom P
    (residueSize J) (unramified_away r n P hp.maximal hp.away) x y hx hy

/-- Transport of actual invertible fractional ideals by the action on S-integers. -/
noncomputable def transport (r n : ℕ) (g : Global) :
    InvertibleIdeals (SIntegers r n) →* InvertibleIdeals (SIntegers r n) :=
  let σ := onSIntegers r n g
  Units.map (FractionalIdeal.extendedHom' (FractionRing (SIntegers r n))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective σ.toRingHom σ.injective)).toMonoidHom

theorem transport_class {r n : ℕ} (g : Global) (I : InvertibleIdeals (SIntegers r n)) :
    onClass r n g (ClassGroup.mk (FractionRing (SIntegers r n)) I) =
      ClassGroup.mk (FractionRing (SIntegers r n)) (transport r n g I) := by
  rw [← ClassGroup.Quot_mk_eq_mk, ← ClassGroup.Quot_mk_eq_mk]
  rfl

/-- The global arithmetic input. Its symbol is surjective with kernel the principal
fractional ideals. Each prime receives the forward power Frobenius in the unramified,
split quotient; naturality is stated on fractional ideal representatives. -/
structure Input (r n : ℕ) where
  ideals : IdealSymbol (SIntegers r n) (G := UnramifiedSplitQuotient r n)
  frobenius : ∀ (J : IntegralIdeals r n), J.val.IsMaximal → ∀ P, Prolongs J P →
    ∃ x : globalKernel r n, FrobeniusAt J P x ∧
      ideals.symbol (FractionalIdeal.mk0 (FractionRing (SIntegers r n)) J) = project r n x
  conjugation : ∀ (g : Global) (x : globalKernel r n) (I : InvertibleIdeals (SIntegers r n)),
    ideals.symbol I = project r n x →
      ideals.symbol (transport r n g I) = project r n (conjugateKernel g x)

noncomputable def reciprocity {r n : ℕ} (a : Input r n) : ClassReciprocity r n :=
  fromIdealSymbol a.ideals

theorem inverse_symbol {r n : ℕ} (a : Input r n) (I : InvertibleIdeals (SIntegers r n)) :
    reciprocity a (a.ideals.symbol I) = ClassGroup.mk (FractionRing (SIntegers r n)) I :=
  ideal_symbol_orientation a.ideals I

theorem forward_frobenius {r n : ℕ} (a : Input r n) (J : IntegralIdeals r n)
    (hJ : J.val.IsMaximal) (P : Ideal ClosureIntegers) (hp : Prolongs J P)
    (x : globalKernel r n) (hx : FrobeniusAt J P x) :
    a.ideals.symbol (FractionalIdeal.mk0 (FractionRing (SIntegers r n)) J) = project r n x := by
  obtain ⟨y,hy,h⟩ := a.frobenius J hJ P hp
  exact h.trans (project_frobenius_independent hp y x hy hx)

theorem independent_prolongations {r n : ℕ} (a : Input r n) (J : IntegralIdeals r n)
    (hJ : J.val.IsMaximal) {P Q : Ideal ClosureIntegers} (hP : Prolongs J P) (hQ : Prolongs J Q)
    (x y : globalKernel r n) (hx : FrobeniusAt J P x) (hy : FrobeniusAt J Q y) :
    project r n x = project r n y :=
  (forward_frobenius a J hJ P hP x hx).symm.trans (forward_frobenius a J hJ Q hQ y hy)

theorem inverse_frobenius {r n : ℕ} (a : Input r n) (J : IntegralIdeals r n)
    (hJ : J.val.IsMaximal) (P : Ideal ClosureIntegers) (hp : Prolongs J P)
    (x : globalKernel r n) (hx : FrobeniusAt J P x) :
    toClassGroup (reciprocity a) x = ClassGroup.mk0 J := by
  change reciprocity a (project r n x) = _
  rw [← forward_frobenius a J hJ P hp x hx, inverse_symbol, ClassGroup.mk_mk0]

theorem reciprocity_equivariant {r n : ℕ} (a : Input r n) :
    ArtinEquivariant (reciprocity a) := by
  intro g x
  obtain ⟨I,hI⟩ := a.ideals.onto (project r n x)
  change reciprocity a (project r n (conjugateKernel g x)) = onClass r n g (reciprocity a (project r n x))
  rw [← a.conjugation g x I hI, ← hI, inverse_symbol, inverse_symbol, transport_class]

end Reimann.TameArithmeticSymbol277
