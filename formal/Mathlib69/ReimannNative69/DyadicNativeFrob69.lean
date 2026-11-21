import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! The arithmetic Frobenius attached to a lower prime in an abelian extension. -/
namespace Reimann.DyadicNativeFrob69

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (G : Type*) [CommGroup G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [Finite G] [Algebra.IsInvariant R S G]

/-- The finite abelian action makes arithmetic Frobenius independent of the
choice of upper prime over the specified lower prime. -/
theorem frobenius_at_contracted_prime (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    [Finite (S ⧸ P)] [Finite (S ⧸ Q)] (h : P.under R = Q.under R) :
    arithFrobAt R G P = arithFrobAt R G Q := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_arithFrobAt R G P Q h)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hg

/-- Lying over supplies an upper prime with finite quotient when all the
upper residue rings are finite. -/
theorem finite_above_of_finite_quotients (p : Ideal R) [p.IsPrime] [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (residueFinite : ∀ Q : Ideal.primesOver p S, Finite (S ⧸ Q.val)) :
    ∃ Q : Ideal.primesOver p S, Finite (S ⧸ Q.val) := by
  let Q : Ideal.primesOver p S := Classical.ofNonempty
  exact ⟨Q, residueFinite Q⟩

/-- A prime of the base has a single arithmetic Frobenius choice which
satisfies the residue congruence at every prime of S above it. -/
theorem exists_common_frobenius (p : Ideal R)
    (finiteAbove : ∃ Q : Ideal.primesOver p S, Finite (S ⧸ Q.val)) :
    ∃ g : G, ∀ Q : Ideal.primesOver p S, IsArithFrobAt R g Q.val := by
  obtain ⟨s, hs, conj⟩ := IsArithFrobAt.exists_primesOver_isConj (R := R) S G p finiteAbove
  obtain ⟨Q, _⟩ := finiteAbove
  refine ⟨s Q, fun Q' => ?_⟩
  obtain ⟨u, hu⟩ := isConj_iff.mp (conj Q Q')
  have e : s Q = s Q' := by simpa [mul_comm, mul_left_comm, mul_assoc] using hu
  rw [e]
  exact hs Q'

noncomputable def primeFrobenius (p : Ideal R)
    (finiteAbove : ∃ Q : Ideal.primesOver p S, Finite (S ⧸ Q.val)) : G :=
  Classical.choose (exists_common_frobenius R G p finiteAbove)

/-- The exponent is the norm of the contracted lower prime. -/
theorem prime_residue_power (p : Ideal R)
    (finiteAbove : ∃ Q : Ideal.primesOver p S, Finite (S ⧸ Q.val))
    (Q : Ideal.primesOver p S) (x : S) :
    primeFrobenius R G p finiteAbove • x - x ^ (Nat.card (R ⧸ p)) ∈ Q.val := by
  have h := Classical.choose_spec (exists_common_frobenius R G p finiteAbove) Q
  change primeFrobenius R G p finiteAbove • x - _ ∈ Q.val
  have e := congrArg (fun I : Ideal R => Nat.card (R ⧸ I)) Q.property.2.over
  rw [e]
  exact h x

/-- At an unramified prime even the representative is determined by the
residue - power congruence. -/
theorem primeFrobenius_eq (p : Ideal R)
    (finiteAbove : ∃ Q : Ideal.primesOver p S, Finite (S ⧸ Q.val))
    (Q : Ideal.primesOver p S) (inertia : Q.val.inertia G = ⊥) {g : G}
    (hg : IsArithFrobAt R g Q.val) : g = primeFrobenius R G p finiteAbove := by
  have hp := Classical.choose_spec (exists_common_frobenius R G p finiteAbove) Q
  have h := hg.mul_inv_mem_inertia hp
  rw [inertia, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.mp h

omit [Finite G] [Algebra.IsInvariant R S G] in
theorem power_residue (Q : Ideal S) {g : G} (h : IsArithFrobAt R g Q) (f : ℕ) (x : S) :
    Ideal.Quotient.mk Q ((g ^ f) • x) =
      (Ideal.Quotient.mk Q x) ^ (Nat.card (R ⧸ Q.under R) ^ f) := by
  induction f generalizing x with
  | zero => simp
  | succ n ih =>
    let q := Nat.card (R ⧸ Q.under R)
    change Ideal.Quotient.mk Q ((g ^ (n + 1)) • x) = (Ideal.Quotient.mk Q x) ^ (q ^ (n + 1))
    have he : Ideal.Quotient.mk Q (g • x) = (Ideal.Quotient.mk Q x) ^ q := h.mk_apply x
    rw [pow_succ g, mul_smul, ih, he, ← pow_mul, pow_succ q, Nat.mul_comm q (q ^ n)]

omit [Finite G] in
theorem eq_of_residue_actions (Q : Ideal S) (inertia : Q.inertia G = ⊥) {g h : G}
    (same : ∀ x : S, g • x - h • x ∈ Q) : g = h := by
  have hi : g * h⁻¹ ∈ Q.inertia G := by
    intro x
    simpa [mul_smul] using same (h⁻¹ • x)
  rw [inertia, Subgroup.mem_bot] at hi
  exact mul_inv_eq_one.mp hi

/-- On native rings the restriction of the upper arithmetic Frobenius is
the residue - degree power of the lower arithmetic Frobenius. -/
theorem restriction_of_arithmetic_frobenius {R' S' H : Type*}
    [CommRing R'] [CommRing S'] [Algebra R' S'] [Group H] [MulSemiringAction H S']
    [SMulCommClass H R' S'] [Finite H] [Algebra.IsInvariant R' S' H]
    (Q : Ideal S) (Q' : Ideal S') [Q.IsPrime] [Q'.IsPrime] [Finite (S ⧸ Q)] [Finite (S' ⧸ Q')]
    (j : S →+* S') (res : H →* G) (scalar : ∀ h x, j ((res h) • x) = h • j x)
    (contract : Q = Q'.comap j) (inertia : Q.inertia G = ⊥) (f : ℕ)
    (cards : Nat.card (R' ⧸ Q'.under R') = Nat.card (R ⧸ Q.under R) ^ f) :
    res (arithFrobAt R' H Q') = (arithFrobAt R G Q) ^ f := by
  let q := Nat.card (R ⧸ Q.under R)
  let s := arithFrobAt R G Q
  let t := arithFrobAt R' H Q'
  apply eq_of_residue_actions G Q inertia
  intro x
  have upper : res t • x - x ^ (q ^ f) ∈ Q := by
    apply (show (res t • x - x ^ (q ^ f) ∈ Q) ↔ j (res t • x - x ^ (q ^ f)) ∈ Q' by
      rw [contract]
      rfl).mpr
    rw [map_sub, scalar, map_pow, ← cards]
    exact IsArithFrobAt.arithFrobAt R' H Q' (j x)
  have low : s ^ f • x - x ^ (q ^ f) ∈ Q := by
    apply Ideal.Quotient.eq.mp
    rw [map_pow]
    exact power_residue R G Q (IsArithFrobAt.arithFrobAt R G Q) f x
  simpa only [sub_sub_sub_cancel_right] using Q.sub_mem upper low

/-- In a finite integral extension with injective scalar map, the base
residue cardinal alone suffices to construct the prime symbol. -/
theorem finite_above_of_finite_base (p : Ideal R) [p.IsPrime] [Finite (R ⧸ p)]
    [Module.Finite R S] [FaithfulSMul R S] :
    ∃ Q : Ideal.primesOver p S, Finite (S ⧸ Q.val) := by
  apply finite_above_of_finite_quotients R p
  intro Q
  let I := Q.val
  let J := I.under R
  have h : p = J := Q.property.2.over
  have : Finite (R ⧸ J) := h ▸ ‹Finite (R ⧸ p)›
  have : Module.Finite (R ⧸ J) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
  exact Module.finite_of_finite (R ⧸ J)

/-- A commutative square of integer - ring embeddings sends a contraction of
an upper prime to the contraction of the corresponding base prime. -/
theorem lies_over_contracted_prime {R' S' : Type*} [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra R' S'] (j : S →+* S')
    (compatible : ∀ x : R, j (algebraMap R S x) = algebraMap R' S' (algebraMap R R' x))
    (Q' : Ideal S') : (Q'.under R').LiesOver ((Q'.comap j).under R) := by
  constructor
  ext x
  change j (algebraMap R S x) ∈ Q' ↔ algebraMap R' S' (algebraMap R R' x) ∈ Q'
  rw [compatible]

attribute [local instance] FractionRing.liftAlgebra

/-- For a square of integer rings, the ideal norm and the restricted
arithmetic Frobenius are powers with the same residue degree. -/
theorem norm_and_restriction {R' S' H : Type*} [CommRing R'] [CommRing S']
    [IsDedekindDomain R] [IsDedekindDomain R'] [Algebra R R'] [Module.Finite R R']
    [Module.IsTorsionFree R R'] [Algebra.IsSeparable (FractionRing R) (FractionRing R')]
    [Algebra R' S'] [Group H] [MulSemiringAction H S'] [SMulCommClass H R' S']
    [Finite H] [Algebra.IsInvariant R' S' H]
    (Q : Ideal S) (Q' : Ideal S') [Q.IsPrime] [Q'.IsPrime] [Finite (S ⧸ Q)] [Finite (S' ⧸ Q')]
    (j : S →+* S') (res : H →* G) (scalar : ∀ h x, j ((res h) • x) = h • j x)
    (compatible : ∀ x : R, j (algebraMap R S x) = algebraMap R' S' (algebraMap R R' x))
    (contract : Q = Q'.comap j) (inertia : Q.inertia G = ⊥) :
    Ideal.relNorm R (Q'.under R') = (Q.under R) ^ (Q'.under R').inertiaDeg R ∧
      res (arithFrobAt R' H Q') = (arithFrobAt R G Q) ^ (Q'.under R').inertiaDeg R := by
  have : Finite (R ⧸ Q.under R) := .of_injective _ Ideal.algebraMap_quotient_injective
  have : Finite (R' ⧸ Q'.under R') := .of_injective _ Ideal.algebraMap_quotient_injective
  have : (Q.under R).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R ⧸ Q.under R))
  have : (Q'.under R').IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R' ⧸ Q'.under R'))
  have : (Q'.under R').LiesOver (Q.under R) := by
    rw [contract]
    exact lies_over_contracted_prime R j compatible Q'
  refine ⟨Ideal.relNorm_eq_pow_of_isMaximal (Q'.under R') (Q.under R), ?_⟩
  apply restriction_of_arithmetic_frobenius R G Q Q' j res scalar contract inertia
  exact (Ideal.cardQuot_pow_inertiaDeg (Q.under R) (Q'.under R')).symm

/-- The prime - symbol function on the support of a native fractional ideal. -/
noncomputable def heightOneFrobenius [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
    [Module.Finite R S] [FaithfulSMul R S] (p : IsDedekindDomain.HeightOneSpectrum R) : G := by
  have : Finite (R ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  exact primeFrobenius R G p.asIdeal (finite_above_of_finite_base (S := S) R p.asIdeal)

/-- At a prime with trivial inertia, the symbol used by the divisor product
is mathlib's arithmetic Frobenius at each chosen upper prime. -/
theorem heightOneFrobenius_eq [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
    [Module.Finite R S] [FaithfulSMul R S] (p : IsDedekindDomain.HeightOneSpectrum R)
    (Q : Ideal.primesOver p.asIdeal S) [Q.val.IsPrime] [Finite (S ⧸ Q.val)]
    (inertia : Q.val.inertia G = ⊥) :
    heightOneFrobenius (S := S) R G p = arithFrobAt R G Q.val := by
  unfold heightOneFrobenius
  exact (primeFrobenius_eq R G p.asIdeal _ Q inertia (IsArithFrobAt.arithFrobAt R G Q.val)).symm

open scoped NumberField IsMulCommutative

/-- The prime symbol of an actual finite abelian extension of number fields. -/
noncomputable def numberFieldFrobenius (K L : Type*) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    L ≃ₐ[K] L :=
  heightOneFrobenius (S := 𝓞 L) (𝓞 K) (L ≃ₐ[K] L) p

/-- The automorphism attached to a prime divisor of K acts on the integers
of L by the arithmetic Frobenius congruence at every prolongation. -/
theorem numberFieldFrobenius_residue (K L : Type*) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)] (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (Q : Ideal.primesOver p.asIdeal (𝓞 L)) (x : 𝓞 L) :
    numberFieldFrobenius K L p • x - x ^ Nat.card ((𝓞 K) ⧸ p.asIdeal) ∈ Q.val := by
  unfold numberFieldFrobenius heightOneFrobenius
  apply prime_residue_power


section NumberFieldTower
open scoped NumberField IsMulCommutative
variable (K L K' L' : Type*) [Field K] [Field L] [Field K'] [Field L']
  [NumberField K] [NumberField L] [NumberField K'] [NumberField L']
  [Algebra K L] [Algebra K K'] [Algebra K L'] [Algebra L L'] [Algebra K' L']
  [IsScalarTower K L L'] [IsScalarTower K K' L']
  [FiniteDimensional K L] [FiniteDimensional K' L'] [IsGalois K L] [IsGalois K' L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K'] L')]

/-- Restriction in a commutative square of number fields with normal lower extension. -/
noncomputable def numberFieldRestriction : (L' ≃ₐ[K'] L') →* (L ≃ₐ[K] L) :=
  (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)

/-- The relative ideal norm and Galois restriction for actual prime symbols
in a square of finite abelian number-field extensions. -/
theorem numberField_prime_norm_transition
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p' : IsDedekindDomain.HeightOneSpectrum (𝓞 K'))
    (Q : Ideal.primesOver p.asIdeal (𝓞 L)) (Q' : Ideal.primesOver p'.asIdeal (𝓞 L'))
    (contract : Q.val = Q'.val.comap (algebraMap (𝓞 L) (𝓞 L')))
    (unramified : Q.val.inertia (L ≃ₐ[K] L) = ⊥)
    (unramified' : Q'.val.inertia (L' ≃ₐ[K'] L') = ⊥) :
    Ideal.relNorm (𝓞 K) p'.asIdeal = p.asIdeal ^ p'.asIdeal.inertiaDeg (𝓞 K) ∧
      numberFieldRestriction K L K' L' (numberFieldFrobenius K' L' p') =
        numberFieldFrobenius K L p ^ p'.asIdeal.inertiaDeg (𝓞 K) := by
  have : Q.val.IsPrime := Q.property.1
  have : Q'.val.IsPrime := Q'.property.1
  have : Q.val.LiesOver p.asIdeal := Q.property.2
  have : Q'.val.LiesOver p'.asIdeal := Q'.property.2
  have : Finite ((𝓞 L) ⧸ Q.val) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q.val)
  have : Finite ((𝓞 L') ⧸ Q'.val) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot p'.ne_bot Q'.val)
  unfold numberFieldFrobenius
  rw [heightOneFrobenius_eq _ _ p Q unramified, heightOneFrobenius_eq _ _ p' Q' unramified']
  have scalar (h : L' ≃ₐ[K'] L') (x : 𝓞 L) :
      algebraMap (𝓞 L) (𝓞 L') ((numberFieldRestriction K L K' L' h) • x) =
        h • algebraMap (𝓞 L) (𝓞 L') x := by
    apply NumberField.RingOfIntegers.ext
    exact (h.restrictScalars K).restrictNormal_commutes L (x : L)
  have compatible (x : 𝓞 K) :
      algebraMap (𝓞 L) (𝓞 L') (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap (𝓞 K') (𝓞 L') (algebraMap (𝓞 K) (𝓞 K') x) := by
    apply NumberField.RingOfIntegers.ext
    exact (IsScalarTower.algebraMap_apply K L L' (x : K)).symm.trans
      (IsScalarTower.algebraMap_apply K K' L' (x : K))
  have square := norm_and_restriction (𝓞 K) (L ≃ₐ[K] L) Q.val Q'.val (algebraMap (𝓞 L) (𝓞 L'))
    (numberFieldRestriction K L K' L') scalar compatible contract unramified
  simpa only [← Q.property.2.over, ← Q'.property.2.over] using square
end NumberFieldTower

/-- At a nonzero prime of a number field, the local unramified condition is
exactly triviality of the Galois inertia acting on the integers. -/
theorem numberField_inertia_eq_bot_iff (K L : Type*) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (Q : Ideal.primesOver p.asIdeal (𝓞 L))
    : Q.val.inertia (L ≃ₐ[K] L) = ⊥ ↔ Algebra.IsUnramifiedAt (𝓞 K) Q.val := by
  have : Q.val.IsPrime := Q.property.1
  have : Finite ((𝓞 K) ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  have : (Q.val.under (𝓞 K)).IsMaximal := Q.property.2.over ▸ p.isMaximal
  have : Finite ((𝓞 K) ⧸ Q.val.under (𝓞 K)) := Q.property.2.over ▸ ‹Finite ((𝓞 K) ⧸ p.asIdeal)›
  rw [Subgroup.eq_bot_iff_card, Ideal.card_inertia_eq_ramificationIdxIn (Q.val.under (𝓞 K)),
    Ideal.ramificationIdxIn_eq_ramificationIdx (Q.val.under (𝓞 K)) Q.val (L ≃ₐ[K] L),
    Ideal.ramificationIdx_eq_one_iff]

/-- Contraction sends a nonzero prime divisor in an extension of number
fields to a nonzero prime divisor of the base. -/
def numberFieldPrimeBelow (K K' : Type*) [Field K] [Field K'] [NumberField K]
    [NumberField K'] [Algebra K K'] (p' : IsDedekindDomain.HeightOneSpectrum (𝓞 K')) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := p'.asIdeal.under (𝓞 K)
  isPrime := inferInstance
  ne_bot := Ideal.under_ne_bot (𝓞 K) p'.ne_bot

section UnramifiedTower
variable (K L K' L' : Type*) [Field K] [Field L] [Field K'] [Field L']
  [NumberField K] [NumberField L] [NumberField K'] [NumberField L']
  [Algebra K L] [Algebra K K'] [Algebra K L'] [Algebra L L'] [Algebra K' L']
  [IsScalarTower K L L'] [IsScalarTower K K' L']
  [FiniteDimensional K L] [FiniteDimensional K' L'] [IsGalois K L] [IsGalois K' L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K'] L')]

/-- For everywhere-unramified stages any upper base prime has a compatible
prolongation, with the same exponent for ideal norm and Galois restriction. -/
theorem numberField_prime_norm_of_unramified
    (unramified : ∀ (P : Ideal (𝓞 L)) [P.IsMaximal], Algebra.IsUnramifiedAt (𝓞 K) P)
    (unramified' : ∀ (P : Ideal (𝓞 L')) [P.IsMaximal], Algebra.IsUnramifiedAt (𝓞 K') P)
    (p' : IsDedekindDomain.HeightOneSpectrum (𝓞 K')) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), p.asIdeal = p'.asIdeal.under (𝓞 K) ∧
      Ideal.relNorm (𝓞 K) p'.asIdeal = p.asIdeal ^ p'.asIdeal.inertiaDeg (𝓞 K) ∧
      numberFieldRestriction K L K' L' (numberFieldFrobenius K' L' p') =
        numberFieldFrobenius K L p ^ p'.asIdeal.inertiaDeg (𝓞 K) := by
  let p := numberFieldPrimeBelow K K' p'
  let Q' : Ideal.primesOver p'.asIdeal (𝓞 L') := Classical.ofNonempty
  have : Q'.val.IsPrime := Q'.property.1
  have : Q'.val.LiesOver p'.asIdeal := Q'.property.2
  let q := Q'.val.under (𝓞 L)
  have compatible (x : 𝓞 K) :
      algebraMap (𝓞 L) (𝓞 L') (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap (𝓞 K') (𝓞 L') (algebraMap (𝓞 K) (𝓞 K') x) := by
    apply NumberField.RingOfIntegers.ext
    exact (IsScalarTower.algebraMap_apply K L L' (x : K)).symm.trans
      (IsScalarTower.algebraMap_apply K K' L' (x : K))
  have below := (lies_over_contracted_prime (𝓞 K) (algebraMap (𝓞 L) (𝓞 L')) compatible Q'.val).over
  have hq : q.LiesOver p.asIdeal :=
    ⟨(congrArg (fun I : Ideal (𝓞 K') => I.under (𝓞 K)) Q'.property.2.over).trans below.symm⟩
  let Q : Ideal.primesOver p.asIdeal (𝓞 L) := ⟨q, inferInstance, hq⟩
  have : Q.val.LiesOver p.asIdeal := Q.property.2
  have : Q.val.IsPrime := Q.property.1
  have : Q.val.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q.val p.asIdeal
  have : Q'.val.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q'.val p'.asIdeal
  exact ⟨p, rfl, numberField_prime_norm_transition K L K' L' p p' Q Q' rfl
    ((numberField_inertia_eq_bot_iff K L p Q).mpr (unramified Q.val))
    ((numberField_inertia_eq_bot_iff K' L' p' Q').mpr (unramified' Q'.val))⟩
end UnramifiedTower

end Reimann.DyadicNativeFrob69
