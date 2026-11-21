import ReimannNative69.DyadicIntegerPrime69
import ReimannNative69.DyadicNormalTower69
import ReimannNative69.DyadicCyclotomicModel69
import Reimann.DyadicLocalRestriction69
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Invariant.Profinite

/-! Restriction of decomposition groups on the actual integral closures of the integers. -/
namespace Reimann.DyadicPrimeGalois69

open scoped Pointwise
open DyadicIntegerPrime69

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The canonical inclusion of the two rings of algebraic integers. -/
def integersInclusion (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] :
    integralClosure ℤ K →+* integralClosure ℤ Ω :=
  integersMap (algebraMap K Ω)

/-- An integral element has an open stabilizer in the Krull topology. -/
theorem integral_stabilizer_open [Algebra.IsIntegral K Ω] (x : integralClosure ℤ Ω) :
    IsOpen (MulAction.stabilizer Gal(Ω/K) x : Set Gal(Ω/K)) := by
  have eq : (MulAction.stabilizer Gal(Ω/K) x : Set Gal(Ω/K)) =
      (MulAction.stabilizer Gal(Ω/K) (x : Ω) : Set Gal(Ω/K)) := by
    ext g
    exact Subtype.ext_iff
  rw [eq]
  exact stabilizer_isOpen_of_isIntegral (x : Ω)

/-- The invariants among all integral elements descend to integers of the fixed field. -/
theorem fixed_integers_descend [IsGalois K Ω] (x : integralClosure ℤ Ω)
    (fixed : ∀ g : Gal(Ω/K), g • x = x) :
    ∃ y : integralClosure ℤ K, integersInclusion K Ω y = x := by
  apply integral_norm_descends _ (algebraMap K Ω).injective x
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (x : Ω)).mpr
  intro g
  exact congrArg Subtype.val (fixed g)

/-- The kernel Galois group is transitive on the fiber of the actual prime contraction,
including for infinite Galois extensions. -/
theorem primes_over_transitive [IsGalois K Ω] (P Q : Ideal (integralClosure ℤ Ω))
    [P.IsPrime] [Q.IsPrime]
    (same : P.comap (integersInclusion K Ω) = Q.comap (integersInclusion K Ω)) :
    ∃ g : Gal(Ω/K), Q = g • P := by
  letI : Algebra (integralClosure ℤ K) (integralClosure ℤ Ω) :=
    (integersInclusion K Ω).toAlgebra
  letI : SMulCommClass Gal(Ω/K) (integralClosure ℤ K) (integralClosure ℤ Ω) := ⟨by
    intro g a b
    apply Subtype.ext
    change g (algebraMap K Ω (a : K) * (b : Ω)) = algebraMap K Ω (a : K) * g (b : Ω)
    rw [map_mul, g.commutes]⟩
  letI : TopologicalSpace (integralClosure ℤ Ω) := ⊥
  letI : DiscreteTopology (integralClosure ℤ Ω) := ⟨rfl⟩
  letI : ContinuousSMul Gal(Ω/K) (integralClosure ℤ Ω) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (fun x => integral_stabilizer_open x)
  letI : Algebra.IsInvariant (integralClosure ℤ K) (integralClosure ℤ Ω) Gal(Ω/K) :=
    ⟨fun x hx => fixed_integers_descend x hx⟩
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G := Gal(Ω/K)) P Q same

variable (L : IntermediateField K Ω) [Normal K L]

/-- Contracting a conjugate prime agrees with conjugating by the restricted automorphism. -/
theorem contraction_conjugate (g : Gal(Ω/K)) (P : Ideal (integralClosure ℤ Ω)) :
    (g • P).comap (integersInclusion L Ω) =
      AlgEquiv.restrictNormalHom L g • P.comap (integersInclusion L Ω) := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  have eq : g⁻¹ • integersInclusion L Ω x =
      integersInclusion L Ω ((AlgEquiv.restrictNormalHom L g)⁻¹ • x) := by
    rw [← map_inv]
    exact Subtype.ext ((g⁻¹).restrictNormal_commutes L (x : L)).symm
  rw [eq]

/-- A correction by the relative Galois group does not alter the restriction to the lower field. -/
theorem correction_restricts_to_one (u : Gal(Ω/L)) :
    AlgEquiv.restrictNormalHom L (u.restrictScalars K) = 1 := by
  apply (AlgEquiv.restrictNormal_eq_one_iff L _).mpr
  intro x hx
  exact u.commutes (⟨x,hx⟩ : L)

/-- Every stabilizing lower automorphism lifts to an actual automorphism preserving the upper prime. -/
theorem lift_stabilizing_prime [IsGalois K Ω] (P : Ideal (integralClosure ℤ Ω)) [P.IsPrime]
    (s : Gal(L/K)) (hs : s • P.comap (integersInclusion L Ω) =
      P.comap (integersInclusion L Ω)) :
    ∃ g : Gal(Ω/K), g • P = P ∧ AlgEquiv.restrictNormalHom L g = s := by
  obtain ⟨g,hg⟩ := AlgEquiv.restrictNormalHom_surjective Ω s
  have eq := (contraction_conjugate L g P).trans (by rw [hg,hs])
  obtain ⟨u,hu⟩ := primes_over_transitive (K := L) (g • P) P eq
  refine ⟨u.restrictScalars K * g, ?_, ?_⟩
  · rw [mul_smul]
    exact hu.symm
  · rw [map_mul, correction_restricts_to_one, one_mul, hg]

/-- Full decomposition-group image in a normal intermediate field, for the actual integral prime. -/
theorem absolute_decomposition_image [IsGalois K Ω] (P : Ideal (integralClosure ℤ Ω)) [P.IsPrime] :
    (MulAction.stabilizer Gal(Ω/K) P).map (AlgEquiv.restrictNormalHom L) =
      MulAction.stabilizer Gal(L/K) (P.comap (integersInclusion L Ω)) := by
  ext s
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (contraction_conjugate L g P).symm.trans
      (congrArg (Ideal.comap (integersInclusion L Ω)) hg)
  · intro hs
    obtain ⟨g,hg,eq⟩ := lift_stabilizing_prime L P s hs
    exact ⟨g,hg,eq⟩

/-- Conjugation fixes the contraction to the base integers. -/
theorem base_contraction_conjugate (g : Gal(Ω/K)) (P : Ideal (integralClosure ℤ Ω)) :
    (g • P).comap (integersInclusion K Ω) = P.comap (integersInclusion K Ω) := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  have eq : g⁻¹ • integersInclusion K Ω x = integersInclusion K Ω x :=
    Subtype.ext ((g⁻¹).commutes (x : K))
  rw [eq]

/-- When the chosen lower prime is the unique prime over its base contraction,
the restriction of the absolute decomposition group surjects onto the entire Galois group. -/
theorem surjective_of_unique_prime [IsGalois K Ω] (P : Ideal (integralClosure ℤ Ω)) [P.IsPrime]
    (unique : ∀ Q : Ideal (integralClosure ℤ L), Q.IsPrime →
      Q.comap (integersInclusion K L) =
        (P.comap (integersInclusion L Ω)).comap (integersInclusion K L) →
      Q = P.comap (integersInclusion L Ω)) :
    Function.Surjective ((AlgEquiv.restrictNormalHom L).comp
      (MulAction.stabilizer Gal(Ω/K) P).subtype) := by
  intro s
  obtain ⟨g,hg,eq⟩ := lift_stabilizing_prime L P s
    (unique _ inferInstance (base_contraction_conjugate s _))
  exact ⟨⟨g,hg⟩,eq⟩

section Centered

open DyadicBottomValue69 DyadicLocalRestriction69 DyadicEmbeddedBase69 DyadicDecomposition69

/-- Restrict the ordinary algebra automorphism to its underlying field automorphism. -/
def placeAutomorphism {F E : Type} [Field F] [Field E] [Algebra E F] (g : Gal(F/E)) :
    Automorphism F :=
  ⟨g,g.injective,g.surjective,map_zero g,map_one g,map_add g,map_mul g⟩

/-- The two labeled bottom places each determine their cyclotomic prolongation.
Consequently every relative Galois automorphism fixes the support of the chosen valuation. -/
theorem galois_preserves_centered_support {F E : Type} [Field F] [Field E] [Algebra E F]
    (f : Embedding F) (C : RootTower F) (generates : GeneratesField (baseImage f) C)
    (base : ∀ z, ∃ e : E, algebraMap E F e = f.app z)
    (v : Bool) (V : DyadicValue F) (center : Centered f V v) (g : Gal(F/E)) (x : F) :
    Supports V (g x) ↔ Supports V x := by
  let h := placeAutomorphism g
  have fix (z) : h.app (f.app z) = f.app z := by
    obtain ⟨e,he⟩ := base z
    rw [← he]
    exact g.commutes e
  have eq := infinite_layer_place_unique f C generates v (pull V h) V
    (pull_centered f v V center h fix) center
  exact stabilizes_ideal_of_isometry V h (fun t => congrArg (fun W : DyadicValue F => W.val t) eq) x

/-- Lift every relative Galois automorphism at either bottom label through the actual
decomposition group. Only the support comparison for the single chosen upper prime is needed. -/
theorem surjective_at_centered_place {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsGalois E Ω]
    (L : IntermediateField E Ω) [Normal E L] (P : Ideal (integralClosure ℤ Ω)) [P.IsPrime]
    (f : Embedding L) (C : RootTower L) (generates : GeneratesField (baseImage f) C)
    (base : ∀ z, ∃ e : E, algebraMap E L e = f.app z)
    (v : Bool) (V : DyadicValue L) (center : Centered f V v)
    (support : ∀ x : integralClosure ℤ L,
      integersInclusion L Ω x ∈ P ↔ Supports V (x : L)) :
    Function.Surjective ((AlgEquiv.restrictNormalHom L).comp
      (MulAction.stabilizer Gal(Ω/E) P).subtype) := by
  intro s
  have stable : s • P.comap (integersInclusion L Ω) = P.comap (integersInclusion L Ω) := by
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap, Ideal.mem_comap, support, support]
    exact galois_preserves_centered_support f C generates base v V center s⁻¹ x
  obtain ⟨g,hg,eq⟩ := lift_stabilizing_prime L P s stable
  exact ⟨⟨g,hg⟩,eq⟩

end Centered

open DyadicNormalTower69 in
/-- At every real layer of conductor 69 the image of the absolute decomposition group
is precisely the stabilizer of the prime contracted to the field of all dyadic roots. -/
theorem cyclotomic_decomposition_image (Ω : Type*) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (x y : Ω) (ζ : ℕ → Ω) (a : ℕ) (hz : ∀ n, (ζ n) ^ (2^(n+1) : ℕ) = -1)
    (P : Ideal (integralClosure ℤ Ω)) [P.IsPrime] :
    let E := realLayer Ω x y (ζ a)
    let F := fullCyclotomic Ω x y ζ a
    ∃ hn : Normal E F, letI := hn
      (MulAction.stabilizer Gal(Ω/E) P).map (AlgEquiv.restrictNormalHom F) =
      MulAction.stabilizer Gal(F/E) (P.comap (integersInclusion F Ω)) := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI := fullCyclotomic_normal Ω x y ζ a hz
  exact ⟨inferInstance, absolute_decomposition_image (fullCyclotomic Ω x y ζ a) P⟩

open DyadicNormalTower69 DyadicCyclotomicModel69 in
/-- In an algebraic closure of the rationals, the two bottom labels each give the full
cyclotomic Galois group once the chosen upper prime contracts to the centered valuation.
The radicals, the real layer and the compatible tower of dyadic roots are explicit. -/
theorem cyclotomic_surjective_at_center (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (x y : Ω) (ζ : ℕ → Ω) (a : ℕ) (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ) = -1) (hs : ∀ n, ζ (n+1) * ζ (n+1) = ζ n)
    (P : Ideal (integralClosure ℤ Ω)) [P.IsPrime] (v : Bool)
    (V : DyadicDecomposition69.DyadicValue (fullCyclotomic Ω x y ζ a))
    (center : DyadicBottomValue69.Centered (bottom Ω x y ζ a hx hy) V v)
    (support : ∀ e : integralClosure ℤ (fullCyclotomic Ω x y ζ a),
      integersInclusion (fullCyclotomic Ω x y ζ a) Ω e ∈ P ↔
        DyadicLocalRestriction69.Supports V (e : fullCyclotomic Ω x y ζ a)) :
    letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    letI := fullCyclotomic_normal Ω x y ζ a hz
    Function.Surjective ((AlgEquiv.restrictNormalHom (fullCyclotomic Ω x y ζ a)).comp
      (MulAction.stabilizer Gal(Ω/(realLayer Ω x y (ζ a))) P).subtype) := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI := fullCyclotomic_normal Ω x y ζ a hz
  exact surjective_at_centered_place (fullCyclotomic Ω x y ζ a) P (bottom Ω x y ζ a hx hy)
    (tower Ω x y ζ a hz hs) (full_generation Ω x y ζ a hx hy hz hs)
    (base_containment Ω x y ζ a hx hy) v V center support

end Reimann.DyadicPrimeGalois69
