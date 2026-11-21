import ReimannNative69.DyadicNativeValue69
import Reimann.DyadicCenterCriterion69
import ReimannNative69.DyadicValueSupport69
import Mathlib.NumberTheory.NumberField.Basic

/-! Normalize the finite contractions of one actual prime over two in the ring
of integers of a possibly infinite algebraic field. -/
namespace Reimann.DyadicPrimeValueTower69

open IsDedekindDomain NumberField DyadicIntegerPrime69 DyadicNativeValue69 DyadicValueUnion69
open DyadicDecomposition69 DyadicLocalRestriction69 DyadicBottomValue69
open scoped NumberField

variable {K L : Type} [Field K] [NumberField K] [Field L]
  (j : K →+* L) (P : Ideal (integerRing L)) [P.IsPrime] (h₂ : (2:integerRing L) ∈ P)

def contractedPrime : HeightOneSpectrum (𝓞 K) where
  asIdeal := P.comap (integersMap j)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have h₂' : (2 : 𝓞 K) ∈ P.comap (integersMap j) := by
      change integersMap j 2 ∈ P
      rwa [map_ofNat]
    have hz : (2:𝓞 K) = 0 := (Ideal.mem_bot).mp (h ▸ h₂')
    exact (by norm_num : (2:𝓞 K) ≠ 0) hz

theorem contracted_prime_dyadic : (2 : 𝓞 K) ∈ (contractedPrime j P h₂).asIdeal := by
  change integersMap j 2 ∈ P
  rwa [map_ofNat]

noncomputable def stageValue : DyadicValue K :=
  normalized_prime_value (contractedPrime j P h₂) (contracted_prime_dyadic j P h₂)

theorem stage_support (x : integerRing K) :
    x ∈ P.comap (integersMap j) ↔ Supports (stageValue j P h₂) x.val :=
  (integer_support (contractedPrime j P h₂) (contracted_prime_dyadic j P h₂) x).symm

theorem stage_support_generator (S : Subfield L) [NumberField S] (f : Embedding L) (i : Bool)
    (base : ∀ t, f.app t ∈ S) (w : integerRing L) (hw : w∈P)
    (eq : f.app (DyadicArithmetic69.primeGenerator i).val = w.val) :
    Supports (stageValue S.subtype P h₂)
      ((stageEmbedding f S base).app (DyadicArithmetic69.primeGenerator i).val) := by
  let z := (stageEmbedding f S base).app (DyadicArithmetic69.primeGenerator i).val
  have integ : z ∈ integerRing S := by
    apply (integers_reflect S.subtype Subtype.val_injective z).mp
    change f.app (DyadicArithmetic69.primeGenerator i).val ∈ integerRing L
    rw [eq]
    exact w.property
  let u : integerRing S := ⟨z,integ⟩
  apply (stage_support S.subtype P h₂ u).mp
  change integersMap S.subtype u ∈ P
  exact (show integersMap S.subtype u=w from Subtype.ext eq) ▸ hw

/-- A prime of the ambient ring of integers supplies every finite-stage
valuation. A common label and generation by the finite cyclotomic root glue
them, and the whole support on the union is the original ideal. -/
theorem centered_union_of_contractions (S : ℕ → Subfield L) [∀ n, NumberField (S n)]
    (inc : Monotone S) (covers : ∀ x, ∃ n, x ∈ S n) (f : Embedding L) (i : Bool)
    (base : ∀ n t, f.app t ∈ S n)
    (centers : ∀ n, Centered (stageEmbedding f (S n) (base n)) (stageValue (S n).subtype P h₂) i)
    (level : ℕ → ℕ) (z : ∀ n, S n) (prim : ∀ n, (z n)^(2^(level n) : ℕ) = -1)
    (gen : ∀ n x, DyadicCyclotomicSpan69.Generated
      (DyadicEmbeddedBase69.baseImage (stageEmbedding f _ (base n))) (z n) x) :
    ∃ V : DyadicValue L, Centered f V i ∧ ∀ x : integerRing L, x∈P ↔ Supports V x.val := by
  let D := of_centered_cyclotomic f i S inc covers base (fun n => stageValue (S n).subtype P h₂)
    centers level z prim gen
  exact ⟨normalized_union D,union_centered D f i 0 (base 0) (centers 0),
    DyadicValueSupport69.union_integer_support D P (fun n => stage_support (S n).subtype P h₂)⟩


include h₂
/-- The single upper prime and its one distinguished generator force every
finite center. The resulting valuation on the full tower has precisely this
prime as its support on all algebraic integers. -/
theorem centered_union_of_generator (S : ℕ → Subfield L) [∀ n, NumberField (S n)]
    (inc : Monotone S) (covers : ∀ x, ∃ n, x ∈ S n) (f : Embedding L) (i : Bool)
    (base : ∀ n t, f.app t ∈ S n) (w : integerRing L) (hw : w∈P)
    (eq : f.app (DyadicArithmetic69.primeGenerator i).val = w.val)
    (level : ℕ → ℕ) (z : ∀ n, S n) (prim : ∀ n, (z n)^(2^(level n) : ℕ) = -1)
    (gen : ∀ n x, DyadicCyclotomicSpan69.Generated
      (DyadicEmbeddedBase69.baseImage (stageEmbedding f _ (base n))) (z n) x) :
    ∃ V : DyadicValue L, Centered f V i ∧ ∀ x : integerRing L, x∈P ↔ Supports V x.val := by
  apply centered_union_of_contractions P h₂ S inc covers f i base _ level z prim gen
  intro n
  apply DyadicCenterCriterion69.centered_of_generator
  exact stage_support_generator P h₂ (S n) f i (base n) w hw eq


end Reimann.DyadicPrimeValueTower69

