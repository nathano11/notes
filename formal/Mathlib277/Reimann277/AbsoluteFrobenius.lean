import Reimann277.Inertia
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Compactness.Compact

namespace Reimann.TameAbsoluteFrobenius277

open TameInertia277 Set

variable {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]

/-- A test on the image of one algebraic integer is open for the Krull topology. -/
theorem one_test_open (x : Integers L) (test : Integers L → Prop) :
    IsOpen {g : L ≃ₐ[K] L | test (act g x)} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  let H := MulAction.stabilizer (L ≃ₐ[K] L) x.val
  let C : Set (L ≃ₐ[K] L) := {h | g⁻¹*h ∈ H}
  have ho : IsOpen C :=
    (stabilizer_isOpen_of_isIntegral (K := K) x.val).preimage (continuous_const.mul continuous_id)
  have hmem : g ∈ C := by
    change g⁻¹*g ∈ H
    rw [inv_mul_cancel]
    exact H.one_mem
  apply Filter.mem_of_superset (ho.mem_nhds hmem)
  intro h hh
  have hfix : g⁻¹ (h x.val) = x.val := hh
  have heq : act h x = act g x := by
    apply Subtype.ext
    change h x.val = g x.val
    simpa using congrArg g hfix
  change test (act h x)
  rwa [heq]

theorem one_test_closed (x : Integers L) (test : Integers L → Prop) :
    IsClosed {g : L ≃ₐ[K] L | test (act g x)} :=
  isOpen_compl_iff.mp (one_test_open x (fun y => ¬test y))

def TestAt (P : Ideal (Integers L)) (q : ℕ) (x : Integers L) : Set (L ≃ₐ[K] L) :=
  {g | Ideal.Quotient.mk P (act g x) = (Ideal.Quotient.mk P x)^q}

theorem closed_test (P : Ideal (Integers L)) (q : ℕ) (x : Integers L) :
    IsClosed (TestAt (K := K) P q x) :=
  one_test_closed x (fun y => Ideal.Quotient.mk P y = (Ideal.Quotient.mk P x)^q)

/-- The absolute Frobenius congruence follows from simultaneous finite tests.
No compatibility between the choices of individual finite witnesses is required. -/
theorem exists_of_finite_tests [CompactSpace (L ≃ₐ[K] L)] (P : Ideal (Integers L)) (q : ℕ)
    (hf : ∀ F : Finset (Integers L), ∃ g : L ≃ₐ[K] L, ∀ x ∈ F, g ∈ TestAt P q x) :
    ∃ g : L ≃ₐ[K] L, FrobeniusResidue P q g := by
  have h := isCompact_univ.inter_iInter_nonempty (TestAt (K := K) P q) (closed_test P q) ?_
  · obtain ⟨g,_,hg⟩ := h
    exact ⟨g,fun x => Set.mem_iInter.mp hg x⟩
  · intro F
    obtain ⟨g,hg⟩ := hf F
    exact ⟨g,Set.mem_univ _,Set.mem_iInter.mpr (fun x => Set.mem_iInter.mpr (hg x))⟩

end Reimann.TameAbsoluteFrobenius277
