import Reimann.DyadicInert

/-! Prime ideals of the characteristic-two fiber F₄ × F₄. -/

namespace Reimann.DyadicFiberPrimes

open Reimann.DyadicInert (residueAdd residueProduct residue_field_inverse)

abbrev F4 := BitVec 1 × BitVec 1

abbrev Fiber := F4 × F4

def sum (x y : Fiber) : Fiber := (residueAdd x.1 y.1, residueAdd x.2 y.2)

def product (x y : Fiber) : Fiber := (residueProduct x.1 y.1, residueProduct x.2 y.2)

/-- False selects the first coordinate, true the second. -/
def project (i : Bool) (x : Fiber) : F4 := if i then x.2 else x.1

def axis (i : Bool) (a : F4) : Fiber := if i then ((0,0),a) else (a,(0,0))

/-- In characteristic two every element is its own additive inverse. -/
structure IsPrime (P : Fiber → Prop) : Prop where
  zero : P ((0,0),(0,0))
  proper : ¬ P ((1,0),(1,0))
  add_mem : ∀ x y, P x → P y → P (sum x y)
  absorb : ∀ x y, P x → P (product x y)
  prime : ∀ x y, P (product x y) → P x ∨ P y

def kernel (i : Bool) (x : Fiber) : Prop := project i x = (0,0)

theorem project_surjective (i : Bool) (a : F4) : ∃ x, project i x = a :=
  ⟨(a,a), by cases i <;> rfl⟩

theorem field_zero_product (x y : F4) :
    residueProduct x y = (0,0) ↔ x = (0,0) ∨ y = (0,0) := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  revert a b c d
  decide

theorem kernel_prime (i : Bool) : IsPrime (kernel i) := by
  have hmul (x y : Fiber) : project i (product x y) = residueProduct (project i x) (project i y) := by
    cases i <;> rfl
  have hadd (x y : Fiber) : project i (sum x y) = residueAdd (project i x) (project i y) := by
    cases i <;> rfl
  constructor
  · cases i <;> rfl
  · cases i <;> change ¬ ((1,0) : F4) = (0,0) <;> decide
  · intro x y hx hy
    unfold kernel at *
    rw [hadd, hx, hy]
    rfl
  · intro x y hx
    unfold kernel at *
    rw [hmul]
    exact (field_zero_product _ _).mpr (Or.inl hx)
  · intro x y hxy
    unfold kernel at *
    rw [hmul] at hxy
    exact (field_zero_product _ _).mp hxy

theorem orthogonal_idempotents (i : Bool) :
    product (axis i (1,0)) (axis (!i) (1,0)) = ((0,0),(0,0)) ∧
    sum (axis i (1,0)) (axis (!i) (1,0)) = ((1,0),(1,0)) := by
  cases i <;> exact ⟨rfl, rfl⟩

/-- Multiplying by the inverse on a nonzero coordinate produces its idempotent. -/
theorem normalize_axis (i : Bool) (x : Fiber) (h : project i x ≠ (0,0)) :
    product x (axis i (residueProduct (project i x) (project i x))) = axis i (1,0) := by
  have hz (a : F4) : residueProduct a (0,0) = (0,0) :=
    (field_zero_product _ _).mpr (Or.inr rfl)
  cases i with
  | false => exact Prod.ext (residue_field_inverse _ h) (hz _)
  | true => exact Prod.ext (hz _) (residue_field_inverse _ h)

theorem complement_fixes_kernel (i : Bool) (x : Fiber) (hx : kernel i x) :
    product (axis (!i) (1,0)) x = x := by
  have hone (a : F4) : residueProduct (1,0) a = a := by
    have h := DyadicInert.residue_ring_laws a (1,0) a
    exact h.2.2.2.2.2.1.symm.trans h.2.2.2.2.1
  rcases x with ⟨a,b⟩
  cases i with
  | false =>
    change a = (0,0) at hx
    subst a
    exact Prod.ext ((field_zero_product _ _).mpr (Or.inl rfl)) (hone b)
  | true =>
    change b = (0,0) at hx
    subst b
    exact Prod.ext (hone a) ((field_zero_product _ _).mpr (Or.inl rfl))

theorem ideal_with_complement (P : Fiber → Prop) (hP : IsPrime P) (i : Bool)
    (hcomp : P (axis (!i) (1,0))) : P = kernel i := by
  funext x
  apply propext
  constructor
  · intro hx
    apply Classical.byContradiction
    intro hn
    have he := hP.absorb x (axis i (residueProduct (project i x) (project i x))) hx
    rw [normalize_axis i x hn] at he
    have hsum := hP.add_mem _ _ he hcomp
    rw [(orthogonal_idempotents i).2] at hsum
    exact hP.proper hsum
  · intro hx
    have hm := hP.absorb _ x hcomp
    rwa [complement_fixes_kernel i x hx] at hm

/-- The zero product of the two complementary idempotents forces every
prime to contain one coordinate axis. Properness forces the other axis out. -/
theorem prime_iff_coordinate_kernel (P : Fiber → Prop) :
    IsPrime P ↔ P = kernel false ∨ P = kernel true := by
  constructor
  · intro hP
    have he := hP.zero
    rw [← (orthogonal_idempotents false).1] at he
    rcases hP.prime _ _ he with h | h
    · exact Or.inr (ideal_with_complement P hP true h)
    · exact Or.inl (ideal_with_complement P hP false h)
  · rintro (rfl | rfl) <;> apply kernel_prime

theorem kernels_distinct : kernel false ≠ kernel true := by
  intro he
  have h : kernel false (axis true (1,0)) := rfl
  rw [he] at h
  exact (by decide : ¬ ((1,0) : F4) = (0,0)) h

end Reimann.DyadicFiberPrimes
