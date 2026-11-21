import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Algebra.Ring.Subring.Basic

/-! Contraction and exhaustion of the chosen prime in the integral orders of a field tower. -/
namespace Reimann.DyadicNativePrime69

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The inverse image of the actual ideal along the displayed unital ring map. -/
def contraction (f : R →+* S) (P : Ideal S) : Ideal R where
  carrier := {x | f x ∈ P}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; change f (x+y) ∈ P; rw [map_add]; exact P.add_mem hx hy
  smul_mem' := by intro a x hx; change f (a*x) ∈ P; rw [map_mul]; exact P.mul_mem_left _ hx

theorem mem_contraction (f : R →+* S) (P : Ideal S) (x : R) :
    x ∈ contraction f P ↔ f x ∈ P := Iff.rfl

/-- A chosen upper prime restricts to a prime ideal on each finite order. -/
theorem prime_contraction (f : R →+* S) (P : Ideal S) (hP : P.IsPrime) :
    (contraction f P).IsPrime := by
  constructor
  · intro h
    have hone : (1:R) ∈ contraction f P := h.symm ▸ Submodule.mem_top
    exact hP.one_notMem (by simpa only [mem_contraction,map_one] using hone)
  · intro x y h
    exact hP.mem_or_mem (show f x*f y∈P by rwa [←map_mul])

theorem contraction_comp (f : R →+* S) (g : S →+* T) (P : Ideal T) :
    contraction f (contraction g P)=contraction (g.comp f) P := rfl

/-- The integral elements in the n-th embedded field, inside a single ambient algebraic extension. -/
def stageOrder (integers layer : Subring R) : Subring R := integers ⊓ layer

def stageInclusion (integers layer : Subring R) : stageOrder integers layer →+* integers :=
  Subring.inclusion (show stageOrder integers layer ≤ integers from inf_le_left)

def stagePrime (integers layer : Subring R) (P : Ideal integers) :
    Ideal (stageOrder integers layer) := contraction (stageInclusion integers layer) P

theorem stagePrime_isPrime (integers layer : Subring R) (P : Ideal integers) (hP : P.IsPrime) :
    (stagePrime integers layer P).IsPrime := prime_contraction _ P hP

def enlarge (integers : Subring R) {K L : Subring R} (h : K ≤ L) :
    stageOrder integers K →+* stageOrder integers L := Subring.inclusion (inf_le_inf_left integers h)

theorem adjacent_contraction (integers : Subring R) {K L : Subring R} (h : K ≤ L)
    (P : Ideal integers) : contraction (enlarge integers h) (stagePrime integers L P) =
      stagePrime integers K P := rfl

/-- On a cofinal tower the given global ideal is exactly the union of its contractions.
The criterion includes all global integral elements, including zero. -/
theorem exhausts_prime (integers : Subring R) (layer : ℕ → Subring R)
    (exhaustive : ∀ x : R, ∃ n, x ∈ layer n) (P : Ideal integers) (x : integers) :
    x ∈ P ↔ ∃ n, ∃ y : stageOrder integers (layer n),
      y ∈ stagePrime integers (layer n) P ∧ stageInclusion integers (layer n) y=x := by
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := exhaustive x.val
    exact ⟨n,⟨x.val,x.property,hn⟩,hx,rfl⟩
  · rintro ⟨n,y,hy,rfl⟩
    exact hy

end Reimann.DyadicNativePrime69
