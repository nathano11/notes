import Reimann.DyadicFiberPrimes

/-! Prime predicates constant on the fibers of reduction to F₄ × F₄. -/

namespace Reimann.DyadicFiberDescent

open DyadicFiberPrimes (Fiber)
universe u

structure Reduction (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  red : R → Fiber
  surj : ∀ z, ∃ x, red x = z
  red_zero : red zero = ((0,0),(0,0))
  red_one : red one = ((1,0),(1,0))
  red_add : ∀ x y, red (add x y) = DyadicFiberPrimes.sum (red x) (red y)
  red_mul : ∀ x y, red (mul x y) = DyadicFiberPrimes.product (red x) (red y)

variable {R : Type u}

structure IsPrime (A : Reduction R) (P : R → Prop) : Prop where
  zero : P A.zero
  proper : ¬ P A.one
  add_mem : ∀ x y, P x → P y → P (A.add x y)
  absorb : ∀ x y, P x → P (A.mul x y)
  prime : ∀ x y, P (A.mul x y) → P x ∨ P y

def Saturated (A : Reduction R) (P : R → Prop) : Prop :=
  ∀ x y, A.red x = A.red y → (P x ↔ P y)

def coordinateKernel (A : Reduction R) (i : Bool) (x : R) : Prop :=
  DyadicFiberPrimes.kernel i (A.red x)

def image (A : Reduction R) (P : R → Prop) (z : Fiber) : Prop :=
  ∃ x, A.red x = z ∧ P x

theorem image_reduction_iff (A : Reduction R) (P : R → Prop) (hs : Saturated A P) (x : R) :
    image A P (A.red x) ↔ P x := by
  constructor
  · rintro ⟨y,hy,hP⟩
    exact (hs y x hy).mp hP
  · intro hx
    exact ⟨x,rfl,hx⟩

theorem prime_pullback (A : Reduction R) (Q : Fiber → Prop) (hQ : DyadicFiberPrimes.IsPrime Q) :
    IsPrime A (fun x => Q (A.red x)) := by
  constructor
  · exact A.red_zero ▸ hQ.zero
  · simpa only [A.red_one] using hQ.proper
  · intro x y hx hy
    exact (A.red_add x y) ▸ hQ.add_mem _ _ hx hy
  · intro x y hx
    exact (A.red_mul x y) ▸ hQ.absorb _ _ hx
  · intro x y hxy
    apply hQ.prime
    rwa [← A.red_mul]

theorem prime_on_fiber (A : Reduction R) (Q : Fiber → Prop)
    (h : IsPrime A (fun x => Q (A.red x))) : DyadicFiberPrimes.IsPrime Q := by
  constructor
  · simpa only [A.red_zero] using h.zero
  · simpa only [A.red_one] using h.proper
  · intro a b
    obtain ⟨x,rfl⟩ := A.surj a
    obtain ⟨y,rfl⟩ := A.surj b
    rw [← A.red_add]
    exact h.add_mem x y
  · intro a b
    obtain ⟨x,rfl⟩ := A.surj a
    obtain ⟨y,rfl⟩ := A.surj b
    rw [← A.red_mul]
    exact h.absorb x y
  · intro a b
    obtain ⟨x,rfl⟩ := A.surj a
    obtain ⟨y,rfl⟩ := A.surj b
    rw [← A.red_mul]
    exact h.prime x y

/-- A predicate constant on reduction fibers is prime precisely when it is
one of the two full inverse images of the coordinate kernels. -/
theorem prime_iff_coordinate_kernel (A : Reduction R) (P : R → Prop) (hs : Saturated A P) :
    IsPrime A P ↔ P = coordinateKernel A false ∨ P = coordinateKernel A true := by
  constructor
  · intro hP
    let Q := image A P
    have pullback : (fun x => Q (A.red x)) = P :=
      funext (fun x => propext (image_reduction_iff A P hs x))
    have hQ := prime_on_fiber A Q (pullback ▸ hP)
    have lift (i : Bool) (h : Q = DyadicFiberPrimes.kernel i) : P = coordinateKernel A i := by
      rw [← pullback, h]
      rfl
    exact ((DyadicFiberPrimes.prime_iff_coordinate_kernel Q).mp hQ).elim
      (fun h => Or.inl (lift false h)) (fun h => Or.inr (lift true h))
  · rintro (rfl | rfl) <;> exact prime_pullback A _ (DyadicFiberPrimes.kernel_prime _)

theorem coordinate_kernels_distinct (A : Reduction R) :
    coordinateKernel A false ≠ coordinateKernel A true := by
  intro h
  apply DyadicFiberPrimes.kernels_distinct
  funext z
  obtain ⟨x, rfl⟩ := A.surj z
  exact congrFun h x

end Reimann.DyadicFiberDescent
