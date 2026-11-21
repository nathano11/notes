import Std

namespace Reimann.TameFiber277

/-- Residue arithmetic in the prime field. -/
abbrev F := Fin 277

abbrev Fiber := Fin 4 → F

/-- Inversion is certified by 277 one-variable computations. -/
theorem field_unit (x : F) (hx : x ≠ 0) : ∃ y : F, y*x = 1 := by
  have all : ∀ a : F, a ≠ 0 → ((⟨a.val ^ 275 % 277, Nat.mod_lt _ (by decide)⟩ : F)*a) = 1 := by
    decide +kernel
  exact ⟨_,all x hx⟩

theorem field_prime (x y : F) (h : x*y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · obtain ⟨z,hz⟩ := field_unit x hx
    exact Or.inr (by
      calc
        y = (z*x)*y := by rw [hz, Fin.one_mul]
        _ = z*(x*y) := Fin.mul_assoc _ _ _
        _ = 0 := by rw [h, Fin.mul_zero])

/-- A proper prime ideal for pointwise ring operations. Absorption includes
multiplication by −1 and hence additive inverses. -/
structure IsPrime (P : Fiber → Prop) : Prop where
  zero : P (fun _ => 0)
  proper : ¬ P (fun _ => 1)
  add : ∀ {x y}, P x → P y → P (fun i => x i + y i)
  absorb : ∀ (a : Fiber) {x}, P x → P (fun i => a i * x i)
  prime : ∀ {x y}, P (fun i => x i * y i) → P x ∨ P y

def kernel (i : Fin 4) (x : Fiber) : Prop := x i = 0

theorem kernel_prime (i : Fin 4) : IsPrime (kernel i) where
  zero := rfl
  proper := by change ¬ (1 : F) = 0; decide
  add := by
    intro x y hx hy
    change x i + y i = 0
    rw [show x i=0 from hx,show y i=0 from hy]; rfl
  absorb := by
    intro a x hx
    change a i * x i = 0
    rw [show x i=0 from hx,Fin.mul_zero]
  prime h := field_prime _ _ h

def complement (i : Fin 4) : Fiber := fun j => if j = i then 0 else 1

theorem complements_product :
    (fun j => ((complement 0 j * complement 1 j) * complement 2 j) * complement 3 j) =
      (fun _ => (0 : F)) := by
  funext j
  exact (by decide +kernel : ∀ i : Fin 4,
    ((complement 0 i * complement 1 i) * complement 2 i) * complement 3 i = 0) j

theorem some_complement {P : Fiber → Prop} (h : IsPrime P) :
    ∃ i, P (complement i) := by
  have hp := h.zero
  rw [← complements_product] at hp
  rcases h.prime hp with hl | hr
  · rcases h.prime hl with hl | hr
    · rcases h.prime hl with h0 | h1
      · exact ⟨0,h0⟩
      · exact ⟨1,h1⟩
    · exact ⟨2,hr⟩
  · exact ⟨3,hr⟩

theorem complement_fixes {i : Fin 4} {x : Fiber} (hx : kernel i x) :
    (fun j => x j * complement i j) = x := by
  funext j
  by_cases e : j=i
  · subst j
    change x i * complement i i = x i
    simp [complement,show x i = 0 from hx]
  · simp [complement,e,Fin.mul_one]

theorem nonvanishing_spans {i : Fin 4} {x : Fiber} (hx : ¬ kernel i x) :
    ∃ a : Fiber, (fun j => complement i j + a j*x j) = fun _ => 1 := by
  obtain ⟨z,hz⟩ := field_unit (x i) hx
  refine ⟨fun j => if j=i then z else 0, ?_⟩
  funext j
  by_cases e : j=i
  · subst j; simp [complement,hz]
  · simp [complement,e,Fin.zero_mul,Fin.add_zero]

theorem prime_iff_coordinate (P : Fiber → Prop) : IsPrime P ↔ ∃ i, P = kernel i := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := some_complement h
    refine ⟨i,funext fun x => propext ⟨?_,?_⟩⟩
    · intro hx
      apply Classical.byContradiction
      intro bad
      obtain ⟨a,ha⟩ := nonvanishing_spans bad
      have h1 := h.add hi (h.absorb a hx)
      rw [ha] at h1
      exact h.proper h1
    · intro hx
      rw [← complement_fixes hx]
      exact h.absorb x hi
  · rintro ⟨i,rfl⟩
    exact kernel_prime i

theorem kernel_injective {i j : Fin 4} (h : kernel i = kernel j) : i=j := by
  by_cases eq : i=j
  · exact eq
  · have hi : kernel i (complement i) := by simp [kernel,complement]
    rw [h] at hi
    have bad : (1 : F) = 0 := by simpa [kernel,complement,Ne.symm eq] using hi
    exact False.elim ((by decide : ¬ (1 : F)=0) bad)

/-- The four labelled kernels give a bijection onto the prime ideals. -/
theorem classify (P : Fiber → Prop) : IsPrime P ↔
    ∃ i, P = kernel i ∧ ∀ j, P = kernel j → j = i := by
  constructor
  · intro hp
    obtain ⟨i,hi⟩ := (prime_iff_coordinate P).mp hp
    exact ⟨i,hi,fun _ hj => kernel_injective (hj.symm.trans hi)⟩
  · rintro ⟨i,hi,_⟩
    exact (prime_iff_coordinate P).mpr ⟨i,hi⟩

end Reimann.TameFiber277
