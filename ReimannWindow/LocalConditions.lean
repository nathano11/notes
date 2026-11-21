import Std

namespace ReimannWindow.LocalConditions

/-- Applying an operation n times models multiplication by the nth power of p. -/
def iterateOp {A : Type} (f : A → A) : Nat → A → A
  | 0, x => x
  | n + 1, x => f (iterateOp f n x)

/-- Once the kernel of multiplication by p is zero, so is the kernel of
    multiplication by any power of p. -/
theorem zero_kernel_at_every_depth {A : Type} (f : A → A) (z : A)
    (oneStep : ∀ y, f y = z → y = z) (n : Nat) (x : A)
    (h : iterateOp f n x = z) : x = z := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (oneStep _ h)

/-- With local logarithms 2 and 1, reciprocity makes the coefficients
    congruent modulo 3. The conclusion gives the exact quotient. -/
theorem cancel_three (x y k : Int) (h : 2*x + y = 3*k) :
    x - y = 3*(x-k) := by omega

theorem inverse_fifty_eight : (43 : Int)*58 - 9*277 = 1 := by decide

/-- The split unit at 277 yields logarithms 58 and 219. This is the
    integral cancellation identity after applying the displayed inverse. -/
theorem cancel_two_seventy_seven (x y k : Int) (h : 58*x + 219*y = 277*k) :
    x - y = 277*(43*k - 9*x - 34*y) := by omega

/-- A single global boundary then cancels both local coordinates. -/
theorem simultaneous_boundary (p x y k : Int) (h : x-y = p*k) :
    ∃ b j₁ j₂ : Int, x-b = p*j₁ ∧ y-b = p*j₂ := by
  exact ⟨y, k, 0, h, by simp⟩

/-- In the residue-field test, a pth power projects to one when p*d is
    a multiple of the order of its root. The order hypothesis is explicit. -/
theorem residue_of_power (ell p d u v : Nat)
    (power : u % ell = v^p % ell) (order : v^(p*d) % ell = 1) :
    u^d % ell = 1 := by
  calc
    u^d % ell = (u % ell)^d % ell := Nat.pow_mod ..
    _ = (v^p % ell)^d % ell := by rw [power]
    _ = (v^p)^d % ell := (Nat.pow_mod ..).symm
    _ = 1 := by rw [← Nat.pow_mul, order]

theorem nontrivial_projection_excludes_power (ell p d u : Nat)
    (nontrivial : u^d % ell ≠ 1) :
    ¬ ∃ v : Nat, u % ell = v^p % ell ∧ v^(p*d) % ell = 1 := by
  intro root
  obtain ⟨v, power, order⟩ := root
  exact nontrivial (residue_of_power ell p d u v power order)

def inverse277 (a : Nat) : Nat := a^275 % 277

/-- The inverse used on each nonzero coordinate of the unit line. -/
theorem inverse277_spec :
    ∀ a : Fin 277, a.val ≠ 0 → (a.val * inverse277 a.val) % 277 = 1 := by
  decide +kernel

/-- In a chosen coordinate on a rank-one residue space, one nonzero
    coordinate generates every residue. The witness is the required scalar. -/
theorem nonzero_coordinate_spans (a : Fin 277) (ha : a.val ≠ 0) (t : Nat) :
    ∃ k : Nat, (k * a.val) % 277 = t % 277 := by
  refine ⟨t * inverse277 a.val, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_comm (inverse277 a.val) a.val,
      Nat.mul_mod t (a.val * inverse277 a.val), inverse277_spec a ha,
      Nat.mul_one, Nat.mod_mod]

end ReimannWindow.LocalConditions
