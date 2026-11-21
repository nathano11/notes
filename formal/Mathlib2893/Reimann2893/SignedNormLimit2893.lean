import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Equiv.Basic

/-! The inverse limit of a tower of groups, with its coordinatewise equivariant action. -/
namespace Reimann.SignedNormLimit2893

universe u v
variable {G : ℕ → Type u} [∀ n, Group (G n)]

def coherent (N : ∀ n, G (n+1) →* G n) : Subgroup (∀ n, G n) where
  carrier := {x | ∀ n, N n (x (n+1)) = x n}
  one_mem' n := (N n).map_one
  mul_mem' hx hy n := (map_mul (N n) _ _).trans (congrArg₂ (· * ·) (hx n) (hy n))
  inv_mem' hx n := (map_inv (N n) _).trans (congrArg Inv.inv (hx n))

def projection (N : ∀ n, G (n+1) →* G n) (n : ℕ) : coherent N →* G n where
  toFun x := x.1 n
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_norm (N : ∀ n, G (n+1) →* G n) (x : coherent N) (n : ℕ) :
    N n (projection N (n+1) x) = projection N n x := x.2 n

/-- Every compatible family of homomorphisms factors through the norm-coherent families. -/
def lift {H : Type v} [Group H] (N : ∀ n, G (n+1) →* G n) (f : ∀ n, H →* G n)
    (hf : ∀ n x, N n (f (n+1) x) = f n x) : H →* coherent N where
  toFun x := ⟨fun n => f n x, fun n => hf n x⟩
  map_one' := Subtype.ext (funext fun n => (f n).map_one)
  map_mul' x y := Subtype.ext (funext fun n => (f n).map_mul x y)

theorem lift_unique {H : Type v} [Group H] (N : ∀ n, G (n+1) →* G n)
    (f : ∀ n, H →* G n) (hf : ∀ n x, N n (f (n+1) x) = f n x) (h : H →* coherent N)
    (hh : ∀ n x, projection N n (h x) = f n x) : h = lift N f hf := by
  ext x : 1
  exact Subtype.ext (funext fun n => hh n x)

def forward (N : ∀ n, G (n+1) →* G n) (γ : ∀ n, G n ≃* G n)
    (comm : ∀ n x, N n (γ (n+1) x) = γ n (N n x)) : coherent N ≃* coherent N where
  toFun x := ⟨fun n => γ n (x.val n), fun n => (comm n _).trans (congrArg (γ n) (x.property n))⟩
  invFun x := ⟨fun n => (γ n).symm (x.val n), fun n => by
    apply (γ n).injective
    rw [← comm, (γ (n+1)).apply_symm_apply, (γ n).apply_symm_apply]
    exact x.property n⟩
  left_inv x := Subtype.ext (funext fun n => (γ n).symm_apply_apply _)
  right_inv x := Subtype.ext (funext fun n => (γ n).apply_symm_apply _)
  map_mul' x y := Subtype.ext (funext fun n => (γ n).map_mul _ _)

theorem forward_at_level (N : ∀ n, G (n+1) →* G n) (γ : ∀ n, G n ≃* G n)
    (comm : ∀ n x, N n (γ (n+1) x) = γ n (N n x)) (n : ℕ) (x : coherent N) :
    projection N n (forward N γ comm x) = γ n (projection N n x) := rfl

end Reimann.SignedNormLimit2893
