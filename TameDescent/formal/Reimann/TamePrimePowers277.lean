import Reimann.TameBiquadratic277
import Reimann.TameOrderReduction277
import Reimann.TameArithmetic277

namespace Reimann.TamePrimePowers277

open Lean.Grind

open Reimann.TameBiquadratic277

variable {A R : Type} [CommRing R]

/-- Finite sums of products of k members of an ideal, with arbitrary
coefficients allowed (the zeroth power is the whole ring). -/
inductive Power (add mul : A → A → A) (zero : A) (P : A → Prop) : Nat → A → Prop
  | base (v : A) : Power add mul zero P 0 v
  | zeroTerm (k : Nat) : Power add mul zero P k zero
  | productTerm {k : Nat} {w v : A} (hw : P w) (hv : Power add mul zero P k v) :
    Power add mul zero P (k+1) (mul w v)
  | sumTerm {k : Nat} {v z : A}
      (hv : Power add mul zero P k v) (hz : Power add mul zero P k z) :
    Power add mul zero P k (add v z)

def times (mul : A → A → A) (w : A) : Nat → A → A
  | 0, v => v
  | k+1, v => mul w (times mul w k v)

theorem times_in_power (add mul : A → A → A) (zero : A) {P : A → Prop}
    {w : A} (hw : P w) (k : Nat) (v : A) : Power add mul zero P k (times mul w k v) := by
  induction k with
  | zero => exact Power.base v
  | succ k ih => exact Power.productTerm hw ih

/-- Under a ring map, generators with image divisible by p send the
k-th ideal power into the multiples of p^k. -/
theorem power_image (add mul : A → A → A) (zero : A) {P : A → Prop}
    (f : A → R) (p : R) (hz : f zero = 0)
    (ha : ∀ v w, f (add v w) = f v+f w) (hm : ∀ v w, f (mul v w) = f v*f w)
    (hp : ∀ v, P v → ∃ z, f v=p*z) {k : Nat} {v : A}
    (h : Power add mul zero P k v) : ∃ z, f v = p^k*z := by
  induction h with
  | base v => exact ⟨f v, by grind⟩
  | zeroTerm k => exact ⟨0, by grind⟩
  | productTerm hw _ ih =>
    obtain ⟨a,he⟩ := hp _ hw
    obtain ⟨b,hu⟩ := ih
    exact ⟨a*b, by rw [hm,he,hu]; grind⟩
  | sumTerm _ _ ih1 ih2 =>
    obtain ⟨a,h1⟩ := ih1
    obtain ⟨b,h2⟩ := ih2
    exact ⟨a+b, by rw [ha,h1,h2]; grind⟩

theorem times_stable {B : Type} (mul : A → A → A) (F : A → B) (w v : A)
    (oneStep : ∀ z, F z=F v → F (mul w z)=F v) (k : Nat) :
    F (times mul w k v) = F v := by
  induction k with
  | zero => rfl
  | succ k ih => exact oneStep _ ih

/-- A complement selector fixes the residue tuple of v on multiplication.
The remaining congruence error is a multiple of p^k in the order. -/
theorem kernel_in_power {B : Type} (add mul : A → A → A) (zero p w v : A)
    (P : A → Prop) (k : Nat) (F : A → B) (hp : P p) (hw : P w)
    (stable : ∀ z, F z=F v → F (mul w z)=F v)
    (kernel : ∀ z, F z=F v → ∃ u, v=add z (times mul p k u)) :
    Power add mul zero P k v := by
  obtain ⟨u,hu⟩ := kernel _ (times_stable mul F w v stable k)
  rw [hu]
  exact Power.sumTerm (times_in_power add mul zero hw k v) (times_in_power add mul zero hp k u)

open TameArithmetic277 TameOrderReduction277 Fin.IntCast

/-- Zero in the chosen signed coordinate and one in every other coordinate. -/
def complement (sx sy : Bool) : Quad R :=
  let row : R × R := if sy then (1,0) else (0,1)
  if sx then ((1,1),row) else (row,(1,1))

theorem coordinate_complement (sx sy : Bool) :
    coordinate sx sy (complement sx sy : Quad R) = 0 := by
  cases sx <;> cases sy <;> rfl

theorem complement_multiplies (sx sy : Bool) (v : Quad R)
    (h : coordinate sx sy v = 0) :
    pointProduct (complement sx sy) v = v := by
  cases sx <;> cases sy <;>
    simp only [coordinate,complement,ite_true,ite_false,Bool.false_eq_true,pointProduct] at * <;>
    apply Prod.ext <;> apply Prod.ext <;> grind

/-- The combined reduction map of the integral four-coefficient order. -/
def images (n : Nat) (v : Quad Int) : Quad (Residue n) :=
  (finite_splitting277 n).evaluate (reduce n v)

theorem images_product (n : Nat) (u v : Quad Int) :
    images n (product (-3) (-23) u v)=pointProduct (images n u) (images n v) := by
  unfold images
  rw [reduce_product,(finite_splitting277 n).mul]

theorem images_add (n : Nat) (u v : Quad Int) :
    images n (componentAdd u v)=componentAdd (images n u) (images n v) := by
  unfold images
  rw [reduce_add,(finite_splitting277 n).add]

theorem images_surject (n : Nat) (z : Quad (Residue n)) : ∃ w, images n w=z := by
  refine ⟨lift n ((finite_splitting277 n).interpolate z),?_⟩
  unfold images
  rw [reduce_lift,(finite_splitting277 n).realize]

theorem image_fibers (n : Nat) (z v : Quad Int) (h : images n z=images n v) :
    ∃ u : Quad Int, z = componentAdd v (scale (277^(n+1)) u) := by
  apply (reduce_eq_iff n z v).mp
  have he := congrArg (finite_splitting277 n).interpolate h
  simpa only [images,(finite_splitting277 n).reconstruct] using he

/-- Kernel of the selected integral evaluation at the first prime-power level. -/
def primePlace (sx sy : Bool) (v : Quad Int) : Prop :=
  (277 : Int) ∣ branchEval sx sy 0 v

/-- Positive or zeroth ordinary ideal power in the four-coordinate order. -/
def primePower (sx sy : Bool) (k : Nat) : Quad Int → Prop :=
  Power componentAdd (product (-3) (-23)) (integerCoordinates 0) (primePlace sx sy) k

theorem times_integer (p : Int) (k : Nat) (v : Quad Int) :
    times (product (-3) (-23)) (integerCoordinates p) k v=scale (p^k) v := by
  induction k with
  | zero =>
    apply Prod.ext <;> apply Prod.ext <;> simp [times,scale]
  | succ k ih =>
    rw [times,ih,Int.pow_succ]
    apply Prod.ext <;> apply Prod.ext <;> simp [product,integerCoordinates,scale] <;> grind

theorem coordinate_product (sx sy : Bool) (u v : Quad R) :
    coordinate sx sy (pointProduct u v)=coordinate sx sy u*coordinate sx sy v := by
  cases sx <;> cases sy <;> rfl

theorem coordinate_add (sx sy : Bool) (u v : Quad R) :
    coordinate sx sy (componentAdd u v)=coordinate sx sy u+coordinate sx sy v := by
  cases sx <;> cases sy <;> rfl

theorem modulus_zero (n : Nat) : (277 : Residue n)^(n+1) = 0 := by
  have h : (((277 : Int)^(n+1) : Int) : Residue n) = ((0 : Int) : Residue n) :=
    (cast_eq_iff n _ _).mpr (by simp)
  rw [Ring.intCast_pow] at h
  exact h

/-- Every product of n+1 prime-ideal factors vanishes at the chosen
coordinate at depth n+1. -/
theorem power_vanishes (sx sy : Bool) (n : Nat) (v : Quad Int) (hv : primePower sx sy (n+1) v) :
    coordinate sx sy (images n v) = 0 := by
  let f := fun z : Quad Int => coordinate sx sy (images n z)
  have hz : f (integerCoordinates 0) = 0 := by
    change coordinate sx sy ((finite_splitting277 n).evaluate (reduce n (integerCoordinates 0))) = 0
    rw [bridge,branchEval_integer]
    rfl
  have ha (z w : Quad Int) : f (componentAdd z w) = f z+f w := by
    unfold f
    rw [images_add,coordinate_add]
  have hm (z w : Quad Int) : f (product (-3) (-23) z w) = f z*f w := by
    unfold f
    rw [images_product,coordinate_product]
  obtain ⟨z,hz'⟩ := power_image _ _ _ f (277 : Residue n) hz ha hm
    (fun a h => (same_prime_every_depth sx sy n a).mpr h) hv
  change f v = 0
  rw [hz',modulus_zero]
  grind

/-- CRT supplies a single complement selector in the integral order. Its
(n+1)-fold product removes all other coordinates; the error is in 277^(n+1)A. -/
theorem vanishing_in_power (sx sy : Bool) (n : Nat) (v : Quad Int)
    (hv : coordinate sx sy (images n v) = 0) : primePower sx sy (n+1) v := by
  obtain ⟨w,hw⟩ := images_surject n (complement sx sy)
  have hwP : primePlace sx sy w := by
    apply (same_prime_every_depth sx sy n w).mp
    change ∃ z : Residue n, coordinate sx sy (images n w) = 277*z
    rw [hw,coordinate_complement]
    exact ⟨0, by grind⟩
  have hpP : primePlace sx sy (integerCoordinates 277) := by
    unfold primePlace
    rw [branchEval_integer]
    exact Int.dvd_refl _
  apply kernel_in_power componentAdd (product (-3) (-23)) (integerCoordinates 0)
    (integerCoordinates 277) w v (primePlace sx sy) (n+1) (images n) hpP hwP
  · intro z hz
    rw [images_product,hw,hz,complement_multiplies sx sy _ hv]
  · intro z hz
    obtain ⟨u,hu⟩ := image_fibers n v z hz.symm
    exact ⟨u, by rw [times_integer,hu]⟩

/-- The finite congruence filtration at each of the four places is exactly
the filtration by ordinary powers of its first-level kernel. -/
theorem prime_power_iff (sx sy : Bool) (n : Nat) (v : Quad Int) :
    primePower sx sy (n+1) v ↔ (277 : Int)^(n+1) ∣ branchEval sx sy n v := by
  have h : primePower sx sy (n+1) v ↔ coordinate sx sy (images n v) = 0 :=
    ⟨power_vanishes sx sy n v,vanishing_in_power sx sy n v⟩
  rw [h]
  unfold images
  rw [bridge]
  change (((branchEval sx sy n v : Int) : Residue n) = ((0 : Int) : Residue n)) ↔ _
  rw [cast_eq_iff]
  simp

end Reimann.TamePrimePowers277
