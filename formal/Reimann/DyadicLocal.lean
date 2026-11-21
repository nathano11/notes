import Reimann.TameLocal
import Reimann.TameRestriction

/-!
# The two local restrictions at 2

The residue of an integer x at denominator n represents x/n in the divisible
dyadic coefficient group when n is a power of two. Congruences work for any
positive n. All matrix columns below are in the ordered basis (b,c) of Y.
The arithmetic identification of the two decomposition groups is recorded in
PROOF_STATUS.md.
-/

namespace Reimann.DyadicLocal

open Reimann.TameLocal

/-- A single inflation can cancel both local classes exactly when their
difference is a coboundary. We use the sign (1 - action) for the difference. -/
theorem common_inflation_iff {U : Type} (n : Int) (mul : U → U → U)
    (a left right : U → Int) (hleft : Cocycle n mul a left) :
    (∃ c, Cocycle n mul a c ∧
      Principal n a (fun t => left t - c t) ∧
      Principal n a (fun t => right t - c t)) ↔
    ∃ y : Int, ∀ t, n ∣ right t - left t - (1-a t)*y := by
  constructor
  · rintro ⟨c, _, ⟨v, hv⟩, ⟨w, hw⟩⟩
    refine ⟨v-w, fun t => ?_⟩
    obtain ⟨j, hj⟩ := hv t
    obtain ⟨k, hk⟩ := hw t
    exact ⟨k-j, by dsimp at hj hk; grind⟩
  · rintro ⟨y, hy⟩
    refine ⟨left, hleft, ⟨0, fun t => by simp⟩, -y, fun t => ?_⟩
    obtain ⟨k, hk⟩ := hy t
    exact ⟨k, by dsimp; grind⟩

/-- If the second lift is k times the first and k acts trivially, the
difference of the values of a global cocycle is its value on k. In the tower
the quotient k is B s B⁻¹ s⁻¹. -/
theorem difference_on_two_lifts {G : Type} {n : Int} {mul : G → G → G}
    {a c : G → Int} (hc : Cocycle n mul a c) (k first second : G)
    (hquot : mul k first = second) (hker : n ∣ a k - 1) :
    n ∣ c second - c first - c k := by
  obtain ⟨i, hi⟩ := hc k first
  rw [hquot] at hi
  obtain ⟨j, hj⟩ := hker
  refine ⟨i+j*c first, ?_⟩
  have h := congrArg (fun v : Int => v*c first) hj
  grind

/-- Matrix of (g-w) as a map Y → X, with w=1+2j and columns
g(b)=(1+2h)b+l c and g(c)=2k b+d c. The first coordinate in X is
the coefficient of 2b. -/
theorem difference_columns_in_X (h k l d j u v : Int) :
    ((1+2*h)*u+2*k*v-(1+2*j)*u, l*u+d*v-(1+2*j)*v) =
      (2*((h-j)*u+k*v), l*u+(d-1-2*j)*v) := by
  apply Prod.ext <;> dsimp <;> grind

/-- A character given by x=f(2b), z=f(c), at denominator n, vanishes on
(g-w)Y precisely when it kills both columns. -/
theorem annihilates_image_iff (n h k l d j x z : Int) :
    (∀ u v : Int, n ∣ x*((h-j)*u+k*v)+z*(l*u+(d-1-2*j)*v)) ↔
    (n ∣ (h-j)*x+l*z) ∧ (n ∣ k*x+(d-1-2*j)*z) := by
  constructor
  · intro all
    have hb := all 1 0
    have hc := all 0 1
    simpa [Int.mul_comm] using And.intro hb hc
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ u v
    refine ⟨a*u+b*v, ?_⟩
    calc
      _ = ((h-j)*x+l*z)*u + (k*x+(d-1-2*j)*z)*v := by grind
      _ = _ := by rw [ha,hb]; grind

/-- At odd weight sigma gives x=2y, and g gives
-h*x-l*z=(1-w)*y. Once the c-column is equivariant, a common primitive y
is exactly the value on b of an equivariant extension to Y. This statement
uses a single finite denominator for x,z,y. -/
theorem primitive_iff_extension {n h k l d w x z : Int}
    (hc : n ∣ k*x+(d-w)*z) :
    (∃ y : Int, (n ∣ x-2*y) ∧ n ∣ -h*x-l*z-(1-w)*y) ↔
    ∃ y : Int, (n ∣ x-2*y) ∧
      (n ∣ (1+2*h-w)*y+l*z) ∧ (n ∣ 2*k*y+(d-w)*z) := by
  constructor
  · rintro ⟨y, ⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨c, hc⟩ := hc
    refine ⟨y, ⟨a, ha⟩, ⟨-b-h*a, ?_⟩, ⟨c-k*a, ?_⟩⟩
    · have hh := congrArg (fun v : Int => h*v) ha
      grind
    · have hk := congrArg (fun v : Int => k*v) ha
      grind
  · rintro ⟨y, ⟨a, ha⟩, ⟨b, hb⟩, _⟩
    refine ⟨y, ⟨a, ha⟩, ⟨-b-h*a, ?_⟩⟩
    have hh := congrArg (fun v : Int => h*v) ha
    grind

/-- A primitive at any enlarged denominator n*m already forces the
b-column relation at the original denominator n. -/
theorem primitive_forces_b_column {n m h l j x z y : Int} (hm : m ≠ 0)
    (hs : n*m ∣ m*x - 2*y)
    (hg : n*m ∣ -h*(m*x)-l*(m*z)+2*j*y) :
    n ∣ (h-j)*x+l*z := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hg
  refine ⟨-b-j*a, Int.eq_of_mul_eq_mul_left hm ?_⟩
  have hj := congrArg (fun v : Int => j*v) ha
  grind

/-- If the b-column relation holds, x/(2n) is a common primitive for the
two generator discrepancies. This explicitly takes a half in Q₂/Z₂. -/
theorem double_denominator_primitive {n h l j x z : Int}
    (hb : n ∣ (h-j)*x+l*z) :
    (n*2 ∣ 2*x-2*x) ∧ n*2 ∣ -h*(2*x)-l*(2*z)+2*j*x := by
  obtain ⟨a, ha⟩ := hb
  refine ⟨by simp, ⟨-a, ?_⟩⟩
  grind

/-- For odd weight, a character on X that is equivariant on c and admits
one primitive at both generators is precisely a character killing (g-w)Y.
Depth e allows all dyadic denominators for the primitive. The reverse
implication always uses e=1. -/
theorem odd_two_places_iff_annihilates_image (n h k l d j x z : Int) :
    ((n ∣ k*x+(d-1-2*j)*z) ∧
      ∃ (e : Nat) (y : Int), let m := (2:Int)^e
        (n*m ∣ m*x-2*y) ∧ (n*m ∣ -h*(m*x)-l*(m*z)+2*j*y)) ↔
    ∀ u v : Int, n ∣ x*((h-j)*u+k*v)+z*(l*u+(d-1-2*j)*v) := by
  rw [annihilates_image_iff]
  constructor
  · rintro ⟨hc, e, y, hs, hg⟩
    exact ⟨primitive_forces_b_column (Int.pow_ne_zero (by decide : (2:Int) ≠ 0)) hs hg, hc⟩
  · rintro ⟨hb, hc⟩
    exact ⟨hc, 1, x, by simpa using double_denominator_primitive hb⟩

/-- The commutator comparing the two places lies over the difference b-tb.
The group may be nonsplit. The projection is defined only on N (in the
application the group over k-infinity). -/
theorem commutator_projects_to_difference {G Y : Type}
    (P : Transfer.GroupLaw G) (V : Transfer.GroupLaw Y)
    (N : G → Prop) (in_mul : ∀ {u v}, N u → N v → N (P.add u v))
    (π : {x // N x} → Y)
    (map_mul : ∀ {u v} (hu : N u) (hv : N v),
      π ⟨P.add u v, in_mul hu hv⟩ = V.add (π ⟨u,hu⟩) (π ⟨v,hv⟩))
    (B t : G) (hB : N B) (htB : N (TameRestriction.conjugate P t B))
    (hk : N (TameRestriction.commutator P B t)) :
    π ⟨TameRestriction.commutator P B t,hk⟩ =
      V.add (π ⟨B,hB⟩) (V.neg (π ⟨TameRestriction.conjugate P t B,htB⟩)) := by
  have e : P.add (TameRestriction.commutator P B t)
      (TameRestriction.conjugate P t B) = B := by
    unfold TameRestriction.conjugate
    rw [← P.assoc, TameRestriction.commutator_swap, P.assoc, P.add_neg, P.add_zero]
  have he : (⟨_, in_mul hk htB⟩ : Subtype N) = ⟨B,hB⟩ := Subtype.ext e
  have h := map_mul hk htB
  rw [he] at h
  rw [h, V.assoc, V.add_neg, V.add_zero]

/-- The characters on Y vanishing on X are precisely the two possible
values on b, with zero value on c. We use canonical numerators modulo 2n. -/
theorem restriction_kernel_coordinates {n y z : Int} (hn : 0 < n)
    (hy : 0 ≤ y ∧ y < 2*n) (hz : 0 ≤ z ∧ z < 2*n) :
    ((2*n ∣ 2*y) ∧ (2*n ∣ z)) ↔ (y = 0 ∨ y = n) ∧ z = 0 := by
  constructor
  · rintro ⟨⟨a, ha⟩, hzero⟩
    have hu : y = n*a := by rw [Int.mul_assoc] at ha; omega
    have hy0 : 0 ≤ a := by
      by_cases h : a < 0
      · have := Int.mul_neg_of_pos_of_neg hn h
        omega
      · omega
    have hy2 : a < 2 := by
      by_cases h : 2 ≤ a
      · have he := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hn)
        omega
      · omega
    have hr := Int.emod_eq_zero_of_dvd hzero
    rw [Int.emod_eq_of_lt hz.1 hz.2] at hr
    refine ⟨?_, hr⟩
    rcases (show a = 0 ∨ a = 1 by omega) with e | e <;> simp_all
  · rintro ⟨ha, rfl⟩
    rcases ha with rfl | rfl <;> simp

/-- Both kernel characters actually satisfy the g-equivariance equations.
For n>0 the two displayed representatives at denominator 2n are distinct. -/
theorem restriction_kernel_equivariant {n y z : Int} (h k l d j : Int)
    (hy : (y = 0 ∨ y = n) ∧ z = 0) :
    (2*n ∣ (2*h-2*j)*y+l*z) ∧ (2*n ∣ 2*k*y+(d-1-2*j)*z) := by
  obtain ⟨e, rfl⟩ := hy
  rcases e with rfl | rfl
  · simp
  · exact ⟨⟨h-j, by grind⟩, ⟨k, by grind⟩⟩

end Reimann.DyadicLocal
