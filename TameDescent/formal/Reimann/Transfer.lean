import Std

/-!
The finite algebra used in the low-weight estimate.  All arithmetic inputs
(Hurewicz kernel, transfer identity, and geometric bound) appear as arguments.
The declarations use Lean's standard library only.
-/

namespace Reimann.Transfer

/-- The finite proof uses just an additive group and its homomorphisms.
The identities are also valid for a noncommutative group written additively. -/
structure GroupLaw (A : Type u) where
  zero : A
  add : A → A → A
  neg : A → A
  assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  neg_add : ∀ a, add (neg a) a = zero

structure Hom {A : Type u} {B : Type v} (G : GroupLaw A) (H : GroupLaw B) where
  app : A → B
  preserves_zero : app G.zero = H.zero
  preserves_add : ∀ a b, app (G.add a b) = H.add (app a) (app b)
  preserves_neg : ∀ a, app (G.neg a) = H.neg (app a)

/-- T01. Integer multiplication is built from the group law. -/
def multiple (G : GroupLaw A) : Nat → A → A
  | 0, _ => G.zero
  | n + 1, x => G.add (multiple G n x) x

theorem multiple_add (G : GroupLaw A) (a b : Nat) (x : A) :
    multiple G (a+b) x = G.add (multiple G a x) (multiple G b x) := by
  induction b with
  | zero => simp [multiple, G.add_zero]
  | succ b ih =>
    change G.add (multiple G (a+b) x) x =
      G.add (multiple G a x) (G.add (multiple G b x) x)
    rw [ih, G.assoc]

theorem multiple_mul (G : GroupLaw A) (a b : Nat) (x : A) :
    multiple G (a*b) x = multiple G a (multiple G b x) := by
  induction a with
  | zero => simp [multiple]
  | succ a ih => rw [Nat.succ_mul, multiple_add, ih, multiple]

theorem hom_multiple (G : GroupLaw A) (H : GroupLaw B) (f : Hom G H) (n : Nat) (x : A) :
    f.app (multiple G n x) = multiple H n (f.app x) := by
  induction n with
  | zero => exact f.preserves_zero
  | succ n ih => simp only [multiple, f.preserves_add, ih]

/-- T02. A certificate for an element of exact p-power order. -/
def HasPrimaryOrder (G : GroupLaw A) (p : Nat) (x : A) : Prop :=
  ∃ j : Nat, ∀ n : Nat, multiple G n x = G.zero ↔ p^j ∣ n

/-- Any certified upper bound on v_p(index) suffices. -/
def ValuationAtMost (p index v : Nat) : Prop :=
  ∀ j : Nat, p^j ∣ index → j ≤ v

/-- T02a. The same integer log bound works at every prime, including
prime divisors of the subgroup index. -/
theorem valuation_le_log2 (p index : Nat) (hp : 2 ≤ p) (hi : 0 < index) :
    ValuationAtMost p index index.log2 := by
  intro j hj
  have mono (n : Nat) : 2^n ≤ p^n := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [Nat.pow_succ] using Nat.mul_le_mul ih hp
  exact (Nat.le_log2 (by omega)).mpr (Nat.le_trans (mono j) (Nat.le_of_dvd hi hj))

/-- T02b. For the level-three subgroup, d = h*N^2. This elementary
integer bound avoids rounding a real logarithm. -/
theorem congruence_index_depth (index d : Nat) (hi : 0 < index)
    (bound : index ≤ 3^d) : index.log2 ≤ 2*d := by
  have powerBound (n : Nat) : (3:Nat)^n ≤ 4^n := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [Nat.pow_succ] using Nat.mul_le_mul ih (by decide : 3 ≤ 4)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [Nat.pow_mul]
  exact Nat.le_trans ((Nat.le_log2 (by omega : index ≠ 0)).mp (Nat.le_refl _))
    (Nat.le_trans bound (powerBound d))

theorem primary_index_annihilator (G : GroupLaw A) (p index v : Nat) (x : A)
    (order : HasPrimaryOrder G p x) (valuation : ValuationAtMost p index v)
    (h : multiple G index x = G.zero) : multiple G (p^v) x = G.zero := by
  obtain ⟨j, orderSpec⟩ := order
  exact (orderSpec _).mpr (Nat.pow_dvd_pow p (valuation j ((orderSpec _).mp h)))

/-- T03. Transfer followed by inclusion is multiplication by the subgroup
index. A kernel of p-depth u before transfer gains at most v further levels. -/
theorem transfer_kernel_depth (G : GroupLaw A) (H : GroupLaw B) (J : GroupLaw C)
    (f : Hom G H) (transfer : Hom H J) (inclusion : Hom J H)
    (p u index v : Nat) (valuation : ValuationAtMost p index v)
    (transfer_identity : ∀ y, inclusion.app (transfer.app y) = multiple H index y)
    (hurewicz : ∀ z, f.app z = H.zero → multiple G (p^u) z = G.zero)
    (x : A) (order : HasPrimaryOrder H p (f.app x))
    (hx : transfer.app (f.app x) = J.zero) :
    multiple G (p^(u+v)) x = G.zero := by
  have hindex : multiple H index (f.app x) = H.zero := by
    rw [← transfer_identity, hx, inclusion.preserves_zero]
  have hv := primary_index_annihilator H p index v (f.app x) order valuation hindex
  rw [Nat.pow_add, multiple_mul]
  apply hurewicz
  rw [hom_multiple, hv]

/-- T04. The two finite sets used in the image-kernel count. -/
def Kernel (G : GroupLaw A) (H : GroupLaw B) (f : Hom G H) :=
  {x : A // f.app x = H.zero}

def Image (G : GroupLaw A) (H : GroupLaw B) (f : Hom G H) :=
  {y : B // ∃ x, f.app x = y}

/-- Explicit bijections avoid any dependency on a cardinality library. -/
structure Bijection (A : Type u) (B : Type v) where
  forward : A → B
  backward : B → A
  left_inv : ∀ x, backward (forward x) = x
  right_inv : ∀ y, forward (backward y) = y

/-- T05. Every element has unique coordinates given by its image and a
kernel displacement from a chosen representative of that image. -/
noncomputable def imageKernelBijection (G : GroupLaw A) (H : GroupLaw B) (f : Hom G H) :
    Bijection A (Image G H f × Kernel G H f) := by
  let rep : Image G H f → A := fun y => Classical.choose y.property
  have rep_spec (y : Image G H f) : f.app (rep y) = y.val := Classical.choose_spec y.property
  let imageOf (x : A) : Image G H f := ⟨f.app x, x, rfl⟩
  let displacement (x : A) : Kernel G H f :=
    ⟨G.add x (G.neg (rep (imageOf x))), by
      rw [f.preserves_add, f.preserves_neg, rep_spec]
      exact H.add_neg (f.app x)⟩
  refine ⟨fun x => (imageOf x, displacement x),
    fun z => G.add z.2.val (rep z.1), ?_, ?_⟩
  · intro x
    change G.add (G.add x (G.neg (rep (imageOf x)))) (rep (imageOf x)) = x
    rw [G.assoc, G.neg_add, G.add_zero]
  · intro z
    rcases z with ⟨y, k⟩
    have hi : imageOf (G.add k.val (rep y)) = y := by
      apply Subtype.ext
      change f.app (G.add k.val (rep y)) = y.val
      rw [f.preserves_add, k.property, rep_spec, H.zero_add]
    apply Prod.ext
    · exact hi
    · apply Subtype.ext
      change G.add (G.add k.val (rep y)) (G.neg (rep (imageOf (G.add k.val (rep y))))) = k.val
      rw [hi, G.assoc, G.add_neg, G.add_zero]

/-- A concrete presentation of a finite type by an exhaustive list with no repeats. -/
structure Enumeration (A : Type u) where
  elements : List A
  distinct : elements.Nodup
  covers : ∀ x, x ∈ elements

private theorem nodupMap {f : A → B} (inj : ∀ x y, f x = f y → x = y)
    (xs : List A) (h : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hs⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hs⟩
    intro hm
    obtain ⟨b, hb, eq⟩ := List.mem_map.mp hm
    exact ha (inj b a eq ▸ hb)

private theorem bijection_card (e : Bijection A B) (xs : Enumeration A) (ys : Enumeration B) :
    xs.elements.length = ys.elements.length := by
  have hi : ∀ x y, e.forward x = e.forward y → x = y := by
    intro x y h
    simpa only [e.left_inv] using congrArg e.backward h
  have hp := List.perm_ext_iff_of_nodup (nodupMap hi xs.elements xs.distinct) ys.distinct
  have perm : (xs.elements.map e.forward).Perm ys.elements := hp.mpr (by
    intro b
    constructor
    · intro _; exact ys.covers b
    · intro _; exact List.mem_map.mpr ⟨e.backward b, xs.covers _, e.right_inv b⟩)
  simpa using perm.length_eq

private def pairs (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap (fun x => ys.map (Prod.mk x))

private theorem pairs_length (xs : List A) (ys : List B) :
    (pairs xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih =>
    change ((ys.map (Prod.mk x)) ++ pairs xs ys).length = (xs.length+1)*ys.length
    rw [List.length_append, List.length_map, ih, Nat.succ_mul, Nat.add_comm]

private theorem pairs_distinct (xs : List A) (ys : List B) (hx : xs.Nodup) (hy : ys.Nodup) :
    (pairs xs ys).Nodup := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp hx
    change ((ys.map (Prod.mk x)) ++ pairs xs ys).Nodup
    apply List.nodup_append.mpr
    refine ⟨nodupMap (fun _ _ h => congrArg Prod.snd h) _ hy, ih tail, ?_⟩
    intro a ha b hb hab
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨w, hw, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
    have heq : x = w := congrArg Prod.fst hab
    exact fresh (heq.symm ▸ hw)

private def productEnumeration (xs : Enumeration A) (ys : Enumeration B) :
    Enumeration (A × B) where
  elements := pairs xs.elements ys.elements
  distinct := pairs_distinct _ _ xs.distinct ys.distinct
  covers := by
    intro z
    rcases z with ⟨x,y⟩
    exact List.mem_flatMap.mpr ⟨x, xs.covers x, List.mem_map.mpr ⟨y, ys.covers y, rfl⟩⟩

/-- T06. For finite enumerations the bijection gives the exact numerical
identity |A| = |image f| * |kernel f|, even if the codomain is infinite. -/
theorem image_kernel_card (G : GroupLaw A) (H : GroupLaw B) (f : Hom G H)
    (domain : Enumeration A) (im : Enumeration (Image G H f))
    (ker : Enumeration (Kernel G H f)) :
    domain.elements.length = im.elements.length * ker.elements.length := by
  calc
    domain.elements.length = (productEnumeration im ker).elements.length :=
      bijection_card (imageKernelBijection G H f) domain (productEnumeration im ker)
    _ = _ := pairs_length _ _

/-- T07. The arithmetic bound on the kernel and the geometric bound on the
image enter separately here. -/
theorem order_bound (G : GroupLaw A) (H : GroupLaw B) (f : Hom G H)
    (domain : Enumeration A) (im : Enumeration (Image G H f))
    (ker : Enumeration (Kernel G H f)) (geometry arithmetic : Nat)
    (hi : im.elements.length ≤ geometry) (hk : ker.elements.length ≤ arithmetic) :
    domain.elements.length ≤ geometry * arithmetic := by
  rw [image_kernel_card G H f domain im ker]
  exact Nat.mul_le_mul hi hk

/-- T08. Integral bookkeeping for a rational exponent lattice. If
the degree-weight exponent plus the conductor exponent has a positive
margin, the displayed power of x is absorbed with precisely that margin. -/
theorem power_budget (x h R conductor weightDegree conductorExponent total gap : Nat)
    (hw : h*R^2 ≤ x^weightDegree) (hc : conductor ≤ x^conductorExponent)
    (hm : weightDegree + conductorExponent + gap = total) :
    (h*R^2*conductor)*x^gap ≤ x^total := by
  rw [← hm, Nat.pow_add, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hw hc)

/-- T09. At h fixed and R ≈ x^(ε/3), a conductor exponent ε/5 gives
13ε/15 before polylogarithmic factors. Exponents are in fifteenths. -/
theorem bottom_exponent_margin (e : Nat) : 2*(5*e)+3*e+2*e = 15*e := by omega

end Reimann.Transfer

