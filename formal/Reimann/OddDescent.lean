import Std

/-!
# Odd-prime descent and the arithmetic of its finite readouts

The global/local cohomology and number-field inputs of the paper are hypotheses
of the corresponding interface theorems below. The formal results prove the
descent construction, the reflection kernel argument, and the exponent
combinatorics from those inputs. No field-theoretic comparison is postulated
as an axiom.
-/

namespace Reimann.OddDescent

/-- Two maps are two-sided inverses. This small definition uses only core Lean. -/
structure InverseMaps (A B : Type) where
  forward : A → B
  backward : B → A
  backward_forward : ∀ a, backward (forward a) = a
  forward_backward : ∀ b, forward (backward b) = b

/-- Finite-class lifts, their images over the original field and over the
cyclotomic extension, and the obstruction to lifting a restricted character. -/
structure DescentInputs (Place Lift Torsion Character Obstruction : Type) where
  place : Place
  project : Lift → Torsion
  restrict : Lift → Character
  strict : Torsion → Prop
  localZero : Character → Place → Prop
  localInflation : Lift → Place → Prop
  sameInflationCoset : Lift → Lift → Prop
  boundaryComparison : ∀ f g, project f = project g ↔ sameInflationCoset f g
  restrictionKernel : ∀ f g, restrict f = restrict g ↔ sameInflationCoset f g
  torsionLifts : ∀ a, ∃ f, project f = a
  localBoundaryComparison : ∀ f, strict (project f) ↔ ∀ v, localInflation f v
  localRestrictionKernel : ∀ f v, localInflation f v ↔ localZero (restrict f) v
  zeroObstruction : Obstruction
  transgression : Character → Obstruction
  localTransgression : Place → Character → Obstruction
  naturalityFullDecomposition : ∀ v x, transgression x = localTransgression v x
  localTransgressionZero : ∀ v x, localZero x v → localTransgression v x = zeroObstruction
  fiveTermExact : ∀ x, transgression x = zeroObstruction ↔ ∃ f, restrict f = x

namespace DescentInputs

variable {P F A C H : Type} (d : DescentInputs P F A C H)

/-- Finite representatives agree after projection precisely when their
restricted characters agree. -/
theorem equal_fibers (f g : F) :
    d.project f = d.project g ↔ d.restrict f = d.restrict g :=
  (d.boundaryComparison f g).trans (d.restrictionKernel f g).symm

theorem strict_iff_split (f : F) :
    d.strict (d.project f) ↔ ∀ v, d.localZero (d.restrict f) v := by
  constructor
  · intro hs v
    exact (d.localRestrictionKernel f v).mp ((d.localBoundaryComparison f).mp hs v)
  · intro hs
    exact (d.localBoundaryComparison f).mpr (fun v => (d.localRestrictionKernel f v).mpr (hs v))

/-- A split character has zero global transgression by looking at any one
place with full decomposition, hence it has a finite-coefficient global lift. -/
theorem split_lifts (x : C) (hx : ∀ v, d.localZero x v) :
    ∃ f, d.restrict f = x := by
  apply (d.fiveTermExact x).mp
  exact (d.naturalityFullDecomposition d.place x).trans
    (d.localTransgressionZero d.place x (hx d.place))

/-- The two strict groups in the finite descent theorem have inverse maps.
The field, cohomology and class-field identifications are the inputs above. -/
noncomputable def strictCorrespondence :
    InverseMaps {a : A // d.strict a} {x : C // ∀ v, d.localZero x v} := by
  classical
  let fA (a : {a : A // d.strict a}) : F := Classical.choose (d.torsionLifts a.val)
  have hA (a : {a : A // d.strict a}) : d.project (fA a) = a.val :=
    Classical.choose_spec (d.torsionLifts a.val)
  let fC (x : {x : C // ∀ v, d.localZero x v}) : F :=
    Classical.choose (d.split_lifts x.val x.property)
  have hC (x : {x : C // ∀ v, d.localZero x v}) : d.restrict (fC x) = x.val :=
    Classical.choose_spec (d.split_lifts x.val x.property)
  let f (a : {a : A // d.strict a}) : {x : C // ∀ v, d.localZero x v} :=
    ⟨d.restrict (fA a), (d.strict_iff_split (fA a)).mp ((hA a).symm ▸ a.property)⟩
  let g (x : {x : C // ∀ v, d.localZero x v}) : {a : A // d.strict a} :=
    ⟨d.project (fC x), (d.strict_iff_split (fC x)).mpr ((hC x).symm ▸ x.property)⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    exact ((d.equal_fibers (fC (f a)) (fA a)).mpr (hC (f a))).trans (hA a)
  · intro x
    apply Subtype.ext
    exact ((d.equal_fibers (fA (g x)) (fC x)).mp (hA (g x))).trans (hC x)

end DescentInputs

/-- Cyclic-quotient index at the exceptional residual character. A scalar
of valuation w has p-power part p^w, and its remaining factor is a unit
against each power of p. This gcd gives the index p^(min n w). -/
theorem exceptional_cyclic_index (p n w u : Nat)
    (unit : ∀ j, Nat.gcd (p^j) u = 1) :
    Nat.gcd (p^n) (p^w*u) = p^(min n w) := by
  by_cases h : n ≤ w
  · have hw : p^w = p^n*p^(w-n) := by
      calc
        p^w = p^(n+(w-n)) := congrArg (fun j : Nat => p^j) (by omega)
        _ = _ := Nat.pow_add _ _ _
    have hd : p^n ∣ p^w*u := by
      refine ⟨p^(w-n)*u, ?_⟩
      rw [hw, Nat.mul_assoc]
    rw [Nat.gcd_eq_left hd, Nat.min_eq_left h]
  · have hn : p^n = p^w*p^(n-w) := by
      calc
        p^n = p^(w+(n-w)) := congrArg (fun j : Nat => p^j) (by omega)
        _ = _ := Nat.pow_add _ _ _
    rw [hn, Nat.gcd_mul_left, unit, Nat.mul_one, Nat.min_eq_right (by omega)]

/-- Kernel argument for the minus-radical reflection map. Multiplicative
differences are represented by the type R in this statement. The supplied
maps are on the split minus Kummer radicals, their unit representatives,
the eligible roots, local classes, and ordinary ideal classes. -/
theorem reflection_kernel
    {R U Roots L C : Type} (oneR : R) (oneRoots : Roots) (oneL : L) (oneC : C)
    (ideal : R → C) (unitRadical : U → R) (rootRadical : Roots → R)
    (localRoot : Roots → L) (localRadical : R → L)
    (principal : ∀ x, ideal x = oneC → ∃ u, unitRadical u = x)
    (minusUnits : ∀ u, ∃ z, rootRadical z = unitRadical u)
    (localCompatibility : ∀ z, localRadical (rootRadical z) = localRoot z)
    (localSplit : ∀ x, localRadical x = oneL)
    (localRoots : ∀ z, localRoot z = oneL → z = oneRoots)
    (rootOne : rootRadical oneRoots = oneR)
    (x : R) (hx : ideal x = oneC) : x = oneR := by
  obtain ⟨u, hu⟩ := principal x hx
  obtain ⟨z, hz⟩ := minusUnits u
  have hz0 : localRoot z = oneL :=
    (localCompatibility z).symm.trans (localSplit (rootRadical z))
  have hroot : z = oneRoots := localRoots z hz0
  exact hu.symm.trans (hz.symm.trans ((congrArg rootRadical hroot).trans rootOne))

/-- A trivial kernel gives injectivity for a map respecting differences. -/
theorem injective_of_difference_kernel
    {R C : Type} (oneR : R) (oneC : C) (ideal : R → C)
    (difference : R → R → R)
    (differenceZero : ∀ x y, difference x y = oneR → x = y)
    (idealDifference : ∀ x y, ideal x = ideal y → ideal (difference x y) = oneC)
    (trivialKernel : ∀ x, ideal x = oneC → x = oneR)
    (x y : R) (heq : ideal x = ideal y) : x = y :=
  differenceZero x y (trivialKernel _ (idealDifference x y heq))

/-- Iterating the scalar action models a cyclotomic character power. -/
def iterate {A : Type} (step : A → A) : Nat → A → A
  | 0, x => x
  | n+1, x => step (iterate step n x)

/-- The action on μ-valued characters adds one cyclotomic power to the
contragredient action on the additive character. -/
theorem reflected_weight {S A : Type} (f : S → A) (ginv : S → S)
    (unitAction : A → A) (r : Nat)
    (contragredient : ∀ x, f (ginv x) = iterate unitAction r (f x)) (x : S) :
    unitAction (f (ginv x)) = iterate unitAction (r+1) (f x) :=
  congrArg unitAction (contragredient x)

theorem reflected_conjugation {S A : Type} (f : S → A) (c : S → S)
    (negate : A → A) (plus : ∀ x, f (c x) = f x) (x : S) :
    negate (f (c x)) = negate (f x) := congrArg negate (plus x)

theorem iterate_add {A : Type} (step : A → A) (m n : Nat) (x : A) :
    iterate step (m+n) x = iterate step n (iterate step m x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

theorem iterate_add_periods {A : Type} (step : A → A) (m : Nat)
    (period : ∀ x, iterate step m x = x) (r k : Nat) (x : A) :
    iterate step (r+m*k) x = iterate step r x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, iterate_add, period, ih]

theorem iterate_mod_period {A : Type} (step : A → A) (m : Nat)
    (period : ∀ x, iterate step m x = x) (r : Nat) (x : A) :
    iterate step r x = iterate step (r%m) x := by
  calc
    iterate step r x = iterate step (r%m+m*(r/m)) x :=
      congrArg (fun j => iterate step j x) (Nat.mod_add_div r m).symm
    _ = iterate step (r%m) x := iterate_add_periods step m period (r%m) (r/m) x

theorem congruent_weights {A : Type} (step : A → A) (m : Nat)
    (period : ∀ x, iterate step m x = x) (r s : Nat) (same : r%m = s%m) (x : A) :
    iterate step r x = iterate step s x := by
  calc
    iterate step r x = iterate step (r%m) x := iterate_mod_period step m period r x
    _ = iterate step (s%m) x := congrArg (fun j => iterate step j x) same
    _ = iterate step s x := (iterate_mod_period step m period s x).symm

/-- No residual-trivial weight in the indicated large-prime window. -/
theorem large_prime_weight {p h r t : Nat} (hp : 2*t < p) (hr : 0 < r) (hrt : r < t)
    (horder : h = p-1 ∨ h = (p-1)/2) : ¬ h ∣ r := by
  have ht : t ≤ h := by rcases horder with h | h <;> omega
  intro hd
  have := Nat.le_of_dvd hr hd
  omega

/-- A finite sum indexed from zero, used to count the cost of each
tame eigenspace just once per complete cycle of weights. -/
def prefixCost (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => prefixCost cost n + cost n

theorem prefixCost_add (cost : Nat → Nat) (a b : Nat) :
    prefixCost cost (a+b) = prefixCost cost a + prefixCost (fun i => cost (a+i)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change prefixCost cost (a+b) + cost (a+b) =
      prefixCost cost a + (prefixCost (fun i => cost (a+i)) b + cost (a+b))
    rw [ih, Nat.add_assoc]

theorem prefixCost_mono (cost : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    prefixCost cost a ≤ prefixCost cost b := by
  have hsum : a + (b-a) = b := by omega
  have hs := prefixCost_add cost a (b-a)
  rw [hsum] at hs
  omega

theorem periodic_shift (cost : Nat → Nat) (h : Nat)
    (period : ∀ j, cost (j+h) = cost j) (k j : Nat) : cost (h*k+j) = cost j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : h*k+h+j = h*k+j+h := by omega
    rw [Nat.mul_succ, hs, period, ih]

theorem complete_block_cost (cost : Nat → Nat) (h : Nat)
    (period : ∀ j, cost (j+h) = cost j) (k : Nat) :
    prefixCost cost (h*k) = k * prefixCost cost h := by
  induction k with
  | zero => simp [prefixCost]
  | succ k ih =>
    have hfun : (fun j => cost (h*k+j)) = cost :=
      funext (periodic_shift cost h period k)
    rw [Nat.mul_succ, prefixCost_add, hfun, ih, Nat.succ_mul]

/-- The section 7 saving across weights, before bounding the Kummer group:
T consecutive weight costs are bounded by ceil(T/h) times one full cycle. -/
theorem weight_window_cost (cost : Nat → Nat) (h t : Nat) (hh : 0 < h)
    (period : ∀ j, cost (j+h) = cost j) :
    prefixCost cost t ≤ ((t+h-1)/h) * prefixCost cost h := by
  have hcover : t ≤ h*((t+h-1)/h) := by
    have hdecomp := Nat.mod_add_div (t+h-1) h
    have hrem := Nat.mod_lt (t+h-1) hh
    omega
  calc
    prefixCost cost t ≤ prefixCost cost (h*((t+h-1)/h)) := prefixCost_mono cost hcover
    _ = _ := complete_block_cost cost h period _

/-- Sum of exponents in the subgroup killed by p^n, represented by an
elementary-divisor list whose entries are the factor exponents. -/
def cappedLength : List Nat → Nat → Nat
  | [], _ => 0
  | e :: es, n => min e n + cappedLength es n

/-- Number of cyclic factors of exponent strictly greater than n. -/
def width : List Nat → Nat → Nat
  | [], _ => 0
  | e :: es, n => (if n < e then 1 else 0) + width es n

theorem capped_succ (es : List Nat) (n : Nat) :
    cappedLength es (n+1) = cappedLength es n + width es n := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [cappedLength, width, ih]
    by_cases he : n < e
    · have h0 : min e n = n := Nat.min_eq_right (by omega)
      have h1 : min e (n+1) = n+1 := Nat.min_eq_right (by omega)
      rw [h0, h1, ite_eq_left he]
      omega
    · have h0 : min e n = e := Nat.min_eq_left (by omega)
      have h1 : min e (n+1) = e := Nat.min_eq_left (by omega)
      rw [h0, h1, ite_eq_right he]
      omega

/-- Multiplicity of a given exponent in elementary-divisor data. -/
def multiplicity : List Nat → Nat → Nat
  | [], _ => 0
  | a :: as, e => (if a = e then 1 else 0) + multiplicity as e

theorem width_drop (es : List Nat) (n : Nat) :
    width es n = width es (n+1) + multiplicity es (n+1) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [width, multiplicity, ih]
    by_cases he : e = n+1
    · have h0 : n < e := by omega
      have h1 : ¬n+1 < e := by omega
      simp only [ite_eq_left he, ite_eq_left h0, ite_eq_right h1] <;> omega
    · by_cases h0 : n < e
      · have h1 : n+1 < e := by omega
        simp only [ite_eq_right he, ite_eq_left h0, ite_eq_left h1] <;> omega
      · have h1 : ¬n+1 < e := by omega
        simp only [ite_eq_right he, ite_eq_right h0, ite_eq_right h1] <;> omega

/-- Three successive finite-depth log orders recover one exact factor
multiplicity. Thus comparison of the capped groups goes beyond exponents. -/
theorem equal_multiplicity_from_caps (l₁ l₂ : List Nat) (n : Nat)
    (h0 : cappedLength l₁ n = cappedLength l₂ n)
    (h1 : cappedLength l₁ (n+1) = cappedLength l₂ (n+1))
    (h2 : cappedLength l₁ (n+1+1) = cappedLength l₂ (n+1+1)) :
    multiplicity l₁ (n+1) = multiplicity l₂ (n+1) := by
  have ha := capped_succ l₁ n
  have hb := capped_succ l₂ n
  have hc := capped_succ l₁ (n+1)
  have hd := capped_succ l₂ (n+1)
  have he := width_drop l₁ n
  have hf := width_drop l₂ n
  omega

theorem width_zero_iff (es : List Nat) (n : Nat) :
    width es n = 0 ↔ ∀ e, e ∈ es → e ≤ n := by
  induction es with
  | nil => simp [width]
  | cons e es ih =>
    constructor
    · intro hw a ha
      change (if n < e then 1 else 0) + width es n = 0 at hw
      have he : e ≤ n := by
        by_cases h : n < e
        · rw [ite_eq_left h] at hw
          omega
        · omega
      have hw' : width es n = 0 := by omega
      rcases List.mem_cons.mp ha with h | h
      · simpa only [h] using he
      · exact ih.mp hw' a h
    · intro hall
      have he : e ≤ n := hall e (by simp)
      have hw : width es n = 0 := ih.mpr (fun a ha => hall a (List.mem_cons_of_mem _ ha))
      change (if n < e then 1 else 0) + width es n = 0
      rw [ite_eq_right (by omega), hw]

theorem plateau_iff (es : List Nat) (n : Nat) :
    cappedLength es (n+1) = cappedLength es n ↔ ∀ e, e ∈ es → e ≤ n := by
  rw [capped_succ]
  constructor
  · intro heq
    exact (width_zero_iff es n).mp (by omega)
  · intro h
    rw [(width_zero_iff es n).mpr h, Nat.add_zero]

end Reimann.OddDescent
