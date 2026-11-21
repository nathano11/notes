import Std

/-! Finite algebra of the cyclic coinvariant support test. -/
namespace Reimann.CoinvariantSupport

theorem surjective_iterate {A : Type} (d : A → A) (h : Function.Surjective d)
    (n : Nat) : Function.Surjective (Nat.repeat d n) := by
  induction n with
  | zero => exact fun x => ⟨x, rfl⟩
  | succ n ih =>
    intro x
    obtain ⟨y, hy⟩ := h x
    obtain ⟨z, hz⟩ := ih y
    exact ⟨z, by simpa only [Nat.repeat, hz] using hy⟩

/-- For d = T − 1, surjectivity is exactly the vanishing of its cokernel. -/
theorem surjective_nilpotent_iff {A : Type} (zero : A) (d : A → A) (n : Nat)
    (nilpotent : ∀ x, Nat.repeat d n x = zero) :
    Function.Surjective d ↔ ∀ x, x = zero := by
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := surjective_iterate d h n x
    exact hy.symm.trans (nilpotent y)
  · intro trivial x
    exact ⟨zero, (trivial _).trans (trivial x).symm⟩

theorem sub_map_zero {M : Type} [Lean.Grind.IntModule M] (d : M → M)
    (hd : ∀ x y, d (x-y) = d x-d y) : d 0 = 0 := by
  simpa only [Lean.Grind.AddCommGroup.sub_self] using hd 0 0

/-- Two additive classes agree modulo the image of d exactly when their
difference is the image of an element. -/
def imageSetoid {M : Type} [Lean.Grind.IntModule M] (d : M → M)
    (hd : ∀ x y, d (x-y) = d x-d y) : Setoid M where
  r x y := ∃ z, x-y = d z
  iseqv := {
    refl := fun x => ⟨0, (Lean.Grind.AddCommGroup.sub_self x).trans (sub_map_zero d hd).symm⟩
    symm := by
      intro x y h
      obtain ⟨z, hz⟩ := h
      exact ⟨0-z, by rw [hd, sub_map_zero d hd]; grind⟩
    trans := by
      intro x y z h₁ h₂
      obtain ⟨u, hu⟩ := h₁
      obtain ⟨v, hv⟩ := h₂
      exact ⟨u-(0-v), by rw [hd, hd, sub_map_zero d hd]; grind⟩
  }

theorem quotient_trivial_iff_surjective {M : Type} [Lean.Grind.IntModule M]
    (d : M → M) (hd : ∀ x y, d (x-y) = d x-d y) :
    Subsingleton (Quotient (imageSetoid d hd)) ↔ Function.Surjective d := by
  constructor
  · intro h x
    have eq := h.allEq (Quotient.mk (imageSetoid d hd) x) (Quotient.mk (imageSetoid d hd) 0)
    obtain ⟨z, hz⟩ := Quotient.exact eq
    change x-0 = d z at hz
    exact ⟨z, by grind⟩
  · intro h
    constructor
    intro a b
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        obtain ⟨z, hz⟩ := h (x-y)
        exact Quotient.sound ⟨z, hz.symm⟩

theorem nilpotent_cokernel_trivial_iff {M : Type} [Lean.Grind.IntModule M]
    (d : M → M) (hd : ∀ x y, d (x-y) = d x-d y) (n : Nat)
    (nilpotent : ∀ x, Nat.repeat d n x = 0) :
    Subsingleton (Quotient (imageSetoid d hd)) ↔ Subsingleton M := by
  rw [quotient_trivial_iff_surjective d hd, surjective_nilpotent_iff 0 d n nilpotent]
  constructor
  · exact fun h => ⟨fun x y => (h x).trans (h y).symm⟩
  · exact fun h x => h.allEq x 0

theorem augmentation_sub {M : Type} [Lean.Grind.IntModule M] (T : M → M)
    (linear : ∀ x y, T (x-y) = T x-T y) (x y : M) :
    T (x-y) - (x-y) = (T x-x) - (T y-y) := by
  rw [linear]
  grind

/-- The third power is expanded before specializing either the characteristic
or the order of the operator. -/
theorem augmentation_cube {M : Type} [Lean.Grind.IntModule M] (T : M → M)
    (linear : ∀ x y, T (x-y) = T x-T y) (x : M) :
    Nat.repeat (fun y => T y-y) 3 x =
      T (T (T x)) - x + (3 : Int) • T x - (3 : Int) • T (T x) := by
  simp only [Nat.repeat, linear]
  grind

theorem augmentation_cube_zero {M : Type} [Lean.Grind.IntModule M] (T : M → M)
    (linear : ∀ x y, T (x-y) = T x-T y) (order : ∀ x, T (T (T x)) = x)
    (charThree : ∀ x : M, (3 : Int) • x = 0) (x : M) :
    Nat.repeat (fun y => T y-y) 3 x = 0 := by
  rw [augmentation_cube T linear, order, charThree, charThree]
  grind

/-- The actual quotient by (T−1)M is trivial exactly when M is trivial. -/
theorem cyclic_three_coinvariants_trivial_iff {M : Type} [Lean.Grind.IntModule M]
    (T : M → M) (linear : ∀ x y, T (x-y) = T x-T y)
    (order : ∀ x, T (T (T x)) = x) (charThree : ∀ x : M, (3 : Int) • x = 0) :
    Subsingleton (Quotient (imageSetoid (fun x => T x-x) (augmentation_sub T linear))) ↔
      Subsingleton M :=
  nilpotent_cokernel_trivial_iff _ _ 3 (augmentation_cube_zero T linear order charThree)

/-- Pascal coefficients used to expand the order-p relation on the module. -/
def binomial : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => binomial n k + binomial n (k+1)

theorem binomial_zero_column (n : Nat) : binomial n 0 = 1 := by
  cases n <;> rfl

theorem binomial_above (n k : Nat) (h : n < k) : binomial n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [binomial]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [binomial, ih k (by omega), ih (k+1) (by omega)]

theorem binomial_diag (n : Nat) : binomial n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [binomial, ih, binomial_above n (n+1) (by omega)]

/-- Count a subset together with a distinguished member in either order. -/
theorem binomial_marked (n k : Nat) :
    (k+1) * binomial (n+1) (k+1) = (n+1) * binomial n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [binomial]
  | succ n ih =>
    cases k with
    | zero =>
      have h := ih 0
      simp only [Nat.zero_add, Nat.one_mul, binomial_zero_column, Nat.mul_one] at h
      change 1 * (binomial (n+1) 0 + binomial (n+1) 1) = (n+2) * binomial (n+1) 0
      rw [binomial_zero_column, h]
      omega
    | succ k =>
      have h := ih k
      have j := ih (k+1)
      change (k+2) * (binomial (n+1) (k+1) + binomial (n+1) (k+2)) =
        (n+2) * binomial (n+1) (k+1)
      have pascal : binomial (n+1) (k+1) = binomial n k + binomial n (k+1) := rfl
      grind

theorem prime_dvd_middle (p k : Nat) (hk : 0 < k) (hkp : k < p)
    (prime : ∀ j, 0 < j → j < p → Nat.Coprime p j) :
    p ∣ binomial p k := by
  cases p with
  | zero => omega
  | succ n =>
    cases k with
    | zero => omega
    | succ j =>
      apply (prime _ hk hkp).dvd_of_dvd_mul_left
      rw [binomial_marked]
      exact Nat.dvd_mul_right _ _

/-- The prefix of the nth Pascal row applied to a sequence of module elements. -/
def rowSum {M : Type} [Lean.Grind.IntModule M] (n : Nat) (f : Nat → M) : Nat → M
  | 0 => 0
  | k+1 => rowSum n f k + (binomial n k : Int) • f k

theorem rowSum_add {M : Type} [Lean.Grind.IntModule M] (n k : Nat) (f g : Nat → M) :
    rowSum n (fun i => f i + g i) k = rowSum n f k + rowSum n g k := by
  induction k with
  | zero => simp only [rowSum]; grind
  | succ k ih =>
    simp only [rowSum, ih, Lean.Grind.IntModule.zsmul_add]
    grind

theorem rowSum_pascal {M : Type} [Lean.Grind.IntModule M] (n k : Nat) (f : Nat → M) :
    rowSum (n+1) f (k+1) = rowSum n f (k+1) + rowSum n (fun i => f (i+1)) k := by
  induction k with
  | zero =>
    simp only [rowSum, binomial_zero_column]
    grind
  | succ k ih =>
    change rowSum (n+1) f (k+1) + ((↑(binomial n k + binomial n (k+1)) : Int)) • f (k+1) =
      (rowSum n f (k+1) + (binomial n (k+1) : Int) • f (k+1)) +
      (rowSum n (fun i => f (i+1)) k + (binomial n k : Int) • f (k+1))
    rw [ih, Int.natCast_add,
      Lean.Grind.IntModule.add_zsmul]
    grind

theorem rowSum_next {M : Type} [Lean.Grind.IntModule M] (n : Nat) (f : Nat → M) :
    rowSum (n+1) f (n+2) = rowSum n (fun i => f i + f (i+1)) (n+1) := by
  rw [rowSum_pascal, rowSum_add]
  have endTerm : rowSum n f (n+2) = rowSum n f (n+1) := by
    change rowSum n f (n+1) + (binomial n (n+1) : Int) • f (n+1) = rowSum n f (n+1)
    rw [binomial_above n (n+1) (by omega)]
    grind
  rw [endTerm]

theorem repeat_shift {M : Type} (T : M → M) (n : Nat) (x : M) :
    Nat.repeat T (n+1) x = Nat.repeat T n (T x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg T ih

theorem augmentation_commutes {M : Type} [Lean.Grind.IntModule M] (T : M → M)
    (linear : ∀ x y, T (x-y) = T x-T y) (i : Nat) (x : M) :
    Nat.repeat (fun y => T y-y) i (T x) = T (Nat.repeat (fun y => T y-y) i x) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Nat.repeat, ih, linear]

theorem operator_binomial {M : Type} [Lean.Grind.IntModule M] (T : M → M)
    (linear : ∀ x y, T (x-y) = T x-T y) (n : Nat) (x : M) :
    Nat.repeat T n x = rowSum n (fun i => Nat.repeat (fun y => T y-y) i x) (n+1) := by
  induction n generalizing x with
  | zero => simp only [Nat.repeat, rowSum, binomial]; grind
  | succ n ih =>
    rw [repeat_shift, ih, rowSum_next]
    apply congrArg (fun f => rowSum n f (n+1))
    funext i
    rw [augmentation_commutes T linear]
    simp only [Nat.repeat]
    grind

theorem characteristic_kills_multiple {M : Type} [Lean.Grind.IntModule M] (p c : Nat)
    (h : p ∣ c) (charP : ∀ x : M, (p : Int) • x = 0) (x : M) :
    (c : Int) • x = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [hk, Nat.mul_comm, Int.natCast_mul, Lean.Grind.IntModule.mul_zsmul, charP,
    Lean.Grind.IntModule.zsmul_zero]

theorem prime_prefix {M : Type} [Lean.Grind.IntModule M] (p : Nat)
    (prime : ∀ j, 0 < j → j < p → Nat.Coprime p j)
    (charP : ∀ x : M, (p : Int) • x = 0) (f : Nat → M) (k : Nat) (hk : k < p) :
    rowSum p f (k+1) = f 0 := by
  induction k with
  | zero => simp only [rowSum, binomial_zero_column]; grind
  | succ k ih =>
    change rowSum p f (k+1) + (binomial p (k+1) : Int) • f (k+1) = f 0
    rw [ih (by omega), characteristic_kills_multiple p _ (prime_dvd_middle p _ (by omega) hk prime) charP]
    grind

theorem prime_row_endpoints {M : Type} [Lean.Grind.IntModule M] (p : Nat) (hp : 1 < p)
    (prime : ∀ j, 0 < j → j < p → Nat.Coprime p j)
    (charP : ∀ x : M, (p : Int) • x = 0) (f : Nat → M) :
    rowSum p f (p+1) = f 0 + f p := by
  cases p with
  | zero => omega
  | succ k =>
    change rowSum (k+1) f (k+1) + (binomial (k+1) (k+1) : Int) • f (k+1) = _
    rw [prime_prefix (k+1) prime charP f k (by omega), binomial_diag]
    grind

/-- In characteristic p an action with T^p = 1 has (T−1)^p = 0.
Primality is expressed by coprimality with every integer strictly between 0 and p. -/
theorem augmentation_prime_zero {M : Type} [Lean.Grind.IntModule M] (p : Nat) (hp : 1 < p)
    (prime : ∀ j, 0 < j → j < p → Nat.Coprime p j)
    (charP : ∀ x : M, (p : Int) • x = 0) (T : M → M) (linear : ∀ x y, T (x-y) = T x-T y)
    (order : ∀ x, Nat.repeat T p x = x) (x : M) :
    Nat.repeat (fun y => T y-y) p x = 0 := by
  have e := operator_binomial T linear p x
  rw [order, prime_row_endpoints p hp prime charP] at e
  simp only [Nat.repeat] at e
  grind

/-- A cyclic group of prime order acting on a group killed by p has
nonzero coinvariants exactly when the module itself is nonzero. -/
theorem cyclic_prime_coinvariants_trivial_iff {M : Type} [Lean.Grind.IntModule M]
    (p : Nat) (hp : 1 < p) (prime : ∀ j, 0 < j → j < p → Nat.Coprime p j)
    (charP : ∀ x : M, (p : Int) • x = 0) (T : M → M) (linear : ∀ x y, T (x-y) = T x-T y)
    (order : ∀ x, Nat.repeat T p x = x) :
    Subsingleton (Quotient (imageSetoid (fun x => T x-x) (augmentation_sub T linear))) ↔
      Subsingleton M :=
  nilpotent_cokernel_trivial_iff _ _ p (augmentation_prime_zero p hp prime charP T linear order)

end Reimann.CoinvariantSupport
