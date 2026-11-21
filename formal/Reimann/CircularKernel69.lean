import Reimann.CircularPrimitive69

/-! Multiplication by residues modulo 69 on the two products of cyclotomic factors.
The integers 1 and 276 encode the two values of the quadratic character. -/
namespace Reimann.CircularKernel69

open Lean.Grind Reimann.CircularPolynomial69 Reimann.CircularPrimitive69

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The units modulo 69 are exactly the residues of one of the two signs. -/
theorem unit_partition : ∀ a : Fin 69,
    Nat.gcd a.val 69 = 1 ↔ eta a.val = 1 ∨ eta a.val = 276 := by
  decide +kernel

theorem character_multiplicative : ∀ a b : Fin 69,
    eta ((a.val * b.val) % 69) = (eta a.val * eta b.val) % 277 := by
  decide +kernel

theorem positive_closed (a b : Fin 69) (ha : eta a.val = 1) (hb : eta b.val = 1) :
    eta ((a.val * b.val) % 69) = 1 := by
  rw [character_multiplicative, ha, hb]

theorem positive_contains_identity : eta 1 = 1 := by decide

theorem positive_contains_inverses : ∀ a : Fin 69, eta a.val = 1 →
    ∃ b : Fin 69, eta b.val = 1 ∧ (a.val * b.val) % 69 = 1 := by
  decide +kernel

theorem negative_representative : eta 2 = 276 := by decide

/-- Action on cyclotomic exponent labels. -/
def translate (b : Nat) (as : List Nat) : List Nat :=
  as.map (fun a => (b * a) % 69)

theorem positive_permutations : ∀ b : Fin 69, eta b.val = 1 →
    (translate b.val (exponents 1)).Perm (exponents 1) ∧
    (translate b.val (exponents 276)).Perm (exponents 276) := by
  decide +kernel

theorem negative_permutations : ∀ b : Fin 69, eta b.val = 276 →
    (translate b.val (exponents 1)).Perm (exponents 276) ∧
    (translate b.val (exponents 276)).Perm (exponents 1) := by
  decide +kernel

theorem other_coset :
    (translate 2 (exponents 1)).Perm (exponents 276) :=
  (negative_permutations 2 negative_representative).1

theorem power_of_power {R : Type} [CommRing R] (x : R) (b n : Nat) :
    (x^b)^n = x^(b*n) := by
  induction n with
  | zero => simp [Semiring.pow_zero]
  | succ n ih => rw [Semiring.pow_succ, ih, Nat.mul_succ, Semiring.pow_add]

theorem power_period {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1) (n : Nat) :
    x^n = x^(n % 69) := by
  calc
    x^n = x^(69 * (n / 69) + n % 69) := congrArg (fun k : Nat => x^k) (Nat.div_add_mod n 69).symm
    _ = x^(n % 69) := by
      rw [Semiring.pow_add, ← power_of_power, h69, Semiring.one_pow, Semiring.one_mul]

theorem translated_factor {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (b a : Nat) : 1 - (x^b)^a = 1 - x^((b*a) % 69) := by
  rw [power_of_power, power_period x h69 (b*a)]

theorem product_permutation {R : Type} [CommRing R] (x : R) {as bs : List Nat}
    (h : as.Perm bs) :
    eval x (factors as) = eval x (factors bs) := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [factors, eval_factor, ih]
  | swap a b rest =>
    simp only [factors, eval_factor]
    grind only
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem factors_at_power {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (b : Nat) (as : List Nat) :
    eval (x^b) (factors as) = eval x (factors (translate b as)) := by
  induction as with
  | nil => simp [factors, translate, eval, Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.add_zero]
  | cons a rest ih =>
    change eval (x^b) (factor a (factors rest)) =
      eval x (factor ((b*a) % 69) (factors (translate b rest)))
    rw [eval_factor, eval_factor, translated_factor x h69, ih]

theorem signed_action_of_permutation {R : Type} [CommRing R] (x : R)
    (h69 : x^69 = 1) (b sign target : Nat)
    (h : (translate b (exponents sign)).Perm (exponents target)) :
    signedProduct (x^b) sign = signedProduct x target := by
  change ((exponents sign).foldr _ 1) = ((exponents target).foldr _ 1)
  rw [← eval_factors, ← eval_factors, factors_at_power x h69,
    product_permutation x h]

theorem positive_action {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (b : Fin 69) (hb : eta b.val = 1) :
    signedProduct (x^b.val) 1 = signedProduct x 1 ∧
    signedProduct (x^b.val) 276 = signedProduct x 276 := by
  obtain ⟨hp, hn⟩ := positive_permutations b hb
  exact ⟨signed_action_of_permutation x h69 b.val 1 1 hp,
    signed_action_of_permutation x h69 b.val 276 276 hn⟩

theorem negative_action {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (b : Fin 69) (hb : eta b.val = 276) :
    signedProduct (x^b.val) 1 = signedProduct x 276 ∧
    signedProduct (x^b.val) 276 = signedProduct x 1 := by
  obtain ⟨hp, hn⟩ := negative_permutations b hb
  exact ⟨signed_action_of_permutation x h69 b.val 1 276 hp,
    signed_action_of_permutation x h69 b.val 276 1 hn⟩

theorem primitive_products_distinct {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hd : (621 : R) ≠ 0) :
    signedProduct x 1 ≠ signedProduct x 276 := by
  intro heq
  have ht := primitive_products_trace x h69 h23 h3
  have hdisc := primitive_product_discriminant x h69 h23 h3
  have hz : 2 * signedProduct x 1 - 25 = 0 := by grind only
  rw [hz] at hdisc
  exact hd (by grind only)

theorem positive_stabilizer_iff {R : Type} [CommRing R] (x : R)
    (h69 : x^69 = 1) (distinct : signedProduct x 1 ≠ signedProduct x 276)
    (b : Fin 69) (unit : Nat.gcd b.val 69 = 1) :
    signedProduct (x^b.val) 1 = signedProduct x 1 ↔ eta b.val = 1 := by
  constructor
  · intro fixed
    rcases (unit_partition b).mp unit with pos | neg
    · exact pos
    · exact False.elim (distinct (fixed.symm.trans (negative_action x h69 b neg).1))
  · intro pos
    exact (positive_action x h69 b pos).1

/-- For a primitive 69th root in characteristic zero, the stabilizer among
the 44 residue-unit power substitutions consists of the 22 positive labels. -/
theorem primitive_positive_stabilizer {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (b : Fin 69) (unit : Nat.gcd b.val 69 = 1) :
    signedProduct (x^b.val) 1 = signedProduct x 1 ↔ eta b.val = 1 := by
  have hd : (621 : R) ≠ 0 := by
    intro h
    have bad := (IsCharP.ofNat_eq_zero_iff 0 621).mp h
    exact (by decide : ¬ (621 : Nat) % 0 = 0) bad
  exact positive_stabilizer_iff x h69 (primitive_products_distinct x h69 h23 h3 hd) b unit

/-- Sum of root powers for a specified list of labels, including repetitions. -/
def periodSum {R : Type} [CommRing R] (x : R) (as : List Nat) : R :=
  as.foldr (fun a acc => x^a + acc) 0

theorem period_permutation {R : Type} [CommRing R] (x : R)
    {as bs : List Nat} (h : as.Perm bs) : periodSum x as = periodSum x bs := by
  induction h with
  | nil => rfl
  | cons a h ih => exact congrArg (fun v => x^a + v) ih
  | swap a b rest =>
    change x^b + (x^a + periodSum x rest) = x^a + (x^b + periodSum x rest)
    grind only
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem period_at_power {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (b : Nat) (as : List Nat) :
    periodSum (x^b) as = periodSum x (translate b as) := by
  induction as with
  | nil => rfl
  | cons a rest ih =>
    change (x^b)^a + periodSum (x^b) rest =
      x^((b*a) % 69) + periodSum x (translate b rest)
    rw [power_of_power, power_period x h69 (b*a), ih]

/-- A positive residue preserves both periods. -/
theorem positive_period_action {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (b : Fin 69) (hb : eta b.val = 1) :
    periodSum (x^b.val) (exponents 1) = periodSum x (exponents 1) ∧
    periodSum (x^b.val) (exponents 276) = periodSum x (exponents 276) := by
  obtain ⟨hp, hn⟩ := positive_permutations b hb
  exact ⟨(period_at_power x h69 _ _).trans (period_permutation x hp),
    (period_at_power x h69 _ _).trans (period_permutation x hn)⟩

/-- A negative residue exchanges the periods. -/
theorem negative_period_action {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (b : Fin 69) (hb : eta b.val = 276) :
    periodSum (x^b.val) (exponents 1) = periodSum x (exponents 276) ∧
    periodSum (x^b.val) (exponents 276) = periodSum x (exponents 1) := by
  obtain ⟨hp, hn⟩ := negative_permutations b hb
  exact ⟨(period_at_power x h69 _ _).trans (period_permutation x hp),
    (period_at_power x h69 _ _).trans (period_permutation x hn)⟩

end Reimann.CircularKernel69
