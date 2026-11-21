import Std

namespace ReimannWindow.DyadicBaseMatrix

/-- Matrices act on column vectors in the ordered basis `(b,c)`. -/
structure Mat2 (R : Type) where
  tl : R
  tr : R
  bl : R
  br : R
  deriving DecidableEq

def Mat2.mul {R : Type} [Add R] [Mul R] (a b : Mat2 R) : Mat2 R :=
  ⟨a.tl * b.tl + a.tr * b.bl, a.tl * b.tr + a.tr * b.br,
   a.bl * b.tl + a.br * b.bl, a.bl * b.tr + a.br * b.br⟩

def Mat2.subScalar {R : Type} [Sub R] (a : Mat2 R) (s : R) : Mat2 R :=
  ⟨a.tl - s, a.tr, a.bl, a.br - s⟩

def Mat2.det {R : Type} [Sub R] [Mul R] (a : Mat2 R) : R :=
  a.tl * a.br - a.tr * a.bl

def Mat2.map {R S : Type} (f : R → S) (a : Mat2 R) : Mat2 S :=
  ⟨f a.tl, f a.tr, f a.bl, f a.br⟩

/-- Reduction modulo eight retains the parity of the quotient by four on `4ℤ₂`. -/
def quarterBit (x : Fin 8) : Fin 2 :=
  ⟨x.val / 4, by have hx := x.isLt; omega⟩

def polynomial (c₀ c₁ t : Fin 8) : Fin 8 := t * t + c₁ * t + c₀

/-- Five is its own inverse modulo eight. These are the arguments `1/5−1`
and `−1/5−1` after reduction. -/
theorem evaluation_arguments :
    (5 * 5 : Fin 8) = 1 ∧ (5 - 1 : Fin 8) = 4 ∧ (0 - 5 - 1 : Fin 8) = 2 := by
  decide
-- breakpoint evaluation_arguments

/-- A power-series unit evaluates to an odd scalar. Over Fin 8 an odd
multiple of 4 still has residue 4; each evaluation may have a different unit. -/
theorem odd_multiple_of_four : ∀ u : Fin 8, u.val % 2 = 1 → u * 4 = 4 := by
  decide
-- breakpoint odd_multiple_of_four

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The two residues determine the coefficients to the necessary precision.
They imply both coefficient parities without additional hypotheses. -/
theorem evaluations_iff_coefficients :
    ∀ (c₀ c₁ : Fin 8),
      (polynomial c₀ c₁ 4 = 4 ∧ polynomial c₀ c₁ 2 = 4) ↔
        c₀ = 4 ∧ c₁.val % 4 = 2 := by
  decide
-- breakpoint evaluations_iff_coefficients

/-- The companion matrix of `P(T)=T²+C₁T+C₀` for the action `γ=1+T`. -/
def companion (c₀ c₁ : Fin 8) : Mat2 (Fin 8) :=
  ⟨1, 0 - c₀, 1, 1 - c₁⟩

/-- `γ² − u² I`, with the diagonal scalar subtracted after matrix multiplication. -/
def baseDifference (c₀ c₁ u : Fin 8) : Mat2 (Fin 8) :=
  let g := companion c₀ c₁
  (g.mul g).subScalar (u * u)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Both coefficient congruences fix the diagonal modulo eight. The lower-left
entry is `2−C₁` modulo eight. All four entries are divisible by four. -/
theorem base_matrix_mod_eight :
    ∀ (c₁ u : Fin 8), c₁.val % 4 = 2 → u.val % 2 = 1 →
      baseDifference 4 c₁ u = ⟨4, 0, 2 - c₁, 4⟩ := by
  decide
-- breakpoint base_matrix_mod_eight

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The exact normalized matrix over `ℤ/2` has determinant one. The bit in its
lower-left corner is the parity of `(C₁−2)/4`, allowing both lifts modulo eight. -/
theorem normalized_base_matrix :
    ∀ (c₁ u : Fin 8), c₁.val % 4 = 2 → u.val % 2 = 1 →
      let n := (baseDifference 4 c₁ u).map quarterBit
      n = ⟨1, 0, quarterBit c₁, 1⟩ ∧ n.det = 1 := by
  decide
-- breakpoint normalized_base_matrix

/-- Compose both finite steps, starting with the two polynomial values. -/
theorem normalized_base_from_values (c₀ c₁ u : Fin 8)
    (hplus : polynomial c₀ c₁ 4 = 4) (hminus : polynomial c₀ c₁ 2 = 4)
    (hu : u.val % 2 = 1) :
    let n := (baseDifference c₀ c₁ u).map quarterBit
    n = ⟨1, 0, quarterBit c₁, 1⟩ ∧ n.det = 1 := by
  obtain ⟨h₀, h₁⟩ := (evaluations_iff_coefficients c₀ c₁).mp ⟨hplus, hminus⟩
  subst c₀
  exact normalized_base_matrix c₁ u h₁ hu
-- breakpoint normalized_base_from_values

def Mat2.diagonal {R : Type} [Zero R] (s : R) : Mat2 R := ⟨s, 0, 0, s⟩

def Mat2.addScalar {R : Type} [Add R] (m : Mat2 R) (s : R) : Mat2 R :=
  ⟨m.tl + s, m.tr, m.bl, m.br + s⟩

def modFour (x : Fin 8) : Fin 4 := Fin.ofNat 4 x.val

def reducePowerPair (p : Mat2 (Fin 8) × Fin 8) : Mat2 (Fin 4) × Fin 4 :=
  (p.1.map modFour, modFour p.2)

def squarePowerPair (p : Mat2 (Fin 8) × Fin 8) : Mat2 (Fin 8) × Fin 8 :=
  (p.1.mul p.1, p.2 * p.2)

/-- The powers `(γ^(2^a), u^(2^a))` computed modulo eight by repeated squaring. -/
def powerPair (c₀ c₁ u : Fin 8) : Nat → Mat2 (Fin 8) × Fin 8
  | 0 => (companion c₀ c₁, u)
  | a + 1 => squarePowerPair (powerPair c₀ c₁ u a)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The first square is the identity modulo four, and the fourth power already
equals the identity modulo eight. Both claims include the scalar coordinate. -/
theorem first_two_power_residues :
    ∀ (c₁ u : Fin 8), c₁.val % 4 = 2 → u.val % 2 = 1 →
      reducePowerPair (powerPair 4 c₁ u 1) = (Mat2.diagonal 1, 1) ∧
        powerPair 4 c₁ u 2 = (Mat2.diagonal 1, 1) := by
  decide
-- breakpoint first_two_power_residues

/-- For every positive layer the power pair reduces to `(I,1)` modulo four.
From the second layer onward the same equality holds modulo eight. -/
theorem positive_layer_power_residues (c₁ u : Fin 8)
    (hc : c₁.val % 4 = 2) (hu : u.val % 2 = 1) (a : Nat) :
    reducePowerPair (powerPair 4 c₁ u (a + 1)) = (Mat2.diagonal 1, 1) ∧
      powerPair 4 c₁ u (a + 2) = (Mat2.diagonal 1, 1) := by
  induction a with
  | zero => exact first_two_power_residues c₁ u hc hu
  | succ a ih =>
    constructor
    · change reducePowerPair (powerPair 4 c₁ u (a + 2)) = _
      rw [ih.2]
      decide
    · change squarePowerPair (powerPair 4 c₁ u (a + 2)) = _
      rw [ih.2]
      decide
-- breakpoint positive_layer_power_residues

/-- The complementary factor `γ^(2^(a+1)) + u^(2^(a+1)) I`, formed modulo
eight and then reduced modulo four, equals `2I` at every positive layer. -/
theorem complementary_factor_mod_four (c₁ u : Fin 8)
    (hc : c₁.val % 4 = 2) (hu : u.val % 2 = 1) (a : Nat) :
    let p := powerPair 4 c₁ u (a + 1)
    (p.1.addScalar p.2).map modFour = Mat2.diagonal 2 := by
  let p := powerPair 4 c₁ u (a + 1)
  have h : reducePowerPair p = (Mat2.diagonal 1, 1) :=
    (positive_layer_power_residues c₁ u hc hu a).1
  have ha : ∀ x y : Fin 8, modFour (x + y) = modFour x + modFour y := by decide
  change (p.1.addScalar p.2).map modFour = Mat2.diagonal 2
  calc
    (p.1.addScalar p.2).map modFour =
        (reducePowerPair p).1.addScalar (reducePowerPair p).2 := by
          simp [Mat2.map, Mat2.addScalar, reducePowerPair, ha]
    _ = Mat2.diagonal 2 := by rw [h]; decide
-- breakpoint complementary_factor_mod_four

end ReimannWindow.DyadicBaseMatrix
