import Reimann.DyadicLattice
import Reimann.DyadicQuotient

/-!
The companion matrix acts on a free rank-two lattice over the coherent
residues modulo powers of two. Coefficient congruences are represented by
their quotient witnesses. Positive layers are indexed by n+1, starting with
the square of the companion at n=0.
-/

namespace Reimann.DyadicLayers

open Reimann.DyadicLattice

local infixl:65 " ⊞ " => add
local infixl:70 " ⊠ " => mul
local prefix:max "⊟" => neg

def companion (c0 c1 : Scalar) : Matrix :=
  ⟨natScalar 1, ⊟c0, natScalar 1, natScalar 1 ⊞ ⊟c1⟩

def squareMatrix (m : Matrix) : Matrix :=
  ⟨m.a ⊠ m.a ⊞ m.b ⊠ m.c, m.a ⊠ m.b ⊞ m.b ⊠ m.d,
   m.c ⊠ m.a ⊞ m.d ⊠ m.c, m.c ⊠ m.b ⊞ m.d ⊠ m.d⟩

/-- The matrix sI + kM. -/
def diagonalShift (s k : Scalar) (m : Matrix) : Matrix :=
  ⟨s ⊞ k ⊠ m.a, k ⊠ m.b, k ⊠ m.c, s ⊞ k ⊠ m.d⟩

/-- At index a these are the powers J^(2^a) and s^(2^a). -/
def powerPair (j : Matrix) (s : Scalar) : Nat → Matrix × Scalar
  | 0 => (j, s)
  | a+1 =>
    let p := powerPair j s a
    (squareMatrix p.1, p.2 ⊠ p.2)

/-- The coordinates h and k witness C₀ ≡ 4 modulo 8 and C₁ ≡ 2 modulo 4. -/
def congruentCompanion (h k : Scalar) : Matrix :=
  companion (natScalar 4 ⊞ natScalar 8 ⊠ h) (natScalar 2 ⊞ natScalar 4 ⊠ k)

/-- Every scalar 5^(-r) has the form 1+4v in the dyadic integers. -/
def congruentScalar (v : Scalar) : Scalar := natScalar 1 ⊞ natScalar 4 ⊠ v

/-- The normalized difference (J²-s²I)/4; the bottom-left entry may be odd. -/
def firstQuotient (h k v : Scalar) : Matrix :=
  let c0 := natScalar 4 ⊞ natScalar 8 ⊠ h
  let c1 := natScalar 2 ⊞ natScalar 4 ⊠ k
  let a := ⊟(natScalar 1 ⊞ natScalar 2 ⊠ h ⊞ natScalar 2 ⊠ v ⊞ natScalar 4 ⊠ v ⊠ v)
  ⟨a, c0 ⊠ k, ⊟k, a ⊞ c1 ⊠ k⟩

/-- Exact first square identity over the coherent residues at every precision. -/
theorem first_square_normalization (h k v : Scalar) :
    squareMatrix (congruentCompanion h k) =
      diagonalShift (congruentScalar v ⊠ congruentScalar v) (natScalar 4)
        (firstQuotient h k v) := by
  simp only [squareMatrix, congruentCompanion, congruentScalar, companion,
    diagonalShift, firstQuotient, Matrix.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply scalar_ext <;> intro n <;>
    simp only [add, mul, neg, natScalar] <;> grind

theorem first_quotient_odd (h k v : Scalar) :
    (det (firstQuotient h k v)).residue 0 = 1 := by
  apply unipotent_det_odd <;> simp [firstQuotient, add, mul, neg, natScalar]

/-- Subtract the diagonal scalar from the matrix. -/
def difference (m : Matrix) (s : Scalar) : Matrix :=
  ⟨m.a ⊞ ⊟s, m.b, m.c, m.d ⊞ ⊟s⟩

theorem act_difference_of_shift (s k : Scalar) (m : Matrix) (x : Scalar × Scalar) :
    act (difference (diagonalShift s k m) s) x = scaleVector k (act m x) := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [difference, diagonalShift, act, scaleVector, add, neg, mul] <;> grind

/-- At the first positive layer the difference has image exactly 4Y. -/
theorem first_square_image (h k v : Scalar) (y : Scalar × Scalar) :
    (∃ x, act (difference (squareMatrix (congruentCompanion h k))
      (congruentScalar v ⊠ congruentScalar v)) x = y) ↔
        ∃ z, scaleVector (natScalar 4) z = y := by
  rw [first_square_normalization h k v]
  simp only [act_difference_of_shift]
  exact scaled_matrix_image _ _ (first_quotient_odd h k v) y

/-- Squaring sI+4mU gives next normalized matrix sU+2mU². -/
def nextQuotient (s m : Scalar) (u : Matrix) : Matrix :=
  let q := squareMatrix u
  let b := natScalar 2 ⊠ m
  ⟨s ⊠ u.a ⊞ b ⊠ q.a, s ⊠ u.b ⊞ b ⊠ q.b,
   s ⊠ u.c ⊞ b ⊠ q.c, s ⊠ u.d ⊞ b ⊠ q.d⟩

/-- The next difference factors by twice the previous scalar at every precision. -/
theorem double_normalization (s m : Scalar) (u : Matrix) :
    squareMatrix (diagonalShift s (natScalar 4 ⊠ m) u) =
      diagonalShift (s ⊠ s) (natScalar 4 ⊠ (natScalar 2 ⊠ m))
        (nextQuotient s m u) := by
  simp only [squareMatrix, diagonalShift, nextQuotient, Matrix.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply scalar_ext <;> intro n <;>
    simp only [add, mul, natScalar] <;> grind

/-- For odd s the new quotient has the same determinant modulo two. -/
theorem next_quotient_odd (s m : Scalar) (u : Matrix) (hs : s.residue 0 = 1) :
    (det (nextQuotient s m u)).residue 0 = (det u).residue 0 := by
  simp [det, nextQuotient, add, mul, neg, natScalar, hs]

theorem nat_scale_product (k m : Nat) :
    natScalar (k*m) = natScalar k ⊠ natScalar m := by
  apply scalar_ext
  intro n
  exact BitVec.ofNat_mul k m

theorem scale_at_positive_layer (n : Nat) :
    natScalar (2^(n+2)) = natScalar 4 ⊠ natScalar (2^n) := by
  rw [← nat_scale_product, Nat.pow_add, Nat.mul_comm]

/-- Induction on a=n+1 constructs an odd-determinant matrix U such that
J^(2^a) = s^(2^a) I + 4·2^n U. -/
theorem positive_normalization (h k v : Scalar) (n : Nat) :
    let p := powerPair (congruentCompanion h k) (congruentScalar v) (n+1)
    p.2.residue 0 = 1 ∧ ∃ u, (det u).residue 0 = 1 ∧
      p.1 = diagonalShift p.2 (natScalar 4 ⊠ natScalar (2^n)) u := by
  induction n with
  | zero =>
    dsimp only [powerPair]
    rw [← nat_scale_product, Nat.pow_zero, Nat.mul_one]
    exact ⟨by simp [congruentScalar, add, mul, natScalar],
      firstQuotient h k v, first_quotient_odd h k v, first_square_normalization h k v⟩
  | succ n ih =>
    let p := powerPair (congruentCompanion h k) (congruentScalar v) (n+1)
    obtain ⟨hs, u, hu, hpow⟩ := ih
    change p.2.residue 0 = 1 at hs
    change p.1 = diagonalShift p.2 (natScalar 4 ⊠ natScalar (2^n)) u at hpow
    change (p.2 ⊠ p.2).residue 0 = 1 ∧ ∃ w, (det w).residue 0 = 1 ∧
      squareMatrix p.1 = diagonalShift (p.2 ⊠ p.2) (natScalar 4 ⊠ natScalar (2^(n+1))) w
    have hscale : natScalar (2^(n+1)) = natScalar 2 ⊠ natScalar (2^n) := by
      rw [← nat_scale_product, Nat.pow_succ, Nat.mul_comm]
    refine ⟨by change p.2.residue 0 * p.2.residue 0 = 1; rw [hs]; rfl,
      nextQuotient p.2 (natScalar (2^n)) u, (next_quotient_odd _ _ _ hs).trans hu, ?_⟩
    rw [hpow, double_normalization, hscale]

/-- At each positive layer a=n+1 the difference has image precisely 2^(a+1)Y. -/
theorem positive_layer_image (h k v : Scalar) (n : Nat) (y : Scalar × Scalar) :
    let p := powerPair (congruentCompanion h k) (congruentScalar v) (n+1)
    (∃ x, act (difference p.1 p.2) x = y) ↔
      ∃ z, scaleVector (natScalar (2^(n+2))) z = y := by
  dsimp only
  obtain ⟨_, u, hu, h⟩ := positive_normalization h k v n
  rw [h, scale_at_positive_layer]
  simp only [act_difference_of_shift]
  exact scaled_matrix_image _ u hu y

/-- Direct form for the actual coefficient residues. Here c₀ is known modulo
8, c₁ and s modulo 4. No matrix surjectivity or lattice-image input is needed. -/
theorem positive_layer_image_of_residues (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (n : Nat) (y : Scalar × Scalar) :
    let p := powerPair (companion c0 c1) s (n+1)
    (∃ x, act (difference p.1 p.2) x = y) ↔
      ∃ z, scaleVector (natScalar (2^(n+2))) z = y := by
  obtain ⟨h, hc0⟩ :=
    (Reimann.DyadicQuotient.residue_eq_iff_multiple 2 c0 (natScalar 4)).mp h0
  obtain ⟨k, hc1⟩ :=
    (Reimann.DyadicQuotient.residue_eq_iff_multiple 1 c1 (natScalar 2)).mp h1
  obtain ⟨v, hsv⟩ :=
    (Reimann.DyadicQuotient.residue_eq_iff_multiple 1 s (natScalar 1)).mp hs
  rw [hc0, hc1, hsv]
  exact positive_layer_image h k v n y

end Reimann.DyadicLayers
