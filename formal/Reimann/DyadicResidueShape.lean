import Reimann.SampleSpacing

/-! Elementary kernels of the residue-shape theorem, `Dyadic_Residue_Shape.md` §3.

The class-field inputs (Mizusawa's module, the ambiguous class formula over
ℚ(√2), the Rédei criterion) are paper statements recorded in `PROOF_STATUS.md`.
This file checks the integer and 𝔽₂ calculations those statements are fed with,
and the passage from the two residue shapes to the valuations used by
`PairedOrders` and Appendix A.2. -/

namespace Reimann.DyadicResidueShape

open Reimann.Dyadic Reimann.SampleSpacing

/-! ### §3.1 The two lattices -/

/-- Split case. The lattice of `T(T+2)` in the basis `1, T` has generators
`(c0, c1-2)` and `(0, c0-2c1+4)`. It lies in `4ℤ²` exactly when `c1 ≡ 2 (mod 4)`. -/
theorem split_lattice_iff (c0 c1 : Int) (h0 : c0 % 4 = 0) (h1 : c1 % 2 = 0) :
    (c0 % 4 = 0 ∧ (c1 - 2) % 4 = 0 ∧ (c0 - 2*c1 + 4) % 4 = 0) ↔ c1 % 4 = 2 := by
  omega

/-- Eisenstein case. The lattice of `(1+T)²+1` has generators `(2-c0, 2-c1)` and
`(-c0(2-c1), 2-c0-c1(2-c1))`. It lies in `4ℤ²` exactly when `c1 ≡ 2 (mod 4)`. -/
theorem eisenstein_lattice_iff (c0 c1 : Int) (h0 : c0 % 4 = 2) (h1 : c1 % 2 = 0) :
    ((2 - c0) % 4 = 0 ∧ (2 - c1) % 4 = 0 ∧ (-(c0*(2 - c1))) % 4 = 0 ∧
      (2 - c0 - c1*(2 - c1)) % 4 = 0) ↔ c1 % 4 = 2 := by
  obtain ⟨u, rfl⟩ : ∃ u, c0 = 4*u + 2 := ⟨c0/4, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c1 = 2*v := ⟨c1/2, by omega⟩
  have e1 : -((4*u + 2)*(2 - 2*v)) = 4*(-((2*u+1)*(1 - v))) := by grind
  have e2 : 2 - (4*u + 2) - 2*v*(2 - 2*v) = 4*(-u - v*(1 - v)) := by grind
  rw [e1, e2]
  generalize (2*u+1)*(1 - v) = w
  generalize v*(1 - v) = z
  omega

/-! ### §3.4 The two Rédei matrices over 𝔽₂ -/

/-- Number of 𝔽₂-combinations of the three rows that vanish: `2^(3 - rank)`. -/
def kernelCount (R : List (List Bool)) : Nat :=
  ([false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].map fun c =>
    (List.range 3).all fun j =>
      (((a && (R.getD 0 []).getD j false) ^^ (b && (R.getD 1 []).getD j false)) ^^
        (c && (R.getD 2 []).getD j false)) == false).count true

/-- `k₁ = ℚ(√2, √-m)`: rows `-1, π*, π'*`, columns `𝔓₂, 𝔓_π, 𝔓_π'`; `c` is true for `(q/d) = -1`. -/
def redeiSplit (c : Bool) : List (List Bool) :=
  [[true, true, true], [true, c ^^ true, true], [true, true, c ^^ true]]

/-- `F' = ℚ(√(-m(2+√2)))`: rows `-q, π*, π'*`, columns `𝔔_q, 𝔓_π, 𝔓_π'`. -/
def redeiEisenstein (c : Bool) : List (List Bool) :=
  [[true, c ^^ true, c ^^ true], [c, c, true], [c, true, c]]

/-- `(q/d) = +1`: rank 1, so the 4-rank of `A(k₁)` is 2. `(q/d) = -1`: rank 3. -/
theorem rank_split : kernelCount (redeiSplit false) = 4 ∧ kernelCount (redeiSplit true) = 1 := by
  decide

/-- `(q/d) = -1`: rank 2, so the 4-rank of `A(F')` is 1. `(q/d) = +1`: rank 3. -/
theorem rank_eisenstein :
    kernelCount (redeiEisenstein true) = 2 ∧ kernelCount (redeiEisenstein false) = 1 := by
  decide

/-! ### §3.3 The symbols: residue arithmetic -/

theorem odd_square (y : Int) (hy : y % 2 = 1) : y*y % 8 = 1 := by
  have h := Int.mul_emod y y 8
  have c : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by omega
  rcases c with e | e | e | e <;> rw [e] at h <;> omega

/-- `d = x² - 2y² ≡ 7 (mod 16)` with `x, y` odd forces `x ≡ ±3 (mod 8)`, hence `(2/x) = -1`. -/
theorem x_residue (x y : Int) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : (x*x - 2*(y*y)) % 16 = 7) : x % 8 = 3 ∨ x % 8 = 5 := by
  have hy8 := odd_square y hy
  have hx16 : x*x % 16 = 9 := by omega
  have s := Int.mul_emod x x 16
  have c : x % 16 = 1 ∨ x % 16 = 3 ∨ x % 16 = 5 ∨ x % 16 = 7 ∨ x % 16 = 9 ∨ x % 16 = 11 ∨
      x % 16 = 13 ∨ x % 16 = 15 := by omega
  rcases c with e | e | e | e | e | e | e | e <;> rw [e] at s <;> omega

/-- `N(ε π) = -N(π)` for `ε = 1+√2`, `π = x + y√2`: `επ = (x+2y) + (x+y)√2`. -/
theorem pistar_norm (x y : Int) :
    (x + 2*y)*(x + 2*y) - 2*((x + y)*(x + y)) = -(x*x - 2*(y*y)) := by
  grind

/-- Squares of units of `ℤ[√2]` modulo `4√2`: `(a + b√2)² = (a²+2b²) + 2ab√2`
is `1` or `3 + 2√2` modulo `(8, 4√2)`. -/
theorem unit_square_classes (a b : Int) (ha : a % 2 = 1) :
    ((a*a + 2*(b*b)) % 8 = 1 ∧ (2*(a*b)) % 4 = 0) ∨
    ((a*a + 2*(b*b)) % 8 = 3 ∧ (2*(a*b)) % 4 = 2) := by
  have ha8 := odd_square a ha
  have hab := Int.mul_emod a b 2
  rw [ha] at hab
  have hb := Int.mul_emod b b 4
  have c : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  rcases c with e | e | e | e <;> rw [e] at hb <;> omega

/-- `π* = (-1/y) ε π` for `y ≡ 1 (mod 4)`: a square modulo 4 and not modulo `4√2`. -/
theorem pistar_nonsquare_pos (x y : Int) (hx : x % 8 = 3 ∨ x % 8 = 5) (hy : y % 4 = 1) :
    (((x + 2*y) % 4 = 1 ∧ (x + y) % 4 = 0) ∨ ((x + 2*y) % 4 = 3 ∧ (x + y) % 4 = 2)) ∧
    ¬ (((x + 2*y) % 8 = 1 ∧ (x + y) % 4 = 0) ∨ ((x + 2*y) % 8 = 3 ∧ (x + y) % 4 = 2)) := by
  omega

/-- The same for `y ≡ 3 (mod 4)`, where `π* = -επ`. -/
theorem pistar_nonsquare_neg (x y : Int) (hx : x % 8 = 3 ∨ x % 8 = 5) (hy : y % 4 = 3) :
    (((-(x + 2*y)) % 4 = 1 ∧ (-(x + y)) % 4 = 0) ∨
      ((-(x + 2*y)) % 4 = 3 ∧ (-(x + y)) % 4 = 2)) ∧
    ¬ (((-(x + 2*y)) % 8 = 1 ∧ (-(x + y)) % 4 = 0) ∨
      ((-(x + 2*y)) % 8 = 3 ∧ (-(x + y)) % 4 = 2)) := by
  omega

/-! ### From the residue shape to the valuations of Appendix A.2

`numerator c0 c1 ε a = a² P(ε/a - 1)`; at `a = 5^r` this is `a² f(ε s)`.
`quarticNumerator c0 c1 a = a⁴ f(is) f(-is) = (Δ a² - 1)² + a² τ²`. -/

def quarticNumerator (c0 c1 a : Int) : Int :=
  ((1 - c1 + c0)*(a*a) - 1)*((1 - c1 + c0)*(a*a) - 1) + (a*a)*((2 - c1)*(2 - c1))

theorem exactV_one_of_mod {x : Int} (h : x % 4 = 2) : exactV x 1 :=
  ⟨x/4, by simp only [twoPower]; omega⟩

theorem exactV_two_of_mod {x : Int} (h : x % 8 = 4) : exactV x 2 :=
  ⟨x/8, by simp only [twoPower]; omega⟩

theorem exactV_three_of_mod {x : Int} (h : x % 16 = 8) : exactV x 3 :=
  ⟨x/16, by simp only [twoPower]; omega⟩

/-- Shape I, `(q/d) = -1`: `k = l = 1` at every sample `a ≡ 1 (mod 4)`. -/
theorem eisenstein_profile (c0 c1 a : Int) (h0 : c0 % 4 = 2) (h1 : c1 % 4 = 0)
    (ha : a % 4 = 1) :
    exactV (numerator c0 c1 1 a) 1 ∧ exactV (numerator c0 c1 (-1) a) 1 := by
  obtain ⟨u, rfl⟩ : ∃ u, c0 = 4*u + 2 := ⟨c0/4, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c1 = 4*v := ⟨c1/4, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, a = 4*w + 1 := ⟨a/4, by omega⟩
  constructor
  · obtain ⟨z, hz⟩ : ∃ z, numerator (4*u + 2) (4*v) 1 (4*w + 1) = 4*z + 2 :=
      ⟨4*w + 12*(w*w) - 4*(v*w) - 16*(v*w*w) + u + 8*(u*w) + 16*(u*w*w),
        by unfold numerator; grind⟩
    exact exactV_one_of_mod (by rw [hz]; omega)
  · obtain ⟨z, hz⟩ : ∃ z, numerator (4*u + 2) (4*v) (-1) (4*w + 1) = 4*z + 2 :=
      ⟨1 + 8*w + 12*(w*w) - 2*v - 12*(v*w) - 16*(v*w*w) + u + 8*(u*w) + 16*(u*w*w),
        by unfold numerator; grind⟩
    exact exactV_one_of_mod (by rw [hz]; omega)

/-- Shape I: the quartic value has valuation exactly three, `h = 3`. -/
theorem eisenstein_quartic (c0 c1 a : Int) (h0 : c0 % 4 = 2) (h1 : c1 % 4 = 0)
    (ha : a % 2 = 1) : exactV (quarticNumerator c0 c1 a) 3 := by
  have ha8 := odd_square a ha
  obtain ⟨u, rfl⟩ : ∃ u, c0 = 4*u + 2 := ⟨c0/4, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c1 = 4*v := ⟨c1/4, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, a*a = 8*n + 1 := ⟨a*a/8, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z, quarticNumerator (4*u + 2) (4*v) a = 16*z + 8 :=
    ⟨8*n + 36*(n*n) - 2*v - 28*(v*n) - 96*(v*n*n) + 2*(v*v) + 24*(v*v*n) + 64*(v*v*n*n) + u
        + 20*(u*n) + 96*(u*n*n) - 2*(u*v) - 32*(u*v*n) - 128*(u*v*n*n) + (u*u) + 16*(u*u*n)
        + 64*(u*u*n*n),
      by unfold quarticNumerator; rw [hn]; grind⟩
  exact exactV_three_of_mod (by rw [hz]; omega)

/-- Shape II, `(q/d) = +1`: the quartic value has valuation exactly two, `h = 2`. -/
theorem split_quartic (c0 c1 a : Int) (h0 : c0 % 4 = 0) (h1 : c1 % 4 = 2)
    (ha : a % 2 = 1) : exactV (quarticNumerator c0 c1 a) 2 := by
  have ha8 := odd_square a ha
  obtain ⟨u, rfl⟩ : ∃ u, c0 = 4*u := ⟨c0/4, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c1 = 4*v + 2 := ⟨c1/4, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, a*a = 8*n + 1 := ⟨a*a/8, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z, quarticNumerator (4*u) (4*v + 2) a = 8*z + 4 :=
    ⟨4*n + 8*(n*n) + 2*v + 24*(v*n) + 64*(v*n*n) + 4*(v*v) + 48*(v*v*n) + 128*(v*v*n*n) - 2*u
        - 24*(u*n) - 64*(u*n*n) - 4*(u*v) - 64*(u*v*n) - 256*(u*v*n*n) + 2*(u*u) + 32*(u*u*n)
        + 128*(u*u*n*n),
      by unfold quarticNumerator; rw [hn]; grind⟩
  exact exactV_two_of_mod (by rw [hz]; omega)

/-- Shape II: both real values are divisible by four, `k, l ≥ 2`. -/
theorem split_profile (c0 c1 a : Int) (h0 : c0 % 4 = 0) (h1 : c1 % 4 = 2) (ha : a % 4 = 1) :
    numerator c0 c1 1 a % 4 = 0 ∧ numerator c0 c1 (-1) a % 4 = 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, c0 = 4*u := ⟨c0/4, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c1 = 4*v + 2 := ⟨c1/4, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, a = 4*w + 1 := ⟨a/4, by omega⟩
  constructor
  · obtain ⟨z, hz⟩ : ∃ z, numerator (4*u) (4*v + 2) 1 (4*w + 1) = 4*z :=
      ⟨-2*w - 4*(w*w) - 4*(v*w) - 16*(v*w*w) + u + 8*(u*w) + 16*(u*w*w),
        by unfold numerator; grind⟩
    rw [hz]; omega
  · obtain ⟨z, hz⟩ : ∃ z, numerator (4*u) (4*v + 2) (-1) (4*w + 1) = 4*z :=
      ⟨-2*w - 4*(w*w) - 2*v - 12*(v*w) - 16*(v*w*w) + u + 8*(u*w) + 16*(u*w*w),
        by unfold numerator; grind⟩
    rw [hz]; omega

/-- Shape IIa, `c0 ≡ 4 (mod 8)`: `k = l = 2` at every sample `a ≡ 5 (mod 8)`,
in particular at `a = 5^r` for odd `r`. -/
theorem inert_profile (c0 c1 a : Int) (h0 : c0 % 8 = 4) (h1 : c1 % 4 = 2) (ha : a % 8 = 5) :
    exactV (numerator c0 c1 1 a) 2 ∧ exactV (numerator c0 c1 (-1) a) 2 := by
  obtain ⟨u, rfl⟩ : ∃ u, c0 = 8*u + 4 := ⟨c0/8, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c1 = 4*v + 2 := ⟨c1/4, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, a = 8*w + 5 := ⟨a/8, by omega⟩
  constructor
  · obtain ⟨z, hz⟩ : ∃ z, numerator (8*u + 4) (4*v + 2) 1 (8*w + 5) = 8*z + 4 :=
      ⟨9 + 30*w + 24*(w*w) - 10*v - 36*(v*w) - 32*(v*w*w) + 25*u + 80*(u*w) + 64*(u*w*w),
        by unfold numerator; grind⟩
    exact exactV_two_of_mod (by rw [hz]; omega)
  · obtain ⟨z, hz⟩ : ∃ z, numerator (8*u + 4) (4*v + 2) (-1) (8*w + 5) = 8*z + 4 :=
      ⟨9 + 30*w + 24*(w*w) - 15*v - 44*(v*w) - 32*(v*w*w) + 25*u + 80*(u*w) + 64*(u*w*w),
        by unfold numerator; grind⟩
    exact exactV_two_of_mod (by rw [hz]; omega)

theorem five_pow_odd (k : Nat) : (5 : Int)^(2*k + 1) % 8 = 5 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have e : (5 : Int)^(2*(k + 1) + 1) = 25 * 5^(2*k + 1) := by
      rw [show 2*(k + 1) + 1 = (2*k + 1) + 2 by omega, Int.pow_add]; grind
    omega

/-! ### The implication used in `Dyadic_Residue_Shape.md` §3.1

The 4-rank statements enter as hypotheses on the two lattices: the quotient of
`ℤ²` by a lattice inside `2ℤ²` has 4-rank two exactly when the lattice lies in
`4ℤ²`. Their arithmetic source is the Rédei computation, a paper input. -/

/-- `(q/d) = +1`: 4-rank two for `A(k₁)` forces `c1 ≡ 2 (mod 4)`. -/
theorem split_shape (c0 c1 : Int) (h0 : c0 % 4 = 0) (h1 : c1 % 2 = 0)
    (fourRankTwo : (c1 - 2) % 4 = 0 ∧ (c0 - 2*c1 + 4) % 4 = 0) : c1 % 4 = 2 :=
  (split_lattice_iff c0 c1 h0 h1).mp ⟨h0, fourRankTwo⟩

/-- `(q/d) = -1`: 4-rank at most one for `A(F')` forces `c1 ≡ 0 (mod 4)`. -/
theorem eisenstein_shape (c0 c1 : Int) (h0 : c0 % 4 = 2) (h1 : c1 % 2 = 0)
    (fourRankOne : ¬ ((2 - c0) % 4 = 0 ∧ (2 - c1) % 4 = 0 ∧ (-(c0*(2 - c1))) % 4 = 0 ∧
      (2 - c0 - c1*(2 - c1)) % 4 = 0)) : c1 % 4 = 0 := by
  have h := eisenstein_lattice_iff c0 c1 h0 h1
  have : ¬ c1 % 4 = 2 := fun e => fourRankOne (h.mpr e)
  omega

/-- Shape I at every odd weight: `(k, l, h) = (1, 1, 3)`. -/
theorem eisenstein_weight_profile (c0 c1 : Int) (h0 : c0 % 4 = 2) (h1 : c1 % 4 = 0) (k : Nat) :
    exactV (numerator c0 c1 1 (5^(2*k + 1))) 1 ∧ exactV (numerator c0 c1 (-1) (5^(2*k + 1))) 1 ∧
      exactV (quarticNumerator c0 c1 (5^(2*k + 1))) 3 := by
  have a8 := five_pow_odd k
  obtain ⟨p, m⟩ := eisenstein_profile c0 c1 (5^(2*k + 1)) h0 h1 (by omega)
  exact ⟨p, m, eisenstein_quartic c0 c1 _ h0 h1 (by omega)⟩

/-- Shape IIa at every odd weight: `(k, l, h) = (2, 2, 2)`. -/
theorem inert_weight_profile (c0 c1 : Int) (h0 : c0 % 8 = 4) (h1 : c1 % 4 = 2) (k : Nat) :
    exactV (numerator c0 c1 1 (5^(2*k + 1))) 2 ∧ exactV (numerator c0 c1 (-1) (5^(2*k + 1))) 2 ∧
      exactV (quarticNumerator c0 c1 (5^(2*k + 1))) 2 := by
  have a8 := five_pow_odd k
  obtain ⟨p, m⟩ := inert_profile c0 c1 (5^(2*k + 1)) h0 h1 a8
  exact ⟨p, m, split_quartic c0 c1 _ (by omega) h1 (by omega)⟩

end Reimann.DyadicResidueShape
