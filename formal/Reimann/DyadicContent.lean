/-! Content and norm: the Smith form of an element of a quadratic order acting on a
lattice, uniformly in the coefficients (`Dyadic_Residue_Shape.md` §6).

For `ω = A + B·T` in `ℤ[T]/(T² + c1 T + c0)` the quotient by `ω` has invariant
factors `g` and `g·n`, where `g` is the content of `ω` and `n` a binary quadratic
form at the primitive vector `ω/g`. The 2-adic valuation of `n` is the distance in
the tree of lattices; the last three theorems evaluate it in the three shapes. -/

namespace Reimann.DyadicContent

/-- A 2×2 integer matrix with rows `(p, q)` and `(r, s)`. -/
structure Mat where
  p : Int
  q : Int
  r : Int
  s : Int

def Mat.mul (A B : Mat) : Mat :=
  ⟨A.p*B.p + A.q*B.r, A.p*B.q + A.q*B.s, A.r*B.p + A.s*B.r, A.r*B.q + A.s*B.s⟩

def Mat.det (A : Mat) : Int := A.p*A.s - A.q*A.r

/-- Smith form of a 2×2 integer matrix all of whose entries are divisible by `g`
and whose first column divided by `g` is primitive, with a Bézout witness. -/
theorem smith_two_by_two (g a b q s x y : Int) (bez : x*a + y*b = 1) :
    ∃ U V : Mat, U.det = 1 ∧ V.det = 1 ∧
      (U.mul ⟨g*a, g*q, g*b, g*s⟩).mul V = ⟨g, 0, 0, g*(a*s - b*q)⟩ := by
  refine ⟨⟨x, y, -b, a⟩, ⟨1, -(x*q + y*s), 0, 1⟩, ?_, ?_, ?_⟩
  · simp only [Mat.det]; grind
  · simp only [Mat.det]; grind
  · have h1 : x*(g*a) + y*(g*b) = g := by
      have e : x*(g*a) + y*(g*b) = g*(x*a + y*b) := by grind
      rw [e, bez, Int.mul_one]
    have h2 : -b*(g*a) + a*(g*b) = 0 := by grind
    have h3 : -b*(g*q) + a*(g*s) = g*(a*s - b*q) := by grind
    simp only [Mat.mul, Mat.mk.injEq]
    rw [h1, h2, h3]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- `ω = A + B·T` on `Y = ℤ[T]/(T² + c1 T + c0)` in the basis `1, T`, with
`A = g a`, `B = g b`: `Y/ωY ≅ ℤ/g ⊕ ℤ/(g n)`, `n = a² - c1 a b + c0 b²`. -/
theorem regular_smith (g a b c0 c1 x y : Int) (bez : x*a + y*b = 1) :
    ∃ U V : Mat, U.det = 1 ∧ V.det = 1 ∧
      (U.mul ⟨g*a, -(c0*(g*b)), g*b, g*a - c1*(g*b)⟩).mul V =
        ⟨g, 0, 0, g*(a*a - c1*(a*b) + c0*(b*b))⟩ := by
  have h := smith_two_by_two g a b (-(c0*b)) (a - c1*b) x y bez
  have e1 : g*(-(c0*b)) = -(c0*(g*b)) := by grind
  have e2 : g*(a - c1*b) = g*a - c1*(g*b) := by grind
  have e3 : a*(a - c1*b) - b*(-(c0*b)) = a*a - c1*(a*b) + c0*(b*b) := by grind
  rw [e1, e2, e3] at h
  exact h

/-- The same operator from `Y` into `X = ⟨2, T⟩` (target basis `2, T`), with
`A = 2 g a`, `B = g b`, `c0 = 2 c`: `X/ωY ≅ ℤ/g ⊕ ℤ/(g n)`,
`n = 2a² - c1 a b + c b²`. Here `g` is the content of `(A/2, B)`. -/
theorem strict_smith (g a b c c1 x y : Int) (bez : x*a + y*b = 1) :
    ∃ U V : Mat, U.det = 1 ∧ V.det = 1 ∧
      (U.mul ⟨g*a, -(c*(g*b)), g*b, 2*(g*a) - c1*(g*b)⟩).mul V =
        ⟨g, 0, 0, g*(2*(a*a) - c1*(a*b) + c*(b*b))⟩ := by
  have h := smith_two_by_two g a b (-(c*b)) (2*a - c1*b) x y bez
  have e1 : g*(-(c*b)) = -(c*(g*b)) := by grind
  have e2 : g*(2*a - c1*b) = 2*(g*a) - c1*(g*b) := by grind
  have e3 : a*(2*a - c1*b) - b*(-(c*b)) = 2*(a*a) - c1*(a*b) + c*(b*b) := by grind
  rw [e1, e2, e3] at h
  exact h

/-! ### The distance `v₂(n)` in the three shapes

`c = c0/2`. The vector `(a, b)` is primitive. -/

/-- Shape I (`c` odd, `c1 ≡ 0 mod 4`): the distance is 0 or 1, according to the
parity of `b`. The torus stabilizes one edge and its uniformizer flips it. -/
theorem eisenstein_distance (a b c c1 : Int) (hc : c % 2 = 1) (h1 : c1 % 4 = 0) :
    (b % 2 = 1 → (2*(a*a) - c1*(a*b) + c*(b*b)) % 2 = 1) ∧
    (b % 2 = 0 → a % 2 = 1 → (2*(a*a) - c1*(a*b) + c*(b*b)) % 4 = 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = 2*e + 1 := ⟨c/2, by omega⟩
  obtain ⟨f, rfl⟩ : ∃ f, c1 = 4*f := ⟨c1/4, by omega⟩
  constructor
  · intro hb
    obtain ⟨j, rfl⟩ : ∃ j, b = 2*j + 1 := ⟨b/2, by omega⟩
    obtain ⟨z, hz⟩ : ∃ z, 2*(a*a) - 4*f*(a*(2*j + 1)) + (2*e + 1)*((2*j + 1)*(2*j + 1)) = 2*z + 1 :=
      ⟨(a*a) - 2*(f*a) + e + 2*j - 4*(j*f*a) + 4*(j*e) + 2*(j*j) + 4*(j*j*e), by grind⟩
    rw [hz]; omega
  · intro hb ha
    obtain ⟨j, rfl⟩ : ∃ j, b = 2*j := ⟨b/2, by omega⟩
    obtain ⟨i, rfl⟩ : ∃ i, a = 2*i + 1 := ⟨a/2, by omega⟩
    obtain ⟨z, hz⟩ : ∃ z, 2*((2*i + 1)*(2*i + 1)) - 4*f*((2*i + 1)*(2*j)) +
        (2*e + 1)*((2*j)*(2*j)) = 4*z + 2 :=
      ⟨-2*(j*f) + (j*j) + 2*(j*j*e) + 2*i - 4*(i*j*f) + 2*(i*i), by grind⟩
    rw [hz]; omega

/-- Shape IIa (`c ≡ 2 mod 4`, `c1 ≡ 2 mod 4`): the distance is exactly 1 for every
primitive vector. The torus fixes one vertex and turns its three neighbours. -/
theorem inert_distance (a b c c1 : Int) (hc : c % 4 = 2) (h1 : c1 % 4 = 2)
    (prim : a % 2 = 1 ∨ b % 2 = 1) :
    (2*(a*a) - c1*(a*b) + c*(b*b)) % 4 = 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, c = 4*e + 2 := ⟨c/4, by omega⟩
  obtain ⟨f, rfl⟩ : ∃ f, c1 = 4*f + 2 := ⟨c1/4, by omega⟩
  have cases' : (a % 2 = 1 ∧ b % 2 = 0) ∨ (a % 2 = 1 ∧ b % 2 = 1) ∨ (a % 2 = 0 ∧ b % 2 = 1) := by
    omega
  rcases cases' with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨i, rfl⟩ : ∃ i, a = 2*i + 1 := ⟨a/2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = 2*j := ⟨b/2, by omega⟩
    obtain ⟨z, hz⟩ : ∃ z, 2*((2*i + 1)*(2*i + 1)) - (4*f + 2)*((2*i + 1)*(2*j)) +
        (4*e + 2)*((2*j)*(2*j)) = 4*z + 2 :=
      ⟨-j - 2*(j*f) + 2*(j*j) + 4*(j*j*e) + 2*i - 2*(i*j) - 4*(i*j*f) + 2*(i*i), by grind⟩
    rw [hz]; omega
  · obtain ⟨i, rfl⟩ : ∃ i, a = 2*i + 1 := ⟨a/2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = 2*j + 1 := ⟨b/2, by omega⟩
    obtain ⟨z, hz⟩ : ∃ z, 2*((2*i + 1)*(2*i + 1)) - (4*f + 2)*((2*i + 1)*(2*j + 1)) +
        (4*e + 2)*((2*j + 1)*(2*j + 1)) = 4*z + 2 :=
      ⟨-f + e + j - 2*(j*f) + 4*(j*e) + 2*(j*j) + 4*(j*j*e) + i - 2*(i*f) - 2*(i*j)
        - 4*(i*j*f) + 2*(i*i), by grind⟩
    rw [hz]; omega
  · obtain ⟨i, rfl⟩ : ∃ i, a = 2*i := ⟨a/2, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = 2*j + 1 := ⟨b/2, by omega⟩
    obtain ⟨z, hz⟩ : ∃ z, 2*((2*i)*(2*i)) - (4*f + 2)*((2*i)*(2*j + 1)) +
        (4*e + 2)*((2*j + 1)*(2*j + 1)) = 4*z + 2 :=
      ⟨e + 2*j + 4*(j*e) + 2*(j*j) + 4*(j*j*e) - i - 2*(i*f) - 2*(i*j) - 4*(i*j*f) + 2*(i*i),
        by grind⟩
    rw [hz]; omega

/-- Shape IIb (`c = 2e`, `c1 = 2h`): the distance is one more than the valuation of
the norm form of the maximal order at `(a, b)`, the translation length of the
split torus. -/
theorem split_distance (a b e h : Int) :
    2*(a*a) - (2*h)*(a*b) + (2*e)*(b*b) = 2*(a*a - h*(a*b) + e*(b*b)) := by
  grind

/-! ### Layers

Elements of `ℤ[T]/(T² + c1 T + c0)` are pairs `(A, B) = A + B·T`. The operator of
layer `a` and weight `r` is `ω_a = (1+T)^(2^a) - s^(2^a)`, `s = 5^(-r) ≡ 1 (mod 4)`.
It factors as `Φ₀ Φ₁ ⋯ Φ_a`, `Φ₀ = (1+T) - s`, `Φ_j = (1+T)^(2^(j-1)) + s^(2^(j-1))`.
The theorems below give the content and the primitive part of `ω₁ = Φ₀Φ₁` and of
the quartic factor `Φ₂` in each shape, and show that every later factor is twice
a unit, for all coefficients. -/

/-- Multiplication in `ℤ[T]/(T² + c1 T + c0)`. -/
def qmul (c0 c1 : Int) (x y : Int × Int) : Int × Int :=
  (x.1*y.1 - c0*(x.2*y.2), x.1*y.2 + x.2*y.1 - c1*(x.2*y.2))

/-- `(1+T)² = (1 - c0) + (2 - c1)·T`. -/
theorem gamma_sq (c0 c1 : Int) : qmul c0 c1 (1, 1) (1, 1) = (1 - c0, 2 - c1) := by
  simp only [qmul, Prod.mk.injEq]
  constructor <;> omega

/-- `(1+T)² ≡ 1 (mod 2)` in the order as soon as `c0` and `c1` are even. -/
theorem gamma_sq_one_mod_two (c0 c1 : Int) (h0 : c0 % 2 = 0) (h1 : c1 % 2 = 0) :
    ∃ w1 w2 : Int, qmul c0 c1 (1, 1) (1, 1) = (1 + 2*w1, 2*w2) := by
  refine ⟨-(c0/2), 1 - c1/2, ?_⟩
  simp only [qmul, Prod.mk.injEq]
  constructor <;> omega

/-- Shape I, layer one: `ω₁ = A + B·T` with `A ≡ B ≡ 2 (mod 4)`. So `(A/2, B)` has
content one, `A/2` is odd and `B` is even: distance 1, group `C₂`, and `ω₁` is
twice a unit. -/
theorem eisenstein_layer_one (c0 c1 s : Int) (h0 : c0 % 4 = 2) (h1 : c1 % 4 = 0)
    (hs : s % 4 = 1) : (1 - c0 - s*s) % 4 = 2 ∧ (2 - c1) % 4 = 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = 4*t + 1 := ⟨s/4, by omega⟩
  have e : (4*t + 1)*(4*t + 1) = 16*(t*t) + 8*t + 1 := by grind
  rw [e]
  constructor <;> omega

/-- Shape I, quartic factor: `Φ₂ = 2·(2a + b·T)` with `b` odd. So `Φ₂/2` generates
the maximal ideal: it is `T` times a unit, and the vertex is flipped once more. -/
theorem eisenstein_quartic_factor (c0 c1 s : Int) (h0 : c0 % 4 = 2) (h1 : c1 % 4 = 0)
    (hs : s % 4 = 1) : (1 - c0 + s*s) % 4 = 0 ∧ (2 - c1) % 4 = 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = 4*t + 1 := ⟨s/4, by omega⟩
  have e : (4*t + 1)*(4*t + 1) = 16*(t*t) + 8*t + 1 := by grind
  rw [e]
  constructor <;> omega

/-- Shape IIa, layer one: `ω₁ = 4·(u + β·T)` with `u` odd, a unit of the order.
Hence `ω₁·O = 4·O`. -/
theorem inert_layer_one (c0 c1 s : Int) (h0 : c0 % 8 = 4) (h1 : c1 % 4 = 2)
    (hs : s % 4 = 1) : (1 - c0 - s*s) % 8 = 4 ∧ (2 - c1) % 4 = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = 4*t + 1 := ⟨s/4, by omega⟩
  have e : (4*t + 1)*(4*t + 1) = 16*(t*t) + 8*t + 1 := by grind
  rw [e]
  constructor <;> omega

/-- Shape IIb, layer one: both coordinates of `ω₁/4` are integral and the constant
one is even, so `ω₁/4` is not a unit; its two real valuations enter. -/
theorem split_layer_one (c0 c1 s : Int) (h0 : c0 % 8 = 0) (h1 : c1 % 4 = 2)
    (hs : s % 4 = 1) : (1 - c0 - s*s) % 8 = 0 ∧ (2 - c1) % 4 = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = 4*t + 1 := ⟨s/4, by omega⟩
  have e : (4*t + 1)*(4*t + 1) = 16*(t*t) + 8*t + 1 := by grind
  rw [e]
  constructor <;> omega

/-- Shape II (a or b), quartic factor: `Φ₂ = 2·(u + 2β·T)` with `u` odd: twice a
unit of the order. -/
theorem split_quartic_factor (c0 c1 s : Int) (h0 : c0 % 4 = 0) (h1 : c1 % 4 = 2)
    (hs : s % 4 = 1) : (1 - c0 + s*s) % 4 = 2 ∧ (2 - c1) % 4 = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = 4*t + 1 := ⟨s/4, by omega⟩
  have e : (4*t + 1)*(4*t + 1) = 16*(t*t) + 8*t + 1 := by grind
  rw [e]
  constructor <;> omega

/-- If `z ≡ 1 (mod 2)` in the order then `z² ≡ 1 (mod 4)`, for all `c0, c1`. -/
theorem sq_one_mod_four (c0 c1 w1 w2 : Int) :
    ∃ v1 v2 : Int,
      qmul c0 c1 (1 + 2*w1, 2*w2) (1 + 2*w1, 2*w2) = (1 + 4*v1, 4*v2) := by
  refine ⟨w1 + w1*w1 - c0*(w2*w2), w2 + 2*(w1*w2) - c1*(w2*w2), ?_⟩
  simp only [qmul, Prod.mk.injEq]
  constructor <;> grind

/-- Every factor above the quartic one is twice a unit: if `z ≡ 1 (mod 2)` and `t`
is odd then `z² + t² = 2·(u1 + u2·T)` with `u1` odd and `u2` even. Applied to
`z = (1+T)^(2^(j-2))`, `t = s^(2^(j-2))`, `j ≥ 3`, this is `Φ_j`. -/
theorem higher_layer_twice_unit (c0 c1 w1 w2 σ : Int) :
    ∃ u1 u2 : Int,
      (qmul c0 c1 (1 + 2*w1, 2*w2) (1 + 2*w1, 2*w2)).1 + (1 + 2*σ)*(1 + 2*σ)
        = 2*(1 + 2*u1) ∧
      (qmul c0 c1 (1 + 2*w1, 2*w2) (1 + 2*w1, 2*w2)).2 = 2*(2*u2) := by
  refine ⟨w1 + w1*w1 - c0*(w2*w2) + σ + σ*σ, w2 + 2*(w1*w2) - c1*(w2*w2), ?_, ?_⟩
  · simp only [qmul]; grind
  · simp only [qmul]; grind

/-- Multiplying `2a + b·T` by `u1 + u2·T` in the order with `c0 = 2c`. -/
theorem unit_mul (c c1 a b u1 u2 : Int) :
    qmul (2*c) c1 (2*a, b) (u1, u2) =
      (2*(a*u1 - c*(b*u2)), 2*(a*u2) + b*u1 - c1*(b*u2)) := by
  simp only [qmul, Prod.mk.injEq]
  constructor <;> grind

/-- A unit `u1 + u2·T` (`u1` odd) keeps the parity of `b`, and the parity of `a`
when `b` is even. So it preserves primitivity of `(a, b)` and the case of the
distance theorems; with `strict_smith` this is invariance of the quotient under
units. -/
theorem unit_mul_parity (c c1 a b u1 u2 : Int) (h1 : c1 % 2 = 0) (hu : u1 % 2 = 1) :
    (2*(a*u2) + b*u1 - c1*(b*u2)) % 2 = b % 2 ∧
    (b % 2 = 0 → (a*u1 - c*(b*u2)) % 2 = a % 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, u1 = 2*k + 1 := ⟨u1/2, by omega⟩
  obtain ⟨f, rfl⟩ : ∃ f, c1 = 2*f := ⟨c1/2, by omega⟩
  constructor
  · obtain ⟨z, hz⟩ : ∃ z, 2*(a*u2) + b*(2*k + 1) - 2*f*(b*u2) = b + 2*z :=
      ⟨a*u2 + b*k - f*(b*u2), by grind⟩
    rw [hz]; omega
  · intro hb
    obtain ⟨j, rfl⟩ : ∃ j, b = 2*j := ⟨b/2, by omega⟩
    obtain ⟨z, hz⟩ : ∃ z, a*(2*k + 1) - c*(2*j*u2) = a + 2*z :=
      ⟨a*k - c*(j*u2), by grind⟩
    rw [hz]; omega

end Reimann.DyadicContent
