import Std

/-!
# Dyadic arithmetic in the strict-group computation

The identities below are over the integers. The polynomial identities apply to
integral representatives modulo any power of two. The arithmetic descent,
the analytic interpolation, and the abelian-group Smith decomposition do not
appear as assumptions or conclusions in this module.
-/

namespace Reimann.Dyadic

-- Step D01
structure Matrix where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq

-- Step D02
def mul (x y : Matrix) : Matrix :=
  ⟨x.a*y.a + x.b*y.c, x.a*y.b + x.b*y.d,
   x.c*y.a + x.d*y.c, x.c*y.b + x.d*y.d⟩

-- Step D03
def shift (x : Matrix) (s : Int) : Matrix :=
  ⟨x.a+s, x.b, x.c, x.d+s⟩

-- Step D04
def scale (s : Int) (x : Matrix) : Matrix :=
  ⟨s*x.a, s*x.b, s*x.c, s*x.d⟩

-- Step D05
def det (x : Matrix) : Int := x.a*x.d-x.b*x.c

-- Step D06
def companion (c₀ c₁ : Int) : Matrix := ⟨1,-c₀,1,1-c₁⟩

-- Step D07
def characteristic (t d s : Int) : Int := s*s-t*s+d

-- Step D08
theorem det_mul (x y : Matrix) : det (mul x y) = det x * det y := by
  simp only [det, mul]
  grind

-- Step D09
theorem determinant_specialization (c₀ c₁ s : Int) :
    det (shift (companion c₀ c₁) (-s)) =
      characteristic (2-c₁) (1-c₁+c₀) s := by
  simp only [det, shift, companion, characteristic]
  grind

-- Step D10
theorem difference_of_squares (x : Matrix) (s : Int) :
    mul (shift x (-s)) (shift x s) = shift (mul x x) (-(s*s)) := by
  cases x
  simp only [mul, shift, Matrix.mk.injEq]
  grind

-- Step D11
theorem det_quartic_factor (c₀ c₁ s : Int) :
    det (shift (mul (companion c₀ c₁) (companion c₀ c₁)) (s*s)) =
    ((1-c₁+c₀)-s*s)^2+s^2*(2-c₁)^2 := by
  simp only [det, shift, mul, companion]
  grind

/-- The basis change to (2b,c) sends the endomorphism 2A I+B(J−I) to this matrix. -/
-- Step D12
def targetMatrix (a b h k : Int) : Matrix :=
  ⟨a, -h*b, b, 2*a-k*b⟩

-- Step D13
def divides (d n : Int) : Prop := ∃ z : Int, n=d*z

-- Step D14
def entryDivisor (d : Int) (x : Matrix) : Prop :=
  divides d x.a ∧ divides d x.b ∧ divides d x.c ∧ divides d x.d

/-- The content of all four entries equals the content of just (A,B). -/
-- Step D15
theorem target_content (z a b h k : Int) :
    entryDivisor z (targetMatrix a b h k) ↔ divides z a ∧ divides z b := by
  constructor
  · intro hh
    exact ⟨hh.1, hh.2.2.1⟩
  · rintro ⟨⟨j,hj⟩, ⟨l,hl⟩⟩
    unfold entryDivisor targetMatrix
    exact ⟨⟨j,hj⟩, ⟨-h*l, by dsimp; grind⟩,
      ⟨l,hl⟩, ⟨2*j-k*l, by dsimp; grind⟩⟩

/-- Replacing the first column coefficient by its shear preserves the entry ideal. -/
-- Step D16
theorem shear_content (d a b u : Int) :
    (divides d (a+b*u) ∧ divides d b) ↔ (divides d a ∧ divides d b) := by
  constructor
  · rintro ⟨⟨j,hj⟩, ⟨l,hl⟩⟩
    exact ⟨⟨j-l*u, by grind⟩, ⟨l,hl⟩⟩
  · rintro ⟨⟨j,hj⟩, ⟨l,hl⟩⟩
    exact ⟨⟨j+l*u, by grind⟩, ⟨l,hl⟩⟩

-- Step D17
theorem real_value_difference (t d s : Int) :
    characteristic t d (-s)-characteristic t d s=2*s*t := by
  simp only [characteristic]
  grind

/-- Squaring any matrix I+2U gives I+4(U+U²). -/
-- Step D18
theorem square_one_mod_two (x : Matrix) :
    mul (shift (scale 2 x) 1) (shift (scale 2 x) 1) =
      shift (scale 4 ⟨x.a+(mul x x).a, x.b+(mul x x).b,
                       x.c+(mul x x).c, x.d+(mul x x).d⟩) 1 := by
  cases x
  simp only [mul, shift, scale, Matrix.mk.injEq]
  grind

/-- det(I+2U) is odd, the elementary invertibility test used at higher layers. -/
-- Step D19
theorem det_one_mod_two (x : Matrix) :
    ∃ z : Int, det (shift (scale 2 x) 1) = 2*z+1 := by
  refine ⟨x.a+x.d+2*det x, ?_⟩
  simp only [det, shift, scale]
  grind

-- Step D20
def twoPower : Nat → Int
  | 0 => 1
  | n+1 => 2*twoPower n

/-- A witness for exact two-adic valuation on nonzero integer samples. -/
-- Step D21
def exactV (x : Int) (j : Nat) : Prop :=
  ∃ z : Int, x=twoPower j*(2*z+1)

-- Step D22
theorem twoPower_add (i j : Nat) : twoPower (i+j)=twoPower i*twoPower j := by
  induction j with
  | zero => simp [twoPower]
  | succ j ih =>
    simp only [twoPower]
    grind

/-- When the first square has strictly smaller valuation, its order survives. -/
-- Step D23
theorem norm_unequal (j : Nat) (a b s : Int) :
    exactV ((twoPower j*(2*a+1))^2 + (s*(2*twoPower j*b))^2) (j+j) := by
  refine ⟨2*a*(a+1)+2*s^2*b^2, ?_⟩
  rw [twoPower_add]
  grind

/-- When the scaled odd parts agree in valuation, the norm gains exactly one. -/
-- Step D24
theorem norm_equal (j : Nat) (a b c : Int) :
    exactV ((twoPower j*(2*a+1))^2 + ((2*c+1)*twoPower j*(2*b+1))^2)
      ((j+j)+1) := by
  let w := b+c+2*b*c
  refine ⟨a*(a+1)+w*(w+1), ?_⟩
  simp only [twoPower, twoPower_add, w]
  grind

/-- The same valuation in the other ordering, with an odd multiplier. -/
-- Step D25
theorem norm_unequal_right (j : Nat) (a b c : Int) :
    exactV ((2*twoPower j*a)^2 + ((2*c+1)*twoPower j*(2*b+1))^2) (j+j) := by
  let w := b+c+2*b*c
  refine ⟨2*a^2+2*w*(w+1), ?_⟩
  simp only [twoPower_add, w]
  grind

/-- The residue distinction is finite. The arguments index all possible residues
of the even trace, odd determinant, and odd scalar congruent to 1 modulo four,
at the precision used in this test. -/
-- Step D26
theorem residue_dichotomy :
    ∀ ti di wi : Fin 4,
      let t : Int := 2*ti.val
      let d : Int := 1+2*di.val
      let s : Int := 1+4*wi.val
      let k := characteristic t d s
      let l := characteristic t d (-s)
      let h := (d-s*s)^2+s^2*t^2
      ((k%4=0 ∧ l%4=0) ∨ (k%4=2 ∧ l%4=2)) ∧
      ((k%4=0 ∧ l%4=0) ↔ h%8=4) := by decide

/-- 5^(2^j), specified by repeated squaring. -/
-- Step D27
def cyclotomicSample : Nat → Int
  | 0 => 5
  | n+1 => cyclotomicSample n*cyclotomicSample n

/-- Exact spacing at power-of-two steps. The odd witness is constructed at
each doubling; this is the dyadic core of the weight-spacing argument. -/
-- Step D28
theorem cyclotomic_spacing (j : Nat) :
    exactV (cyclotomicSample j-1) (j+2) := by
  induction j with
  | zero => exact ⟨0, by decide⟩
  | succ j ih =>
    obtain ⟨a,ha⟩ := ih
    have he : cyclotomicSample j = 1+4*twoPower j*(2*a+1) := by
      simp only [twoPower] at ha
      grind
    refine ⟨a+twoPower j*(2*a+1)^2, ?_⟩
    simp only [cyclotomicSample, twoPower, he]
    grind

/-- The even coefficients of the companion matrix force its square to be I modulo 2. -/
-- Step D29
theorem companion_square_shape (h k : Int) :
    mul (companion (2*h) (2*k)) (companion (2*h) (2*k)) =
      shift (scale 2 ⟨-h, h*(2*k-2), 1-k, -h+k*(2*k-2)⟩) 1 := by
  simp only [mul, companion, shift, scale, Matrix.mk.injEq]
  grind

-- Step D30
def iterSquare (x : Matrix) : Nat → Matrix
  | 0 => x
  | j+1 => mul (iterSquare x j) (iterSquare x j)

/-- Starting at the fourth power, every iterated square of J has form I+4U. -/
-- Step D31
theorem higher_layers (h k : Int) (a : Nat) :
    ∃ u : Matrix, iterSquare (companion (2*h) (2*k)) (a+2) = shift (scale 4 u) 1 := by
  induction a with
  | zero =>
    simp only [iterSquare, companion_square_shape]
    exact ⟨_, square_one_mod_two _⟩
  | succ a ih =>
    obtain ⟨u, hu⟩ := ih
    change ∃ v, mul (iterSquare (companion (2*h) (2*k)) (a+2))
      (iterSquare (companion (2*h) (2*k)) (a+2)) = shift (scale 4 v) 1
    rw [hu]
    refine ⟨⟨2*u.a+4*(mul u u).a, 2*u.b+4*(mul u u).b,
              2*u.c+4*(mul u u).c, 2*u.d+4*(mul u u).d⟩, ?_⟩
    simp only [mul, scale, shift, Matrix.mk.injEq]
    grind

/-- The complementary factor in all higher layers is twice an odd-determinant matrix. -/
-- Step D32
theorem higher_factor (u : Matrix) (z : Int) :
    ∃ b : Matrix, shift (shift (scale 4 u) 1) (1+4*z) = scale 2 b ∧
      ∃ k : Int, det b=2*k+1 := by
  refine ⟨shift (scale 2 (shift u z)) 1, ?_, det_one_mod_two _⟩
  simp only [scale, shift, Matrix.mk.injEq]
  grind

/-- Euler's criterion for the two small verification sums. -/
-- Step D33
def quadSymbol (p b : Nat) : Int :=
  let t := (b%p)^((p-1)/2)%p
  if t = p-1 then -1 else Int.ofNat t

/-- The numerator sums for the trivial, quadratic, and two components of the
quartic character. Each stored entry must be divided by 24 times the modulus. -/
-- Step D34
structure Sums where
  trivial : Int
  quadratic : Int
  realPart : Int
  imaginaryPart : Int
  deriving DecidableEq

-- Step D35
def weightOneNumerators (q d : Nat) : Sums :=
  let m := 16*q*d
  (List.range m).foldl (fun (acc : Sums) (b : Nat) =>
    if b%2=0 then acc else
    let bi : Int := b
    let mi : Int := m
    let w := -(quadSymbol q b) * quadSymbol d b * (6*bi*bi-6*mi*bi+mi*mi)
    let a := b%16
    if a=1 ∨ a=15 then
      ⟨acc.trivial+w, acc.quadratic+w, acc.realPart+w, acc.imaginaryPart⟩
    else if a=5 ∨ a=11 then
      ⟨acc.trivial+w, acc.quadratic-w, acc.realPart, acc.imaginaryPart+w⟩
    else if a=7 ∨ a=9 then
      ⟨acc.trivial+w, acc.quadratic+w, acc.realPart-w, acc.imaginaryPart⟩
    else
      ⟨acc.trivial+w, acc.quadratic-w, acc.realPart, acc.imaginaryPart-w⟩)
    ⟨0,0,0,0⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
-- Step D36
theorem values_3_7 : weightOneNumerators 3 7 =
    ⟨-6*(24*336), -54*(24*336), -66*(24*336), -142*(24*336)⟩ := by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
-- Step D37
theorem values_3_23 : weightOneNumerators 3 23 =
    ⟨-36*(24*1104), -308*(24*1104), -404*(24*1104), -862*(24*1104)⟩ := by decide

/-- Content valuation of a pair via divisibility of both entries and an odd
quotient for at least one of them. -/
-- Step D38
def contentV (x y : Int) (j : Nat) : Prop :=
  divides (twoPower j) x ∧ divides (twoPower j) y ∧ (exactV x j ∨ exactV y j)

/-- If u has the lesser valuation, the target entry ideal has valuation j
and the norm has valuation 2j. -/
-- Step D39
theorem gaussian_first_lower (j : Nat) (a b s : Int) :
    let u := twoPower j*(2*a+1)
    let t := 2*twoPower j*b
    contentV (u+t) (2*t) j ∧ exactV (u^2+(s*t)^2) (j+j) := by
  dsimp only
  constructor
  · refine ⟨⟨2*a+1+2*b, ?_⟩, ⟨4*b, ?_⟩, Or.inl ⟨a+b, ?_⟩⟩ <;> grind
  · exact norm_unequal j a b s

/-- If t has the lesser valuation, oddness of the cyclotomic scalar suffices. -/
-- Step D40
theorem gaussian_second_lower (j : Nat) (a b c : Int) :
    let u := 2*twoPower j*a
    let t := twoPower j*(2*b+1)
    contentV (u+t) (2*t) j ∧ exactV (u^2+((2*c+1)*t)^2) (j+j) := by
  dsimp only
  constructor
  · refine ⟨⟨2*a+2*b+1, ?_⟩, ⟨2*(2*b+1), ?_⟩, Or.inl ⟨a+b, ?_⟩⟩ <;> grind
  · have hh := norm_unequal_right j a b c
    have he : (2*c+1)*(twoPower j*(2*b+1)) =
        (2*c+1)*twoPower j*(2*b+1) := by grind
    rw [he]
    exact hh

/-- If u and t have common valuation j, the target entry ideal has valuation
j+1, and the norm has valuation 2j+1. These three cases recover ceil(h/2). -/
-- Step D41
theorem gaussian_tied (j : Nat) (a b c : Int) :
    let u := twoPower j*(2*a+1)
    let t := twoPower j*(2*b+1)
    contentV (u+t) (2*t) (j+1) ∧ exactV (u^2+((2*c+1)*t)^2) ((j+j)+1) := by
  dsimp only
  constructor
  · refine ⟨⟨a+b+1, ?_⟩, ⟨2*b+1, ?_⟩, Or.inr ⟨b, ?_⟩⟩ <;>
      simp only [twoPower] <;> grind
  · have he : (2*c+1)*(twoPower j*(2*b+1)) =
        (2*c+1)*twoPower j*(2*b+1) := by grind
    rw [he]
    exact norm_equal j a b c

/-- Repeated odd powers x^(2n+1). -/
-- Step D42
def oddPower (x : Int) : Nat → Int
  | 0 => x
  | n+1 => oddPower x n*(x*x)

/-- Raising the sample with index 2^j to any positive odd power preserves
the exact valuation of its difference from 1. -/
-- Step D43
theorem spacing_odd_multiple (j n : Nat) :
    exactV (oddPower (cyclotomicSample j) n-1) (j+2) := by
  obtain ⟨v,hv⟩ := cyclotomic_spacing j
  have hs : cyclotomicSample j = 1+4*twoPower j*(2*v+1) := by
    simp only [twoPower] at hv
    grind
  induction n with
  | zero => exact ⟨v,hv⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := ih
    have hp : oddPower (cyclotomicSample j) n = 1+4*twoPower j*(2*a+1) := by
      simp only [twoPower] at ha
      grind
    let w := 2*v+1+2*twoPower j*(2*v+1)^2
    refine ⟨a+w+4*twoPower j*(2*a+1)*w, ?_⟩
    simp only [oddPower, twoPower, hs, w]
    grind

/-- An odd integer has a multiplicative inverse modulo every 2^j.
The correction step adds 2^j times the previous error. -/
-- Step D44
theorem odd_inverse (a : Int) (j : Nat) :
    ∃ v w : Int, (1+2*a)*v = 1+twoPower j*w := by
  induction j with
  | zero => exact ⟨0,-1, by simp [twoPower]⟩
  | succ j ih =>
    obtain ⟨v,w,hw⟩ := ih
    refine ⟨v+twoPower j*w, (1+a)*w, ?_⟩
    simp only [twoPower]
    grind

-- Step D45
theorem cancel_odd_factor (j : Nat) (a x : Int) :
    divides (twoPower j) ((1+2*a)*x) ↔ divides (twoPower j) x := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨v,w,hw⟩ := odd_inverse a j
    refine ⟨v*z-w*x, ?_⟩
    calc
      x = ((1+2*a)*v-twoPower j*w)*x := by rw [hw]; grind
      _ = v*((1+2*a)*x)-twoPower j*(w*x) := by grind
      _ = twoPower j*(v*z-w*x) := by rw [hz]; grind
  · rintro ⟨z,hz⟩
    exact ⟨(1+2*a)*z, by rw [hz]; grind⟩

/-- All powers of two divide the first-layer entry ideal exactly to the extent
that they divide both real character values after halving. Here a=f(s)/2,
s=1+4u, and t is the trace. -/
-- Step D46
theorem first_layer_threshold (j : Nat) (a t u : Int) :
    (divides (twoPower j) (-(a+2*u*t)) ∧ divides (twoPower j) t) ↔
    (divides (twoPower j) a ∧ divides (twoPower j) (a+(1+4*u)*t)) := by
  constructor
  · rintro ⟨⟨z,hz⟩,⟨w,hw⟩⟩
    refine ⟨⟨-z-2*u*w, ?_⟩, ⟨-z+(1+2*u)*w, ?_⟩⟩ <;> grind
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have hprod : divides (twoPower j) ((1+2*(2*u))*t) := by
      exact ⟨y-x, by grind⟩
    obtain ⟨w,hw⟩ := (cancel_odd_factor j (2*u) t).mp hprod
    exact ⟨⟨-x-2*u*w, by grind⟩, ⟨w,hw⟩⟩

/-- Integer realization of half of f(s) and half of f(-s), with even trace
2t, odd determinant 1+2d, and s congruent to 1 modulo four. -/
-- Step D47
theorem halves_of_real_values (t d u : Int) :
    let s := 1+4*u
    let a := 1+4*u+8*u*u-t-4*u*t+d
    2*a = characteristic (2*t) (1+2*d) s ∧
      2*(a+s*(2*t)) = characteristic (2*t) (1+2*d) (-s) := by
  simp only [characteristic]
  grind

/-- The difference n²−n is even for every signed integer. -/
-- Step D48
theorem square_parity (n : Int) : ∃ a : Int, n*n=n+2*a := by
  have hp : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hp with h | h
  · exact ⟨(n/2)*(2*(n/2)-1), by grind⟩
  · exact ⟨(n/2)*(2*(n/2)+1), by grind⟩

/-- The two real values modulo four and the Gaussian norm modulo eight,
with explicit integer quotients valid at arbitrary precision. -/
-- Step D49
theorem residue_witnesses (t d u : Int) :
    let s := 1+4*u
    ∃ v w z : Int,
      characteristic (2*t) (1+2*d) s = 2*(1+d-t)+4*v ∧
      characteristic (2*t) (1+2*d) (-s) = 2*(1+d+t)+4*w ∧
      ((1+2*d)-s*s)^2+s^2*(2*t)^2 = 4*(d+t)+8*z := by
  obtain ⟨a,ha⟩ := square_parity d
  obtain ⟨b,hb⟩ := square_parity t
  let z := u+2*u*u
  refine ⟨2*u+4*u*u-2*t*u, 2*u+4*u*u+2*t*u,
          a+b-4*d*z+8*z^2+4*u*t^2+8*u^2*t^2, ?_⟩
  simp only [characteristic, z]
  grind

/-- The residue dichotomy at every integral trace, determinant and scalar
allowed by the descent, without any finite bound on representatives. -/
-- Step D50
theorem integer_dichotomy (t d u : Int) :
    let s := 1+4*u
    let k := characteristic (2*t) (1+2*d) s
    let l := characteristic (2*t) (1+2*d) (-s)
    let h := ((1+2*d)-s*s)^2+s^2*(2*t)^2
    ((k%4=0 ∧ l%4=0) ∨ (k%4=2 ∧ l%4=2)) ∧
      ((k%4=0 ∧ l%4=0) ↔ h%8=4) := by
  obtain ⟨v,w,z,hk,hl,hh⟩ := residue_witnesses t d u
  dsimp only
  rw [hk,hl,hh]
  omega

end Reimann.Dyadic

