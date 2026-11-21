import Reimann.SignedPreparation

/-! Lift a product by a quadratic in the order-64 cyclic group ring to an
ordinary integral polynomial identity modulo 64 and the cycle relation. -/
namespace Reimann.SignedCyclicFactor

open SignedPreparation

/-- Missing coefficients of an integral polynomial are zero. -/
def coeff (p : List Int) (n : Nat) : Int := p[n]?.getD 0

theorem coeff_add (p q : List Int) (n : Nat) :
    coeff (sumPoly p q) n = coeff p n + coeff q n := by
  induction p generalizing n q with
  | nil => simp [sumPoly,coeff]
  | cons a p ih =>
    cases q with
    | nil => simp [sumPoly,coeff]
    | cons b q =>
      cases n with
      | zero => rfl
      | succ n => exact ih q n

theorem coeff_scale (a : Int) (p : List Int) (n : Nat) :
    coeff (p.map (a * ·)) n = a * coeff p n := by
  simp only [coeff, List.getElem?_map]
  cases p[n]? <;> simp

theorem coeff_zero_past (p : List Int) (n : Nat) (h : p.length ≤ n) : coeff p n = 0 := by
  simp [coeff, List.getElem?_eq_none h]

theorem product_head (a : Int) (p q : List Int) :
    coeff (productPoly (a::p) q) 0 = a * coeff q 0 := by
  rw [productPoly, coeff_add, coeff_scale]
  simp [coeff]

theorem product_succ (a : Int) (p q : List Int) (n : Nat) :
    coeff (productPoly (a::p) q) (n+1) = a*coeff q (n+1) + coeff (productPoly p q) n := by
  rw [productPoly, coeff_add, coeff_scale]
  rfl

theorem quadratic_zero (p : List Int) (a b : Int) :
    coeff (productPoly p [a,b,1]) 0 = coeff p 0 * a := by
  cases p with
  | nil => simp [productPoly, coeff]
  | cons v p => rw [product_head]; rfl

theorem quadratic_one (p : List Int) (a b : Int) :
    coeff (productPoly p [a,b,1]) 1 = coeff p 0 * b + coeff p 1 * a := by
  cases p with
  | nil => simp [productPoly, coeff]
  | cons v p => rw [product_succ, quadratic_zero]; rfl

theorem quadratic_at (p : List Int) (a b : Int) (n : Nat) :
    coeff (productPoly p [a,b,1]) (n+2) =
      coeff p n + coeff p (n+1) * b + coeff p (n+2) * a := by
  induction p generalizing n with
  | nil => simp [productPoly, coeff]
  | cons v p ih =>
    rw [product_succ]
    cases n with
    | zero =>
      rw [quadratic_one]
      change v*1 + (coeff p 0*b + coeff p 1*a) = v + coeff p 0*b + coeff p 1*a
      grind
    | succ n =>
      rw [ih]
      change v*0 + _ = _
      simp only [Int.mul_zero, Int.zero_add]
      rfl

theorem cycle_coeff (n : Nat) :
    coeff cycle n = if n = 0 then -1 else if n = 64 then 1 else 0 := by
  by_cases h : n < 65
  · have check : ∀ i : Fin 65, coeff cycle i.val =
        if i.val=0 then -1 else if i.val=64 then 1 else 0 := by decide
    exact check ⟨n,h⟩
  · rw [coeff_zero_past cycle n (by change 65 ≤ n; omega)]
    simp [show n ≠ 0 by omega, show n ≠ 64 by omega]

theorem correction_zero (a b : Int) : coeff (productPoly [a,b] cycle) 0 = -a := by
  rw [product_head, cycle_coeff]
  simp

theorem correction_succ (a b : Int) (n : Nat) :
    coeff (productPoly [a,b] cycle) (n+1) = a*coeff cycle (n+1) + b*coeff cycle n := by
  rw [product_succ]
  cases n with
  | zero => rw [product_head]
  | succ n => rw [product_succ]; simp [productPoly, coeff]

/-- Canonical coefficient representatives of a cyclic multiplier. -/
def liftRow (u : Fin 64 → BitVec 6) : List Int :=
  List.ofFn (fun i => ((u i).toNat : Int))

theorem lift_length (u : Fin 64 → BitVec 6) : (liftRow u).length = 64 := by
  simp [liftRow]

theorem lift_at (u : Fin 64 → BitVec 6) (i : Fin 64) :
    coeff (liftRow u) i.val = ((u i).toNat : Int) := by
  have hi : i.val < (liftRow u).length := (lift_length u).symm ▸ i.isLt
  unfold coeff
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.getD_some, liftRow, List.getElem_ofFn]

theorem lift_cast (u : Fin 64 → BitVec 6) (i : Fin 64) :
    BitVec.ofInt 6 (coeff (liftRow u) i.val) = u i := by
  rw [lift_at]
  exact BitVec.eq_of_toNat_eq (by simp)

/-- Two high coefficients of UQ, moved to indices zero and one by X^64=1. -/
def wrap (u : List Int) (a b : Int) : List Int :=
  sumPoly (productPoly u [a,b,1])
    (productPoly [-(coeff u 62 + coeff u 63*b), -coeff u 63] cycle)

theorem wrap_zero (u : List Int) (a b : Int) :
    coeff (wrap u a b) 0 = coeff u 0*a + coeff u 63*b + coeff u 62 := by
  rw [wrap, coeff_add, quadratic_zero, correction_zero]
  grind

theorem wrap_one (u : List Int) (a b : Int) :
    coeff (wrap u a b) 1 = coeff u 1*a + coeff u 0*b + coeff u 63 := by
  rw [wrap, coeff_add, quadratic_one, correction_succ, cycle_coeff, cycle_coeff]
  simp
  grind

theorem wrap_interior (u : List Int) (a b : Int) (n : Nat) (hn : n+2<64) :
    coeff (wrap u a b) (n+2) = coeff u (n+2)*a + coeff u (n+1)*b + coeff u n := by
  rw [wrap, coeff_add, quadratic_at, correction_succ, cycle_coeff, cycle_coeff]
  simp [show n+1 ≠ 64 by omega, show n+2 ≠ 64 by omega]
  grind

theorem wrap_past (u : List Int) (a b : Int) (hu : u.length=64) (n : Nat) (hn : 64≤n) :
    coeff (wrap u a b) n = 0 := by
  have zero (k : Nat) (hk : 64≤k) : coeff u k=0 := coeff_zero_past u k (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, n=k+64 := ⟨n-64, by omega⟩
  cases k with
  | zero =>
    change coeff (wrap u a b) (62+2) = 0
    rw [wrap, coeff_add, quadratic_at, correction_succ, cycle_coeff, cycle_coeff, zero 64 (by decide)]
    simp <;> omega
  | succ k =>
    cases k with
    | zero =>
      change coeff (wrap u a b) (63+2) = 0
      rw [wrap, coeff_add, quadratic_at, correction_succ, cycle_coeff, cycle_coeff,
        zero 64 (by decide), zero 65 (by decide)]
      simp <;> omega
    | succ k =>
      rw [show k+1+1+64=k+64+2 by omega, wrap, coeff_add, quadratic_at, correction_succ,
        cycle_coeff, cycle_coeff, zero (k+64) (by omega), zero (k+64+1) (by omega),
        zero (k+64+2) (by omega)]
      simp [show k+64+2 ≠ 64 by omega, show k+64+1 ≠ 64 by omega]

theorem lift_at_offset (u : Fin 64 → BitVec 6) (n : Nat) (hn : n<64) :
    BitVec.ofInt 6 (coeff (liftRow u) n) = u ⟨n,hn⟩ := lift_cast u ⟨n,hn⟩

theorem predecessors (n : Nat) (hn : n+2<64) :
    (⟨n+2,hn⟩ : Fin 64) - 1 = ⟨n+1,by omega⟩ ∧
    (⟨n+2,hn⟩ : Fin 64) - 2 = ⟨n,by omega⟩ := by
  constructor
  · apply Fin.ext
    change (63 + (n+2)) % 64 = n+1
    omega
  · apply Fin.ext
    change (62 + (n+2)) % 64 = n
    omega

/-- The cyclic coordinates of the corrected ordinary product. The two
predecessors are subtraction in Fin 64, including wrap-around at zero. -/
theorem wrap_lift (u : Fin 64 → BitVec 6) (a b : Int) (i : Fin 64) :
    BitVec.ofInt 6 (coeff (wrap (liftRow u) a b) i.val) =
      BitVec.ofInt 6 a*u i + BitVec.ofInt 6 b*u (i-1) + u (i-2) := by
  obtain ⟨n, hn⟩ := i
  cases n with
  | zero =>
    change BitVec.ofInt 6 (coeff _ 0) = BitVec.ofInt 6 a*u 0 + BitVec.ofInt 6 b*u 63 + u 62
    rw [wrap_zero]
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, lift_at_offset u 0 (by decide),
      lift_at_offset u 63 (by decide), lift_at_offset u 62 (by decide)]
    grind
  | succ n =>
    cases n with
    | zero =>
      change BitVec.ofInt 6 (coeff _ 1) = BitVec.ofInt 6 a*u 1 + BitVec.ofInt 6 b*u 0 + u 63
      rw [wrap_one]
      simp only [BitVec.ofInt_add, BitVec.ofInt_mul, lift_at_offset u 1 (by decide),
        lift_at_offset u 0 (by decide), lift_at_offset u 63 (by decide)]
      grind
    | succ n =>
      rw [(predecessors n hn).1, (predecessors n hn).2, wrap_interior _ _ _ n hn]
      simp only [BitVec.ofInt_add, BitVec.ofInt_mul, lift_at_offset u (n+2) hn,
        lift_at_offset u (n+1) (by omega), lift_at_offset u n (by omega)]
      grind

theorem mod_of_bits {a b : Int} (h : BitVec.ofInt 6 a = BitVec.ofInt 6 b) :
    a%64=b%64 := by
  have h' : (a%64).toNat = (b%64).toNat := congrArg BitVec.toNat h
  omega

/-- A coordinate identity in the order-64 cyclic ring yields ordinary
polynomials witnessing ideal membership; no parity condition is needed here. -/
theorem coordinates_to_factor (c0 c1 : Int) (row : List Int) (hr : row.length ≤ 64)
    (u : Fin 64 → BitVec 6)
    (h : ∀ i : Fin 64, BitVec.ofInt 6 (row[i.val]?.getD 0) =
      BitVec.ofInt 6 (1+c0-c1)*u i + BitVec.ofInt 6 (c1-2)*u (i-1) + u (i-2)) :
    CyclicFactor c0 c1 row := by
  let a := 1+c0-c1
  let b := c1-2
  let v := liftRow u
  refine ⟨v, [-(coeff v 62 + coeff v 63*b), -coeff v 63], ?_⟩
  intro n
  change coeff row n % 64 = coeff (wrap v a b) n % 64
  by_cases hn : n<64
  · let i : Fin 64 := ⟨n,hn⟩
    exact mod_of_bits ((h i).trans (wrap_lift u a b i).symm)
  · rw [coeff_zero_past row n (by omega), wrap_past v a b (lift_length u) n (by omega)]

end Reimann.SignedCyclicFactor
