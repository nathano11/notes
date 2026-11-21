import Std

/-! Quadratic reduction at precision 64. Coefficients are written in
ascending powers of X. The two output coordinates use the basis 1,T
with X = 1+T and T² = -c₁T-c₀. -/
namespace Reimann.SignedPreparation

abbrev Coord := BitVec 6 × BitVec 6

/-- Multiplication by X in the quadratic quotient. -/
def mulX (c0 c1 : BitVec 6) (z : Coord) : Coord :=
  (z.1 - c0*z.2, z.1 + (1-c1)*z.2)

def reduce (c0 c1 : BitVec 6) : List Int → Coord
  | [] => (0,0)
  | a :: as =>
    let z := mulX c0 c1 (reduce c0 c1 as)
    (BitVec.ofInt 6 a + z.1, z.2)

/-- Least nonnegative representatives of the constant and linear remainders. -/
def remainder (c0 c1 : Int) (coeffs : List Int) : Int × Int :=
  let z := reduce (BitVec.ofInt 6 c0) (BitVec.ofInt 6 c1) coeffs
  ((z.1.toNat : Int), (z.2.toNat : Int))

def add (v w : Coord) : Coord := (v.1 + w.1, v.2 + w.2)

def scale (k : BitVec 6) (v : Coord) : Coord := (k*v.1, k*v.2)

theorem mulX_add (c0 c1 : BitVec 6) (v w : Coord) :
    mulX c0 c1 (add v w) = add (mulX c0 c1 v) (mulX c0 c1 w) := by
  simp only [add, mulX, Prod.mk.injEq]
  grind

theorem mulX_scale (c0 c1 k : BitVec 6) (v : Coord) :
    mulX c0 c1 (scale k v) = scale k (mulX c0 c1 v) := by
  simp only [scale, mulX, Prod.mk.injEq]
  grind

/-- Coefficientwise polynomial addition, allowing different lengths. -/
def sumPoly : List Int → List Int → List Int
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a+b) :: sumPoly as bs

theorem reduce_sum (c0 c1 : BitVec 6) (as bs : List Int) :
    reduce c0 c1 (sumPoly as bs) = add (reduce c0 c1 as) (reduce c0 c1 bs) := by
  induction as generalizing bs with
  | nil => simp [sumPoly, reduce, add]
  | cons a as ih =>
    cases bs with
    | nil => simp [sumPoly, reduce, add]
    | cons b bs =>
      simp only [sumPoly, reduce, ih]
      rw [mulX_add, BitVec.ofInt_add]
      simp [add, BitVec.add_assoc]
      ac_rfl

theorem reduce_scale (c0 c1 : BitVec 6) (u : Int) (as : List Int) :
    reduce c0 c1 (as.map (u * ·)) = scale (BitVec.ofInt 6 u) (reduce c0 c1 as) := by
  induction as with
  | nil => simp [reduce, scale]
  | cons a as ih =>
    simp only [List.map_cons, reduce, ih]
    rw [mulX_scale, BitVec.ofInt_mul]
    simp [scale, BitVec.mul_add]

/-- Ordinary polynomial multiplication in ascending coefficient order. -/
def productPoly : List Int → List Int → List Int
  | [], _ => []
  | a :: as, bs => sumPoly (bs.map (a * ·)) (0 :: productPoly as bs)

theorem product_vanishes (c0 c1 : BitVec 6) (as bs : List Int)
    (hb : reduce c0 c1 bs = (0,0)) : reduce c0 c1 (productPoly as bs) = (0,0) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [productPoly, reduce_sum, reduce_scale, hb, reduce, ih, add, scale, mulX]

/-- In the X basis this is (X−1)² + c₁(X−1) + c₀. -/
def quadratic (c0 c1 : Int) : List Int := [1 + c0 + (-c1), c1 + (-2), 1]

theorem quadratic_vanishes (c0 c1 : Int) :
    reduce (BitVec.ofInt 6 c0) (BitVec.ofInt 6 c1) (quadratic c0 c1) = (0,0) := by
  simp [quadratic, reduce, mulX, BitVec.ofInt_add, BitVec.ofInt_neg]
  grind

/-- X⁶⁴−1 as a polynomial in X. -/
def cycle : List Int := -1 :: (List.replicate 63 0 ++ [1])

theorem even_cast (c : Int) (hc : c % 2 = 0) :
    BitVec.ofInt 6 c = BitVec.ofNat 6 (2*((c%64).toNat/2)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  change (c%64).toNat = 2*((c%64).toNat/2) % 64
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- The 1024 even coefficient pairs exhaust all distinguished quadratics at
this precision. This proof computes X⁶⁴−1 in each quadratic quotient. -/
theorem cycle_at_even_residues :
    ∀ i j : Fin 32, reduce (BitVec.ofNat 6 (2*i.val)) (BitVec.ofNat 6 (2*j.val)) cycle = (0,0) := by
  decide +kernel

theorem cycle_vanishes (c0 c1 : Int) (h0 : c0 % 2 = 0) (h1 : c1 % 2 = 0) :
    reduce (BitVec.ofInt 6 c0) (BitVec.ofInt 6 c1) cycle = (0,0) := by
  rw [even_cast c0 h0, even_cast c1 h1]
  exact cycle_at_even_residues ⟨(c0%64).toNat/2, by omega⟩ ⟨(c1%64).toNat/2, by omega⟩

/-- Polynomial membership in (Q(X−1), X⁶⁴−1, 64) in ℤ[X]. Equality
up to trailing zeros is handled by comparing coefficient functions. -/
def CyclicFactor (c0 c1 : Int) (row : List Int) : Prop :=
  ∃ u v : List Int, ∀ n : Nat, row[n]?.getD 0 % 64 =
    (sumPoly (productPoly u (quadratic c0 c1)) (productPoly v cycle))[n]?.getD 0 % 64

theorem reduce_uncons (c0 c1 : BitVec 6) (as : List Int) :
    reduce c0 c1 as =
      let z := mulX c0 c1 (reduce c0 c1 as.tail)
      (BitVec.ofInt 6 (as[0]?.getD 0) + z.1, z.2) := by
  cases as with
  | nil => simp [reduce, mulX]
  | cons => rfl

theorem congr_of_bound (c0 c1 : BitVec 6) (bound : Nat) (as bs : List Int)
    (ha : as.length ≤ bound) (hb : bs.length ≤ bound)
    (h : ∀ n : Nat, as[n]?.getD 0 % 64 = bs[n]?.getD 0 % 64) :
    reduce c0 c1 as = reduce c0 c1 bs := by
  induction bound generalizing as bs with
  | zero =>
    rw [List.eq_nil_of_length_eq_zero (by omega : as.length = 0),
        List.eq_nil_of_length_eq_zero (by omega : bs.length = 0)]
  | succ n ih =>
    have ht := ih as.tail bs.tail (by rw [List.length_tail]; omega)
      (by rw [List.length_tail]; omega) (fun j => by simpa only [List.getElem?_tail] using h (j+1))
    have hh : BitVec.ofInt 6 (as[0]?.getD 0) = BitVec.ofInt 6 (bs[0]?.getD 0) := by
      apply BitVec.eq_of_toNat_eq
      exact congrArg Int.toNat (h 0)
    rw [reduce_uncons c0 c1 as, reduce_uncons c0 c1 bs, ht, hh]

/-- A distinguished quadratic divisor of the row in the cyclic group ring
must have zero remainder. The two moduli and all multiplier terms are explicit. -/
theorem cyclic_factor_remainder (c0 c1 : Int) (row : List Int)
    (h0 : c0%2=0) (h1 : c1%2=0) (h : CyclicFactor c0 c1 row) :
    remainder c0 c1 row = (0,0) := by
  obtain ⟨u,v, huv⟩ := h
  let g := sumPoly (productPoly u (quadratic c0 c1)) (productPoly v cycle)
  have hsame := congr_of_bound (BitVec.ofInt 6 c0) (BitVec.ofInt 6 c1)
    (row.length + g.length) row g (by omega) (by omega) huv
  unfold remainder
  rw [hsame]
  dsimp only [g]
  rw [reduce_sum, product_vanishes _ _ u _ (quadratic_vanishes c0 c1),
    product_vanishes _ _ v _ (cycle_vanishes c0 c1 h0 h1)]
  rfl

end Reimann.SignedPreparation
