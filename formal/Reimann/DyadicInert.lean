import Reimann.DyadicQuotient

/-! The quadratic dyadic algebra with basis (1,e) and e²=e−c. For
c=(q+1)/4 and q≡3 mod 8 this gives an explicit local integral model with
four residue classes. -/

namespace Reimann.DyadicInert

open Reimann.DyadicLattice

abbrev Pair := Scalar × Scalar

/-- Multiplication in the basis (1,e) of the quadratic order. -/
def product (c : Scalar) (x y : Pair) : Pair :=
  (add (mul x.1 y.1) (neg (mul c (mul x.2 y.2))),
   add (add (mul x.1 y.2) (mul x.2 y.1)) (mul x.2 y.2))

def one : Pair := (natScalar 1,natScalar 0)

def generator : Pair := (natScalar 0,natScalar 1)

def residue (x : Pair) : BitVec 1 × BitVec 1 := (x.1.residue 0,x.2.residue 0)

theorem generator_square (c : Scalar) :
    product c generator generator = (neg c,natScalar 1) := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;> simp [product, generator, add, neg, mul, natScalar]

/-- Norm of a+be from e²=e−c. -/
def norm (c : Scalar) (x : Pair) : Scalar :=
  add (mul x.1 (add x.1 x.2)) (mul c (mul x.2 x.2))

def conjugate (x : Pair) : Pair := (add x.1 x.2,neg x.2)

theorem product_conjugate (c : Scalar) (x : Pair) :
    product c x (conjugate x) = (norm c x,natScalar 0) := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [product, conjugate, norm, add, mul, neg, natScalar] <;> grind

/-- Multiplication in F₂[e]/(e²+e+1). -/
def residueProduct (x y : BitVec 1 × BitVec 1) : BitVec 1 × BitVec 1 :=
  (x.1*y.1-x.2*y.2, x.1*y.2+x.2*y.1+x.2*y.2)

theorem residue_product (c : Scalar) (hc : c.residue 0 = 1) (x y : Pair) :
    residue (product c x y) = residueProduct (residue x) (residue y) := by
  apply Prod.ext <;> simp only [residue, product, residueProduct, add, neg, mul,hc] <;> grind

/-- The binary quadratic form a²+ab+b² is nonzero at each nonzero pair. -/
theorem residue_norm (c : Scalar) (hc : c.residue 0 = 1) (x : Pair) :
    (norm c x).residue 0 = 1 ↔ residue x ≠ (0,0) := by
  have check : ∀ a b : BitVec 1, a*(a+b)+b*b=1 ↔ (a,b) ≠ (0,0) := by decide
  simpa [norm, add, mul, residue,hc] using check (x.1.residue 0) (x.2.residue 0)

theorem product_scaled (c u : Scalar) (x y : Pair) :
    product c x (scaleVector u y) = scaleVector u (product c x y) := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [product, add, neg, mul, scaleVector] <;> grind

theorem product_comm (c : Scalar) (x y : Pair) : product c x y = product c y x := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [product, add, mul, neg] <;> grind

theorem product_assoc (c : Scalar) (x y z : Pair) :
    product c (product c x y) z = product c x (product c y z) := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [product,add,mul,neg] <;> grind

/-- The full ring of compatible pairs has a unit precisely when reduction
is nonzero. A two-sided inverse is conjugation followed by division by the norm. -/
theorem unit_iff_nonzero_residue (c : Scalar) (hc : c.residue 0 = 1) (x : Pair) :
    (∃ y, product c x y = one ∧ product c y x = one) ↔ residue x ≠ (0,0) := by
  constructor
  · rintro ⟨y,hy,_⟩ hx
    have h := congrArg residue hy
    rw [residue_product c hc, hx] at h
    have bad := congrArg Prod.fst h
    simp [residueProduct,residue,one,natScalar] at bad
  · intro hx
    obtain ⟨u,hu⟩ := odd_scalar_inverse _ ((residue_norm c hc x).mpr hx)
    let y := scaleVector u (conjugate x)
    have hinv : product c x y = one := by
      rw [show y = scaleVector u (conjugate x) by rfl,product_scaled,product_conjugate]
      apply Prod.ext
      · apply scalar_ext; intro n
        change u.residue n * (norm c x).residue n = 1
        rw [BitVec.mul_comm,hu n]
      · apply scalar_ext; intro n; simp [scaleVector,one,mul,natScalar]
    exact ⟨y,hinv,(product_comm c y x).trans hinv⟩

def residueAdd (x y : BitVec 1 × BitVec 1) : BitVec 1 × BitVec 1 :=
  (x.1+y.1,x.2+y.2)

theorem residue_ring_laws : ∀ x y z : BitVec 1 × BitVec 1,
    residueAdd x (0,0) = x ∧ residueAdd x x = (0,0) ∧
    residueAdd x y = residueAdd y x ∧
    residueAdd (residueAdd x y) z = residueAdd x (residueAdd y z) ∧
    residueProduct x (1,0) = x ∧ residueProduct x y = residueProduct y x ∧
    residueProduct (residueProduct x y) z = residueProduct x (residueProduct y z) ∧
    residueProduct x (residueAdd y z) = residueAdd (residueProduct x y) (residueProduct x z)
    := by
  rintro ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩
  revert a b c d e f
  decide

/-- Squaring is the inverse on the three nonzero residue classes. -/
theorem residue_field_inverse : ∀ x : BitVec 1 × BitVec 1, x ≠ (0,0) →
    residueProduct x (residueProduct x x) = (1,0) := by
  rintro ⟨a,b⟩
  revert a b
  decide

theorem residue_section (x : BitVec 1 × BitVec 1) :
    residue (natScalar x.1.toNat,natScalar x.2.toNat) = x := by
  simp [residue,natScalar,BitVec.ofNat_toNat]

/-- The residue classes have canonical indices 0,1,2,3 in coordinates
(0,0),(1,0),(0,1),(1,1); the encoding is a bijection. -/
theorem residue_four :
    ∃ encode : BitVec 1 × BitVec 1 → Fin 4, ∃ decode : Fin 4 → BitVec 1 × BitVec 1,
      (∀ x, decode (encode x) = x) ∧ (∀ n, encode (decode n) = n) := by
  refine ⟨fun x => ⟨(x.1.toNat+2*x.2.toNat)%4,Nat.mod_lt _ (by decide)⟩,
    fun n => (BitVec.ofNat 1 n.val,BitVec.ofNat 1 (n.val/2)), ?_, ?_⟩
  · rintro ⟨a,b⟩; revert a b; decide
  · decide

theorem parameter_odd (q : Nat) (hq : q%8 = 3) :
    (natScalar ((q+1)/4)).residue 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  change ((q+1)/4)%2 = 1
  omega

theorem prime_pair_unit_test (q : Nat) (hq : q%8 = 3) (x : Pair) :
    (∃ y, product (natScalar ((q+1)/4)) x y = one ∧
      product (natScalar ((q+1)/4)) y x = one) ↔ residue x ≠ (0,0) :=
  unit_iff_nonzero_residue _ (parameter_odd q hq) x

/-- The kernel of reduction is the principal ideal (2), coordinate by coordinate. -/
theorem residue_kernel (x : Pair) : residue x = (0,0) ↔
    ∃ y : Pair, scaleVector (natScalar 2) y = x := by
  constructor
  · intro h
    obtain ⟨u,hu⟩ := (DyadicQuotient.residue_eq_iff_multiple 0 x.1 (natScalar 0)).mp
      (congrArg Prod.fst h)
    obtain ⟨v,hv⟩ := (DyadicQuotient.residue_eq_iff_multiple 0 x.2 (natScalar 0)).mp
      (congrArg Prod.snd h)
    refine ⟨(u,v), Prod.ext ?_ ?_⟩
    · apply scalar_ext; intro n
      simpa [scaleVector, add, mul, natScalar] using
        congrArg (fun z : Scalar => z.residue n) hu.symm
    · apply scalar_ext; intro n
      simpa [scaleVector, add, mul, natScalar] using
        congrArg (fun z : Scalar => z.residue n) hv.symm
  · rintro ⟨y,rfl⟩
    simp [residue,scaleVector,natScalar,mul]

/-- At q=3 the generator has exact inverse 1−e in the full dyadic algebra. -/
theorem q_three_generator_inverse :
    product (natScalar ((3+1)/4)) generator (natScalar 1,neg (natScalar 1)) = one := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp [product, generator,one, natScalar,neg,add,mul] <;> grind

/-- The defining polynomial at q=3 has no binary roots and its generator
in the reduction has square e+1. -/
theorem q_three_residue_polynomial :
    (∀ x : BitVec 1, x*x+x+1 ≠ 0) ∧
    residue (product (natScalar ((3+1)/4)) generator generator) = (1,1) := by
  constructor <;> decide

end Reimann.DyadicInert
