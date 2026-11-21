import Std

/-!
The inverse limit of the rings Z/(2^(n+1)) is represented by compatible
fixed-width words. Its square models a free rank-two lattice after choosing a basis.
-/

namespace Reimann.DyadicLattice

structure Scalar where
  residue (n : Nat) : BitVec (n + 1)
  reduce {i j : Nat} (h : i ≤ j) : (residue j).setWidth (i + 1) = residue i

theorem scalar_ext {x y : Scalar} (h : ∀ n, x.residue n = y.residue n) : x = y := by
  cases x; cases y
  congr
  exact funext h

def add (x y : Scalar) : Scalar where
  residue n := x.residue n + y.residue n
  reduce h := by rw [BitVec.setWidth_add _ _ (by omega), x.reduce h, y.reduce h]

def neg (x : Scalar) : Scalar where
  residue n := -x.residue n
  reduce h := by rw [BitVec.setWidth_neg_of_le (by omega), x.reduce h]

def mul (x y : Scalar) : Scalar where
  residue n := x.residue n * y.residue n
  reduce h := by rw [BitVec.setWidth_mul _ _ (by omega), x.reduce h, y.reduce h]

/-- Lift an inverse for an odd integer one bit at a time. -/
theorem inverse_precision (k : Int) (n : Nat) :
    ∃ b z : Int, (1 + 2*k)*b = 1 + (2:Int)^n*z := by
  induction n with
  | zero => exact ⟨0, -1, by simp⟩
  | succ n ih =>
    obtain ⟨b,z,h⟩ := ih
    refine ⟨b - 2^n*z, -k*z, ?_⟩
    rw [Int.pow_succ]
    grind

/-- Every odd residue has a multiplicative inverse at the given precision. -/
theorem unit_at_precision {n : Nat} (d : BitVec (n+1)) (hd : d.toNat % 2 = 1) :
    ∃ b : BitVec (n+1), d * b = 1 := by
  have hpar : (d.toNat : Int) % 2 = 1 := by exact_mod_cast hd
  have hform : 1 + 2*((d.toNat : Int)/2) = d.toNat := by omega
  obtain ⟨b,z,h⟩ := inverse_precision ((d.toNat : Int)/2) (n+1)
  rw [hform] at h
  have hmod : BitVec.ofInt (n+1) ((2:Int)^(n+1)) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp
  have heq := congrArg (BitVec.ofInt (n+1)) h
  rw [BitVec.ofInt_mul, BitVec.ofInt_add, BitVec.ofInt_mul, hmod] at heq
  exact ⟨BitVec.ofInt (n+1) b, by simpa [BitVec.ofNat_toNat] using heq⟩

theorem odd_residue (d : Scalar) (hd : d.residue 0 = 1) (n : Nat) :
    (d.residue n).toNat % 2 = 1 := by
  have h := congrArg BitVec.toNat ((d.reduce (Nat.zero_le n)).trans hd)
  simpa [BitVec.toNat_setWidth] using h

theorem inverse_unique {n : Nat} {d x y : BitVec (n+1)}
    (hx : d*x = 1) (hy : d*y = 1) : x = y := by
  calc
    x = x * (d * y) := by rw [hy]; simp
    _ = (d * x) * y := by grind
    _ = y := by rw [hx]; simp

/-- The finite inverses agree under truncation by uniqueness. This constructs
an inverse on the full inverse limit from its lowest bit alone. -/
theorem odd_scalar_inverse (d : Scalar) (hd : d.residue 0 = 1) :
    ∃ u : Scalar, ∀ n, d.residue n * u.residue n = 1 := by
  have existsInv (n : Nat) := unit_at_precision (d.residue n) (odd_residue d hd n)
  let inv (n : Nat) := Classical.choose (existsInv n)
  have hinv (n : Nat) : d.residue n * inv n = 1 := Classical.choose_spec (existsInv n)
  refine ⟨⟨inv, ?_⟩, hinv⟩
  intro i j hij
  apply inverse_unique (d := d.residue i) _ (hinv i)
  have h := congrArg (BitVec.setWidth (i+1)) (hinv j)
  rw [BitVec.setWidth_mul _ _ (by omega), d.reduce hij] at h
  simpa [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt] using h

structure Matrix where
  a : Scalar
  b : Scalar
  c : Scalar
  d : Scalar

def det (m : Matrix) : Scalar := add (mul m.a m.d) (neg (mul m.b m.c))

def act (m : Matrix) (x : Scalar × Scalar) : Scalar × Scalar :=
  (add (mul m.a x.1) (mul m.b x.2), add (mul m.c x.1) (mul m.d x.2))

def adjugate (m : Matrix) : Matrix := ⟨m.d, neg m.b, neg m.c, m.a⟩

def scaleVector (k : Scalar) (x : Scalar × Scalar) : Scalar × Scalar :=
  (mul k x.1, mul k x.2)

theorem act_adjugate (m : Matrix) (x : Scalar × Scalar) :
    act m (act (adjugate m) x) = scaleVector (det m) x := by
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [act, adjugate, scaleVector, det, add, neg, mul] <;> grind

/-- A normalized matrix with determinant one modulo two is surjective on
the entire rank-two dyadic lattice. The inverse is the scaled adjugate. -/
theorem odd_det_surjective (m : Matrix) (h : (det m).residue 0 = 1) :
    ∀ y : Scalar × Scalar, ∃ x, act m x = y := by
  obtain ⟨u,hu⟩ := odd_scalar_inverse (det m) h
  intro y
  refine ⟨act (adjugate m) (scaleVector u y), ?_⟩
  rw [act_adjugate]
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [scaleVector, mul] <;> rw [← BitVec.mul_assoc, hu n] <;> simp

/-- The image of a scalar multiple of an odd-determinant matrix is the
scalar multiple of the whole lattice, including scales 4 and 2. -/
theorem scaled_matrix_image (k : Scalar) (m : Matrix) (h : (det m).residue 0 = 1)
    (y : Scalar × Scalar) :
    (∃ x, scaleVector k (act m x) = y) ↔ ∃ z, scaleVector k z = y := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨act m x, hx⟩
  · rintro ⟨z,hz⟩
    obtain ⟨x,hx⟩ := odd_det_surjective m h z
    exact ⟨x, by rw [hx, hz]⟩

def natScalar (v : Nat) : Scalar where
  residue n := BitVec.ofNat (n+1) v
  reduce h := BitVec.setWidth_ofNat_of_le (by omega) _

/-- The bottom-left bit of the normalized first difference may be either
bit. The same test includes normalized complementary factors with reduction I. -/
theorem unipotent_det_odd (m : Matrix)
    (ha : m.a.residue 0 = 1) (hb : m.b.residue 0 = 0) (hd : m.d.residue 0 = 1) :
    (det m).residue 0 = 1 := by
  simp [det, add, mul, neg, ha, hb, hd]

theorem normalized_image (m : Matrix) (k : Nat)
    (ha : m.a.residue 0 = 1) (hb : m.b.residue 0 = 0) (hd : m.d.residue 0 = 1)
    (y : Scalar × Scalar) :
    (∃ x, scaleVector (natScalar k) (act m x) = y) ↔
      ∃ z, scaleVector (natScalar k) z = y :=
  scaled_matrix_image _ m (unipotent_det_odd m ha hb hd) y

end Reimann.DyadicLattice
