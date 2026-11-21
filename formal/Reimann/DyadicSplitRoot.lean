import Reimann.DyadicLattice

/-! Compatible dyadic roots of W² − W + c for an even constant c. -/

namespace Reimann.DyadicSplitRoot

open Reimann.DyadicLattice

/-- For every precision an even integral representative solves the quadratic
with any prescribed even integer constant. The second witness records its error. -/
theorem even_root_precision (k : Int) (n : Nat) :
    ∃ w e : Int, (2*w)*(2*w) + 2*k = 2*w + (2:Int)^(n+1)*e := by
  induction n with
  | zero => exact ⟨0, k, by simp⟩
  | succ n ih =>
    obtain ⟨w,e,he⟩ := ih
    refine ⟨w + 2^n*e, e*(2*w + 2^n*e), ?_⟩
    rw [Int.pow_succ] at he
    simp only [Int.pow_succ]
    grind

theorem finite_even_root {n : Nat} (c : BitVec (n+1)) (hc : c.setWidth 1 = 0) :
    ∃ x : BitVec (n+1), x.setWidth 1 = 0 ∧ x*x + c = x := by
  have hnat := congrArg BitVec.toNat hc
  simp [BitVec.toNat_setWidth] at hnat
  have hpar : (c.toNat : Int) % 2 = 0 := by exact_mod_cast hnat
  have htwice : 2*((c.toNat : Int)/2) = c.toNat := by omega
  obtain ⟨w,e,he⟩ := even_root_precision ((c.toNat : Int)/2) n
  rw [htwice] at he
  let x := BitVec.ofInt (n+1) (2*w)
  refine ⟨x, ?_, ?_⟩
  · simp [x, BitVec.ofInt_mul, BitVec.setWidth_mul _ _ (show 1 ≤ n+1 by omega),
      BitVec.setWidth_ofNat_of_le (show 1 ≤ n+1 by omega)]
  · have hz : BitVec.ofInt (n+1) ((2:Int)^(n+1)) = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp
    have h := congrArg (BitVec.ofInt (n+1)) he
    simp only [BitVec.ofInt_add, BitVec.ofInt_mul, hz] at h
    simpa [x, BitVec.ofInt_mul, BitVec.ofNat_toNat] using h

/-- The other factor in the difference of two root equations is odd, so
two roots with low bit zero agree at the entire precision. -/
theorem finite_even_root_unique {n : Nat} {c x y : BitVec (n+1)}
    (hx0 : x.setWidth 1 = 0) (hy0 : y.setWidth 1 = 0)
    (hx : x*x + c = x) (hy : y*y + c = y) : x = y := by
  let z := 1 + (-x) + (-y)
  have hz : z.setWidth 1 = 1 := by
    simp [z, BitVec.setWidth_add _ _ (show 1 ≤ n+1 by omega),
      BitVec.setWidth_neg_of_le (show 1 ≤ n+1 by omega),
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (show 0 < n+1 by omega), hx0, hy0]
  have hp := congrArg BitVec.toNat hz
  obtain ⟨v,hv⟩ := unit_at_precision z (by simpa [BitVec.toNat_setWidth] using hp)
  have he : (x-y)*z = 0 := by dsimp [z]; grind
  have hxy : x-y = 0 := calc
    x-y = (x-y)*(z*v) := by rw [hv]; simp
    _ = 0 := by rw [← BitVec.mul_assoc, he]; simp
  grind

/-- Compatibility follows from uniqueness after reducing any higher root. -/
theorem coherent_even_root (c : Scalar) (hc : c.residue 0 = 0) :
    ∃ x : Scalar, x.residue 0 = 0 ∧ add (mul x x) c = x := by
  have existsRoot (n : Nat) := finite_even_root (c.residue n)
    ((c.reduce (Nat.zero_le n)).trans hc)
  let root (n : Nat) := Classical.choose (existsRoot n)
  have hroot (n : Nat) : (root n).setWidth 1 = 0 ∧ root n*root n+c.residue n=root n :=
    Classical.choose_spec (existsRoot n)
  have compat {i j : Nat} (hij : i ≤ j) : (root j).setWidth (i+1) = root i := by
    apply finite_even_root_unique (c := c.residue i) _ (hroot i).1 _ (hroot i).2
    · rw [BitVec.setWidth_setWidth_of_le _ (show 1 ≤ i+1 by omega), (hroot j).1]
    · have he := congrArg (BitVec.setWidth (i+1)) (hroot j).2
      rwa [BitVec.setWidth_add _ _ (by omega), BitVec.setWidth_mul _ _ (by omega), c.reduce hij] at he
  let x : Scalar := ⟨root, compat⟩
  exact ⟨x, by simpa [x] using (hroot 0).1, scalar_ext (fun n => (hroot n).2)⟩

theorem complement_root (c x : Scalar) (hx : add (mul x x) c = x) :
    let y := add (natScalar 1) (neg x)
    add (mul y y) c = y := by
  apply scalar_ext
  intro n
  have he := congrArg (fun v : Scalar => v.residue n) hx
  simp only [add, neg, mul, natScalar] at he ⊢
  grind

/-- Opposite residues distinguish the two roots and their difference has a
single inverse compatible at every precision. -/
theorem coherent_split_roots (c : Scalar) (hc : c.residue 0 = 0) :
    ∃ x y u : Scalar, add (mul x x) c = x ∧ add (mul y y) c = y ∧
      x.residue 0 = 0 ∧ y.residue 0 = 1 ∧
      ∀ n, (add y (neg x)).residue n * u.residue n = 1 := by
  obtain ⟨x,hx0,hx⟩ := coherent_even_root c hc
  let y := add (natScalar 1) (neg x)
  have hy : y.residue 0 = 1 := by simp [y, add, natScalar, neg, hx0]
  have hd : (add y (neg x)).residue 0 = 1 := by
    change y.residue 0 + -(x.residue 0) = 1
    rw [hy, hx0]
    decide
  obtain ⟨u, hu⟩ := odd_scalar_inverse (add y (neg x)) hd
  exact ⟨x, y, u, hx, complement_root c x hx, hx0, hy, hu⟩

theorem split_constant_even (d : Nat) (hd : d % 16 = 7) :
    (natScalar ((d+1)/4)).residue 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [natScalar, BitVec.toNat_ofNat]
  omega

/-- The dyadic residue family supplies the even constant; primality of d
is unnecessary for this local calculation. -/
theorem split_roots_of_prime_residue (d : Nat) (hd : d % 16 = 7) :
    let c := natScalar ((d+1)/4)
    ∃ x y u : Scalar, add (mul x x) c = x ∧ add (mul y y) c = y ∧
      x.residue 0 = 0 ∧ y.residue 0 = 1 ∧
      ∀ n, (add y (neg x)).residue n * u.residue n = 1 :=
  coherent_split_roots _ (split_constant_even d hd)

end Reimann.DyadicSplitRoot
