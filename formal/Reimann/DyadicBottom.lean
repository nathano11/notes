import Reimann.Dyadic
import Reimann.DyadicLattice
import Reimann.DyadicQuotient

/-! The bottom layer in the basis `(b,c)`. The hypotheses are parameterized
as `C₀ = 4(1 + 2h)`, `C₁ = 2k`, `s = 1 + 4u`. At every precision at least
four the image of `J - sI` consists of the pairs with first coordinate
divisible by four. This calculation accepts integer representatives of the
coefficients at each precision. -/

namespace Reimann.DyadicBottom

open Reimann.Dyadic

/-- Matrix after dividing the first output coordinate of the difference by four. -/
def bottomNormalizer (h k u : Int) : Matrix :=
  ⟨-u, -(1 + 2*h), 1, -2*k - 4*u⟩

theorem bottom_factorization (h k u : Int) :
    shift (companion (4*(1 + 2*h)) (2*k)) (-(1 + 4*u)) =
      mul ⟨4, 0, 0, 1⟩ (bottomNormalizer h k u) := by
  simp only [shift, companion, mul, bottomNormalizer, Matrix.mk.injEq]
  grind

theorem bottom_normalizer_determinant (h k u : Int) :
    det (bottomNormalizer h k u) = 1 + 2*(h + k*u + 2*u*u) := by
  simp only [det, bottomNormalizer]
  grind

/-- An integral pair represents an image point modulo the indicated modulus. -/
def inImageMod (m : Int) (a : Matrix) (p q : Int) : Prop :=
  ∃ x y e f : Int,
    a.a*x + a.b*y = p + m*e ∧ a.c*x + a.d*y = q + m*f

theorem odd_det_image_mod (a : Matrix) (j : Nat) (p q t : Int)
    (hd : det a = 1 + 2*t) : inImageMod (twoPower j) a p q := by
  obtain ⟨v, w, hv⟩ := odd_inverse t j
  refine ⟨v*(a.d*p - a.b*q), v*(a.a*q - a.c*p), w*p, w*q, ?_, ?_⟩
  · calc
      _ = p*(det a*v) := by unfold det; grind
      _ = _ := by rw [hd, hv]; grind
  · calc
      _ = q*(det a*v) := by unfold det; grind
      _ = _ := by rw [hd, hv]; grind

/-- At every precision 2^(j+2), the image is exactly `(4Z, Z)` reduced
modulo that precision. No surjectivity assumption is needed. -/
theorem bottom_image_mod_iff (j : Nat) (h k u p q : Int) :
    inImageMod (twoPower (j+2)) (shift (companion (4*(1+2*h)) (2*k)) (-(1+4*u))) p q ↔
      ∃ t : Int, p = 4*t := by
  rw [bottom_factorization]
  let a := bottomNormalizer h k u
  change inImageMod (twoPower (j+2)) (mul ⟨4,0,0,1⟩ a) p q ↔ _
  constructor
  · rintro ⟨x, y, e, _, hx, _⟩
    refine ⟨a.a*x + a.b*y - twoPower j*e, ?_⟩
    simp only [mul, twoPower] at hx
    grind
  · rintro ⟨t, rfl⟩
    obtain ⟨x, y, e, f, hx, hy⟩ :=
      odd_det_image_mod a (j+2) t q _ (bottom_normalizer_determinant h k u)
    refine ⟨x, y, 4*e, f, ?_, ?_⟩ <;> simp only [mul] <;> grind

/-- In the coordinates of X, (x,y) denotes (2x,y). The second coordinate
drops out of the bottom quotient, and the first is read modulo two. -/
theorem bottom_coset_iff (j : Nat) (h k u x y x' y' : Int) :
    inImageMod (twoPower (j+2)) (shift (companion (4*(1+2*h)) (2*k)) (-(1+4*u)))
        (2*x - 2*x') (y-y') ↔ x % 2 = x' % 2 := by
  rw [bottom_image_mod_iff]
  constructor
  · rintro ⟨t, ht⟩
    omega
  · intro hx
    exact ⟨x/2 - x'/2, by omega⟩

open Reimann.DyadicLattice (Scalar scalar_ext)

/-- Drop the low bit. Coherence requires one extra input bit at each precision. -/
def halfShift (x : Scalar) : Scalar where
  residue n := (x.residue (n+1)).extractLsb' 1 (n+1)
  reduce {i j} hij := by
    rw [BitVec.setWidth_extractLsb'_of_le (by omega)]
    have h := x.reduce (Nat.succ_le_succ hij)
    rw [← h, BitVec.extractLsb'_setWidth_of_le (by omega)]

theorem double_is_shift {w : Nat} (v : BitVec w) : v + v = v <<< 1 := by
  rw [← BitVec.mul_two, BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  cases w with
  | zero => rfl
  | succ w => simp [BitVec.twoPow, Nat.one_mod_two_pow, Nat.shiftLeft_eq]

theorem double_halfShift (x : Scalar) (hx : x.residue 0 = 0) :
    DyadicLattice.add (halfShift x) (halfShift x) = x := by
  apply scalar_ext
  intro n
  change (halfShift x).residue n + (halfShift x).residue n = x.residue n
  rw [double_is_shift, ← x.reduce (Nat.le_succ n)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases i with
  | zero =>
    have h := congrArg (fun z : BitVec 1 => z.getLsbD 0)
      ((x.reduce (Nat.zero_le (n+1))).trans hx)
    simpa [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth] using h.symm
  | succ i =>
    simp [halfShift, hi, Nat.add_comm 1 i,
      show i < n+1 by omega]

theorem halfShift_double (x : Scalar) : halfShift (DyadicLattice.add x x) = x := by
  apply scalar_ext
  intro n
  change ((x.residue (n+1) + x.residue (n+1)).extractLsb' 1 (n+1)) = x.residue n
  rw [double_is_shift, ← x.reduce (Nat.le_succ n)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show 1 + i < n+1+1 by omega, show ¬1+i<1 by omega,
    BitVec.getLsbD_eq_getElem (h := show i < n+1+1 by omega)]

open Reimann.DyadicLattice (act natScalar add neg)

/-- The normalized operator on the inverse limit, in the basis (b,c). -/
def coherentNormalizer (h k u : Scalar) : DyadicLattice.Matrix :=
  ⟨neg u, neg (add (natScalar 1) (DyadicLattice.mul (natScalar 2) h)),
    natScalar 1, neg (add (DyadicLattice.mul (natScalar 2) k)
      (DyadicLattice.mul (natScalar 4) u))⟩

theorem coherent_normalizer_odd (h k u : Scalar) :
    (DyadicLattice.det (coherentNormalizer h k u)).residue 0 = 1 := by
  simp [DyadicLattice.det, coherentNormalizer, add, neg, DyadicLattice.mul, natScalar]

/-- J - sI, with rows (1-s, -C₀) and (1, 1-C₁-s). -/
def bottomDifference (c0 c1 s : Scalar) : DyadicLattice.Matrix :=
  ⟨add (natScalar 1) (neg s), neg c0, natScalar 1,
    add (add (natScalar 1) (neg c1)) (neg s)⟩

theorem coherent_factorization (c0 c1 s h k u : Scalar)
    (h0 : c0 = DyadicLattice.mul (natScalar 4) (add (natScalar 1) (DyadicLattice.mul (natScalar 2) h)))
    (h1 : c1 = DyadicLattice.mul (natScalar 2) k)
    (hs : s = add (natScalar 1) (DyadicLattice.mul (natScalar 4) u))
    (x : Scalar × Scalar) :
    act (bottomDifference c0 c1 s) x =
      let v := act (coherentNormalizer h k u) x
      (DyadicLattice.mul (natScalar 4) v.1, v.2) := by
  subst c0; subst c1; subst s
  apply Prod.ext <;> apply scalar_ext <;> intro n <;>
    simp only [bottomDifference, coherentNormalizer, act, add, neg, DyadicLattice.mul, natScalar] <;>
    grind

/-- The actual image equality on compatible residue sequences. -/
theorem coherent_bottom_image (c0 c1 s h k u : Scalar)
    (h0 : c0 = DyadicLattice.mul (natScalar 4) (add (natScalar 1) (DyadicLattice.mul (natScalar 2) h)))
    (h1 : c1 = DyadicLattice.mul (natScalar 2) k)
    (hs : s = add (natScalar 1) (DyadicLattice.mul (natScalar 4) u))
    (y : Scalar × Scalar) :
    (∃ x, act (bottomDifference c0 c1 s) x = y) ↔
      ∃ p, y.1 = DyadicLattice.mul (natScalar 4) p := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, congrArg Prod.fst (coherent_factorization _ _ _ _ _ _ h0 h1 hs x)⟩
  · rintro ⟨p, hp⟩
    obtain ⟨x, hx⟩ := DyadicLattice.odd_det_surjective _ (coherent_normalizer_odd h k u) (p,y.2)
    exact ⟨x, by rw [coherent_factorization _ _ _ _ _ _ h0 h1 hs, hx]; exact Prod.ext hp.symm rfl⟩

theorem double_in_four_iff (z : Scalar) :
    (∃ p, add z z = DyadicLattice.mul (natScalar 4) p) ↔ z.residue 0 = 0 := by
  have hfour (p : Scalar) :
      DyadicLattice.mul (natScalar 4) p = add (add p p) (add p p) := by
    apply scalar_ext
    intro n
    simp only [DyadicLattice.mul, natScalar, add]
    grind
  constructor
  · rintro ⟨p, hp⟩
    rw [hfour] at hp
    have hc := congrArg halfShift hp
    rw [halfShift_double, halfShift_double] at hc
    rw [hc]
    change p.residue 0 + p.residue 0 = 0
    generalize p.residue 0 = b
    exact (by decide : ∀ b : BitVec 1, b+b=0) b
  · intro hz
    let p := halfShift z
    have hp : add p p = z := double_halfShift z hz
    exact ⟨p, by rw [hfour, hp]⟩

/-- Coset equality on X, written in X-coordinates so (x,y) stands for (2x,y). -/
def bottomClassRel (c0 c1 s : Scalar) (p q : Scalar × Scalar) : Prop :=
  let dx := add p.1 (neg q.1)
  ∃ x, act (bottomDifference c0 c1 s) x = (add dx dx, add p.2 (neg q.2))

theorem coherent_bottom_classes (c0 c1 s h k u : Scalar)
    (h0 : c0 = DyadicLattice.mul (natScalar 4) (add (natScalar 1) (DyadicLattice.mul (natScalar 2) h)))
    (h1 : c1 = DyadicLattice.mul (natScalar 2) k)
    (hs : s = add (natScalar 1) (DyadicLattice.mul (natScalar 4) u))
    (p q : Scalar × Scalar) :
    bottomClassRel c0 c1 s p q ↔ p.1.residue 0 = q.1.residue 0 := by
  unfold bottomClassRel
  rw [coherent_bottom_image _ _ _ _ _ _ h0 h1 hs]
  change (∃ t, add (add p.1 (neg q.1)) (add p.1 (neg q.1)) = DyadicLattice.mul (natScalar 4) t) ↔ _
  rw [double_in_four_iff]
  change p.1.residue 0 + -(q.1.residue 0) = 0 ↔ p.1.residue 0 = q.1.residue 0
  exact (by decide : ∀ a b : BitVec 1, a + -b = 0 ↔ a = b) _ _

/-- Explicit inverse maps to the additive group of one-bit words. The last
identity verifies addition of arbitrary representatives. -/
theorem coherent_bottom_quotient (c0 c1 s h k u : Scalar)
    (h0 : c0 = DyadicLattice.mul (natScalar 4) (add (natScalar 1) (DyadicLattice.mul (natScalar 2) h)))
    (h1 : c1 = DyadicLattice.mul (natScalar 2) k)
    (hs : s = add (natScalar 1) (DyadicLattice.mul (natScalar 4) u)) :
    let rel := bottomClassRel c0 c1 s
    ∃ read : Quot rel → BitVec 1, ∃ write : BitVec 1 → Quot rel,
      (∀ t, read (write t) = t) ∧ (∀ z, write (read z) = z) ∧
      (∀ p : Scalar × Scalar, read (Quot.mk rel p) = p.1.residue 0) ∧
      (∀ p q : Scalar × Scalar, read (Quot.mk rel (add p.1 q.1, add p.2 q.2)) =
        read (Quot.mk rel p) + read (Quot.mk rel q)) := by
  let rel := bottomClassRel c0 c1 s
  let read := Quot.lift (fun p : Scalar × Scalar => p.1.residue 0)
    (fun p q hrel => (coherent_bottom_classes _ _ _ _ _ _ h0 h1 hs p q).mp hrel)
  let rep (t : BitVec 1) := (natScalar t.toNat, natScalar 0)
  have hrep (t : BitVec 1) : (rep t).1.residue 0 = t := by simp [rep, natScalar]
  refine ⟨read, fun t => Quot.mk rel (rep t), hrep, ?_, fun _ => rfl, fun _ _ => rfl⟩
  intro z
  induction z using Quot.ind with
  | _ p =>
    apply Quot.sound
    exact (coherent_bottom_classes _ _ _ _ _ _ h0 h1 hs _ _).mpr (hrep _)

/-- The interpolation residues and s ≡ 1 mod 4 suffice for the bottom quotient. -/
theorem coherent_bottom_quotient_of_residues (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1) :
    let rel := bottomClassRel c0 c1 s
    ∃ read : Quot rel → BitVec 1, ∃ write : BitVec 1 → Quot rel,
      (∀ t, read (write t) = t) ∧ (∀ z, write (read z) = z) ∧
      (∀ p : Scalar × Scalar, read (Quot.mk rel p) = p.1.residue 0) ∧
      (∀ p q : Scalar × Scalar, read (Quot.mk rel (add p.1 q.1, add p.2 q.2)) =
        read (Quot.mk rel p) + read (Quot.mk rel q)) := by
  obtain ⟨h, hh⟩ := (DyadicQuotient.residue_eq_iff_multiple 2 c0 (natScalar 4)).mp h0
  obtain ⟨k, hk⟩ := (DyadicQuotient.residue_eq_iff_multiple 1 c1 (natScalar 2)).mp h1
  obtain ⟨u, hu⟩ := (DyadicQuotient.residue_eq_iff_multiple 1 s (natScalar 1)).mp hs
  apply coherent_bottom_quotient c0 c1 s h (add (natScalar 1) (DyadicLattice.mul (natScalar 2) k)) u _ _ hu
  · rw [hh]
    apply scalar_ext
    intro n
    change BitVec.ofNat (n+1) 4 + BitVec.ofNat (n+1) 8 * h.residue n =
      BitVec.ofNat (n+1) 4 * (1 + BitVec.ofNat (n+1) 2 * h.residue n)
    grind
  · rw [hk]
    apply scalar_ext
    intro n
    change BitVec.ofNat (n+1) 2 + BitVec.ofNat (n+1) 4 * k.residue n =
      BitVec.ofNat (n+1) 2 * (1 + BitVec.ofNat (n+1) 2 * k.residue n)
    grind

end Reimann.DyadicBottom
