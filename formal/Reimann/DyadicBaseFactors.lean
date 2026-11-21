import Reimann.DyadicBottom

/-! The two cyclic factors at layer zero, in the same width convention as the
positive layers. The nontrivial bit comes from the coefficient of (2b).
-/

namespace Reimann.DyadicBaseFactors

open Reimann.DyadicLattice
open Reimann.DyadicBottom (bottomClassRel)

/-- The trivial factor has width zero. The other factor records the parity of
the first coordinate in the basis (2b,c). -/
def bottomFactors (x : Scalar × Scalar) : BitVec 0 × BitVec 1 :=
  (0, x.1.residue 0)

/-- Canonical representative for each pair of bottom-layer residues. -/
def bottomSection (p : BitVec 0 × BitVec 1) : Scalar × Scalar :=
  (natScalar p.2.toNat, natScalar 0)

theorem bottomFactors_section (p : BitVec 0 × BitVec 1) :
    bottomFactors (bottomSection p) = p := by
  apply Prod.ext
  · exact (by decide : ∀ v : BitVec 0, 0 = v) _
  · simp [bottomFactors, bottomSection, natScalar]

theorem bottomFactors_add (x y : Scalar × Scalar) :
    bottomFactors (add x.1 y.1, add x.2 y.2) =
      ((bottomFactors x).1 + (bottomFactors y).1, (bottomFactors x).2 + (bottomFactors y).2) :=
  rfl

/-- In bottom-layer coordinates the matrix image identifies exactly the
representatives with equal residue pairs. -/
theorem bottomCoset_iff_factors (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (x y : Scalar × Scalar) :
    bottomClassRel c0 c1 s x y ↔ bottomFactors x = bottomFactors y := by
  obtain ⟨h, hh⟩ := (DyadicQuotient.residue_eq_iff_multiple 2 c0 (natScalar 4)).mp h0
  obtain ⟨k, hk⟩ := (DyadicQuotient.residue_eq_iff_multiple 1 c1 (natScalar 2)).mp h1
  obtain ⟨u, hu⟩ := (DyadicQuotient.residue_eq_iff_multiple 1 s (natScalar 1)).mp hs
  have e0 : c0 = mul (natScalar 4) (add (natScalar 1) (mul (natScalar 2) h)) := by
    rw [hh]
    apply scalar_ext
    intro n
    change BitVec.ofNat (n+1) 4 + BitVec.ofNat (n+1) 8 * h.residue n =
      BitVec.ofNat (n+1) 4 * (1 + BitVec.ofNat (n+1) 2 * h.residue n)
    grind
  have e1 : c1 = mul (natScalar 2) (add (natScalar 1) (mul (natScalar 2) k)) := by
    rw [hk]
    apply scalar_ext
    intro n
    change BitVec.ofNat (n+1) 2 + BitVec.ofNat (n+1) 4 * k.residue n =
      BitVec.ofNat (n+1) 2 * (1 + BitVec.ofNat (n+1) 2 * k.residue n)
    grind
  rw [DyadicBottom.coherent_bottom_classes _ _ _ _ _ _ e0 e1 hu]
  exact ⟨fun e => Prod.ext rfl e, fun e => congrArg Prod.snd e⟩

def bottomEncode (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1) :
    Quot (bottomClassRel c0 c1 s) → BitVec 0 × BitVec 1 :=
  Quot.lift bottomFactors (fun x y h => (bottomCoset_iff_factors c0 c1 s h0 h1 hs x y).mp h)

def bottomDecode (c0 c1 s : Scalar) (p : BitVec 0 × BitVec 1) :
    Quot (bottomClassRel c0 c1 s) :=
  Quot.mk _ (bottomSection p)

theorem bottomEncode_mk (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (x : Scalar × Scalar) :
    bottomEncode c0 c1 s h0 h1 hs (Quot.mk _ x) = bottomFactors x := rfl

theorem bottomEncode_decode (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (p : BitVec 0 × BitVec 1) :
    bottomEncode c0 c1 s h0 h1 hs (bottomDecode c0 c1 s p) = p :=
  bottomFactors_section p

theorem bottomDecode_encode (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (z : Quot (bottomClassRel c0 c1 s)) :
    bottomDecode c0 c1 s (bottomEncode c0 c1 s h0 h1 hs z) = z := by
  induction z using Quot.ind with
  | mk x =>
    apply Quot.sound
    exact (bottomCoset_iff_factors c0 c1 s h0 h1 hs _ _).mpr (bottomFactors_section _)

/-- The group sum of cosets, computed by adding their finite residues. -/
def bottomAdd (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (x y : Quot (bottomClassRel c0 c1 s)) : Quot (bottomClassRel c0 c1 s) :=
  let p := bottomEncode c0 c1 s h0 h1 hs x
  let q := bottomEncode c0 c1 s h0 h1 hs y
  bottomDecode c0 c1 s (p.1 + q.1, p.2 + q.2)

theorem bottomAdd_mk (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (x y : Scalar × Scalar) :
    bottomAdd c0 c1 s h0 h1 hs (Quot.mk _ x) (Quot.mk _ y) =
      Quot.mk _ (add x.1 y.1, add x.2 y.2) :=
  bottomDecode_encode c0 c1 s h0 h1 hs (Quot.mk _ (add x.1 y.1, add x.2 y.2))

theorem bottomEncode_add (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (x y : Quot (bottomClassRel c0 c1 s)) :
    let p := bottomEncode c0 c1 s h0 h1 hs x
    let q := bottomEncode c0 c1 s h0 h1 hs y
    bottomEncode c0 c1 s h0 h1 hs (bottomAdd c0 c1 s h0 h1 hs x y) =
      (p.1 + q.1, p.2 + q.2) :=
  bottomEncode_decode c0 c1 s h0 h1 hs _

theorem bottomDecode_add (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1)
    (p q : BitVec 0 × BitVec 1) :
    bottomDecode c0 c1 s (p.1 + q.1, p.2 + q.2) =
      bottomAdd c0 c1 s h0 h1 hs (bottomDecode c0 c1 s p) (bottomDecode c0 c1 s q) := by
  simp only [bottomAdd, bottomEncode_decode]

theorem bottom_factor_classification (c0 c1 s : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) (hs : s.residue 1 = 1) :
    ∃ encode : Quot (bottomClassRel c0 c1 s) → BitVec 0 × BitVec 1,
    ∃ decode : BitVec 0 × BitVec 1 → Quot (bottomClassRel c0 c1 s),
      (∀ x, encode (Quot.mk _ x) = bottomFactors x) ∧
      (∀ z, decode (encode z) = z) ∧ (∀ p, encode (decode p) = p) :=
  ⟨bottomEncode c0 c1 s h0 h1 hs, bottomDecode c0 c1 s, bottomEncode_mk _ _ _ _ _ _,
    bottomDecode_encode _ _ _ _ _ _, bottomEncode_decode _ _ _ _ _ _⟩

end Reimann.DyadicBaseFactors
