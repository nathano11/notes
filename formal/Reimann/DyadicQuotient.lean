import Reimann.DyadicLattice

/-! Finite residues for the lattice inclusion (2x,y) in the coherent dyadic plane. -/

namespace Reimann.DyadicQuotient

open Reimann.DyadicLattice

/-- Reading a residue one block farther along the compatible binary expansion. -/
def dropBits (k : Nat) (x : Scalar) : Scalar where
  residue n := (x.residue (n+k)).extractLsb' k (n+1)
  reduce {i j} hij := by
    rw [BitVec.setWidth_extractLsb'_of_le (by omega)]
    have h := x.reduce (show i+k ≤ j+k by omega)
    rw [← h, BitVec.extractLsb'_setWidth_of_le (by omega)]

/-- Division with remainder in the inverse limit. Extremal precisions do
not require an equicharacteristic representation of a dyadic integer. -/
theorem split_at_residue (j : Nat) (x : Scalar) :
    x = add (natScalar (x.residue j).toNat)
      (mul (natScalar (2^(j+1))) (dropBits (j+1) x)) := by
  apply scalar_ext
  intro n
  let v := (x.residue (n+(j+1))).toNat
  have lo : v % 2^(j+1) = (x.residue j).toNat := by
    have e := congrArg BitVec.toNat (x.reduce (show j ≤ n+(j+1) by omega))
    simpa [BitVec.toNat_setWidth, v] using e
  have en : BitVec.ofNat (n+1) v = x.residue n := by
    rw [show BitVec.ofNat (n+1) v = _ from BitVec.ofNat_toNat _ _, x.reduce (by omega)]
  have e := congrArg (BitVec.ofNat (n+1)) (Nat.mod_add_div v (2^(j+1)))
  rw [lo, BitVec.ofNat_add, BitVec.ofNat_mul, en] at e
  simpa only [add, mul, natScalar, dropBits, BitVec.extractLsb', Nat.shiftRight_eq_div_pow] using e.symm

/-- The kernel of reduction at depth j+1 is exactly 2^(j+1) times the lattice. -/
theorem residue_eq_iff_multiple (j : Nat) (x y : Scalar) :
    x.residue j = y.residue j ↔ ∃ t, x = add y (mul (natScalar (2^(j+1))) t) := by
  constructor
  · intro h
    refine ⟨add (dropBits (j+1) x) (neg (dropBits (j+1) y)), ?_⟩
    have hx := split_at_residue j x
    rw [h] at hx
    have hy := split_at_residue j y
    apply scalar_ext
    intro n
    have ex := congrArg (fun z : Scalar => z.residue n) hx
    have ey := congrArg (fun z : Scalar => z.residue n) hy
    simp only [add, mul, neg] at ex ey ⊢
    grind
  · rintro ⟨t, rfl⟩
    change y.residue j + BitVec.ofNat (j+1) (2^(j+1))*t.residue j = y.residue j
    have hz : BitVec.ofNat (j+1) (2^(j+1)) = 0 := by apply BitVec.eq_of_toNat_eq; simp
    simp [hz]

/-- At precision j+2 the doubled ambient coordinate remembers exactly
j+1 bits of the first X-coordinate. -/
theorem double_residue (j : Nat) (x : Scalar) :
    ((mul (natScalar 2) x).residue (j+1)).toNat = 2*(x.residue j).toNat := by
  have e := congrArg BitVec.toNat (x.reduce (show j ≤ j+1 by omega))
  rw [BitVec.toNat_setWidth] at e
  change (BitVec.ofNat (j+1+1) 2 * x.residue (j+1)).toNat = _
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod,
    Nat.pow_succ, Nat.mul_comm (2^(j+1)) 2, Nat.mul_mod_mul_left, e]

/-- X has ordered basis (2b,c). This map expresses its coordinates in Y. -/
def inAmbient (x : Scalar × Scalar) : Scalar × Scalar := (mul (natScalar 2) x.1, x.2)

theorem inAmbient_injective {x y : Scalar × Scalar} (h : inAmbient x = inAmbient y) : x = y := by
  apply Prod.ext
  · apply scalar_ext
    intro j
    have e := congrArg (fun p : Scalar × Scalar => (p.1.residue (j+1)).toNat) h
    change ((mul (natScalar 2) x.1).residue (j+1)).toNat =
      ((mul (natScalar 2) y.1).residue (j+1)).toNat at e
    rw [double_residue, double_residue] at e
    apply BitVec.eq_of_toNat_eq
    omega
  · have e := congrArg Prod.snd h
    exact e

/-- Translation by the sublattice 2^(a+1)Y, expressed in ambient coordinates. -/
def sameCoset (a : Nat) (x y : Scalar × Scalar) : Prop :=
  ∃ v : Scalar × Scalar, let u := scaleVector (natScalar (2^(a+1))) v
    inAmbient x = (add (inAmbient y).1 u.1, add (inAmbient y).2 u.2)

/-- j indexes positive layers a=j+1. Each word represents its additive
cyclic group modulo the power of two given by its width. -/
def residuePair (j : Nat) (x : Scalar × Scalar) : BitVec (j+1) × BitVec (j+2) :=
  (x.1.residue j, x.2.residue (j+1))

theorem sameCoset_iff_residuePair (j : Nat) (x y : Scalar × Scalar) :
    sameCoset (j+1) x y ↔ residuePair j x = residuePair j y := by
  have hd : (mul (natScalar 2) x.1).residue (j+1) = (mul (natScalar 2) y.1).residue (j+1)
      ↔ x.1.residue j = y.1.residue j := by
    rw [← BitVec.toNat_inj, double_residue, double_residue, ← BitVec.toNat_inj]
    omega
  constructor
  · rintro ⟨v, hv⟩
    have e₁ := congrArg Prod.fst hv
    have e₂ := congrArg Prod.snd hv
    apply Prod.ext
    · exact hd.mp ((residue_eq_iff_multiple _ _ _).mpr ⟨v.1,e₁⟩)
    · exact (residue_eq_iff_multiple _ _ _).mpr ⟨v.2,e₂⟩
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    obtain ⟨u, hu⟩ := (residue_eq_iff_multiple _ _ _).mp (hd.mpr h₁)
    obtain ⟨v, hv⟩ := (residue_eq_iff_multiple _ _ _).mp h₂
    exact ⟨(u,v), Prod.ext hu hv⟩

/-- Every pair of finite residues has an explicit integral representative in X. -/
theorem residuePair_section (j : Nat) (p : BitVec (j+1) × BitVec (j+2)) :
    residuePair j (natScalar p.1.toNat, natScalar p.2.toNat) = p := by
  apply Prod.ext <;> simp [residuePair, natScalar]

/-- Addition in the X basis is componentwise. Reduction respects the
additive cyclic structures of the two target factors. -/
theorem residuePair_add (j : Nat) (x y : Scalar × Scalar) :
    residuePair j (add x.1 y.1, add x.2 y.2) =
      ((residuePair j x).1+(residuePair j y).1, (residuePair j x).2+(residuePair j y).2) := rfl

/-- The quotient itself is in bijection with the pair of residue groups. -/
theorem quotient_classification (j : Nat) :
    ∃ encode : Quot (sameCoset (j+1)) → BitVec (j+1) × BitVec (j+2),
    ∃ decode : BitVec (j+1) × BitVec (j+2) → Quot (sameCoset (j+1)),
      (∀ x, encode (Quot.mk _ x) = residuePair j x) ∧
      (∀ c, decode (encode c) = c) ∧ (∀ p, encode (decode p) = p) := by
  let encode := Quot.lift (residuePair j) (fun x y h => (sameCoset_iff_residuePair j x y).mp h)
  let decode := fun p : BitVec (j+1) × BitVec (j+2) =>
    Quot.mk (sameCoset (j+1)) (natScalar p.1.toNat, natScalar p.2.toNat)
  refine ⟨encode, decode, fun _ => rfl, ?_, residuePair_section j⟩
  intro c
  induction c using Quot.ind with
  | mk x =>
    apply Quot.sound
    exact (sameCoset_iff_residuePair j _ _).mpr (residuePair_section j (residuePair j x))

/-- Counting uses concatenation of the two residue words. For a=j+1
the quotient therefore has exactly 2^(2a+1) elements. -/
theorem quotient_cardinality (j : Nat) :
    ∃ encode : Quot (sameCoset (j+1)) → Fin (2^(2*(j+1)+1)),
    ∃ decode : Fin (2^(2*(j+1)+1)) → Quot (sameCoset (j+1)),
      (∀ c, decode (encode c) = c) ∧ (∀ i, encode (decode i) = i) := by
  rw [show 2*(j+1)+1 = (j+1)+(j+2) by omega]
  obtain ⟨f, g, _, left, right⟩ := quotient_classification j
  let pack := fun p : BitVec (j+1) × BitVec (j+2) => (p.1 ++ p.2).toFin
  let unpack := fun i : Fin (2^((j+1)+(j+2))) =>
    ((BitVec.ofFin i).extractLsb' (j+2) (j+1), (BitVec.ofFin i).extractLsb' 0 (j+2))
  refine ⟨fun c => pack (f c), fun i => g (unpack i), ?_, ?_⟩
  · intro c
    simp only [pack, unpack, BitVec.ofFin_toFin, BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right, left]
  · intro i
    change pack (f (g (unpack i))) = i
    rw [right]
    simp only [pack, unpack, BitVec.extractLsb'_append_extractLsb', BitVec.toFin_ofFin]

end Reimann.DyadicQuotient
