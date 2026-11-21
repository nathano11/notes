import Std

namespace ReimannWindow.LatticeQuotient

/-! In lattice coordinates `(x,y)` the inclusion into the ambient integer
lattice sends `(x,y)` to `(2*x,y)`. Its quotient here uses congruence
modulo `2*m` in both ambient coordinates. -/

abbrev Point := Int × Int

def ambientCongruent (m : Nat) (p q : Point) : Prop :=
  (2 * p.1) % (2 * (m : Int)) = (2 * q.1) % (2 * (m : Int)) ∧
  p.2 % (2 * (m : Int)) = q.2 % (2 * (m : Int))

theorem ambient_congruence_iff (m : Nat) (p q : Point) :
    ambientCongruent m p q ↔
      p.1 % (m : Int) = q.1 % (m : Int) ∧
      p.2 % ((2*m : Nat) : Int) = q.2 % ((2*m : Nat) : Int) := by
  unfold ambientCongruent
  simp only [Int.natCast_mul, Int.mul_emod_mul_of_pos _ _ (by decide : (0 : Int) < 2)]
  change (2 * (p.1 % (m : Int)) = 2 * (q.1 % (m : Int)) ∧ _) ↔
    (p.1 % (m : Int) = q.1 % (m : Int) ∧
      p.2 % (2 * (m : Int)) = q.2 % (2 * (m : Int)))
  omega
-- breakpoint ambient_congruence_iff

def residue (m : Nat) (hm : 0 < m) (z : Int) : Fin m :=
  ⟨(z % (m : Int)).toNat, (Int.toNat_lt' hm).2 (Int.emod_lt_of_pos z (by omega))⟩

theorem residue_eq_iff (m : Nat) (hm : 0 < m) (x y : Int) :
    residue m hm x = residue m hm y ↔ x % (m : Int) = y % (m : Int) := by
  rw [Fin.ext_iff]
  change (x % (m : Int)).toNat = (y % (m : Int)).toNat ↔ _
  have hx := Int.emod_nonneg x (by omega : (m : Int) ≠ 0)
  have hy := Int.emod_nonneg y (by omega : (m : Int) ≠ 0)
  omega
-- breakpoint residue_eq_iff

theorem residue_of_representative (m : Nat) (hm : 0 < m) (x : Fin m) :
    residue m hm (x.val : Int) = x := by
  apply Fin.ext
  change ((x.val : Int) % (m : Int)).toNat = x.val
  rw [Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)]
  rfl
-- breakpoint residue_of_representative

theorem residue_add (m : Nat) (hm : 0 < m) (x y : Int) :
    residue m hm (x + y) = residue m hm x + residue m hm y := by
  apply Fin.ext
  rw [Fin.val_add]
  change ((x + y) % (m : Int)).toNat =
    ((x % (m : Int)).toNat + (y % (m : Int)).toNat) % m
  have hx := Int.emod_nonneg x (by omega : (m : Int) ≠ 0)
  have hy := Int.emod_nonneg y (by omega : (m : Int) ≠ 0)
  rw [Int.add_emod, Int.toNat_emod (by omega) (by omega), Int.toNat_add hx hy]
  rfl
-- breakpoint residue_add

abbrev ResiduePair (m : Nat) := Fin m × Fin (2*m)

def coordinates (m : Nat) (hm : 0 < m) (p : Point) : ResiduePair m :=
  (residue m hm p.1, residue (2*m) (by omega) p.2)

theorem coordinates_eq_iff (m : Nat) (hm : 0 < m) (p q : Point) :
    coordinates m hm p = coordinates m hm q ↔ ambientCongruent m p q := by
  rw [ambient_congruence_iff, Prod.ext_iff]
  exact and_congr (residue_eq_iff m hm _ _) (residue_eq_iff (2*m) (by omega) _ _)
-- breakpoint coordinates_eq_iff

def representative {m : Nat} (z : ResiduePair m) : Point :=
  ((z.1.val : Int), (z.2.val : Int))

theorem coordinates_representative (m : Nat) (hm : 0 < m) (z : ResiduePair m) :
    coordinates m hm (representative z) = z := by
  apply Prod.ext
  · exact residue_of_representative m hm z.1
  · exact residue_of_representative (2*m) (by omega) z.2
-- breakpoint coordinates_representative

def latticeSetoid (m : Nat) : Setoid Point where
  r := ambientCongruent m
  iseqv := ⟨fun _ => ⟨rfl, rfl⟩,
    fun h => ⟨h.1.symm, h.2.symm⟩, fun h k => ⟨h.1.trans k.1, h.2.trans k.2⟩⟩

abbrev LatticeQuotient (m : Nat) := Quotient (latticeSetoid m)

def toResidues (m : Nat) (hm : 0 < m) : LatticeQuotient m → ResiduePair m :=
  Quotient.lift (coordinates m hm) (fun p q h => (coordinates_eq_iff m hm p q).2 h)

def fromResidues (m : Nat) (z : ResiduePair m) : LatticeQuotient m :=
  Quotient.mk (latticeSetoid m) (representative z)

theorem toResidues_fromResidues (m : Nat) (hm : 0 < m) (z : ResiduePair m) :
    toResidues m hm (fromResidues m z) = z :=
  coordinates_representative m hm z
-- breakpoint toResidues_fromResidues

theorem fromResidues_toResidues (m : Nat) (hm : 0 < m) (v : LatticeQuotient m) :
    fromResidues m (toResidues m hm v) = v := by
  induction v using Quotient.inductionOn with
  | _ p =>
    apply Quotient.sound
    exact (coordinates_eq_iff m hm _ p).1 (coordinates_representative m hm _)
-- breakpoint fromResidues_toResidues

def addPoint (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)

def addResidues {m : Nat} (z w : ResiduePair m) : ResiduePair m :=
  (z.1 + w.1, z.2 + w.2)

theorem coordinates_add (m : Nat) (hm : 0 < m) (p q : Point) :
    coordinates m hm (addPoint p q) =
      addResidues (coordinates m hm p) (coordinates m hm q) := by
  apply Prod.ext
  · exact residue_add m hm p.1 q.1
  · exact residue_add (2*m) (by omega) p.2 q.2
-- breakpoint coordinates_add

def addClasses (m : Nat) (hm : 0 < m) (v w : LatticeQuotient m) : LatticeQuotient m :=
  Quotient.liftOn₂ v w (fun p q => Quotient.mk (latticeSetoid m) (addPoint p q))
    (fun p q p' q' hp hq => Quotient.sound <|
      (coordinates_eq_iff m hm _ _).1 <| by
        rw [coordinates_add, coordinates_add, (coordinates_eq_iff m hm _ _).2 hp,
          (coordinates_eq_iff m hm _ _).2 hq])

theorem toResidues_add (m : Nat) (hm : 0 < m) (v w : LatticeQuotient m) :
    toResidues m hm (addClasses m hm v w) =
      addResidues (toResidues m hm v) (toResidues m hm w) := by
  induction v using Quotient.inductionOn with
  | _ p =>
    induction w using Quotient.inductionOn with
    | _ q => exact coordinates_add m hm p q
-- breakpoint toResidues_add

def classCount (m : Nat) := m * (2*m)

/-- Number the residue pairs by rows. This encoding is used only for counting. -/
def pack {m : Nat} (z : ResiduePair m) : Fin (classCount m) :=
  ⟨z.2.val + z.1.val * (2*m), by
    have h := Nat.mul_le_mul_right (2*m) z.1.isLt
    rw [Nat.succ_mul] at h
    have hy := z.2.isLt
    unfold classCount
    omega⟩

def unpack (m : Nat) (hm : 0 < m) (k : Fin (classCount m)) : ResiduePair m :=
  (⟨k.val / (2*m), (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*m)).2 k.isLt⟩,
   ⟨k.val % (2*m), Nat.mod_lt _ (by omega)⟩)

theorem unpack_pack (m : Nat) (hm : 0 < m) (z : ResiduePair m) :
    unpack m hm (pack z) = z := by
  apply Prod.ext
  · apply Fin.ext
    change (z.2.val + z.1.val * (2*m)) / (2*m) = z.1.val
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt z.2.isLt, Nat.zero_add]
  · apply Fin.ext
    change (z.2.val + z.1.val * (2*m)) % (2*m) = z.2.val
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt z.2.isLt]
-- breakpoint unpack_pack

theorem pack_unpack (m : Nat) (hm : 0 < m) (k : Fin (classCount m)) :
    pack (unpack m hm k) = k := by
  apply Fin.ext
  change k.val % (2*m) + (k.val / (2*m)) * (2*m) = k.val
  rw [Nat.mul_comm (k.val / (2*m)), Nat.mod_add_div]
-- breakpoint pack_unpack

def classIndex (m : Nat) (hm : 0 < m) (v : LatticeQuotient m) : Fin (classCount m) :=
  pack (toResidues m hm v)

def classAt (m : Nat) (hm : 0 < m) (j : Fin (classCount m)) : LatticeQuotient m :=
  fromResidues m (unpack m hm j)

/-- A two-sided counting bijection from the actual quotient onto a finite interval. -/
theorem quotient_count (m : Nat) (hm : 0 < m) :
    (∀ v, classAt m hm (classIndex m hm v) = v) ∧
    (∀ j, classIndex m hm (classAt m hm j) = j) := by
  constructor
  · intro v
    unfold classAt classIndex
    rw [unpack_pack, fromResidues_toResidues]
  · intro j
    unfold classAt classIndex
    rw [toResidues_fromResidues, pack_unpack]
-- breakpoint quotient_count

theorem dyadic_class_count (a : Nat) : classCount (2^a) = 2^(2*a + 1) := by
  unfold classCount
  rw [Nat.pow_succ, Nat.two_mul a, Nat.pow_add]
  rw [Nat.mul_comm 2 (2^a), Nat.mul_assoc]
-- breakpoint dyadic_class_count

theorem first_dyadic_class_counts :
    [0, 1, 2, 3, 4].map (fun a => classCount (2^a)) = [2, 8, 32, 128, 512] := by
  decide
-- breakpoint first_dyadic_class_counts

end ReimannWindow.LatticeQuotient
