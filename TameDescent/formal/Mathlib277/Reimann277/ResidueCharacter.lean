import Mathlib.Data.ZMod.Basic
import Reimann.TameRestriction

namespace Reimann.TameResidueCharacter277

open TameRestriction

variable {m : ℕ} [NeZero m] {G : Type} {P : Transfer.GroupLaw G} {t : G}

/-- The canonical integer representative of a finite coefficient. -/
def representative (z : ZMod m) : ℤ := z.val

theorem cast_representative (z : ZMod m) : (representative z : ZMod m) = z := by
  rw [representative, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem difference_iff (a b : ℤ) : (m : ℤ) ∣ a-b ↔ (a : ZMod m) = (b : ZMod m) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]

theorem representative_add (x y : ZMod m) :
    (m : ℤ) ∣ representative (x+y) - (representative x + representative y) := by
  rw [difference_iff, Int.cast_add, cast_representative, cast_representative, cast_representative]

theorem representative_scale (a : ℤ) (x : ZMod m) :
    (m : ℤ) ∣ representative ((a : ZMod m)*x) - a * representative x := by
  rw [difference_iff, Int.cast_mul, cast_representative, cast_representative]

variable (T : TameData P t (m : ℤ))

/-- Residue-valued kernel character with the conjugation convention used by the twist. -/
structure ResidueCharacter where
  value : Subtype T.kernel → ZMod m
  additive : ∀ {x y} (hx : T.kernel x) (hy : T.kernel y),
    value ⟨P.add x y,T.mul_in hx hy⟩ = value ⟨x,hx⟩ + value ⟨y,hy⟩
  equivariant : ∀ g {x} (hx : T.kernel x),
    value ⟨conjugate P g x,T.conj_in g hx⟩ = (T.scalar g : ZMod m) * value ⟨x,hx⟩

variable {T}

def realize (F : ResidueCharacter T) : KernelCharacter T where
  value x := representative (F.value x)
  additive hx hy := by rw [F.additive hx hy]; exact representative_add _ _
  equivariant g {x} hx := by rw [F.equivariant g hx]; exact representative_scale _ _

theorem extend_crossed_residue (F : ResidueCharacter T) : Crossed T (extend (realize F)) :=
  extend_crossed (realize F)

theorem extend_at_kernel (F : ResidueCharacter T) (x : Subtype T.kernel) :
    (extend (realize F) x.val : ZMod m) = F.value x :=
  ((difference_iff _ _).mp (extend_restrict (realize F) x.property)).trans (cast_representative _)

theorem extend_formula (F : ResidueCharacter T) (g : G) :
    (extend (realize F) g : ZMod m) = (T.inverse : ZMod m) *
      F.value ⟨commutator P t g, T.comm_in g⟩ := by
  change ((T.inverse * representative _ : ℤ) : ZMod m) = _
  rw [Int.cast_mul, cast_representative]

theorem restrictions_equal_iff_principal {c d : G → ℤ} (hc : Crossed T c) (hd : Crossed T d) :
    (∀ x : Subtype T.kernel, (c x.val : ZMod m) = (d x.val : ZMod m)) ↔
      ∃ b : ℤ, ∀ g, (m : ℤ) ∣ c g-d g-(T.scalar g-1)*b := by
  rw [← fibres_iff hc hd]
  exact ⟨fun h g hg => (difference_iff _ _).mpr (h ⟨g,hg⟩),
    fun h x => (difference_iff _ _).mp (h x.val x.property)⟩

end Reimann.TameResidueCharacter277
