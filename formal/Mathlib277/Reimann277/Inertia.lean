import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Reimann.TameUnramified277

namespace Reimann.TameInertia277

variable {K L : Type} [Field K] [Field L] [Algebra K L]

abbrev Integers (L : Type*) [Field L] := integralClosure ℤ L

theorem integral_of_power_root (n : ℕ) {x : L} (hx : x ^ (277^(n+1)) = 1) : IsIntegral ℤ x := by
  apply IsIntegral.of_pow (n := 277^(n+1)) (pow_pos (by decide : 0 < (277 : ℕ)) _)
  rw [hx]
  exact isIntegral_one

/-- Every field automorphism preserves the monic-integral elements. -/
def act (g : L ≃ₐ[K] L) (x : Integers L) : Integers L :=
  ⟨g x.val, map_isIntegral_int g x.property⟩

theorem act_one (x : Integers L) : act (1 : L ≃ₐ[K] L) x = x := rfl

theorem act_mul (g h : L ≃ₐ[K] L) (x : Integers L) :
    act (g*h) x = act g (act h x) := rfl

theorem act_inv (g : L ≃ₐ[K] L) (x : Integers L) : act g (act g⁻¹ x) = x := by
  apply Subtype.ext
  exact g.apply_symm_apply x.val

theorem act_inv_left (g : L ≃ₐ[K] L) (x : Integers L) : act g⁻¹ (act g x) = x :=
  Subtype.ext (g.symm_apply_apply x.val)

def integralEquiv (g : L ≃ₐ[K] L) : Integers L ≃+* Integers L where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_left g
  right_inv := act_inv g
  map_add' x y := Subtype.ext (g.map_add x.val y.val)
  map_mul' x y := Subtype.ext (g.map_mul x.val y.val)

def conjugateIdeal (g : L ≃ₐ[K] L) (P : Ideal (Integers L)) : Ideal (Integers L) :=
  P.comap (integralEquiv g⁻¹).toRingHom

abbrev integralMulAction : MulAction (L ≃ₐ[K] L) (Integers L) where
  smul := act
  one_smul := act_one
  mul_smul := act_mul

/-- The inertia subgroup acts trivially on residues at the specified ideal.
For a maximal ideal of the absolute integral closure this is the usual
inertia condition on algebraic integers. -/
def inertia (P : Ideal (Integers L)) : Subgroup (L ≃ₐ[K] L) where
  carrier := {g | ∀ x : Integers L, act g x - x ∈ P}
  one_mem' := by intro x; rw [act_one,sub_self]; exact P.zero_mem
  mul_mem' := by
    intro g h hg hh x
    rw [act_mul, ← sub_add_sub_cancel (act g (act h x)) (act h x) x]
    exact P.add_mem (hg (act h x)) (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (act g⁻¹ x)
    rw [act_inv] at h
    simpa only [neg_sub] using P.neg_mem h

theorem inertia_eq_mathlib (P : Ideal (Integers L)) :
    letI := integralMulAction (K := K) (L := L)
    inertia P = P.toAddSubgroup.inertia (L ≃ₐ[K] L) := by
  letI := integralMulAction (K := K) (L := L)
  ext g
  rfl

theorem inertia_iff_residue (P : Ideal (Integers L)) (g : L ≃ₐ[K] L) :
    g ∈ inertia P ↔ ∀ x, Ideal.Quotient.mk P (act g x) = Ideal.Quotient.mk P x := by
  change (∀ x, act g x - x ∈ P) ↔ _
  exact forall_congr' (fun x => Ideal.Quotient.eq.symm)

theorem same_residue_iff (P : Ideal (Integers L)) (g h : L ≃ₐ[K] L) :
    g*h⁻¹ ∈ inertia P ↔ ∀ x, Ideal.Quotient.mk P (act g x) = Ideal.Quotient.mk P (act h x) := by
  rw [inertia_iff_residue]
  constructor
  · intro hs x
    simpa only [act_mul, act_inv_left] using hs (act h x)
  · intro hs x
    rw [act_mul]
    simpa only [act_inv] using hs (act h⁻¹ x)

/-- For a prime of the base with residue cardinality q, this is the defining
arithmetic Frobenius congruence at a prime P over it. -/
def FrobeniusResidue (P : Ideal (Integers L)) (q : ℕ) (g : L ≃ₐ[K] L) : Prop :=
  ∀ x : Integers L, Ideal.Quotient.mk P (act g x) = (Ideal.Quotient.mk P x)^q

theorem frobenius_iff (P : Ideal (Integers L)) (q : ℕ) (h : L ≃ₐ[K] L) :
    FrobeniusResidue P q h ↔ ∀ x, act h x - x^q ∈ P := by
  unfold FrobeniusResidue
  simp only [← map_pow, Ideal.Quotient.eq]

theorem frobenius_preserves_ideal (P : Ideal (Integers L)) (hP : P.IsPrime) (q : ℕ)
    (hq : 0 < q) (g : L ≃ₐ[K] L) (hg : FrobeniusResidue P q g) (x : Integers L) :
    act g x ∈ P ↔ x ∈ P := by
  calc
    act g x ∈ P ↔ Ideal.Quotient.mk P (act g x) = 0 := Ideal.Quotient.eq_zero_iff_mem.symm
    _ ↔ Ideal.Quotient.mk P (x^q) = 0 := by rw [hg x, map_pow]
    _ ↔ x^q ∈ P := Ideal.Quotient.eq_zero_iff_mem
    _ ↔ x ∈ P := hP.pow_mem_iff_mem q hq

theorem frobenius_conjugate (P : Ideal (Integers L)) (q : ℕ) (g h : L ≃ₐ[K] L)
    (hh : FrobeniusResidue P q h) : FrobeniusResidue (conjugateIdeal g P) q (g*h*g⁻¹) := by
  apply (frobenius_iff _ _ _).mpr
  intro x
  change integralEquiv g⁻¹ (act (g*h*g⁻¹) x - x^q) ∈ P
  rw [map_sub, map_pow]
  change act g⁻¹ (act (g*h*g⁻¹) x) - (act g⁻¹ x)^q ∈ P
  rw [act_mul,act_mul,act_inv_left]
  exact (frobenius_iff _ _ _).mp hh _

theorem frobenius_lifts_equal {H : Type*} [Group H] (N : Subgroup (L ≃ₐ[K] L))
    (χ : N →* H) (P : Ideal (Integers L)) (q : ℕ)
    (unramified : ∀ z : N, z.val ∈ inertia P → χ z = 1)
    (u v : N) (hu : FrobeniusResidue P q u.val) (hv : FrobeniusResidue P q v.val) : χ u = χ v := by
  have hdiff := (same_residue_iff P u.val v.val).mpr (fun x => (hu x).trans (hv x).symm)
  have hone := unramified (u*v⁻¹) hdiff
  simpa only [map_mul, map_inv, mul_inv_eq_one] using hone

theorem inertia_preserves_ideal (P : Ideal (Integers L)) {g : L ≃ₐ[K] L}
    (hg : g ∈ inertia P) (x : Integers L) : act g x ∈ P ↔ x ∈ P := by
  have hr := hg x
  constructor
  · intro h
    have v := P.sub_mem h hr
    simpa only [sub_sub_cancel] using v
  · intro h
    have v := P.add_mem hr h
    simpa only [sub_add_cancel] using v

/-- All finite-prime inertia elements away from 277. A maximal ideal occurs
once for each prolongation to L, so all conjugates are included. -/
def away (N : Subgroup (L ≃ₐ[K] L)) : Set N :=
  {g | ∃ P : Ideal (Integers L), P.IsMaximal ∧ (277 : Integers L) ∉ P ∧ g.val ∈ inertia P}

theorem away_iff (N : Subgroup (L ≃ₐ[K] L)) (g : N) :
    g ∈ away N ↔ ∃ P : Ideal (Integers L), P.IsMaximal ∧ (277 : Integers L) ∉ P ∧
      ∀ x, Ideal.Quotient.mk P (act g.val x) = Ideal.Quotient.mk P x := by
  simp only [away, Set.mem_ofPred_eq, inertia_iff_residue]

def residueMap (P : Ideal (Integers L)) :
    TameUnramified277.Reduction (Integers L) (Integers L ⧸ P) where
  app := Ideal.Quotient.mk P
  zero := map_zero _
  one := map_one _
  add := map_add _
  mul := map_mul _

def integralAction (g : L ≃ₐ[K] L) : TameUnramified277.Reduction (Integers L) (Integers L) where
  app := act g
  zero := Subtype.ext (g.map_zero)
  one := Subtype.ext (g.map_one)
  add x y := Subtype.ext (g.map_add x.val y.val)
  mul x y := Subtype.ext (g.map_mul x.val y.val)

theorem survives (P : Ideal (Integers L)) (hP : P.IsMaximal) (hp : (277 : Integers L) ∉ P)
    (n : ℕ) : ((277^(n+1) : ℕ) : Integers L ⧸ P) ≠ 0 := by
  letI := hP
  have h : (277 : Integers L ⧸ P) ≠ 0 := by
    intro h0
    apply hp
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    simpa only [map_ofNat] using h0
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using pow_ne_zero (n+1) h

/-- Inertia away from 277 fixes all 277-power roots in the algebraic closure.
The argument uses the divided difference at two roots with the same residue. -/
theorem fixes_power_root (P : Ideal (Integers L)) (hP : P.IsMaximal)
    (hp : (277 : Integers L) ∉ P) {g : L ≃ₐ[K] L} (hg : g ∈ inertia P)
    (n : ℕ) {x : L} (hx : x ^ (277^(n+1)) = 1) : g x = x := by
  let a : Integers L := ⟨x,integral_of_power_root n hx⟩
  have ha : a^(277^(n+1)) = 1 := Subtype.ext hx
  have h := TameUnramified277.inertia_fixes (residueMap P) (integralAction g)
    (fun _ _ => mul_eq_zero.mp) _ (survives P hP hp n)
    ((inertia_iff_residue P g).mp hg) a ha
  exact congrArg Subtype.val h

end Reimann.TameInertia277
