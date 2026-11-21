import Reimann.DyadicArtinImage69
import Reimann.DyadicQuotient

/-! Normal coordinates for Mizusawa's presentation at (3,23).
Write elements A^u Z^w B^v with Z=A⁻¹C. The exponent v acts on u
by its sign, and Z is central. -/
namespace Reimann.DyadicMizusawaCoordinates69

open Reimann.Transfer Reimann.TameRestriction Reimann.DyadicLattice
open Reimann.DyadicArtinCommutator69 Reimann.DyadicArtinImage69

def scalarLaw : GroupLaw Scalar where
  zero := natScalar 0
  add := add
  neg := neg
  assoc x y z := by apply scalar_ext; intro n; exact BitVec.add_assoc _ _ _
  zero_add x := by apply scalar_ext; intro n; exact BitVec.zero_add _
  add_zero x := by apply scalar_ext; intro n; exact BitVec.add_zero _
  add_neg x := by apply scalar_ext; intro n; change x.residue n + -(x.residue n) = 0; grind
  neg_add x := by apply scalar_ext; intro n; change -(x.residue n) + x.residue n = 0; grind

def signBit (p : BitVec 1) (x : Scalar) : Scalar := if p=0 then x else neg x

theorem signBit_add (p : BitVec 1) (x y : Scalar) :
    signBit p (add x y) = add (signBit p x) (signBit p y) := by
  by_cases h : p=0
  · simp [signBit,h]
  · simp only [signBit,h,ite_false]
    apply scalar_ext
    intro n
    change -(x.residue n + y.residue n) = -(x.residue n) + -(y.residue n)
    grind

theorem signBit_comp (p q : BitVec 1) (x : Scalar) :
    signBit (p+q) x = signBit p (signBit q x) := by
  have bits : ∀ b : BitVec 1, b=0 ∨ b=1 := by decide
  rcases bits p with rfl|rfl <;> rcases bits q with rfl|rfl <;> try rfl
  apply scalar_ext
  intro n
  change x.residue n = - -(x.residue n)
  grind

@[ext]
structure Point where
  a : Scalar
  b : Scalar
  z : Scalar

def product (g h : Point) : Point :=
  ⟨add g.a (signBit (g.b.residue 0) h.a), add g.b h.b, add g.z h.z⟩

def reciprocal (g : Point) : Point :=
  ⟨signBit (g.b.residue 0) (neg g.a), neg g.b, neg g.z⟩

theorem product_assoc (g h k : Point) : product (product g h) k = product g (product h k) := by
  apply Point.ext
  · change add (add _ _) (signBit (g.b.residue 0 + h.b.residue 0) k.a) =
      add _ (signBit _ (add _ _))
    rw [signBit_add, signBit_comp]
    exact scalarLaw.assoc _ _ _
  · exact scalarLaw.assoc _ _ _
  · exact scalarLaw.assoc _ _ _

def origin : Point := ⟨scalarLaw.zero,scalarLaw.zero,scalarLaw.zero⟩

theorem signBit_zero (p : BitVec 1) : signBit p scalarLaw.zero=scalarLaw.zero := by
  by_cases h : p=0
  · simp [signBit,h]
  · apply scalar_ext; intro n; simp [signBit,scalarLaw,neg,natScalar]

def pointLaw : GroupLaw Point where
  zero := origin
  add := product
  neg := reciprocal
  assoc := product_assoc
  zero_add g := by
    apply Point.ext <;> exact scalarLaw.zero_add _
  add_zero g := by
    apply Point.ext
    · change add g.a (signBit _ scalarLaw.zero)=_
      rw [signBit_zero]
      exact scalarLaw.add_zero _
    · exact scalarLaw.add_zero _
    · exact scalarLaw.add_zero _
  add_neg g := by
    apply Point.ext
    · change add g.a (signBit _ (signBit _ (neg g.a))) = _
      rw [←signBit_comp,show g.b.residue 0+g.b.residue 0=0 from (by decide : ∀ s : BitVec 1, s+s=0) _]
      exact scalarLaw.add_neg _
    · exact scalarLaw.add_neg _
    · exact scalarLaw.add_neg _
  neg_add g := by
    apply Point.ext
    · change add (signBit (g.b.residue 0) (neg g.a)) (signBit (-g.b.residue 0) g.a)=_
      rw [show -g.b.residue 0=g.b.residue 0 from (by decide : ∀ s : BitVec 1, -s=s) _,←signBit_add]
      rw [show add (neg g.a) g.a=scalarLaw.zero from scalarLaw.neg_add _,signBit_zero]
      rfl
    · exact scalarLaw.neg_add _
    · exact scalarLaw.neg_add _

def axisA (u : Scalar) : Point := ⟨u,scalarLaw.zero,scalarLaw.zero⟩

def axisB (v : Scalar) : Point := ⟨scalarLaw.zero,v,scalarLaw.zero⟩

def axisC (w : Scalar) : Point := ⟨w,scalarLaw.zero,w⟩

/-- The paper's bracket is x⁻¹y⁻¹xy. The three words are evaluated in
the nonabelian model at all precisions. -/
theorem paper_relations :
    let A := axisA (natScalar 1)
    let B := axisB (natScalar 1)
    let C := axisC (natScalar 1)
    let bracket := fun (x y : Point) => product (product (product (reciprocal x) (reciprocal y)) x) y
    bracket A B = axisA (neg (natScalar 2)) ∧ bracket B C = axisA (natScalar 2) ∧
    bracket A C = origin := by
  dsimp only
  refine ⟨?_,?_,?_⟩ <;> apply Point.ext <;> apply scalar_ext <;> intro n <;>
    simp [axisA,axisB,axisC,origin,product,reciprocal,signBit,scalarLaw,add,neg,natScalar] <;> grind

def planeLaw : GroupLaw (Scalar × Scalar) where
  zero := (scalarLaw.zero,scalarLaw.zero)
  add x y := (add x.1 y.1,add x.2 y.2)
  neg x := (neg x.1,neg x.2)
  assoc _ _ _ := Prod.ext (scalarLaw.assoc _ _ _) (scalarLaw.assoc _ _ _)
  zero_add _ := Prod.ext (scalarLaw.zero_add _) (scalarLaw.zero_add _)
  add_zero _ := Prod.ext (scalarLaw.add_zero _) (scalarLaw.add_zero _)
  add_neg _ := Prod.ext (scalarLaw.add_neg _) (scalarLaw.add_neg _)
  neg_add _ := Prod.ext (scalarLaw.neg_add _) (scalarLaw.neg_add _)

def plane : Hom pointLaw planeLaw where
  app g := (g.b,g.z)
  preserves_zero := rfl
  preserves_add _ _ := rfl
  preserves_neg _ := rfl

/-- Kernel of the two free abelian coordinates. The identification of the
dyadic stabilizer with this axis is treated by its finite Frobenius images. -/
def decomposition := DyadicPlaceProduct.kernel plane

theorem decomposition_is_A (g : Point) :
    decomposition.mem g ↔ ∃ u, g=axisA u := by
  change (g.b,g.z)=(scalarLaw.zero,scalarLaw.zero) ↔ _
  constructor
  · intro h
    exact ⟨g.a,Point.ext rfl (congrArg Prod.fst h) (congrArg Prod.snd h)⟩
  · rintro ⟨u,rfl⟩; rfl

theorem decomposition_normal : Normal decomposition := fun g a =>
  DyadicPlaceProduct.kernel_normal plane g a.val a.property

def genusLaw : GroupLaw (BitVec 1 × BitVec 1) where
  zero := (0,0)
  add x y := (x.1+y.1,x.2+y.2)
  neg x := (-x.1,-x.2)
  assoc _ _ _ := Prod.ext (BitVec.add_assoc _ _ _) (BitVec.add_assoc _ _ _)
  zero_add _ := Prod.ext (BitVec.zero_add _) (BitVec.zero_add _)
  add_zero _ := Prod.ext (BitVec.add_zero _) (BitVec.add_zero _)
  add_neg p := Prod.ext ((by decide : ∀ s : BitVec 1, s + -s=0) p.1) ((by decide : ∀ s : BitVec 1, s + -s=0) p.2)
  neg_add p := Prod.ext ((by decide : ∀ s : BitVec 1, -s + s=0) p.1) ((by decide : ∀ s : BitVec 1, -s + s=0) p.2)

theorem signBit_parity (p : BitVec 1) (x : Scalar) : (signBit p x).residue 0=x.residue 0 := by
  by_cases h : p=0
  · simp [signBit,h]
  · simp only [signBit,h,ite_false,neg]
    exact (by decide : ∀ s : BitVec 1, -s=s) _

def genus : Hom pointLaw genusLaw where
  app g := (g.a.residue 0+g.z.residue 0,g.b.residue 0)
  preserves_zero := rfl
  preserves_add g h := by
    apply Prod.ext
    · change (g.a.residue 0+(signBit _ h.a).residue 0)+(g.z.residue 0+h.z.residue 0) = _
      rw [signBit_parity]
      change _ = (g.a.residue 0+g.z.residue 0)+(h.a.residue 0+h.z.residue 0)
      exact (by decide : ∀ a b c d : BitVec 1, (a+b)+(c+d)=(a+c)+(b+d)) _ _ _ _
    · rfl
  preserves_neg g := by
    apply Prod.ext
    · change (signBit _ (neg g.a)).residue 0 + -g.z.residue 0 = -(g.a.residue 0+g.z.residue 0)
      rw [signBit_parity]
      change -g.a.residue 0 + -g.z.residue 0 = _
      exact (by decide : ∀ a b : BitVec 1, -a + -b = -(a+b)) _ _
    · rfl

theorem genus_on_generators :
    genus.app (axisA (natScalar 1))=(1,0) ∧ genus.app (axisB (natScalar 1))=(0,1) ∧
    genus.app (axisC (natScalar 1))=(0,0) := by decide

theorem even_iff_double (v : Scalar) :
    v.residue 0=0 ↔ ∃ u, v=mul (natScalar 2) u := by
  have h := DyadicQuotient.residue_eq_iff_multiple 0 v scalarLaw.zero
  change v.residue 0=0 ↔ ∃ u, v=scalarLaw.add scalarLaw.zero (mul (natScalar 2) u) at h
  simpa only [scalarLaw.zero_add] using h

theorem intersection_is_A_squared (g : Point) :
    (DyadicPlaceProduct.kernel genus).mem g ∧ decomposition.mem g ↔
      ∃ u, g=axisA (mul (natScalar 2) u) := by
  constructor
  · rintro ⟨hh,hd⟩
    obtain ⟨v,rfl⟩ := (decomposition_is_A g).mp hd
    have h := congrArg Prod.fst hh
    change v.residue 0+0=0 at h
    obtain ⟨u,hu⟩ := (even_iff_double v).mp ((by decide : ∀ s : BitVec 1, s+0=0 → s=0) _ h)
    exact ⟨u,congrArg axisA hu⟩
  · rintro ⟨u,rfl⟩
    have h := (even_iff_double _).mpr ⟨u,rfl⟩
    refine ⟨?_,(decomposition_is_A _).mpr ⟨_,rfl⟩⟩
    change ((mul _ u).residue 0+0, (0:BitVec 1))=(0,0)
    rw [h]; rfl

/-- The image of the genus kernel in the free split plane is the actual
DyadicQuotient.inAmbient lattice (2b,c) at every precision. -/
theorem split_image (y : Scalar × Scalar) :
    (∃ h : Subtype (DyadicPlaceProduct.kernel genus).mem, plane.app h.val=y) ↔
      ∃ x, DyadicQuotient.inAmbient x=y := by
  constructor
  · rintro ⟨⟨h,hh⟩,rfl⟩
    have hb := congrArg Prod.snd hh
    change h.b.residue 0=0 at hb
    obtain ⟨u,hu⟩ := (even_iff_double h.b).mp hb
    exact ⟨(u,h.z),Prod.ext hu.symm rfl⟩
  · rintro ⟨⟨u,w⟩,rfl⟩
    let h : Point := ⟨w,mul (natScalar 2) u,w⟩
    refine ⟨⟨h,?_⟩,rfl⟩
    change (w.residue 0+w.residue 0,(mul _ u).residue 0)=(0,0)
    exact Prod.ext ((by decide : ∀ s : BitVec 1, s+s=0) _) ((even_iff_double _).mpr ⟨u,rfl⟩)

/-- Coordinates on G/D, as a quotient type. -/
def quotientCoordinates : Hom (targetLaw decomposition decomposition_normal) planeLaw :=
  descend decomposition decomposition_normal plane (fun a => a.property)

theorem quotient_coordinates_iso :
    Function.Injective quotientCoordinates.app ∧ Function.Surjective quotientCoordinates.app := by
  have fibers (g h : Point) (eq : plane.app g=plane.app h) : cls decomposition g=cls decomposition h := by
    apply Quotient.sound
    let k := pointLaw.add g (pointLaw.neg h)
    have hk : decomposition.mem k := by
      change plane.app (pointLaw.add g (pointLaw.neg h))=planeLaw.zero
      rw [plane.preserves_add,plane.preserves_neg,eq,planeLaw.add_neg]
    exact ⟨⟨k,hk⟩,(DyadicPlaceProduct.difference_times (P:=pointLaw) g h).symm⟩
  refine ⟨?_,fun y => ⟨cls decomposition ⟨scalarLaw.zero,y.1,y.2⟩,rfl⟩⟩
  intro u v
  induction u using Quotient.inductionOn with | _ g =>
    induction v using Quotient.inductionOn with | _ h =>
      exact fibers g h

theorem switching_class : quotientCoordinates.app (cls decomposition (axisB (natScalar 1))) =
      (natScalar 1,scalarLaw.zero) ∧
    ¬(imageSubgroup (DyadicPlaceProduct.kernel genus) decomposition decomposition_normal).mem
      (cls decomposition (axisB (natScalar 1))) := by
  refine ⟨rfl,?_⟩
  rintro ⟨h,e⟩
  have eq := congrArg quotientCoordinates.app e
  obtain ⟨x,hx⟩ := (split_image (plane.app (axisB (natScalar 1)))).mp ⟨h,eq⟩
  have bit := congrArg (fun y : Scalar × Scalar => y.1.residue 0) hx
  change 2*x.1.residue 0=(1:BitVec 1) at bit
  exact (by decide : ∀ s : BitVec 1, 2*s ≠ 1) _ bit

/-- Equality at the finite quotient of precision 2^(n+1). -/
def AtLevel (n : Nat) (x y : Point) : Prop :=
  x.a.residue n=y.a.residue n ∧ x.b.residue n=y.b.residue n ∧ x.z.residue n=y.z.residue n

/-- Finite words in commutators and their inverses. -/
inductive DerivedWord : Point → Prop
  | one : DerivedWord pointLaw.zero
  | comm (x y) : DerivedWord (TameRestriction.commutator pointLaw x y)
  | prod {x y} : DerivedWord x → DerivedWord y → DerivedWord (pointLaw.add x y)
  | inv {x} : DerivedWord x → DerivedWord (pointLaw.neg x)

theorem derived_plane_zero {x : Point} (hx : DerivedWord x) : decomposition.mem x := by
  induction hx with
  | one => exact decomposition.identity
  | prod _ _ ih jh => exact decomposition.product ih jh
  | inv _ ih => exact decomposition.inverse ih
  | comm x y =>
    change plane.app (TameRestriction.commutator pointLaw x y)=planeLaw.zero
    simp only [TameRestriction.commutator,plane.preserves_add,plane.preserves_neg]
    apply Prod.ext <;> apply scalar_ext <;> intro n <;>
      simp only [planeLaw,plane,scalarLaw,add,neg,natScalar] <;> grind

def ClosedDerived (g : Point) : Prop := ∀ n, ∃ h, DerivedWord h ∧ AtLevel n g h

theorem closed_derived_plane_zero {g : Point} (hg : ClosedDerived g) : decomposition.mem g := by
  change (g.b,g.z)=(scalarLaw.zero,scalarLaw.zero)
  apply Prod.ext <;> apply scalar_ext <;> intro n
  · obtain ⟨h,wh,_,eb,_⟩ := hg n
    have eq := congrArg Prod.fst (derived_plane_zero wh)
    change h.b=scalarLaw.zero at eq
    exact eb.trans (congrArg (fun s : Scalar => s.residue n) eq)
  · obtain ⟨h,wh,_,_,ez⟩ := hg n
    have eq := congrArg Prod.snd (derived_plane_zero wh)
    change h.z=scalarLaw.zero at eq
    exact ez.trans (congrArg (fun s : Scalar => s.residue n) eq)

theorem two_times (u : Scalar) : mul (natScalar 2) u=add u u := by
  apply scalar_ext
  intro n
  change 2*u.residue n=u.residue n+u.residue n
  grind

theorem square_zero_free (x : Scalar) (h : add x x=scalarLaw.zero) : x=scalarLaw.zero := by
  let p := (x,scalarLaw.zero)
  let q := (scalarLaw.zero,scalarLaw.zero)
  have eq : DyadicQuotient.inAmbient p=DyadicQuotient.inAmbient q := by
    apply Prod.ext
    · change mul (natScalar 2) x=mul (natScalar 2) scalarLaw.zero
      rw [two_times,two_times,h]
      exact (scalarLaw.add_zero _).symm
    · rfl
  exact congrArg Prod.fst (DyadicQuotient.inAmbient_injective eq)

/-- A nonzero genus Frobenius of order dividing two in the abelianization
has an odd A-exponent. The input requires no identification with A. -/
theorem frobenius_on_axis (F : Point) (square : ClosedDerived (pointLaw.add F F))
    (nontrivial : genus.app F≠genusLaw.zero) :
    ∃ u : Scalar, F=axisA u ∧ u.residue 0=1 := by
  have h := closed_derived_plane_zero square
  have hb := square_zero_free F.b (congrArg Prod.fst h)
  have hz := square_zero_free F.z (congrArg Prod.snd h)
  refine ⟨F.a,Point.ext rfl hb hz,?_⟩
  have ne : F.a.residue 0≠0 := by
    intro he
    apply nontrivial
    change (F.a.residue 0+F.z.residue 0,F.b.residue 0)=(0,0)
    rw [he,hb,hz]
    rfl
  exact (by decide : ∀ s : BitVec 1, s≠0 → s=1) _ ne

theorem axisA_add (x y : Scalar) : pointLaw.add (axisA x) (axisA y)=axisA (add x y) := by
  exact Point.ext rfl (scalarLaw.zero_add _) (scalarLaw.zero_add _)

theorem axisA_natural_power (u : Scalar) (k : Nat) :
    multiple pointLaw k (axisA u) = axisA (mul (natScalar k) u) := by
  induction k with
  | zero =>
    apply Point.ext
    · apply scalar_ext; intro n; change (0:BitVec (n+1))=0*u.residue n; simp
    · rfl
    · rfl
  | succ k ih =>
    rw [multiple,ih,axisA_add]
    apply congrArg axisA
    apply scalar_ext
    intro n
    change BitVec.ofNat _ k*u.residue n + u.residue n = BitVec.ofNat _ (k+1)*u.residue n
    rw [BitVec.ofNat_add]
    change _=(BitVec.ofNat _ k+1)*u.residue n
    grind

/-- Closure of the natural powers in the inverse-limit topology. -/
def Procyclic (F g : Point) : Prop :=
  ∀ n, ∃ k : Nat, AtLevel n g (multiple pointLaw k F)

theorem frobenius_generates_decomposition (F : Point) (square : ClosedDerived (pointLaw.add F F))
    (nontrivial : genus.app F≠genusLaw.zero) (g : Point) : Procyclic F g ↔ decomposition.mem g := by
  obtain ⟨u,rfl,odd⟩ := frobenius_on_axis F square nontrivial
  constructor
  · intro h
    change (g.b,g.z)=(scalarLaw.zero,scalarLaw.zero)
    apply Prod.ext <;> apply scalar_ext <;> intro n
    · obtain ⟨k,hk⟩ := h n
      rw [axisA_natural_power] at hk
      exact hk.2.1
    · obtain ⟨k,hk⟩ := h n
      rw [axisA_natural_power] at hk
      exact hk.2.2
  · intro hg
    obtain ⟨v,rfl⟩ := (decomposition_is_A g).mp hg
    obtain ⟨inv,hinv⟩ := odd_scalar_inverse u odd
    intro n
    let k := (v.residue n*inv.residue n).toNat
    refine ⟨k,?_⟩
    rw [axisA_natural_power]
    refine ⟨?_,rfl,rfl⟩
    change v.residue n=BitVec.ofNat (n+1) k * u.residue n
    have repr : BitVec.ofNat (n+1) k=v.residue n*inv.residue n := by
      apply BitVec.eq_of_toNat_eq
      exact Nat.mod_eq_of_lt (v.residue n*inv.residue n).isLt
    rw [repr,BitVec.mul_assoc,BitVec.mul_comm (inv.residue n),hinv]
    grind

def axisZ (w : Scalar) : Point := ⟨scalarLaw.zero,scalarLaw.zero,w⟩

theorem axisB_add (v w : Scalar) : pointLaw.add (axisB v) (axisB w)=axisB (add v w) :=
  Point.ext ((congrArg (add scalarLaw.zero) (signBit_zero _)).trans (scalarLaw.add_zero _)) rfl
    (scalarLaw.zero_add _)

theorem axisZ_add (v w : Scalar) : pointLaw.add (axisZ v) (axisZ w)=axisZ (add v w) :=
  Point.ext (scalarLaw.zero_add _) (scalarLaw.zero_add _) rfl

theorem normal_factorization (g : Point) :
    g = product (axisA g.a) (product (axisZ g.z) (axisB g.b)) := by
  apply Point.ext
  · change g.a=add g.a (add scalarLaw.zero scalarLaw.zero)
    rw [show add scalarLaw.zero scalarLaw.zero=scalarLaw.zero from scalarLaw.add_zero _]
    exact (scalarLaw.add_zero _).symm
  · change g.b=add scalarLaw.zero (add scalarLaw.zero g.b)
    rw [show add scalarLaw.zero g.b=g.b from scalarLaw.zero_add _]
    exact (scalarLaw.zero_add _).symm
  · change g.z=add scalarLaw.zero (add g.z scalarLaw.zero)
    rw [show add g.z scalarLaw.zero=g.z from scalarLaw.add_zero _]
    exact (scalarLaw.zero_add _).symm

theorem generator_C_decomposes (u : Scalar) :
    axisC u=product (axisA u) (axisZ u) :=
  Point.ext (scalarLaw.add_zero _).symm (scalarLaw.zero_add _).symm (scalarLaw.zero_add _).symm

/-- Maps from one dyadic axis to the genus group are forced by the
image of its generator since the target has exponent two. -/
theorem genus_hom_scalar (j : Scalar → Point) (hj0 : j scalarLaw.zero=origin)
    (hj : ∀ x y, j (add x y)=product (j x) (j y)) (f : Hom pointLaw genusLaw) (u : Scalar) :
    f.app (j u) = if u.residue 0=0 then genusLaw.zero else f.app (j (natScalar 1)) := by
  have h2 (k : Scalar) : f.app (j (mul (natScalar 2) k))=genusLaw.zero := by
    rw [two_times,hj]
    change f.app (pointLaw.add _ _)=_
    rw [f.preserves_add]
    have h (p : BitVec 1 × BitVec 1) : genusLaw.add p p=genusLaw.zero := by
      exact Prod.ext ((by decide : ∀ s : BitVec 1, s+s=0) _) ((by decide : ∀ s : BitVec 1, s+s=0) _)
    exact h _
  have decomp := congrArg (fun w => f.app (j w)) (DyadicQuotient.split_at_residue 0 u)
  change f.app (j u)=f.app (j (add (natScalar (u.residue 0).toNat) (mul (natScalar 2) _))) at decomp
  rw [hj] at decomp
  change f.app (j u)=f.app (pointLaw.add _ _) at decomp
  rw [f.preserves_add,h2,genusLaw.add_zero] at decomp
  rcases (by decide : ∀ s : BitVec 1, s=0 ∨ s=1) (u.residue 0) with h|h
  · rw [h] at decomp ⊢
    exact decomp.trans ((congrArg f.app hj0).trans f.preserves_zero)
  · rw [h] at decomp ⊢
    exact decomp

/-- Only three generator restrictions on the actual genus field are
needed to determine its action on all normal coordinates. -/
theorem genus_determined_by_generators (f : Hom pointLaw genusLaw)
    (hA : f.app (axisA (natScalar 1))=(1,0)) (hB : f.app (axisB (natScalar 1))=(0,1))
    (hC : f.app (axisC (natScalar 1))=(0,0)) (g : Point) : f.app g=genus.app g := by
  have first (j : Scalar → Point) (j0 : j scalarLaw.zero=origin)
      (ha : ∀ u v, j (add u v)=product (j u) (j v))
      (eq : f.app (j (natScalar 1))=genus.app (j (natScalar 1))) (s : Scalar) :
      f.app (j s)=genus.app (j s) := by
    rw [genus_hom_scalar j j0 ha f,genus_hom_scalar j j0 ha genus,eq]
  have a := first axisA rfl (fun u v => (axisA_add u v).symm) (hA.trans genus_on_generators.1.symm)
  have b := first axisB rfl (fun u v => (axisB_add u v).symm) (hB.trans genus_on_generators.2.1.symm)
  have hZ : f.app (axisZ (natScalar 1))=genus.app (axisZ (natScalar 1)) := by
    rw [generator_C_decomposes] at hC
    change f.app (pointLaw.add _ _)=(0,0) at hC
    rw [f.preserves_add,hA] at hC
    have h := congrArg (genusLaw.add (genusLaw.neg (1,0))) hC
    rw [←genusLaw.assoc,genusLaw.neg_add,genusLaw.zero_add] at h
    exact h
  have z := first axisZ rfl (fun u v => (axisZ_add u v).symm) hZ
  have E := normal_factorization g
  calc
    f.app g = f.app (pointLaw.add (axisA g.a) (pointLaw.add (axisZ g.z) (axisB g.b))) := congrArg _ E
    _ = genus.app (pointLaw.add (axisA g.a) (pointLaw.add (axisZ g.z) (axisB g.b))) := by
      rw [f.preserves_add,f.preserves_add,genus.preserves_add,genus.preserves_add,a,b,z]
    _ = genus.app g := congrArg _ E.symm

theorem marking_genus {S : Type} {G : GroupLaw S} (m : Hom pointLaw G) (ρ : Hom G genusLaw)
    (hA : ρ.app (m.app (axisA (natScalar 1)))=(1,0))
    (hB : ρ.app (m.app (axisB (natScalar 1)))=(0,1))
    (hC : ρ.app (m.app (axisC (natScalar 1)))=(0,0)) (g : Point) :
    ρ.app (m.app g)=genus.app g := by
  let f : Hom pointLaw genusLaw := {
    app x := ρ.app (m.app x)
    preserves_zero := by rw [m.preserves_zero,ρ.preserves_zero]
    preserves_add x y := by rw [m.preserves_add,ρ.preserves_add]
    preserves_neg x := by rw [m.preserves_neg,ρ.preserves_neg] }
  exact genus_determined_by_generators f hA hB hC g

/-- The abelian index-two subgroup alone supplies the independence and
spanning tests. These inputs come from the free basis A, B², C in the
arithmetic application, with Z=A⁻¹C. -/
theorem marking_bijective {S : Type} {G : GroupLaw S} (m : Hom pointLaw G) (ρ : Hom G genusLaw)
    (hA : ρ.app (m.app (axisA (natScalar 1)))=(1,0))
    (hB : ρ.app (m.app (axisB (natScalar 1)))=(0,1))
    (hC : ρ.app (m.app (axisC (natScalar 1)))=(0,0))
    (independent : ∀ u v w : Scalar, m.app ⟨u,mul (natScalar 2) v,w⟩=G.zero →
      u=scalarLaw.zero ∧ v=scalarLaw.zero ∧ w=scalarLaw.zero)
    (span : ∀ x, (ρ.app x).2=0 → ∃ u v w, m.app ⟨u,mul (natScalar 2) v,w⟩=x) :
    Function.Injective m.app ∧ Function.Surjective m.app := by
  have kernel_trivial (g : Point) (e : m.app g=G.zero) : g=pointLaw.zero := by
    have eq := marking_genus m ρ hA hB hC g
    rw [e,ρ.preserves_zero] at eq
    obtain ⟨v,hv⟩ := (even_iff_double g.b).mp (congrArg Prod.snd eq.symm)
    have repr : g=⟨g.a,mul (natScalar 2) v,g.z⟩ := Point.ext rfl hv rfl
    obtain ⟨ha,ev,hz⟩ := independent g.a v g.z ((congrArg m.app repr).symm.trans e)
    apply Point.ext ha _ hz
    rw [hv,ev,two_times]
    exact scalarLaw.zero_add _
  constructor
  · intro x y h
    have e : m.app (pointLaw.add x (pointLaw.neg y))=G.zero := by
      rw [m.preserves_add,m.preserves_neg,h,G.add_neg]
    have eq := congrArg (fun s => pointLaw.add s y) (kernel_trivial _ e)
    simpa only [pointLaw.assoc,pointLaw.neg_add,pointLaw.add_zero,pointLaw.zero_add] using eq
  · intro x
    rcases (by decide : ∀ s : BitVec 1, s=0 ∨ s=1) (ρ.app x).2 with even|odd
    · obtain ⟨u,v,w,h⟩ := span _ even
      exact ⟨_,h⟩
    · let B := axisB (natScalar 1)
      have even : (ρ.app (G.add x (G.neg (m.app B)))).2=0 := by
        rw [ρ.preserves_add,ρ.preserves_neg,hB]
        change (ρ.app x).2 + -(1:BitVec 1) = 0
        rw [odd]; rfl
      obtain ⟨u,v,w,h⟩ := span _ even
      refine ⟨pointLaw.add ⟨u,mul (natScalar 2) v,w⟩ B,?_⟩
      rw [m.preserves_add,h,G.assoc,G.neg_add,G.add_zero]

open Reimann.DyadicLift (Subgroup)

/-- Identify D and H∩D inside any actual realization of the marked
presentation. Local procyclicity is tested with the class of Frobenius in
the abelianization and its action on the genus field. -/
theorem field_subgroup_identifications {S : Type} {G : GroupLaw S} (m : Hom pointLaw G)
    (onto : Function.Surjective m.app) (ρ : Hom G genusLaw)
    (hA : ρ.app (m.app (axisA (natScalar 1)))=(1,0))
    (hB : ρ.app (m.app (axisB (natScalar 1)))=(0,1))
    (hC : ρ.app (m.app (axisC (natScalar 1)))=(0,0))
    (D : Subgroup G) (F : Point) (square : ClosedDerived (pointLaw.add F F))
    (nontrivial : ρ.app (m.app F)≠genusLaw.zero)
    (frobenius : ∀ g, D.mem (m.app g) ↔ Procyclic F g) (x : S) :
    (D.mem x ↔ ∃ u, x=m.app (axisA u)) ∧
    ((DyadicPlaceProduct.kernel ρ).mem x ∧ D.mem x ↔
      ∃ v, x=m.app (axisA (mul (natScalar 2) v))) := by
  have ng : genus.app F≠genusLaw.zero := by rwa [←marking_genus m ρ hA hB hC]
  have localD (g : Point) := (frobenius g).trans (frobenius_generates_decomposition F square ng g)
  have H (g : Point) : (DyadicPlaceProduct.kernel ρ).mem (m.app g) ↔
      (DyadicPlaceProduct.kernel genus).mem g := by
    change ρ.app (m.app g)=genusLaw.zero ↔ genus.app g=genusLaw.zero
    rw [marking_genus m ρ hA hB hC]
  constructor
  · constructor
    · intro h
      obtain ⟨g,rfl⟩ := onto x
      obtain ⟨u,hu⟩ := (decomposition_is_A g).mp ((localD g).mp h)
      exact ⟨u,congrArg m.app hu⟩
    · rintro ⟨u,rfl⟩
      exact (localD _).mpr ((decomposition_is_A _).mpr ⟨u,rfl⟩)
  · constructor
    · rintro ⟨hx,dx⟩
      obtain ⟨g,rfl⟩ := onto x
      obtain ⟨v,hv⟩ := (intersection_is_A_squared g).mp ⟨(H g).mp hx,(localD g).mp dx⟩
      exact ⟨v,congrArg m.app hv⟩
    · rintro ⟨v,rfl⟩
      have he := (intersection_is_A_squared _).mpr ⟨v,rfl⟩
      exact ⟨(H _).mpr he.1,(localD _).mpr he.2⟩

/-- Equality of actual marked classes is detected by the two coherent coordinates. -/
theorem marked_class_eq {S : Type} {G : GroupLaw S} (m : Hom pointLaw G) (D : Subgroup G)
    (localD : ∀ s, D.mem (m.app s) ↔ decomposition.mem s) (s g : Point) :
    cls D (m.app s)=cls D (m.app g) ↔ plane.app s=plane.app g := by
  let v := pointLaw.add s (pointLaw.neg g)
  have am : m.app v=G.add (m.app s) (G.neg (m.app g)) := by
    rw [show v=pointLaw.add s (pointLaw.neg g) from rfl,m.preserves_add,m.preserves_neg]
  constructor
  · intro e
    obtain ⟨d,hd⟩ := Quotient.exact e
    have dv : D.mem (m.app v) := by
      rw [am,hd,G.assoc,G.add_neg,G.add_zero]
      exact d.property
    have he := (localD v).mp dv
    change plane.app (pointLaw.add s (pointLaw.neg g))=planeLaw.zero at he
    rw [plane.preserves_add,plane.preserves_neg] at he
    have h := congrArg (fun q => planeLaw.add q (plane.app g)) he
    simpa only [planeLaw.assoc,planeLaw.neg_add,planeLaw.add_zero,planeLaw.zero_add] using h
  · intro e
    have dv : decomposition.mem v := by
      change plane.app (pointLaw.add s (pointLaw.neg g))=planeLaw.zero
      rw [plane.preserves_add,plane.preserves_neg,e,planeLaw.add_neg]
    apply Quotient.sound
    refine ⟨⟨m.app v,(localD v).mpr dv⟩,?_⟩
    change m.app s=G.add (m.app v) (m.app g)
    rw [am,G.assoc,G.neg_add,G.add_zero]

/-- The image of the actual genus kernel in the actual quotient by D,
evaluated on a lift of a pair of coherent coefficients. [B] corresponds
to (1,0) by taking the lift B, and the image condition is b-coordinate
even. The scalar witnesses refer to DyadicQuotient.inAmbient. -/
theorem field_split_image {S : Type} {G : GroupLaw S} (m : Hom pointLaw G)
    (onto : Function.Surjective m.app) (ρ : Hom G genusLaw)
    (hA : ρ.app (m.app (axisA (natScalar 1)))=(1,0))
    (hB : ρ.app (m.app (axisB (natScalar 1)))=(0,1))
    (hC : ρ.app (m.app (axisC (natScalar 1)))=(0,0))
    (D : Subgroup G) (hD : Normal D) (F : Point) (square : ClosedDerived (pointLaw.add F F))
    (nontrivial : ρ.app (m.app F)≠genusLaw.zero) (frobenius : ∀ g, D.mem (m.app g) ↔ Procyclic F g)
    (g : Point) :
    (imageSubgroup (DyadicPlaceProduct.kernel ρ) D hD).mem (cls D (m.app g)) ↔
      ∃ x, DyadicQuotient.inAmbient x=plane.app g := by
  have ng : genus.app F≠genusLaw.zero := by rwa [←marking_genus m ρ hA hB hC]
  have localD (s : Point) := (frobenius s).trans (frobenius_generates_decomposition F square ng s)
  have kernelTest (s : Point) : (DyadicPlaceProduct.kernel ρ).mem (m.app s) ↔
      (DyadicPlaceProduct.kernel genus).mem s := by
    change ρ.app (m.app s)=genusLaw.zero ↔ genus.app s=genusLaw.zero
    rw [marking_genus m ρ hA hB hC]
  have same (s : Point) := marked_class_eq m D localD s g
  rw [←split_image]
  constructor
  · rintro ⟨h,he⟩
    obtain ⟨s,hs⟩ := onto h.val
    exact ⟨⟨s,(kernelTest s).mp (hs.symm ▸ h.property)⟩,(same s).mp ((congrArg (cls D) hs).trans he)⟩
  · rintro ⟨h,he⟩
    exact ⟨⟨m.app h.val,(kernelTest _).mpr h.property⟩,(same h.val).mpr he⟩

/-- Normality of the actual dyadic stabilizer follows from its
Frobenius generator and the abelianization and genus tests. -/
theorem field_decomposition_normal {S : Type} {G : GroupLaw S} (m : Hom pointLaw G)
    (onto : Function.Surjective m.app) (D : Subgroup G) (F : Point)
    (square : ClosedDerived (pointLaw.add F F)) (nontrivial : genus.app F≠genusLaw.zero)
    (frobenius : ∀ g, D.mem (m.app g) ↔ Procyclic F g) : Normal D := by
  have localD (g : Point) := (frobenius g).trans (frobenius_generates_decomposition F square nontrivial g)
  intro y d
  obtain ⟨v,rfl⟩ := onto y
  obtain ⟨w,hw⟩ := onto d.val
  have wD : decomposition.mem w := (localD _).mp (hw.symm ▸ d.property)
  have h := (localD (conjugate pointLaw v w)).mpr (decomposition_normal v ⟨w,wD⟩)
  simpa only [conjugate,m.preserves_add,m.preserves_neg,hw] using h

/-- The three continuous exponent maps in a marked pro-2 realization.
The relations below are the central Z and sign conjugation relations on
powers. The commutator and quotient conclusions are absent from the data. -/
structure Powers {S : Type} (G : GroupLaw S) where
  A : Hom scalarLaw G
  Z : Hom scalarLaw G
  B : Hom scalarLaw G
  za : ∀ w u, G.add (Z.app w) (A.app u)=G.add (A.app u) (Z.app w)
  bz : ∀ v w, G.add (B.app v) (Z.app w)=G.add (Z.app w) (B.app v)
  ba : ∀ v u, G.add (B.app v) (A.app u)=G.add (A.app (signBit (v.residue 0) u)) (B.app v)

def evaluate {S : Type} {G : GroupLaw S} (e : Powers G) (x : Point) : S :=
  G.add (e.A.app x.a) (G.add (e.Z.app x.z) (e.B.app x.b))

theorem evaluate_zero {S : Type} {G : GroupLaw S} (e : Powers G) :
    evaluate e origin=G.zero := by
  change G.add (e.A.app scalarLaw.zero) (G.add (e.Z.app scalarLaw.zero) (e.B.app scalarLaw.zero))=G.zero
  rw [e.A.preserves_zero,e.B.preserves_zero,e.Z.preserves_zero,G.zero_add,G.zero_add]

theorem evaluate_product {S : Type} {G : GroupLaw S} (e : Powers G) (x y : Point) :
    evaluate e (product x y)=G.add (evaluate e x) (evaluate e y) := by
  have swap {u v w t : S} (eq : G.add u v=G.add w t) (k : S) :
      G.add u (G.add v k)=G.add w (G.add t k) := by rw [←G.assoc,eq,G.assoc]
  change G.add (e.A.app (scalarLaw.add x.a (signBit (x.b.residue 0) y.a)))
    (G.add (e.Z.app (scalarLaw.add x.z y.z)) (e.B.app (scalarLaw.add x.b y.b)))=_
  rw [e.A.preserves_add,e.Z.preserves_add,e.B.preserves_add]
  simp only [evaluate,G.assoc]
  symm
  rw [swap (e.ba x.b y.a),swap (e.za x.z (signBit (x.b.residue 0) y.a)),swap (e.bz x.b y.z)]

/-- Evaluation is a homomorphism for the concrete nonabelian field group
when the arithmetic exponent maps obey their marked relations. -/
def markedHom {S : Type} {G : GroupLaw S} (e : Powers G) : Hom pointLaw G where
  app := evaluate e
  preserves_zero := evaluate_zero e
  preserves_add := evaluate_product e
  preserves_neg x := by
    apply right_cancel G _ _ (evaluate e x)
    change G.add (evaluate e (pointLaw.neg x)) (evaluate e x)=G.add (G.neg _) _
    rw [←evaluate_product]
    change evaluate e (pointLaw.add (pointLaw.neg x) x)=_
    rw [pointLaw.neg_add,G.neg_add]
    exact evaluate_zero e

/-- The marked field quotient maps isomorphically to the dyadic plane.
The formula for all marked representatives specifies the images of B and C. -/
theorem field_quotient_coordinates {S : Type} {G : GroupLaw S} (m : Hom pointLaw G)
    (onto : Function.Surjective m.app) (D : Subgroup G) (hD : Normal D)
    (F : Point) (square : ClosedDerived (pointLaw.add F F)) (nontrivial : genus.app F≠genusLaw.zero)
    (frobenius : ∀ g, D.mem (m.app g) ↔ Procyclic F g) :
    ∃ Y : Hom (targetLaw D hD) planeLaw, Function.Injective Y.app ∧ Function.Surjective Y.app ∧
      ∀ g, Y.app (cls D (m.app g))=plane.app g := by
  let π := projection D hD
  have localD (s : Point) := (frobenius s).trans (frobenius_generates_decomposition F square nontrivial s)
  have all (q : Target D) : ∃ s, π.app (m.app s)=q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      obtain ⟨s,rfl⟩ := onto x
      exact ⟨s,rfl⟩
  let sec (q : Target D) := Classical.choose (all q)
  have right (q : Target D) : π.app (m.app (sec q))=q := Classical.choose_spec (all q)
  let Y (q : Target D) := plane.app (sec q)
  have he (g : Point) : Y (π.app (m.app g))=plane.app g :=
    (marked_class_eq m D localD _ _).mp (right _)
  let toPlane : Hom (targetLaw D hD) planeLaw := {
    app := Y
    preserves_zero := by
      have e := he pointLaw.zero
      rwa [m.preserves_zero,π.preserves_zero,plane.preserves_zero] at e
    preserves_add x y := by
      obtain ⟨g,rfl⟩ := all x
      obtain ⟨s,rfl⟩ := all y
      rw [←π.preserves_add,←m.preserves_add,he,plane.preserves_add,he,he]
    preserves_neg x := by
      obtain ⟨g,rfl⟩ := all x
      rw [←π.preserves_neg,←m.preserves_neg,he,plane.preserves_neg,he] }
  refine ⟨toPlane,?_,?_,he⟩
  · intro x y e
    have k := (marked_class_eq m D localD (sec x) (sec y)).mpr e
    change π.app (m.app (sec x))=π.app (m.app (sec y)) at k
    rwa [right,right] at k
  · intro y
    exact ⟨π.app (m.app ⟨scalarLaw.zero,y.1,y.2⟩),he _⟩

/-- Joint arithmetic interface. The only lattice-basis inputs are on the
abelian index-two subgroup. The local Artin inputs are procyclic Frobenius
generation, two-torsion in the abelianization, and a nonidentity genus image. -/
theorem marked_field_handoff {S : Type} {G : GroupLaw S} (powers : Powers G) (ρ : Hom G genusLaw)
    (D : Subgroup G) (F : Point)
    (hA : ρ.app ((markedHom powers).app (axisA (natScalar 1)))=(1,0))
    (hB : ρ.app ((markedHom powers).app (axisB (natScalar 1)))=(0,1))
    (hC : ρ.app ((markedHom powers).app (axisC (natScalar 1)))=(0,0))
    (independent : ∀ u v w : Scalar, (markedHom powers).app ⟨u,mul (natScalar 2) v,w⟩=G.zero →
      u=scalarLaw.zero ∧ v=scalarLaw.zero ∧ w=scalarLaw.zero)
    (span : ∀ x, (ρ.app x).2=0 → ∃ u v w, (markedHom powers).app ⟨u,mul (natScalar 2) v,w⟩=x)
    (square : ClosedDerived (pointLaw.add F F)) (nontrivial : ρ.app ((markedHom powers).app F)≠genusLaw.zero)
    (frobenius : ∀ g, D.mem ((markedHom powers).app g) ↔ Procyclic F g) :
    let m := markedHom powers
    (∀ x, (D.mem x ↔ ∃ u, x=m.app (axisA u)) ∧
      ((DyadicPlaceProduct.kernel ρ).mem x ∧ D.mem x ↔ ∃ v, x=m.app (axisA (mul (natScalar 2) v)))) ∧
    ∃ hD : Normal D, ∃ Y : Hom (targetLaw D hD) planeLaw,
      Function.Injective Y.app ∧ Function.Surjective Y.app ∧
      Y.app (cls D (m.app (axisB (natScalar 1))))=(natScalar 1,scalarLaw.zero) ∧
      (∀ q, (imageSubgroup (DyadicPlaceProduct.kernel ρ) D hD).mem q ↔
        ∃ x, DyadicQuotient.inAmbient x=Y.app q) := by
  let m := markedHom powers
  have onto := (marking_bijective m ρ hA hB hC independent span).2
  have ng : genus.app F≠genusLaw.zero := by rwa [←marking_genus m ρ hA hB hC]
  have hD := field_decomposition_normal m onto D F square ng frobenius
  obtain ⟨Y,yinj,ysurj,ym⟩ := field_quotient_coordinates m onto D hD F square ng frobenius
  refine ⟨field_subgroup_identifications m onto ρ hA hB hC D F square nontrivial frobenius,
    hD,Y,yinj,ysurj,ym _,?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨g,rfl⟩ := onto x
    change (imageSubgroup (DyadicPlaceProduct.kernel ρ) D hD).mem (cls D (m.app g)) ↔
      ∃ r, DyadicQuotient.inAmbient r=Y.app (cls D (m.app g))
    rw [ym]
    exact field_split_image m onto ρ hA hB hC D hD F square nontrivial frobenius g

/-- Images of the normal-coordinate cylinders modulo 2^(n+1) in G/D. -/
def QuotientCongruence {S : Type} {G : GroupLaw S} (m : Hom pointLaw G)
    (D : Subgroup G) (n : Nat) (x y : Target D) : Prop :=
  ∃ s t, cls D (m.app s)=x ∧ cls D (m.app t)=y ∧ AtLevel n s t

/-- At each precision the coordinates identify a quotient cylinder exactly
with the two residue equalities in Z₂². Thus both directions of the
coordinate isomorphism respect the marked profinite topology. -/
theorem quotient_precision {S : Type} {G : GroupLaw S} (m : Hom pointLaw G)
    (D : Subgroup G) (hD : Normal D) (Y : Hom (targetLaw D hD) planeLaw)
    (injective : Function.Injective Y.app) (marks : ∀ g, Y.app (cls D (m.app g))=plane.app g)
    (n : Nat) (x y : Target D) :
    QuotientCongruence m D n x y ↔
      (Y.app x).1.residue n=(Y.app y).1.residue n ∧ (Y.app x).2.residue n=(Y.app y).2.residue n := by
  constructor
  · rintro ⟨s,t,rfl,rfl,h⟩
    rw [marks,marks]
    exact ⟨h.2.1,h.2.2⟩
  · rintro ⟨hb,hc⟩
    let lift (q : Target D) : Point := ⟨scalarLaw.zero,(Y.app q).1,(Y.app q).2⟩
    have eq (q : Target D) : cls D (m.app (lift q))=q := injective (marks (lift q))
    exact ⟨lift x,lift y,eq x,eq y,rfl,hb,hc⟩

/-- Project Mizusawa's two forward-generator words on the actual field
quotient. A^{C₁} disappears in Y, fixing the columns and their signs. -/
theorem forward_generator_columns {S : Type} {G : GroupLaw S} (m : Hom pointLaw G)
    (D : Subgroup G) (hD : Normal D) (Y : Hom (targetLaw D hD) planeLaw)
    (marks : ∀ g, Y.app (cls D (m.app g))=plane.app g)
    (γ : S → S) (c₀ c₁ : Scalar)
    (hB : γ (m.app (axisB (natScalar 1))) =
      G.add (m.app (axisB (natScalar 1))) (m.app (axisC (natScalar 1))))
    (hC : γ (m.app (axisC (natScalar 1))) =
      G.add (G.add (m.app (axisA c₁)) (m.app (axisB (neg c₀))))
        (m.app (axisC (add (natScalar 1) (neg c₁))))) :
    Y.app (cls D (γ (m.app (axisB (natScalar 1)))))=(natScalar 1,natScalar 1) ∧
    Y.app (cls D (γ (m.app (axisC (natScalar 1)))))=(neg c₀,add (natScalar 1) (neg c₁)) := by
  constructor
  · rw [hB,←m.preserves_add,marks]
    exact Prod.ext (scalarLaw.add_zero _) (scalarLaw.zero_add _)
  · rw [hC,←m.preserves_add,←m.preserves_add,marks]
    apply Prod.ext
    · change scalarLaw.add (scalarLaw.add scalarLaw.zero (neg c₀)) scalarLaw.zero=_
      rw [scalarLaw.zero_add,scalarLaw.add_zero]
    · change scalarLaw.add (scalarLaw.add scalarLaw.zero scalarLaw.zero) (add (natScalar 1) (neg c₁))=_
      rw [scalarLaw.zero_add,scalarLaw.zero_add]

end Reimann.DyadicMizusawaCoordinates69
