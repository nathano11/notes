import Reimann.DyadicMizusawaCoordinates69
import Reimann.DyadicArtinLimit69

/-! The closed commutator quotient in normal coordinates and the
dyadic Frobenius square detected by finite Hilbert Artin restrictions. -/
namespace Reimann.DyadicArtinSquare69

open Reimann.Transfer Reimann.TameRestriction Reimann.DyadicLattice
open Reimann.DyadicMizusawaCoordinates69 Reimann.DyadicArtinLimit69
open Reimann.DyadicArtinCommutator69

abbrev Abelian := BitVec 1 × (Scalar × Scalar)

def abelianLaw : GroupLaw Abelian where
  zero := (0,planeLaw.zero)
  add s t := (s.1+t.1,planeLaw.add s.2 t.2)
  neg s := (-s.1,planeLaw.neg s.2)
  assoc _ _ _ := Prod.ext (BitVec.add_assoc _ _ _) (planeLaw.assoc _ _ _)
  zero_add _ := Prod.ext (BitVec.zero_add _) (planeLaw.zero_add _)
  add_zero _ := Prod.ext (BitVec.add_zero _) (planeLaw.add_zero _)
  add_neg s := Prod.ext ((by decide : ∀ e : BitVec 1, e + -e=0) _) (planeLaw.add_neg s.2)
  neg_add s := Prod.ext ((by decide : ∀ e : BitVec 1, -e + e=0) _) (planeLaw.neg_add s.2)

theorem abelian_commutes (s t : Abelian) : abelianLaw.add s t=abelianLaw.add t s := by
  apply Prod.ext (BitVec.add_comm _ _)
  apply Prod.ext <;> apply scalar_ext <;> intro n <;> exact BitVec.add_comm _ _

def abelianization : Hom pointLaw abelianLaw where
  app g := (g.a.residue 0,plane.app g)
  preserves_zero := rfl
  preserves_add g h := by
    refine Prod.ext ?_ rfl
    change g.a.residue 0 + (signBit _ h.a).residue 0=_
    rw [signBit_parity]
    rfl
  preserves_neg g := Prod.ext (signBit_parity _ _) rfl

theorem abelianization_onto : Function.Surjective abelianization.app := by
  rintro ⟨p,v,w⟩
  refine ⟨⟨natScalar p.toNat,v,w⟩,Prod.ext ?_ rfl⟩
  exact (by decide : ∀ z : BitVec 1, BitVec.ofNat 1 z.toNat=z) p

theorem derived_zero {g : Point} (h : DerivedWord g) : abelianization.app g=abelianLaw.zero := by
  induction h with
  | one => exact abelianization.preserves_zero
  | prod _ _ ih jh => rw [abelianization.preserves_add,ih,jh,abelianLaw.zero_add]
  | inv _ ih =>
    rw [abelianization.preserves_neg,ih]
    exact (abelianLaw.zero_add _).symm.trans (abelianLaw.add_neg _)
  | comm x y =>
    simp only [commutator,abelianization.preserves_add,abelianization.preserves_neg]
    rw [abelian_commutes (abelianization.app x) (abelianization.app y),
      abelianLaw.assoc (abelianization.app y) _ _,abelianLaw.add_neg,abelianLaw.add_zero,abelianLaw.add_neg]

/-- Every even A-power is one commutator with the switching generator. -/
theorem single_commutator (u : Scalar) :
    commutator pointLaw (axisA u) (axisB (natScalar 1))=axisA (mul (natScalar 2) u) := by
  apply Point.ext <;> apply scalar_ext <;> intro n <;>
    simp [commutator,pointLaw,product,reciprocal,axisA,axisB,signBit,scalarLaw,add,neg,natScalar,mul] <;> grind

theorem kernel_is_derived (g : Point) : abelianization.app g=abelianLaw.zero ↔ DerivedWord g := by
  constructor
  · intro h
    have hbc := congrArg Prod.snd h
    obtain ⟨u,e⟩ := (even_iff_double g.a).mp (congrArg Prod.fst h)
    have eq : g=axisA (mul (natScalar 2) u) := Point.ext e (congrArg Prod.fst hbc) (congrArg Prod.snd hbc)
    rw [eq,←single_commutator]
    exact .comm _ _
  · exact derived_zero

theorem closed_derived_iff (g : Point) : ClosedDerived g ↔ abelianization.app g=abelianLaw.zero := by
  constructor
  · intro h
    obtain ⟨s,word,ea,_,_⟩ := h 0
    exact Prod.ext (ea.trans (congrArg Prod.fst (derived_zero word))) (closed_derived_plane_zero h)
  · intro h n
    exact ⟨g,(kernel_is_derived g).mp h,rfl,rfl,rfl⟩

/-- In the two free coordinates, checking that the square vanishes at
every finite precision suffices. The remaining parity coordinate has exponent two. -/
theorem square_iff_free_residues (F : Point) :
    ClosedDerived (pointLaw.add F F) ↔ ∀ n,
      F.b.residue n + F.b.residue n=0 ∧ F.z.residue n + F.z.residue n=0 := by
  rw [closed_derived_iff,abelianization.preserves_add]
  constructor
  · intro h n
    exact ⟨congrArg (fun s : Abelian => s.2.1.residue n) h,congrArg (fun s : Abelian => s.2.2.residue n) h⟩
  · intro h
    exact Prod.ext ((by decide : ∀ p : BitVec 1, p+p=0) _)
      (Prod.ext (scalar_ext (fun n => (h n).1)) (scalar_ext (fun n => (h n).2)))

/-- The Galois group's marked commutator quotient, as a quotient group,
is C₂ × Z₂². The subgroup being quotiented has exactly predicate ClosedDerived. -/
theorem commutator_quotient_iso :
    let D := DyadicPlaceProduct.kernel abelianization
    (∀ g, D.mem g ↔ ClosedDerived g) ∧ ∃ hD : Normal D, ∃ f : Hom (targetLaw D hD) abelianLaw,
      Function.Injective f.app ∧ Function.Surjective f.app ∧
      ∀ g, f.app (cls D g)=abelianization.app g := by
  let D := DyadicPlaceProduct.kernel abelianization
  have hD : Normal D := fun g h => DyadicPlaceProduct.kernel_normal abelianization g h.val h.property
  let f := descend D hD abelianization (fun g => g.property)
  refine ⟨fun g => (closed_derived_iff g).symm,hD,f,?_,?_,fun _ => rfl⟩
  · intro u v
    induction u using Quotient.inductionOn with | _ g =>
      induction v using Quotient.inductionOn with | _ h =>
        intro eq
        change abelianization.app g=abelianization.app h at eq
        let k := pointLaw.add g (pointLaw.neg h)
        have hk : D.mem k := DyadicPlaceProduct.same_image_difference abelianization _ _ eq.symm
        exact Quotient.sound ⟨⟨k,hk⟩,(DyadicPlaceProduct.difference_times (P:=pointLaw) g h).symm⟩
  · intro y
    obtain ⟨g,h⟩ := abelianization_onto y
    exact ⟨cls D g,h⟩

/-- Joint faithfulness can use the finite Hilbert restrictions in any
cofinal system. Injectivity of a single finite-stage restriction is unnecessary. -/
theorem square_of_finite_restrictions (F : Point) (S : Nat → Stage)
    (res : ∀ n, Hom abelianLaw (S n).galois)
    (separates : Function.Injective (fun u n => (res n).app u))
    (square : ∀ n, (S n).galois.add ((res n).app (abelianization.app F))
      ((res n).app (abelianization.app F))=(S n).galois.zero) :
    ClosedDerived (pointLaw.add F F) := by
  apply (closed_derived_iff _).mpr
  rw [abelianization.preserves_add]
  apply separates
  funext n
  exact ((res n).preserves_add _ _).trans ((square n).trans (res n).preserves_zero.symm)

theorem inverse_of_two_torsion {K : Type} (G : GroupLaw K) {x : K} (hx : G.add x x=G.zero) :
    G.neg x=x := by
  calc
    G.neg x = G.add (G.neg x) G.zero := (G.add_zero _).symm
    _ = G.add (G.neg x) (G.add x x) := congrArg (G.add (G.neg x)) hx.symm
    _ = x := by rw [← G.assoc,G.neg_add,G.zero_add]

/-- Every odd power of a finite symbol of order dividing two agrees with
the symbol. This includes the finite images of a change of procyclic generator. -/
theorem odd_generator_same_symbol {K : Type} (G : GroupLaw K) (x : K)
    (hx : G.add x x=G.zero) (k : Nat) : multiple G (2*k+1) x=x := by
  have two : multiple G 2 x=G.zero := by
    change G.add (G.add G.zero x) x=G.zero
    rw [G.zero_add,hx]
  change G.add (multiple G (2*k) x) x=x
  rw [Nat.mul_comm 2 k,multiple_mul,two,multiple_identity,G.zero_add]

/-- A norm-coherent 2-primary class system of exponent at most two gives
the closed-derived square of a marked Frobenius when its finite restrictions
are the corresponding Artin images. Inverse symbols give the same test. -/
theorem square_from_coherent_classes (F : Point) (S : Nat → Stage)
    (r : ∀ n, Transition (S (n+1)) (S n)) (c : primaryLimit (classSystem S r))
    (res : ∀ n, Hom abelianLaw (S n).galois)
    (separates : Function.Injective (fun u n => (res n).app u))
    (torsion : ∀ n, (S n).classes.add (c.val n) (c.val n)=(S n).classes.zero)
    (symbol_match : ∀ n, let g := (artinLimit S r c).val n
      (res n).app (abelianization.app F)=g ∨ (res n).app (abelianization.app F)=(S n).galois.neg g) :
    ClosedDerived (pointLaw.add F F) := by
  apply square_of_finite_restrictions F S res separates
  intro n
  have g2 : (S n).galois.add ((artinLimit S r c).val n) ((artinLimit S r c).val n)=(S n).galois.zero :=
    ((finiteArtin (S n)).preserves_add _ _).symm.trans
      ((congrArg (finiteArtin (S n)).app (torsion n)).trans (finiteArtin (S n)).preserves_zero)
  have eq := (symbol_match n).elim id (fun h => h.trans (inverse_of_two_torsion _ g2))
  rw [eq]
  exact g2

/-- At each real-cyclotomic level, use the actual class of the chosen
dyadic prime ideal. Norm compatibility, principality of its square, and
the finite prime-symbol match suffice through jointly faithful restrictions. -/
theorem square_from_ideal_classes (F : Point) (S : Nat → Stage)
    (r : ∀ n, Transition (S (n+1)) (S n)) (I : ∀ n, (S n).Ideal)
    (norm : ∀ n, (r n).norm.app (I (n+1))=I n)
    (principal : ∀ n, (S n).idealClass.proj.app ((S n).ideals.add (I n) (I n))=(S n).classes.zero)
    (res : ∀ n, Hom abelianLaw (S n).galois)
    (separates : Function.Injective (fun u n => (res n).app u))
    (symbol_match : ∀ n, (res n).app (abelianization.app F)=(S n).symbol.app (I n) ∨
      (res n).app (abelianization.app F)=(S n).galois.neg ((S n).symbol.app (I n))) :
    ClosedDerived (pointLaw.add F F) := by
  let v (n : Nat) := (S n).idealClass.proj.app (I n)
  have torsion (n : Nat) : (S n).classes.add (v n) (v n)=(S n).classes.zero :=
    ((S n).idealClass.proj.preserves_add _ _).symm.trans (principal n)
  have coh : Coherent (classSystem S r) v := fun n =>
    (class_norm_of_ideal (r n) (I (n+1))).trans (congrArg (S n).idealClass.proj.app (norm n))
  let c : primaryLimit (classSystem S r) := ⟨v,coh, fun n =>
    ⟨1,by
      change (S n).classes.add ((S n).classes.add (S n).classes.zero (v n)) (v n)=(S n).classes.zero
      rw [(S n).classes.zero_add,torsion]⟩⟩
  apply square_from_coherent_classes F S r c res separates torsion
  intro n
  change _=(finiteArtin (S n)).app ((S n).idealClass.proj.app (I n)) ∨
    _=(S n).galois.neg ((finiteArtin (S n)).app ((S n).idealClass.proj.app (I n)))
  rw [artin_of_ideal]
  exact symbol_match n

end Reimann.DyadicArtinSquare69
