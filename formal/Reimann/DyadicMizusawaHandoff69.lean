import Reimann.DyadicMizusawaCoordinates69
import Reimann.DyadicArtinPlace69

/-! Identify the actual second-place commutator in the marked coordinates
over k∞. D is the stabilizer of the chosen upper prime throughout. -/
namespace Reimann.DyadicMizusawaHandoff69

open Lean.Grind Reimann.Transfer Reimann.TameRestriction Reimann.DyadicLift Reimann.DyadicPlaceProduct
open Reimann.DyadicAutomorphism69 (law push)
open Reimann.DyadicLocalRestriction69 Reimann.DyadicArtinCommutator69 Reimann.DyadicArtinImage69
open Reimann.DyadicMizusawaCoordinates69 Reimann.DyadicArtinPlace69
open Reimann.DyadicLattice Reimann.DyadicGenusField69
open Reimann.TameRationalField277 (gen3 gen23)
open Reimann.DyadicUnramifiedBase69 (RingMap)

theorem embedding_inverse {F Ω : Type} [Field F] [Field Ω] (j : RingMap F Ω) (x : F) :
    j.app x⁻¹=(j.app x)⁻¹ := by
  by_cases h : x=0
  · rw [h,Field.inv_zero,j.zero,Field.inv_zero]
  · have h' := j.mul x⁻¹ x
    rw [Field.inv_mul_cancel h,j.one] at h'
    exact Field.eq_inv_of_mul_eq_one h'.symm

theorem fixed_subfield {F Ω : Type} [Field F] [Field Ω] (j : RingMap F Ω) (g : Automorphism Ω) :
    DyadicCyclotomicSpan69.Subfield (fun x => g.app (j.app x)=j.app x) where
  zero := by rw [j.zero,g.zero]
  one := by rw [j.one,g.one]
  add := by intro x y hx hy; rw [j.add,g.add,hx,hy]
  mul := by intro x y hx hy; rw [j.mul,g.mul,hx,hy]
  neg := by intro x hx; rw [j.neg,DyadicAutomorphism69.map_neg,hx]
  inv := by intro x hx; rw [embedding_inverse,DyadicAbelianTower69.map_inverse,hx]

/-- An automorphism fixing k∞ fixes L exactly when it fixes the two genus
radicals ix=√3, iy=√23 in the field embedding. -/
theorem fixes_genus_iff {F Ω : Type} [Field F] [Field Ω] [IsCharP F 0]
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (j : RingMap F Ω)
    (i : F) (hi : i*i= -1) (g : Automorphism Ω)
    (base : g.app (j.app (i*f.app gen3*f.app gen23))=j.app (i*f.app gen3*f.app gen23))
    (real : ∀ n, g.app (j.app (realTrace (C.root (n+1))))=j.app (realTrace (C.root (n+1)))) :
    (∀ x, g.app (j.app x)=j.app x) ↔
      g.app (j.app (i*f.app gen3))=j.app (i*f.app gen3) ∧
      g.app (j.app (i*f.app gen23))=j.app (i*f.app gen23) := by
  refine ⟨fun all => ⟨all _,all _⟩,?_⟩
  rintro ⟨ex,ey⟩
  let S := fun x => g.app (j.app x)=j.app x
  have alg : DyadicCyclotomicSpan69.Subfield S := fixed_subfield j g
  obtain ⟨hx,hy⟩ := embedded_radical_squares f
  have rt := (real_tower_generators alg (fun n => C.root (n+1)) (fun n => C.half_order (n+1))).mpr real
  obtain ⟨xx,yy,roots⟩ := (subfield_generators_iff alg i (f.app gen3) (f.app gen23) hi hx hy).mpr
    ⟨base,ex,ey,rt⟩
  exact hL S alg ((bottom_image_iff alg f).mpr ⟨xx,yy⟩) (fun n =>
    roots _ (primitive_is_dyadic _ n (C.half_order n)))

/-- Data to be realized on the upper Galois group by the marked pro-2 presentation
and by the unramified dyadic Frobenius. Only the index-two abelian subgroup
requires a basis check, and the decomposition subgroup is the actual stabilizer. -/
structure FieldMark {Ω : Type} [Field Ω] (N : Subgroup (law Ω)) (p : Ω → Prop) where
  powers : Powers (subgroupLaw N)
  genusMap : Hom (subgroupLaw N) genusLaw
  image_A : genusMap.app ((markedHom powers).app (axisA (natScalar 1)))=(1,0)
  image_B : genusMap.app ((markedHom powers).app (axisB (natScalar 1)))=(0,1)
  image_C : genusMap.app ((markedHom powers).app (axisC (natScalar 1)))=(0,0)
  independent : ∀ u v w : Scalar,
    (markedHom powers).app ⟨u,mul (natScalar 2) v,w⟩=(subgroupLaw N).zero →
    u=scalarLaw.zero ∧ v=scalarLaw.zero ∧ w=scalarLaw.zero
  span : ∀ x, (genusMap.app x).2=0 → ∃ u v w,
    (markedHom powers).app ⟨u,mul (natScalar 2) v,w⟩=x
  frob : Point
  square : ClosedDerived (pointLaw.add frob frob)
  nontrivial : genusMap.app ((markedHom powers).app frob)≠genusLaw.zero
  local_frobenius : ∀ g, (primeStabilizer N p).mem ((markedHom powers).app g) ↔ Procyclic frob g

/-- Comparison of the actual subgroup fixing L with the genus test on the
two radicals, with k∞ fixed on its displayed generators. -/
theorem actual_genus_kernel {F Ω : Type} [Field F] [Field Ω] [IsCharP F 0]
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (j : RingMap F Ω)
    (N : Subgroup (law Ω)) (ρ : Hom (subgroupLaw N) genusLaw) (i : F) (hi : i*i= -1)
    (base : ∀ g : Subtype N.mem,
      g.val.app (j.app (i*f.app gen3*f.app gen23))=j.app (i*f.app gen3*f.app gen23))
    (real : ∀ (g : Subtype N.mem) n,
      g.val.app (j.app (realTrace (C.root (n+1))))=j.app (realTrace (C.root (n+1))))
    (tests : ∀ g : Subtype N.mem, ρ.app g=genusLaw.zero ↔
      g.val.app (j.app (i*f.app gen3))=j.app (i*f.app gen3) ∧
      g.val.app (j.app (i*f.app gen23))=j.app (i*f.app gen23)) (g : Subtype N.mem) :
    (fixingLower (onElements Ω) N j.app).mem g ↔ (DyadicPlaceProduct.kernel ρ).mem g :=
  (fixes_genus_iff f C hL j i hi g.val (base g) (real g)).trans (tests g).symm

theorem image_of_same_members {S : Type} {G : GroupLaw S} (H K D : Subgroup G)
    (hD : Normal D) (same : ∀ g, H.mem g ↔ K.mem g) (q : Target D) :
    (imageSubgroup H D hD).mem q ↔ (imageSubgroup K D hD).mem q := by
  constructor
  · rintro ⟨⟨g,hg⟩,e⟩
    exact ⟨⟨g,(same g).mp hg⟩,e⟩
  · rintro ⟨⟨g,hg⟩,e⟩
    exact ⟨⟨g,(same g).mpr hg⟩,e⟩

theorem outside_from_coordinates {S : Type} {G : GroupLaw S} (H D : Subgroup G)
    (hD : Normal D) (Y : Hom (targetLaw D hD) planeLaw) (B : S)
    (hb : Y.app (cls D B)=(natScalar 1,scalarLaw.zero))
    (img : ∀ q, (imageSubgroup H D hD).mem q ↔ ∃ x, DyadicQuotient.inAmbient x=Y.app q) :
    ¬(imageSubgroup H D hD).mem (cls D B) := by
  intro inside
  obtain ⟨x,h⟩ := (img _).mp inside
  rw [hb] at h
  have bit := congrArg (fun y : Scalar × Scalar => y.1.residue 0) h
  change 2*x.1.residue 0=(1:BitVec 1) at bit
  exact (by decide : ∀ s : BitVec 1, 2*s≠1) _ bit

/-- The same marked isomorphism gives both local subgroup descriptions,
the image of the field-fixing subgroup, the class of the switching element,
and the coordinate of its commutator with a prime-preserving lift. -/
theorem field_commutator_coordinates {F Ω : Type} [Field F] [Field Ω] [IsCharP F 0]
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (j : RingMap F Ω)
    (N : Subgroup (law Ω)) (p : Ω → Prop) (M : FieldMark N p) (i : F) (hi : i*i= -1)
    (base : ∀ g : Subtype N.mem,
      g.val.app (j.app (i*f.app gen3*f.app gen23))=j.app (i*f.app gen3*f.app gen23))
    (real : ∀ (g : Subtype N.mem) n,
      g.val.app (j.app (realTrace (C.root (n+1))))=j.app (realTrace (C.root (n+1))))
    (tests : ∀ g : Subtype N.mem, M.genusMap.app g=genusLaw.zero ↔
      g.val.app (j.app (i*f.app gen3))=j.app (i*f.app gen3) ∧
      g.val.app (j.app (i*f.app gen23))=j.app (i*f.app gen23)) :
    let m := markedHom M.powers
    let B := m.app (axisB (natScalar 1))
    let D := primeStabilizer N p
    let H := fixingLower (onElements Ω) N j.app
    (∀ g, (D.mem g ↔ ∃ u, g=m.app (axisA u)) ∧
      ((H.mem g ∧ D.mem g) ↔ ∃ v, g=m.app (axisA (mul (natScalar 2) v)))) ∧
    ∃ hD : Normal D, ∃ Y : Hom (targetLaw D hD) planeLaw,
      Function.Injective Y.app ∧ Function.Surjective Y.app ∧
      Y.app (cls D B)=(natScalar 1,scalarLaw.zero) ∧
      (∀ q, (imageSubgroup H D hD).mem q ↔ ∃ x, DyadicQuotient.inAmbient x=Y.app q) ∧
      ¬(imageSubgroup H D hD).mem (cls D B) ∧
      ∀ (β t : Automorphism F) (d : Automorphism Ω)
        (_ : ∀ x, B.val.app (j.app x)=j.app (β.app x)) (_ : ∀ x, d.app (j.app x)=j.app (t.app x))
        (local_d : ∀ y, p (d.app y) ↔ p y)
        (hd : ∀ x : Subtype N.mem, N.mem (conjugate (law Ω) d x.val)),
        let tY := induced D hD (ambientConjugation N d hd)
          (local_lift_preserves_decomposition N p d local_d hd)
        (∀ x, (conjugate (law Ω) B.val d).app (j.app x)=j.app (t.app x)) ∧
        push (conjugate (law Ω) B.val d) (push B.val p)=push B.val p ∧
        ∃ h : Subtype H.mem, h.val.val=commutator (law Ω) B.val d ∧
          Y.app ((inclusion H D hD).app (cls (intersection H D) h)) =
            planeLaw.add (natScalar 1,scalarLaw.zero) (planeLaw.neg (Y.app (tY.app (cls D B)))) := by
  let m := markedHom M.powers
  let B := m.app (axisB (natScalar 1))
  let D := primeStabilizer N p
  let H := fixingLower (onElements Ω) N j.app
  have same := actual_genus_kernel f C hL j N M.genusMap i hi base real tests
  obtain ⟨groups,hD,Y,yinj,ysur,hb,img⟩ := marked_field_handoff M.powers M.genusMap D M.frob
    M.image_A M.image_B M.image_C M.independent M.span M.square M.nontrivial M.local_frobenius
  have imgH (q : Target D) : (imageSubgroup H D hD).mem q ↔ ∃ x, DyadicQuotient.inAmbient x=Y.app q :=
    (image_of_same_members H _ D hD same q).trans (img q)
  refine ⟨fun g => ⟨(groups g).1, (and_congr (same g) Iff.rfl).trans (groups g).2⟩,
    hD,Y,yinj,ysur,hb,imgH,outside_from_coordinates H D hD Y B hb imgH,?_⟩
  intro β t d rB rd local_d hd
  obtain ⟨restriction,stabilizes,h,word,eq⟩ :=
    split_artin_commutator f C hL j.app N p hD B β t d rB rd local_d hd
  refine ⟨restriction,stabilizes,h,word,?_⟩
  rw [eq,Y.preserves_add,Y.preserves_neg]
  exact congrArg (fun z => planeLaw.add z _) hb

end Reimann.DyadicMizusawaHandoff69
