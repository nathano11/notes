import Reimann.DyadicOneSided69
import Reimann.SignedCommonNormalization
import Reimann.SignedOrientationWitness

/-! The bottom coinvariants of Mizusawa's forward action modulo eight.
At the arithmetic application the finite control quotient is Cl₂(Q(√−69))/8.
The mod-four linear coefficient is the separate computed example on p. 134. -/
namespace Reimann.DyadicControlJet69

open Reimann.DyadicLattice Reimann.DyadicOrder
open Reimann.DyadicClass69 Reimann.DyadicOneSided69

/-- Coordinates on the abelianized presentation, reduced modulo eight.
The first generator is the dyadic class of order two. -/
abbrev Row := BitVec 1 × BitVec 3 × BitVec 3

/-- Two rows differ by (γ−1) of a row.  The A-coordinate of γC is C₁ mod 2. -/
def Related (a b : BitVec 3) (x y : Row) : Prop :=
  ∃ s t : BitVec 3, x.1-y.1 = b.setWidth 1*t.setWidth 1 ∧
    x.2.1-y.2.1 = -a*t ∧ x.2.2-y.2.2 = s-b*t

/-- The column γB−B=C eliminates the last coordinate freely. -/
theorem eliminate_last (a b : BitVec 3) (even : b.setWidth 1=0) (x y : Row) :
    Related a b x y ↔ x.1=y.1 ∧ ∃ t : BitVec 3, x.2.1-y.2.1 = -a*t := by
  constructor
  · rintro ⟨s,t,ht,hm,_⟩
    rw [even] at ht
    exact ⟨(by decide : ∀ p q z : BitVec 1, p-q=0*z → p=q) _ _ _ ht,t,hm⟩
  · rintro ⟨hs,t,ht⟩
    exact ⟨x.2.2-y.2.2+b*t,t,by rw [hs,even]; exact (by decide : ∀ p z : BitVec 1, p-p=0*z) _ _,
      ht,(by decide : ∀ u v w : BitVec 3, u-v=(u-v+w)-w) _ _ _⟩

/-- High bit for the A-coordinate and the canonical b-coordinate in ℤ/(8,C₀). -/
def code (a : BitVec 3) (x : Row) : BitVec 4 :=
  BitVec.ofNat 4 (8*x.1.toNat + x.2.1.toNat % Nat.gcd 8 a.toNat)

set_option maxRecDepth 10000 in
theorem code_eq_iff (a : BitVec 3) (x y : Row) :
    code a x=code a y ↔ x.1=y.1 ∧ ∃ t : BitVec 3, x.2.1-y.2.1 = -a*t :=
  (by decide +kernel : ∀ (c : BitVec 3) (p q : BitVec 1) (u v : BitVec 3),
    BitVec.ofNat 4 (8*p.toNat + u.toNat % Nat.gcd 8 c.toNat) =
      BitVec.ofNat 4 (8*q.toNat + v.toNat % Nat.gcd 8 c.toNat) ↔
      p=q ∧ ∃ t : BitVec 3, u-v = -c*t) a x.1 y.1 x.2.1 y.2.1

theorem relation_iff_code (a b : BitVec 3) (even : b.setWidth 1=0) (x y : Row) :
    Related a b x y ↔ code a x=code a y :=
  (eliminate_last a b even x y).trans (code_eq_iff a x y).symm

def rep (k : BitVec 4) : Row := (BitVec.ofNat 1 (k.toNat/8), k.setWidth 3, 0)

def codes (a : BitVec 3) : List (BitVec 4) :=
  ((List.range 16).map (BitVec.ofNat 4)).filter (fun k => decide (code a (rep k)=k))

theorem mem_codes (a : BitVec 3) (k : BitVec 4) : k ∈ codes a ↔ code a (rep k)=k :=
  (by decide +kernel : ∀ a k, k ∈ codes a ↔ code a (rep k)=k) a k

theorem code_normalized (a : BitVec 3) (x : Row) : code a (rep (code a x))=code a x :=
  (by decide +kernel : ∀ a p u, code a (rep (code a (p,u,0)))=code a (p,u,0)) a x.1 x.2.1

theorem code_count (a : BitVec 3) :
    (codes a).Nodup ∧ (codes a).length = 2*Nat.gcd 8 a.toNat :=
  (by decide +kernel : ∀ a, (codes a).Nodup ∧ (codes a).length=2*Nat.gcd 8 a.toNat) a

def quotientCode (a b : BitVec 3) (even : b.setWidth 1=0) :
    Quot (Related a b) → BitVec 4 :=
  Quot.lift (code a) (fun x y h => (relation_iff_code a b even x y).mp h)

theorem quotientCode_injective (a b : BitVec 3) (even : b.setWidth 1=0) :
    Function.Injective (quotientCode a b even) := by
  intro x y
  induction x using Quot.ind with
  | mk p =>
    induction y using Quot.ind with
    | mk q =>
      intro h
      exact Quot.sound ((relation_iff_code a b even p q).mpr h)

theorem quotientCode_mem (a b : BitVec 3) (even : b.setWidth 1=0) (x : Quot (Related a b)) :
    quotientCode a b even x ∈ codes a := by
  induction x using Quot.ind with
  | mk p => exact (mem_codes a _).mpr (code_normalized a p)

theorem quotientCode_hits (a b : BitVec 3) (even : b.setWidth 1=0) (k : BitVec 4)
    (h : k ∈ codes a) : ∃ x, quotientCode a b even x=k :=
  ⟨Quot.mk _ (rep k),(mem_codes a k).mp h⟩

/-- Any exhaustive list without repetition computes the same cardinal as the
canonical reduced rows, independently of the ordering of arithmetic classes. -/
theorem enumeration_count (a b : BitVec 3) (even : b.setWidth 1=0)
    (rows : List (Quot (Related a b))) (nodup : rows.Nodup) (hits : ∀ q, q ∈ rows) :
    rows.length=2*Nat.gcd 8 a.toNat := by
  let f := quotientCode a b even
  have nd : (rows.map f).Nodup :=
    List.pairwise_map.mpr (nodup.imp (fun {x y} ne eq => ne (quotientCode_injective a b even eq)))
  have perm := (List.perm_ext_iff_of_nodup nd (code_count a).1).mpr (by
    intro k
    constructor
    · intro hk
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp hk
      exact quotientCode_mem a b even q
    · intro hk
      obtain ⟨q,hq⟩ := quotientCode_hits a b even k hk
      exact List.mem_map.mpr ⟨q,hits q,hq⟩)
  simpa only [List.length_map,(code_count a).2] using perm.length_eq

/-- Finite field-control obligation.  These are the classes of the genuine
γ-coinvariants modulo 8, counted via the reduced forms of discriminant −276. -/
def BottomControl (c0 c1 : Scalar) : Prop :=
  ∃ rows : List (Quot (Related (c0.residue 2) (c1.residue 2))),
    rows.Nodup ∧ (∀ q, q ∈ rows) ∧ rows.length=(reducedForms 276).length

/-- A reduced-form parametrization of the bottom quotient discharges the list
count. Injectivity is required only on reduced primitive forms. -/
theorem control_of_form_correspondence {c0 c1 : Scalar}
    (value : Form → Quot (Related (c0.residue 2) (c1.residue 2)))
    (unique : ∀ x ∈ reducedForms 276, ∀ y ∈ reducedForms 276, value x=value y → x=y)
    (covers : ∀ q, ∃ x ∈ reducedForms 276, value x=q) : BottomControl c0 c1 := by
  refine ⟨(reducedForms 276).map value,?_,fun q => List.mem_map.mpr (covers q),List.length_map value⟩
  apply List.pairwise_map.mpr
  exact two_form_counts.2.1.imp_of_mem (fun {x y} hx hy ne eq => ne (unique x hx y hy eq))

theorem constant_of_bottom_control {c0 c1 : Scalar} (even : c1.residue 0=0)
    (control : BottomControl c0 c1) : c0.residue 2=4 := by
  have ev := (c1.reduce (by decide : 0≤2)).trans even
  obtain ⟨rows,nd,hits,card⟩ := control
  have count := enumeration_count (c0.residue 2) (c1.residue 2) ev rows nd hits
  rw [card,two_form_counts.1] at count
  exact (by decide : ∀ x : BitVec 3, 8=2*Nat.gcd 8 x.toNat → x=4) _ count

/-- P. 134 of Mizusawa reports C₁ modulo four in the square-residue branch.
The second input is the list form of the bottom control comparison. -/
theorem samples_from_bottom_control {c0 c1 : Scalar} (control : BottomControl c0 c1)
    (linear : c1.residue 1=2) : WeightOneSamples c0 c1 := by
  have even : c1.residue 0=0 := by rw [←c1.reduce (by decide : 0≤1),linear]; rfl
  exact sample_bits_of_coefficients c0 c1 (constant_of_bottom_control even control) linear

theorem weighted_jet_from_bottom_control {c0 c1 : Scalar} (control : BottomControl c0 c1)
    (linear : c1.residue 1=2) : WeightedJet c0 c1 :=
  (weighted_jet_iff_samples c0 c1).mpr (samples_from_bottom_control control linear)

/-- The abelianized action in Mizusawa's ordered generators A,B,C.  The
torsion coordinate reads the exponent of A in γC. -/
def forward (c0 c1 : Scalar) (x : BitVec 1 × Scalar × Scalar) :
    BitVec 1 × Scalar × Scalar :=
  (x.1+c1.residue 0*x.2.2.residue 0, act (DyadicLayers.companion c0 c1) x.2)

theorem forward_difference_mod_eight (c0 c1 : Scalar) (x : BitVec 1 × Scalar × Scalar) :
    let y := forward c0 c1 x
    (y.1-x.1, y.2.1.residue 2-x.2.1.residue 2, y.2.2.residue 2-x.2.2.residue 2) =
      ((c1.residue 2).setWidth 1*(x.2.2.residue 2).setWidth 1,
       -(c0.residue 2)*x.2.2.residue 2, x.2.1.residue 2-c1.residue 2*x.2.2.residue 2) := by
  dsimp only
  rw [c1.reduce (by decide : 0≤2), x.2.2.reduce (by decide : 0≤2)]
  apply Prod.ext
  · exact (by decide : ∀ a b : BitVec 1, a+b-a=b) _ _
  · apply Prod.ext
    · exact (by decide : ∀ a s t : BitVec 3, 1*s + -a*t-s = -a*t) _ _ _
    · exact (by decide : ∀ b s t : BitVec 3, 1*s+(1+ -b)*t-t=s-b*t) _ _ _

/-- The finite relation is the reduction of the full scalar lattice image
(γ−1)M. Every finite image witness lifts to coherent scalar coordinates. -/
theorem relation_is_forward_coinvariant (c0 c1 : Scalar) (x y : Row) :
    Related (c0.residue 2) (c1.residue 2) x y ↔
    ∃ z : BitVec 1 × Scalar × Scalar, let w := forward c0 c1 z
      (x.1-y.1, x.2.1-y.2.1, x.2.2-y.2.2) =
      (w.1-z.1, w.2.1.residue 2-z.2.1.residue 2, w.2.2.residue 2-z.2.2.residue 2) := by
  constructor
  · rintro ⟨s,t,hA,hB,hC⟩
    let z : BitVec 1 × Scalar × Scalar := (0,natScalar s.toNat,natScalar t.toNat)
    refine ⟨z,?_⟩
    dsimp only
    rw [forward_difference_mod_eight c0 c1 z]
    simp only [z,natScalar,BitVec.ofNat_toNat]
    exact Prod.ext hA (Prod.ext hB hC)
  · rintro ⟨z,h⟩
    dsimp only at h
    rw [forward_difference_mod_eight c0 c1 z] at h
    exact ⟨z.2.1.residue 2,z.2.2.residue 2,(Prod.mk.inj h).1,
      (Prod.mk.inj (Prod.mk.inj h).2).1,(Prod.mk.inj (Prod.mk.inj h).2).2⟩

/-- The signed numerator on the inverse-generator fibre is negative at
exponent one. The positive sign at argument five belongs to exponent three.
These four literal integers are independent of the characteristic polynomial. -/
theorem oriented_numerators :
    let χ := DyadicZeroValues.chi276
    (SignedBernoulliPairing.rawFibre χ 13 16 69,
     SignedBernoulliPairing.rawFibre χ 5 16 69) = (-2208,2208) ∧
    (SignedBernoulliPairing.literalFibre χ 13 16 69,
     SignedBernoulliPairing.literalFibre χ 5 16 69) = (-4416,4416) := by
  have h1 := SignedCommonNormalization.gamma_normalization_69 2 1
  have h3 := SignedCommonNormalization.gamma_normalization_69 2 3
  have ⟨arg,rep⟩ := SignedOrientationWitness.order_four_arguments
  obtain ⟨r1,r3⟩ := Prod.mk.inj rep
  have signs := SignedOrientationWitness.first_orientation_witness.1
  rw [arg] at signs
  obtain ⟨s1,s3⟩ := Prod.mk.inj signs
  dsimp only at h1 h3 ⊢
  rw [r1,s1] at h1
  rw [r3,s3] at h3
  exact ⟨Prod.ext h1.1 h3.1,Prod.ext h1.2 h3.2⟩

/-- Field-control handoff in the signed series' inverse-exponent convention. -/
theorem oriented_weighted_jet_from_bottom_control {c0 c1 : Scalar} (control : BottomControl c0 c1)
    (linear : c1.residue 1=2) : WeightedJet c0 c1 ∧
      (SignedBernoulliPairing.rawFibre DyadicZeroValues.chi276 13 16 69,
       SignedBernoulliPairing.rawFibre DyadicZeroValues.chi276 5 16 69) = (-2208,2208) :=
  ⟨weighted_jet_from_bottom_control control linear,oriented_numerators.1⟩

end Reimann.DyadicControlJet69
