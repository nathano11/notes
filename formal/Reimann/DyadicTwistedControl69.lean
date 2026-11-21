import Reimann.DyadicControlJet69

/-! The same cyclotomic union over k=ℚ(√−69) and k'=ℚ(√−138) has two
relative generators. The arithmetic norm identity gives τ = −1 on X for
complex conjugation τ. Thus γ acts at k, and τγ acts at k'. -/
namespace Reimann.DyadicTwistedControl69

open DyadicLattice DyadicClass69 DyadicControlJet69 DyadicOneSided69

/-- Negation on the abelianized lattice fixes the order-two coordinate. -/
def inversion (x : BitVec 1 × Scalar × Scalar) : BitVec 1 × Scalar × Scalar :=
  (x.1,neg x.2.1,neg x.2.2)

/-- The image of τγ−1 in the original A,B,C basis, modulo 8. -/
def TwistedRelated (a b : BitVec 3) (x y : Row) : Prop :=
  ∃ s t : BitVec 3, x.1-y.1 = b.setWidth 1*t.setWidth 1 ∧
    x.2.1-y.2.1 = -2*s+a*t ∧ x.2.2-y.2.2 = -s+(b-2)*t

theorem inverted_difference (c0 c1 : Scalar) (x : BitVec 1 × Scalar × Scalar) :
    let w := inversion (forward c0 c1 x)
    (w.1-x.1,w.2.1.residue 2-x.2.1.residue 2,w.2.2.residue 2-x.2.2.residue 2) =
    ((c1.residue 2).setWidth 1*(x.2.2.residue 2).setWidth 1,
      -2*x.2.1.residue 2+c0.residue 2*x.2.2.residue 2,
      -x.2.1.residue 2+(c1.residue 2-2)*x.2.2.residue 2) := by
  dsimp only
  rw [c1.reduce (by decide : 0≤2),x.2.2.reduce (by decide : 0≤2)]
  apply Prod.ext
  · change x.1+c1.residue 0*x.2.2.residue 0-x.1=_
    grind
  · apply Prod.ext <;>
      simp only [inversion,forward,DyadicLayers.companion,act,add,mul,neg,natScalar] <;> grind

theorem relation_is_inverted_coinvariant (c0 c1 : Scalar) (x y : Row) :
    TwistedRelated (c0.residue 2) (c1.residue 2) x y ↔
    ∃ z : BitVec 1 × Scalar × Scalar, let w := inversion (forward c0 c1 z)
      (x.1-y.1,x.2.1-y.2.1,x.2.2-y.2.2) =
      (w.1-z.1,w.2.1.residue 2-z.2.1.residue 2,w.2.2.residue 2-z.2.2.residue 2) := by
  constructor
  · rintro ⟨s,t,ha,hb,hc⟩
    let z : BitVec 1 × Scalar × Scalar := (0,natScalar s.toNat,natScalar t.toNat)
    refine ⟨z,?_⟩
    dsimp only
    rw [inverted_difference c0 c1 z]
    simp only [z,natScalar,BitVec.ofNat_toNat]
    exact Prod.ext ha (Prod.ext hb hc)
  · rintro ⟨z,h⟩
    dsimp only at h
    rw [inverted_difference c0 c1 z] at h
    exact ⟨_,_,(Prod.mk.inj h).1,(Prod.mk.inj (Prod.mk.inj h).2).1,(Prod.mk.inj (Prod.mk.inj h).2).2⟩

/-- New generators B'=B and C'=(τγ−1)B=−2B−C. The coordinate change
is its own inverse. -/
def basis (x : Row) : Row := (x.1,x.2.1-2*x.2.2,-x.2.2)

theorem basis_twice (x : Row) : basis (basis x) = x := by
  rcases x with ⟨h,b,c⟩
  simp only [basis,Prod.mk.injEq,true_and]
  grind

/-- The conjugate companion has characteristic polynomial P(−2−T),
with constant term P(−2) and linear coefficient 4−C₁. -/
theorem companion_conjugacy (a b : BitVec 3) (x y : Row) :
    TwistedRelated a b x y ↔ Related (4-2*b+a) (4-b) (basis x) (basis y) := by
  have cb : (4-b).setWidth 1=b.setWidth 1 :=
    (by decide : ∀ z : BitVec 3, (4-z).setWidth 1=z.setWidth 1) b
  have nt : ∀ t : BitVec 3, (-t).setWidth 1=t.setWidth 1 := by decide
  constructor
  · rintro ⟨s,t,ha,hb,hc⟩
    refine ⟨s-2*t,-t,?_,?_,?_⟩
    · simpa only [basis,cb,nt] using ha
    · simp only [basis]; grind
    · simp only [basis]; grind
  · rintro ⟨s,t,ha,hb,hc⟩
    simp only [basis,cb] at ha hb hc
    refine ⟨s-2*t,-t,?_,?_,?_⟩
    · simpa only [nt] using ha
    · grind
    · grind

def toCompanion (a b : BitVec 3) :
    Quot (TwistedRelated a b) → Quot (Related (4-2*b+a) (4-b)) :=
  Quot.lift (fun x => Quot.mk _ (basis x)) (fun x y h => Quot.sound ((companion_conjugacy a b x y).mp h))

def fromCompanion (a b : BitVec 3) :
    Quot (Related (4-2*b+a) (4-b)) → Quot (TwistedRelated a b) :=
  Quot.lift (fun x => Quot.mk _ (basis x)) (fun x y h => Quot.sound
    ((companion_conjugacy a b (basis x) (basis y)).mpr (by simpa only [basis_twice] using h)))

theorem inverse_coordinates (a b : BitVec 3) :
    (∀ x, fromCompanion a b (toCompanion a b x)=x) ∧
    (∀ y, toCompanion a b (fromCompanion a b y)=y) := by
  constructor <;> intro x <;> induction x using Quot.ind with
  | mk u => exact congrArg (Quot.mk _) (basis_twice u)

/-- Compare the genuine τγ-coinvariants to Cl₂(ℚ(√−138))/8. -/
def TwistedBottomControl (c0 c1 : Scalar) : Prop :=
  ∃ rows : List (Quot (TwistedRelated (c0.residue 2) (c1.residue 2))),
    rows.Nodup ∧ (∀ q, q∈rows) ∧ rows.length=(reducedForms 552).length

theorem minus_two_of_twisted_control {c0 c1 : Scalar} (even : c1.residue 0=0)
    (control : TwistedBottomControl c0 c1) :
    (4-2*c1.residue 2+c0.residue 2 : BitVec 3)=4 := by
  let a := c0.residue 2
  let b := c1.residue 2
  let f := toCompanion a b
  have ⟨left,right⟩ := inverse_coordinates a b
  obtain ⟨rows,nd,hits,num⟩ := control
  have ninj : Function.Injective f := fun {x y} e => (left x).symm.trans ((congrArg (fromCompanion a b) e).trans (left y))
  have nd' : (rows.map f).Nodup := List.pairwise_map.mpr (nd.imp (fun {x y} ne eq => ne (ninj eq)))
  have onto : ∀ q, q ∈ rows.map f := fun q => List.mem_map.mpr ⟨_,hits (fromCompanion a b q),right q⟩
  have eb : b.setWidth 1=0 := (c1.reduce (by decide : 0≤2)).trans even
  have e4 : (4-b).setWidth 1=0 :=
    (by decide : ∀ b : BitVec 3, b.setWidth 1=0 → (4-b).setWidth 1=0) b eb
  have card := enumeration_count (4-2*b+a) (4-b) e4 (rows.map f) nd' onto
  rw [List.length_map,num,two_form_counts.2.2.1] at card
  exact (by decide : ∀ k : BitVec 3, 8 = 2*Nat.gcd 8 k.toNat → k=4) _ card

theorem samples_of_two_bottom_controls {c0 c1 : Scalar} (even : c1.residue 0=0)
    (k : BottomControl c0 c1) (k' : TwistedBottomControl c0 c1) :
    DyadicOrder.WeightOneSamples c0 c1 :=
  samples_of_zero_and_minus_two c0 c1 (constant_of_bottom_control even k)
    (minus_two_of_twisted_control even k')

theorem weighted_jet_of_two_bottom_controls {c0 c1 : Scalar} (even : c1.residue 0=0)
    (k : BottomControl c0 c1) (k' : TwistedBottomControl c0 c1) :
    WeightedJet c0 c1 :=
  (weighted_jet_iff_samples c0 c1).mpr (samples_of_two_bottom_controls even k k')

/-- No weight restriction enters this lattice count. The arithmetic strict
comparison uses positive odd r separately. -/
theorem lattice_order_of_two_bottom_controls {c0 c1 : Scalar} (even : c1.residue 0=0)
    (k : BottomControl c0 c1) (k' : TwistedBottomControl c0 c1) (r a : Nat) :
    ∃ encode : Quot (DyadicOrder.latticeCoset c0 c1 r a) → Fin (2^(2*a+1)),
    ∃ decode : Fin (2^(2*a+1)) → Quot (DyadicOrder.latticeCoset c0 c1 r a),
      (∀ x, decode (encode x)=x) ∧ (∀ i, encode (decode i)=i) :=
  DyadicOrder.lattice_order_of_weight_one_samples (samples_of_two_bottom_controls even k k') r a

end Reimann.DyadicTwistedControl69

