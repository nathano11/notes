import Reimann.DyadicAbsolutePlace69
import Reimann.DyadicArtinImage69
import Reimann.DyadicAutomorphism69
import Reimann.DyadicAbelianTower69

/-! The chosen field lift, its conjugate at the second place, and its image
in the split unramified quotient. -/
namespace Reimann.DyadicArtinPlace69

open Lean.Grind Reimann.Transfer Reimann.TameRestriction Reimann.DyadicLift
open Reimann.DyadicArtinCommutator69 Reimann.DyadicArtinImage69
open Reimann.DyadicLocalRestriction69
open Reimann.DyadicPlaceProduct

theorem commutator_times_lifts {G : Type} (P : GroupLaw G) (B d : G) :
    P.add (P.add (commutator P B d) d) B = P.add B d := by
  simp only [commutator,P.assoc,P.neg_add,P.add_zero]

/-- The subgroup H of N fixing the embedded lower field pointwise. -/
def fixingLower {G K L : Type} {P : GroupLaw G} (A : DyadicRestrictionTower69.PlaceAction P L)
    (N : Subgroup P) (j : K → L) : Subgroup (subgroupLaw N) where
  mem g := ∀ x, A.move g.val (j x) = j x
  identity x := A.one (j x)
  product := by intro g h hg hh x; change A.move (P.add g.val h.val) (j x) = j x; rw [A.comp,hh,hg]
  inverse := by
    intro g hg x
    change A.move (P.neg g.val) (j x)=j x
    calc
      _ = A.move (P.neg g.val) (A.move g.val (j x)) := congrArg _ (hg x).symm
      _ = j x := by rw [←A.comp,P.neg_add,A.one]

/-- Commutation of the two restricted field automorphisms places the actual
upper commutator in H. It suffices that B and d individually restrict. -/
theorem commutator_fixes_lower {G K L : Type} {P : GroupLaw G} (A : DyadicRestrictionTower69.PlaceAction P L)
    (j : K → L) (B d : G) (b t : K → K)
    (b_onto : Function.Surjective b) (t_onto : Function.Surjective t)
    (rB : ∀ x, A.move B (j x)=j (b x)) (rd : ∀ x, A.move d (j x)=j (t x))
    (commute : ∀ x, b (t x)=t (b x)) (x : K) :
    A.move (commutator P B d) (j x)=j x := by
  obtain ⟨u,hu⟩ := t_onto x
  obtain ⟨v,hv⟩ := b_onto u
  have e := congrArg (fun g => A.move g (j v)) (commutator_times_lifts P B d)
  simpa only [A.comp,rB,rd,commute,hv,hu] using e

theorem project_fixed_commutator {G K L : Type} {P : GroupLaw G} (A : DyadicRestrictionTower69.PlaceAction P L)
    (j : K → L) (N : Subgroup P) (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (B : Subtype N.mem) (d : G) (hd : ∀ x : Subtype N.mem, N.mem (conjugate P d x.val))
    (ha : ∀ a : Subtype D.mem, D.mem ((ambientConjugation N d hd).app a.val))
    (fixed : ∀ x, A.move (commutator P B.val d) (j x)=j x) :
    ∃ h : Subtype (fixingLower A N j).mem,
      h.val.val=commutator P B.val d ∧
      (inclusion (fixingLower A N j) D hD).app (cls (intersection (fixingLower A N j) D) h) =
        (targetLaw D hD).add (cls D B) ((targetLaw D hD).neg
          ((induced D hD (ambientConjugation N d hd) ha).app (cls D B))) := by
  exact ⟨⟨commInN N B d hd,fixed⟩,rfl,artin_commutator N D hD B d hd ha⟩

open Reimann.DyadicAutomorphism69 (law push primeAction conjugate_stabilizes stabilizes_iff)
open Reimann.DyadicDecomposition69 (DyadicValue)

def onElements (K : Type) [Field K] : DyadicRestrictionTower69.PlaceAction (law K) K where
  move g := g.app
  one _ := rfl
  comp _ _ _ := rfl

theorem pushed_lower_prime {F : Type} [Field F] (f : DyadicBottomValue69.Embedding F)
    (C : RootTower F) (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C)
    (i : Bool) (V W : DyadicValue F) (hV : DyadicBottomValue69.Centered f V i)
    (hW : DyadicBottomValue69.Centered f W (!i)) (B : Automorphism F)
    (hs : B.app (f.app TameRationalField277.gen23) = -(f.app TameRationalField277.gen23)) :
    push B (Supports V) = Supports W := by
  rw [DyadicAutomorphism69.push_supports]
  exact congrArg Supports (DyadicAbsolutePlace69.switcher_transports_place f C hL i V W hV hW _
    (DyadicAutomorphism69.inverse_negates B _ hs))

/-- The second upper prime obtained by pushing p along B contracts to the
opposite labeled dyadic ideal wherever the lower center is tested. The test
domain S may be the ring of integers, or the valuation ring. -/
theorem switched_prime_contracts {F Ω : Type} [Field F] [Field Ω]
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (i : Bool)
    (V W : DyadicValue F) (hV : DyadicBottomValue69.Centered f V i)
    (hW : DyadicBottomValue69.Centered f W (!i)) (j : F → Ω)
    (B : Automorphism Ω) (β : Automorphism F) (rB : ∀ x, B.app (j x)=j (β.app x))
    (hs : β.app (f.app TameRationalField277.gen23)= -(f.app TameRationalField277.gen23))
    (p : Ω → Prop) (S : F → Prop) (stable : ∀ x, S x → S ((DyadicAutomorphism69.inverse β).app x))
    (contract : ∀ x, S x → (p (j x) ↔ Supports V x)) (x : F) (hx : S x) :
    push B p (j x) ↔ Supports W x := by
  have up := congrFun (DyadicAutomorphism69.push_contraction j B β rB p) x
  have lo := congrFun (pushed_lower_prime f C hL i V W hV hW β hs) x
  exact (Iff.of_eq up).trans ((contract _ (stable x hx)).trans (Iff.of_eq lo))

theorem conjugated_lift_restricts {F Ω : Type} [Field F] [Field Ω]
    (j : F → Ω) (B d : Automorphism Ω) (β t : Automorphism F)
    (rB : ∀ x, B.app (j x)=j (β.app x)) (rd : ∀ x, d.app (j x)=j (t.app x))
    (commute : ∀ x, β.app (t.app x)=t.app (β.app x)) (x : F) :
    (conjugate (law Ω) B d).app (j x)=j (t.app x) := by
  obtain ⟨u,rfl⟩ := β.surjective x
  have e := congrArg (fun g : Automorphism Ω => g.app (j u)) (conjugate_times (law Ω) B d)
  change (conjugate (law Ω) B d).app (B.app (j u))=B.app (d.app (j u)) at e
  simpa only [rB,rd,commute] using e

/-- The very same field lift d that stabilizes the first upper prime produces
the local lift at the switched prime and the class b−t b. No commutation
hypothesis on the genus-field automorphisms is needed. -/
theorem artin_commutator_at_second_place {F Ω : Type} [Field F] [Field Ω]
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C)
    (j : F → Ω) (N : Subgroup (law Ω)) (D : Subgroup (subgroupLaw N)) (hD : Normal D)
    (B : Subtype N.mem) (β t : Automorphism F) (d : Automorphism Ω)
    (rB : ∀ x, B.val.app (j x)=j (β.app x)) (rd : ∀ x, d.app (j x)=j (t.app x))
    (p : Ω → Prop) (local_d : ∀ y, p (d.app y) ↔ p y)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate (law Ω) d x.val))
    (ha : ∀ u : Subtype D.mem, D.mem ((ambientConjugation N d hd).app u.val)) :
    (∀ x, (conjugate (law Ω) B.val d).app (j x)=j (t.app x)) ∧
    push (conjugate (law Ω) B.val d) (push B.val p) = push B.val p ∧
    ∃ h : Subtype (fixingLower (onElements Ω) N j).mem,
      h.val.val = commutator (law Ω) B.val d ∧
      (inclusion (fixingLower (onElements Ω) N j) D hD).app
        (cls (intersection (fixingLower (onElements Ω) N j) D) h) =
        (targetLaw D hD).add (cls D B) ((targetLaw D hD).neg
          ((induced D hD (ambientConjugation N d hd) ha).app (cls D B))) := by
  refine ⟨conjugated_lift_restricts j B.val d β t rB rd (DyadicAbelianTower69.automorphisms_commute f C hL β t),
    conjugate_stabilizes B.val d p ((stabilizes_iff d p).mpr local_d),?_⟩
  apply project_fixed_commutator (onElements Ω) j N D hD B d hd ha
  exact commutator_fixes_lower (onElements Ω) j B.val d β.app t.app
    β.surjective t.surjective rB rd (DyadicAbelianTower69.automorphisms_commute f C hL β t)

/-- The decomposition subgroup in N for the specified prime p of the upper field. -/
def primeStabilizer {Ω : Type} [Field Ω] (N : Subgroup (law Ω)) (p : Ω → Prop) :
    Subgroup (subgroupLaw N) where
  mem g := push g.val p=p
  identity := (primeAction Ω).one p
  product := by
    intro g h hg hh
    change (primeAction Ω).move ((law Ω).add g.val h.val) p=p
    rw [(primeAction Ω).comp]
    change push g.val (push h.val p)=p
    rw [hh,hg]
  inverse := by
    intro g hg
    have e := (primeAction Ω).comp ((law Ω).neg g.val) g.val p
    change push g.val p=p at hg
    change _ = push _ (push g.val p) at e
    rw [(law Ω).neg_add,(primeAction Ω).one,hg] at e
    exact e.symm

theorem local_lift_preserves_decomposition {Ω : Type} [Field Ω]
    (N : Subgroup (law Ω)) (p : Ω → Prop) (d : Automorphism Ω)
    (local_d : ∀ y, p (d.app y) ↔ p y)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate (law Ω) d x.val))
    (u : Subtype (primeStabilizer N p).mem) :
    (primeStabilizer N p).mem ((ambientConjugation N d hd).app u.val) := by
  have h := conjugate_stabilizes d u.val.val p u.property
  rw [(stabilizes_iff d p).mpr local_d] at h
  exact h

/-- In the quotient by the actual dyadic decomposition subgroup of N, the
projected second-place commutator is (1−t)b. Normality of this subgroup
in N is the arithmetic hypothesis needed to form the group quotient. -/
theorem split_artin_commutator {F Ω : Type} [Field F] [Field Ω]
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (j : F → Ω)
    (N : Subgroup (law Ω)) (p : Ω → Prop) (hD : Normal (primeStabilizer N p))
    (B : Subtype N.mem) (β t : Automorphism F) (d : Automorphism Ω)
    (rB : ∀ x, B.val.app (j x)=j (β.app x)) (rd : ∀ x, d.app (j x)=j (t.app x))
    (local_d : ∀ y, p (d.app y) ↔ p y)
    (hd : ∀ x : Subtype N.mem, N.mem (conjugate (law Ω) d x.val)) :
    let D := primeStabilizer N p
    let H := fixingLower (onElements Ω) N j
    let b := cls D B
    let tY := induced D hD (ambientConjugation N d hd) (local_lift_preserves_decomposition N p d local_d hd)
    (∀ x, (conjugate (law Ω) B.val d).app (j x)=j (t.app x)) ∧
    push (conjugate (law Ω) B.val d) (push B.val p) = push B.val p ∧
    ∃ h : Subtype H.mem, h.val.val=commutator (law Ω) B.val d ∧
      (inclusion H D hD).app (cls (intersection H D) h) =
        (targetLaw D hD).add b ((targetLaw D hD).neg (tY.app b)) :=
  artin_commutator_at_second_place f C hL j N _ hD B β t d rB rd p local_d hd
    (local_lift_preserves_decomposition N p d local_d hd)

/-- A lift with the same genus restriction as B which lies in D puts [B]
in the image of H=ker(res) in N/D. -/
theorem class_of_equal_restriction {N U : Type} {G : GroupLaw N} {Q : GroupLaw U}
    (res : Hom G Q) (D : Subgroup G) (hD : Normal D) (B d : N)
    (hd : D.mem d) (same : res.app d=res.app B) :
    (imageSubgroup (kernel res) D hD).mem (cls D B) := by
  let h : Subtype (kernel res).mem :=
    ⟨G.add B (G.neg d),same_image_difference res B d same⟩
  refine ⟨h,?_⟩
  let π := projection D hD
  have hk : π.app (G.neg d)=(targetLaw D hD).zero := (projection_kernel D _).mpr (D.inverse hd)
  change π.app (G.add B (G.neg d))=π.app B
  rw [π.preserves_add,hk,(targetLaw D hD).add_zero]

/-- Once the Artin class of B lies outside X=im(H→Y), the two-prime
fiber forces B to switch the places. This supplies a coset test independent
of computing the action of a named arithmetic lift on √−23. -/
theorem outside_class_switches_prime {N U W : Type} {G : GroupLaw N} {Q : GroupLaw U}
    (res : Hom G Q) (A : DyadicRestrictionTower69.PlaceAction G W)
    (C : DyadicRestrictionTower69.PlaceAction Q Bool) (below : W → Bool) (p : W)
    (equivariant : ∀ g w, below (A.move g w)=C.move (res.app g) (below w))
    (extend : ∀ t, ∃ g, res.app g=t)
    (transitive : ∀ w, below w=below p → ∃ k, res.app k=Q.zero ∧ A.move k w=p)
    (D : Subgroup G) (hD : Normal D) (stabilizer : ∀ g, A.move g p=p → D.mem g)
    (B : N) (outside : ¬(imageSubgroup (kernel res) D hD).mem (cls D B)) :
    C.move (res.app B) (below p)= !(below p) := by
  have neq : C.move (res.app B) (below p)≠below p := by
    intro he
    obtain ⟨d,hres,hfix⟩ := (DyadicRestrictionTower69.decomposition_image_iff res A C below p
      equivariant extend transitive (res.app B)).mpr he
    exact outside (class_of_equal_restriction res D hD B d (stabilizer d hfix) hres)
  cases h : below p <;> cases e : C.move (res.app B) _ <;> simp_all

end Reimann.DyadicArtinPlace69
