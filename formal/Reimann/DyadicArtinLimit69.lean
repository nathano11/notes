import Reimann.DyadicArtinFrobenius69
import Reimann.TameClassField
import Reimann.TameContinuity

/-! Full finite Artin reciprocity descends through the ideal-class map. Norm
compatibility gives a homeomorphism on the coordinatewise 2-primary limits. -/
namespace Reimann.DyadicArtinLimit69

open Reimann.Transfer Reimann.TameClassField Reimann.TameContinuity

/-- Full finite Hilbert reciprocity data. For a number field the ideal class
of a fractional ideal is trivial precisely when that ideal is principal. -/
structure Stage where
  Ideal : Type
  Class : Type
  Gal : Type
  ideals : GroupLaw Ideal
  classes : GroupLaw Class
  galois : GroupLaw Gal
  idealClass : ArtinQuotient ideals classes
  symbol : Hom ideals galois
  onto : ∀ g, ∃ I, symbol.app I=g
  kernel : ∀ I, symbol.app I=galois.zero ↔ idealClass.proj.app I=classes.zero
  abelian : ∀ x y, classes.add x y=classes.add y x

noncomputable def finiteArtin (S : Stage) : Hom S.classes S.galois :=
  descend S.idealClass S.symbol (fun I h => (S.kernel I).mpr h)

theorem artin_of_ideal (S : Stage) (I : S.Ideal) :
    (finiteArtin S).app (S.idealClass.proj.app I)=S.symbol.app I :=
  descend_projects S.idealClass S.symbol _ I

noncomputable def finiteInverse (S : Stage) : Hom S.galois S.classes :=
  descend ⟨S.symbol,S.onto⟩ S.idealClass.proj (fun I h => (S.kernel I).mp h)

theorem class_of_symbol (S : Stage) (I : S.Ideal) :
    (finiteInverse S).app (S.symbol.app I)=S.idealClass.proj.app I :=
  descend_projects ⟨S.symbol,S.onto⟩ S.idealClass.proj _ I

theorem finite_inverse_laws (S : Stage) :
    (∀ c, (finiteInverse S).app ((finiteArtin S).app c)=c) ∧
    (∀ g, (finiteArtin S).app ((finiteInverse S).app g)=g) := by
  constructor
  · intro c
    obtain ⟨I,rfl⟩ := S.idealClass.onto c
    rw [artin_of_ideal,class_of_symbol]
  · intro g
    obtain ⟨I,rfl⟩ := S.onto g
    rw [class_of_symbol,artin_of_ideal]

/-- The Frobenius norm formula on fractional ideals of two adjacent fields. -/
structure Transition (U L : Stage) where
  norm : Hom U.ideals L.ideals
  restriction : Hom U.galois L.galois
  frobenius_norm : ∀ I, L.symbol.app (norm.app I)=restriction.app (U.symbol.app I)

def composeHom {A B C : Type} {P : GroupLaw A} {Q : GroupLaw B} {R : GroupLaw C}
    (h : Hom Q R) (f : Hom P Q) : Hom P R where
  app x := h.app (f.app x)
  preserves_zero := (congrArg h.app f.preserves_zero).trans h.preserves_zero
  preserves_add x y := (congrArg h.app (f.preserves_add x y)).trans (h.preserves_add _ _)
  preserves_neg x := (congrArg h.app (f.preserves_neg x)).trans (h.preserves_neg _)

noncomputable def classNorm {U L : Stage} (r : Transition U L) : Hom U.classes L.classes :=
  composeHom (finiteInverse L) (composeHom r.restriction (finiteArtin U))

theorem class_norm_of_ideal {U L : Stage} (r : Transition U L) (I : U.Ideal) :
    (classNorm r).app (U.idealClass.proj.app I) = L.idealClass.proj.app (r.norm.app I) := by
  change (finiteInverse L).app (r.restriction.app ((finiteArtin U).app _))=_
  rw [artin_of_ideal,← r.frobenius_norm,class_of_symbol]

theorem artin_norm {U L : Stage} (r : Transition U L) (c : U.Class) :
    (finiteArtin L).app ((classNorm r).app c) = r.restriction.app ((finiteArtin U).app c) :=
  (finite_inverse_laws L).2 _

theorem inverse_restriction {U L : Stage} (r : Transition U L) (g : U.Gal) :
    (classNorm r).app ((finiteInverse U).app g) = (finiteInverse L).app (r.restriction.app g) :=
  congrArg (fun t => (finiteInverse L).app (r.restriction.app t)) ((finite_inverse_laws U).2 g)

/-- Norm compatibility only needs to be checked on prime ideals if their
signed words generate all fractional ideals. -/
def prime_norm_transition {U L : Stage} {P : Type} (primes : P → U.Ideal)
    (factor : ∀ I, ∃ w, DyadicArtinFrobenius69.word U.ideals primes w=I)
    (norm : Hom U.ideals L.ideals) (restriction : Hom U.galois L.galois)
    (prime_norm : ∀ p, L.symbol.app (norm.app (primes p))=restriction.app (U.symbol.app (primes p))) :
    Transition U L where
  norm := norm
  restriction := restriction
  frobenius_norm I := by
    obtain ⟨w,rfl⟩ := factor I
    have h := congrArg (fun q => DyadicArtinFrobenius69.word L.galois q w) (funext prime_norm)
    simpa only [DyadicArtinFrobenius69.word_hom] using h

structure System where
  obj : Nat → Type
  law : (n : Nat) → GroupLaw (obj n)
  down : (n : Nat) → Hom (law (n+1)) (law n)

def Coherent (X : System) (c : (n : Nat) → X.obj n) : Prop :=
  ∀ n, (X.down n).app (c (n+1))=c n

/-- The bound on the exponent may depend on the element and the finite level. -/
def TwoPrimary {A : Type} (G : GroupLaw A) (x : A) : Prop := ∃ j : Nat, multiple G (2^j) x=G.zero

abbrev primaryLimit (X : System) :=
  {x : (n : Nat) → X.obj n // Coherent X x ∧ ∀ n, TwoPrimary (X.law n) (x n)}

theorem primary_map {A B : Type} {G : GroupLaw A} {H : GroupLaw B}
    (f : Hom G H) {x : A} (hx : TwoPrimary G x) : TwoPrimary H (f.app x) := by
  obtain ⟨j,hj⟩ := hx
  exact ⟨j,by rw [← hom_multiple G H f,hj,f.preserves_zero]⟩

noncomputable def classSystem (S : Nat → Stage) (r : ∀ n, Transition (S (n+1)) (S n)) :
    System where
  obj n := (S n).Class
  law n := (S n).classes
  down n := classNorm (r n)

def galoisSystem (S : Nat → Stage) (r : ∀ n, Transition (S (n+1)) (S n)) : System where
  obj n := (S n).Gal
  law n := (S n).galois
  down n := (r n).restriction

noncomputable def artinLimit (S : Nat → Stage) (r : ∀ n, Transition (S (n+1)) (S n))
    (c : primaryLimit (classSystem S r)) : primaryLimit (galoisSystem S r) :=
  ⟨fun n => (finiteArtin (S n)).app (c.val n),
    fun n => (artin_norm (r n) _).symm.trans (congrArg (finiteArtin (S n)).app (c.property.1 n)),
    fun n => primary_map (finiteArtin (S n)) (c.property.2 n)⟩

noncomputable def inverseLimit (S : Nat → Stage) (r : ∀ n, Transition (S (n+1)) (S n))
    (g : primaryLimit (galoisSystem S r)) : primaryLimit (classSystem S r) :=
  ⟨fun n => (finiteInverse (S n)).app (g.val n),
    fun n => (inverse_restriction (r n) _).trans (congrArg (finiteInverse (S n)).app (g.property.1 n)),
    fun n => primary_map (finiteInverse (S n)) (g.property.2 n)⟩

theorem inverse_limit_laws (S : Nat → Stage) (r : ∀ n, Transition (S (n+1)) (S n)) :
    (∀ c, inverseLimit S r (artinLimit S r c)=c) ∧
    (∀ g, artinLimit S r (inverseLimit S r g)=g) :=
  ⟨fun c => Subtype.ext (funext (fun n => (finite_inverse_laws (S n)).1 (c.val n))),
   fun g => Subtype.ext (funext (fun n => (finite_inverse_laws (S n)).2 (g.val n)))⟩

/-- A basic neighborhood fixes a finite initial segment of coordinates. -/
def cylinderTopology (X : System) : Topology (primaryLimit X) where
  isOpen U := ∀ x, U x → ∃ N, ∀ y : primaryLimit X, (∀ n ≤ N, y.val n=x.val n) → U y
  univ_open := fun _ _ => ⟨0,fun _ _ => trivial⟩
  inter_open := by
    intro U V hu hv x hx
    obtain ⟨i,hi⟩ := hu x hx.1
    obtain ⟨j,hj⟩ := hv x hx.2
    exact ⟨max i j,fun y h => ⟨hi y (fun n hn => h n (Nat.le_trans hn (Nat.le_max_left i j))),
      hj y (fun n hn => h n (Nat.le_trans hn (Nat.le_max_right i j)))⟩⟩
  local_open := by
    intro S localData x hx
    obtain ⟨U,openU,hU,inside⟩ := localData x hx
    obtain ⟨i,hi⟩ := openU x hU
    exact ⟨i,fun y h => inside y (hi y h)⟩

theorem coordinate_continuous {X Y : System} (f : primaryLimit X → primaryLimit Y)
    (pointwise : ∀ n (x y : primaryLimit X), x.val n=y.val n → (f x).val n=(f y).val n) :
    Continuous (cylinderTopology X) (cylinderTopology Y) f := by
  intro U hu x hx
  obtain ⟨N,hN⟩ := hu (f x) hx
  exact ⟨N,fun y h => hN (f y) (fun n hn => pointwise n y x (h n hn))⟩

theorem artin_homeomorphism (S : Nat → Stage) (r : ∀ n, Transition (S (n+1)) (S n)) :
    Continuous (cylinderTopology (classSystem S r)) (cylinderTopology (galoisSystem S r)) (artinLimit S r) ∧
    Continuous (cylinderTopology (galoisSystem S r)) (cylinderTopology (classSystem S r)) (inverseLimit S r) :=
  ⟨coordinate_continuous _ (fun n _ _ eq => congrArg (finiteArtin (S n)).app eq),
   coordinate_continuous _ (fun n _ _ eq => congrArg (finiteInverse (S n)).app eq)⟩

theorem multiple_identity {A : Type} (G : GroupLaw A) (n : Nat) : multiple G n G.zero = G.zero := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg (fun t => G.add t G.zero) ih).trans (G.zero_add _)

theorem multiple_of_sum {A : Type} (G : GroupLaw A) (comm : ∀ x y, G.add x y=G.add y x)
    (n : Nat) (x y : A) : multiple G n (G.add x y)=G.add (multiple G n x) (multiple G n y) := by
  induction n with
  | zero => exact (G.zero_add _).symm
  | succ n ih =>
    simp only [multiple,ih,G.assoc]
    rw [← G.assoc (multiple G n y) x,comm (multiple G n y) x,G.assoc]

theorem multiple_of_inverse {A : Type} (G : GroupLaw A) (comm : ∀ x y, G.add x y=G.add y x)
    (n : Nat) (x : A) : multiple G n (G.neg x)=G.neg (multiple G n x) := by
  induction n with
  | zero => exact (G.add_neg G.zero).symm.trans (G.zero_add _)
  | succ n ih =>
    simp only [multiple,ih,DyadicArtinCommutator69.inverse_product]
    apply comm

theorem primary_sum {A : Type} (G : GroupLaw A) (comm : ∀ x y, G.add x y=G.add y x)
    {x y : A} (hx : TwoPrimary G x) (hy : TwoPrimary G y) : TwoPrimary G (G.add x y) := by
  obtain ⟨i,hi⟩ := hx
  obtain ⟨j,hj⟩ := hy
  refine ⟨i+j,?_⟩
  have ex : multiple G (2^(i+j)) x=G.zero := by
    rw [Nat.add_comm i j,Nat.pow_add,multiple_mul,hi,multiple_identity]
  have ey : multiple G (2^(i+j)) y=G.zero := by
    rw [Nat.pow_add,multiple_mul,hj,multiple_identity]
  rw [multiple_of_sum G comm,ex,ey,G.zero_add]

theorem primary_inverse {A : Type} (G : GroupLaw A) (comm : ∀ x y, G.add x y=G.add y x)
    {x : A} (hx : TwoPrimary G x) : TwoPrimary G (G.neg x) := by
  obtain ⟨i,hi⟩ := hx
  exact ⟨i,by rw [multiple_of_inverse G comm,hi]; exact (G.zero_add _).symm.trans (G.add_neg _)⟩

def limitLaw (X : System) (comm : ∀ n x y, (X.law n).add x y=(X.law n).add y x) :
    GroupLaw (primaryLimit X) where
  zero := ⟨fun n => (X.law n).zero,fun n => (X.down n).preserves_zero,
    fun n => ⟨0,multiple_identity _ _⟩⟩
  add x y := ⟨fun n => (X.law n).add (x.val n) (y.val n),
    fun n => ((X.down n).preserves_add _ _).trans (by rw [x.property.1 n,y.property.1 n]),
    fun n => primary_sum _ (comm n) (x.property.2 n) (y.property.2 n)⟩
  neg x := ⟨fun n => (X.law n).neg (x.val n),
    fun n => ((X.down n).preserves_neg _).trans (congrArg (X.law n).neg (x.property.1 n)),
    fun n => primary_inverse _ (comm n) (x.property.2 n)⟩
  assoc _ _ _ := Subtype.ext (funext (fun n => (X.law n).assoc _ _ _))
  zero_add _ := Subtype.ext (funext (fun n => (X.law n).zero_add _))
  add_zero _ := Subtype.ext (funext (fun n => (X.law n).add_zero _))
  add_neg _ := Subtype.ext (funext (fun n => (X.law n).add_neg _))
  neg_add _ := Subtype.ext (funext (fun n => (X.law n).neg_add _))

theorem galois_abelian (S : Stage) (x y : S.Gal) : S.galois.add x y=S.galois.add y x := by
  obtain ⟨a,ha⟩ := S.onto x
  obtain ⟨b,hb⟩ := S.onto y
  have he := congrArg (finiteArtin S).app
    (S.abelian (S.idealClass.proj.app a) (S.idealClass.proj.app b))
  simpa only [(finiteArtin S).preserves_add,artin_of_ideal,ha,hb] using he

/-- Arithmetic Frobenius on representatives induces a continuous isomorphism
of the two-primary inverse limits, with continuous inverse. -/
theorem continuous_artin (S : Nat → Stage) (r : ∀ n, Transition (S (n+1)) (S n)) :
    let C := classSystem S r
    let H := galoisSystem S r
    let P := limitLaw C (fun n => (S n).abelian)
    let Q := limitLaw H (fun n => galois_abelian (S n))
    ∃ f : Hom P Q, ∃ j : Hom Q P,
      (∀ c n, (f.app c).val n=(finiteArtin (S n)).app (c.val n)) ∧
      (∀ c, j.app (f.app c)=c) ∧ (∀ g, f.app (j.app g)=g) ∧
      Continuous (cylinderTopology C) (cylinderTopology H) f.app ∧
      Continuous (cylinderTopology H) (cylinderTopology C) j.app := by
  dsimp only
  let f : Hom (limitLaw (classSystem S r) (fun n => (S n).abelian))
      (limitLaw (galoisSystem S r) (fun n => galois_abelian (S n))) :=
    ⟨artinLimit S r,Subtype.ext (funext (fun n => (finiteArtin (S n)).preserves_zero)),
     fun x y => Subtype.ext (funext (fun n => (finiteArtin (S n)).preserves_add _ _)),
     fun x => Subtype.ext (funext (fun n => (finiteArtin (S n)).preserves_neg _))⟩
  let j : Hom (limitLaw (galoisSystem S r) (fun n => galois_abelian (S n)))
      (limitLaw (classSystem S r) (fun n => (S n).abelian)) :=
    ⟨inverseLimit S r,Subtype.ext (funext (fun n => (finiteInverse (S n)).preserves_zero)),
     fun x y => Subtype.ext (funext (fun n => (finiteInverse (S n)).preserves_add _ _)),
     fun x => Subtype.ext (funext (fun n => (finiteInverse (S n)).preserves_neg _))⟩
  exact ⟨f,j,fun _ _ => rfl,(inverse_limit_laws S r).1,(inverse_limit_laws S r).2,artin_homeomorphism S r⟩

/-- Construct the transition by the residue-degree formula and the standard
ideal norm of a prime. The Galois-side hypothesis is the conclusion of
`DyadicArtinResidueNorm69.frobenius_norm_at_prime` for the two fields. -/
def transition_from_prime_norms {U L : Stage} {P : Type}
    (prime : P → U.Ideal) (under : P → L.Ideal) (residueDegree : P → Nat)
    (factor : ∀ I, ∃ w, DyadicArtinFrobenius69.word U.ideals prime w=I)
    (norm : Hom U.ideals L.ideals) (restriction : Hom U.galois L.galois)
    (norm_prime : ∀ p, norm.app (prime p)=multiple L.ideals (residueDegree p) (under p))
    (restrict_prime : ∀ p, restriction.app (U.symbol.app (prime p))=
      multiple L.galois (residueDegree p) (L.symbol.app (under p))) : Transition U L :=
  prime_norm_transition prime factor norm restriction (fun p => by
    rw [norm_prime,hom_multiple,restrict_prime])

end Reimann.DyadicArtinLimit69
