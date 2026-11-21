import Reimann.DyadicLocalRestriction69
import Reimann.DyadicUnramifiedBase69
import Reimann.DyadicFiniteRestriction69
import Reimann.DyadicPrimeExchange69

/-! Transfer the unique dyadic center on the cyclotomic field to finite
Galois lifting data and to the two place labels. -/
namespace Reimann.DyadicAbsolutePlace69

open Lean.Grind Reimann.DyadicDecomposition69 Reimann.DyadicLocalRestriction69

variable {F : Type} [Field F]

/-- Lower primes in a finite presentation are tested by contracting the
chosen valuation ideal. Every automorphism over Eₐ satisfies all of their
stability tests, for either chosen prime of E₀. -/
theorem lower_prime_stable {A O : Type} (base : A → O) (intoField : A → F) (P : O → Prop)
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (a : Nat) (i : Bool)
    (V : DyadicValue F) (hV : DyadicBottomValue69.Centered f V i)
    (g : Automorphism F) (fixes : FixesRealLayer (DyadicEmbeddedBase69.baseImage f) C a g)
    (lower : A → A) (compatible : ∀ x, intoField (lower x)=g.app (intoField x))
    (contract : ∀ x, P (base x) ↔ Supports V (intoField x)) :
    ∀ x, P (base (lower x)) ↔ P (base x) := by
  intro x
  rw [contract,contract,compatible]
  exact stabilizes_ideal_of_isometry V g (relative_isometry f C hL i V hV a g fixes) _

/-- In a two-prime fiber the coset of the decomposition subgroup already
determines the exchanged prime. -/
theorem other_label_of_outside {G U : Type} {H : Transfer.GroupLaw G}
    (act : DyadicRestrictionTower69.PlaceAction H Bool) (restrict : G → U) (line : U → Prop)
    (i : Bool) (stab : ∀ g, act.move g i=i ↔ line (restrict g))
    (B : G) (outside : ¬line (restrict B)) : act.move B i = !i := by
  have neq := fun he => outside ((stab B).mp he)
  cases i <;> cases h : act.move B _ <;> simp_all

/-- Conjugating a lift stabilizing the first prime gives an element of the
second stabilizer whenever B exchanges the prime labels. -/
theorem conjugated_local_lift {G : Type} {H : Transfer.GroupLaw G} {W : Type}
    (act : DyadicRestrictionTower69.PlaceAction H W) (v w : W) (B d : G)
    (exchange : act.move B v=w) (fixes : act.move d v=v) :
    act.move (H.add (H.add B d) (H.neg B)) w=w := by
  rw [←exchange,←act.comp]
  have e : H.add (H.add (H.add B d) (H.neg B)) B = H.add B d := by
    rw [H.assoc (H.add B d),H.neg_add,H.add_zero]
  rw [e,act.comp,fixes]

def asRingMap (g : Automorphism F) : DyadicUnramifiedBase69.RingMap F F where
  app := g.app
  zero := g.zero
  one := g.one
  add := g.add
  mul := g.mul
  neg x := by
    have e := g.add x (-x)
    rw [show x+ -x=0 by grind only,g.zero] at e
    grind only

open DyadicFiniteRestriction69 (Tower EmbeddedOrders LowerField InUnionPrime Agrees)

/-- At either actual bottom center, for every a, every automorphism over Eₐ lifts
to a prime-preserving field automorphism on the exhausted upper field. Finite
normal lifts in the hypotheses carry no prime condition. -/
theorem decomposition_lifts_every_automorphism {A O G K : Nat → Type} {Ω : Type}
    [Field Ω] [∀ n, CommRing (O n)] [∀ n, CommRing (K n)]
    {T : Tower A O G} {U : DyadicKernelLift69.UnionTower K G Ω}
    (E : EmbeddedOrders T U) (B : LowerField (K:=F) E)
    (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (a : Nat) (i : Bool)
    (V : DyadicValue F) (hV : DyadicBottomValue69.Centered f V i)
    (P : ∀ n, O n → Prop) (p : ∀ n, DyadicPrimeConjugacy69.ResidueMaximal (P n))
    (contracts : ∀ n x, P (n+1) (T.up n x) ↔ P n x)
    (bottom : ∀ n x, P n ((T.stage n).base x) ↔ Supports V (B.element n x))
    (ordinary_lifts : ∀ g : Automorphism F, FixesRealLayer (DyadicEmbeddedBase69.baseImage f) C a g →
      ∃ t : ∀ n, A n → A n, (∀ n x, B.element n (t n x)=g.app (B.element n x)) ∧
        (∀ n x, t (n+1) (T.lowerUp n x)=T.lowerUp n (t n x)) ∧
        ∀ n, ∃ h, Agrees (T.stage n) h (t n)) :
    ∀ g : Automorphism F, FixesRealLayer (DyadicEmbeddedBase69.baseImage f) C a g →
      ∃ d : Automorphism Ω,
        (∀ x, d.app (B.includeBase.app x)=B.includeBase.app (g.app x)) ∧
        ∀ x, InUnionPrime E P (d.app x) ↔ InUnionPrime E P x := by
  intro g hg
  obtain ⟨t,ht,hc,hl⟩ := ordinary_lifts g hg
  obtain ⟨d,hin,hsur,hres,hprime⟩ := DyadicFiniteRestriction69.union_automorphism_lifting
    E B (asRingMap g) t ht hc P p contracts hl (fun n =>
      lower_prime_stable (T.stage n).base (B.element n) (P n) f C hL a i V hV g hg
        (t n) (ht n) (bottom n))
  exact ⟨⟨d.app,hin,hsur,d.zero,d.one,d.add,d.mul⟩,hres,hprime⟩

/-- Acting on √−23 by the negative sign carries one entire infinite-layer
valuation to the other. The sign on √−3 is unrestricted. -/
theorem switcher_transports_place (f : DyadicBottomValue69.Embedding F) (C : RootTower F)
    (hL : GeneratesField (DyadicEmbeddedBase69.baseImage f) C) (i : Bool)
    (V W : DyadicValue F) (hV : DyadicBottomValue69.Centered f V i)
    (hW : DyadicBottomValue69.Centered f W (!i)) (B : Automorphism F)
    (hs : B.app (f.app TameRationalField277.gen23) = -(f.app TameRationalField277.gen23)) :
    pull V B = W := by
  have he := DyadicPrimeExchange69.artin_place_exchange f B.app V (pull V B)
    B.zero B.one B.add B.mul hs i hV (fun _ => rfl)
  exact infinite_layer_place_unique f C hL (!i) _ _ he.1 hW

end Reimann.DyadicAbsolutePlace69
