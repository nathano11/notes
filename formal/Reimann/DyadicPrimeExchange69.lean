import Reimann.DyadicEmbeddedBase69
import Reimann.DyadicGalois69

/-! The action on the two dyadic centers of a bottom-field sign change. -/
namespace Reimann.DyadicPrimeExchange69

open Lean.Grind Reimann.DyadicArithmetic69 Reimann.DyadicBottomValue69
open Reimann.DyadicDecomposition69 Reimann.DyadicPlaceAction69 Reimann.DyadicGalois69
open Reimann.DyadicFiberDescent (coordinateKernel)
open Reimann.TameRationalField277

variable {F : Type} [Field F]
attribute [local instance] Ring.intCast

/-- The field involution on the actual ring of algebraic integers localized at two. -/
def orderAction (s t : Bool) (x : LocalIntegers) : LocalIntegers :=
  ⟨fieldAction s t x.val,(integers_localized_at_two _).mpr
    (action_odd_denominator s t ((integers_localized_at_two _).mp x.property))⟩

theorem order_action_involution (s t : Bool) (x : LocalIntegers) :
    orderAction s t (orderAction s t x)=x :=
  Subtype.ext (action_involution s t x.val)

theorem order_kernel_action (s t i : Bool) (x : LocalIntegers) :
    coordinateKernel residueMap i (orderAction s t x) ↔ coordinateKernel residueMap (Bool.xor i t) x := by
  have h := odd_denominator_kernel s t i ((integers_localized_at_two _).mp x.property)
  have e : (if t then !i else i)=Bool.xor i t := by cases i <;> cases t <;> rfl
  rw [e] at h
  exact h

theorem image_zero_after_action (f : Embedding F) (s t : Bool) (x : Biquad) :
    f.app (fieldAction s t x)=0 ↔ f.app x=0 := by
  have z := (Reimann.DyadicEmbeddedBase69.map_zero_one f).1
  constructor
  · intro h
    have e := congrArg (fieldAction s t) (f.faithful _ h)
    rw [action_involution,fieldAction_scalar] at e
    exact e ▸ z
  · intro h
    rw [f.faithful _ h,fieldAction_scalar,z]

/-- Pullback of the valuation through the automorphism on the bottom field.
Only the displayed value identity is required from the ambient pullback. -/
theorem centered_sign_transport (f : Embedding F) (V W : DyadicValue F) (s t i : Bool)
    (hi : Centered f V i)
    (hval : ∀ x : Biquad, W.val (f.app x)=V.val (f.app (fieldAction s t x))) :
    Centered f W (Bool.xor i t) := by
  constructor
  · intro x
    rw [hval]
    exact hi.nonneg (orderAction s t x)
  · intro x
    rw [hval,← order_kernel_action s t i x,hi.center (orderAction s t x)]
    exact or_congr (image_zero_after_action f s t x.val) Iff.rfl

theorem center_unique (f : Embedding F) (V : DyadicValue F) {i j : Bool}
    (hi : Centered f V i) (hj : Centered f V j) : i=j := by
  have h : coordinateKernel residueMap i=coordinateKernel residueMap j := by
    funext x
    exact propext ((hi.center x).trans (hj.center x).symm)
  cases i <;> cases j
  · rfl
  · exact False.elim (residue_fields.1 h)
  · exact False.elim (residue_fields.1 h.symm)
  · rfl

theorem pullback_label_iff (f : Embedding F) (V W : DyadicValue F) (s t i j : Bool)
    (hi : Centered f V i)
    (hval : ∀ x : Biquad, W.val (f.app x)=V.val (f.app (fieldAction s t x))) :
    Centered f W j ↔ j=Bool.xor i t := by
  have h := centered_sign_transport f V W s t i hi hval
  exact ⟨fun h' => center_unique f W h' h,fun e => e ▸ h⟩

attribute [local instance] Semiring.natCast

theorem fixed_integers (g : F → F) (h0 : g 0=0) (h1 : g 1=1)
    (hadd : ∀ x y, g (x+y)=g x+g y) (m : Int) : g (m:F)=(m:F) := by
  have natfix (n : Nat) : g (n:F)=(n:F) := by
    induction n with
    | zero => simpa only [Semiring.natCast_zero] using h0
    | succ n ih => rw [Semiring.natCast_succ,hadd,ih,h1]
  cases m with
  | ofNat n =>
    change g (((n:Int):F))=((n:Int):F)
    rw [Ring.intCast_natCast]
    exact natfix n
  | negSucc n =>
    have en : ((Int.negSucc n : Int):F)= -((n+1:Nat):F) := by
      rw [Int.negSucc_eq,Ring.intCast_neg,Ring.intCast_add,Ring.intCast_natCast,
        Ring.intCast_one,Semiring.natCast_succ]
    rw [en]
    have h := hadd (-((n+1:Nat):F)) ((n+1:Nat):F)
    rw [show -((n+1:Nat):F)+((n+1:Nat):F)=0 by grind,h0,natfix] at h
    grind

theorem fixed_rationals (f : Embedding F) (g : F → F) (h0 : g 0=0) (h1 : g 1=1)
    (hadd : ∀ x y, g (x+y)=g x+g y) (hmul : ∀ x y, g (x*y)=g x*g y) (q : Rat) :
    g (f.app (scalar q))=f.app (scalar q) := by
  have fix (k : Int) : g (f.app (scalar (k:Rat)))=f.app (scalar (k:Rat)) := by
    rw [f.scalar_int]
    exact fixed_integers g h0 h1 hadd k
  let den := f.app (scalar ((q.den:Int):Rat))
  have dn : den ≠ 0 := positive_integer_nonzero f q.den q.den_pos
  have he : f.app (scalar q)*den = f.app (scalar (q.num:Rat)) := by
    rw [← f.mul,(scalar_embedding _ _).2.2,rational_numerator]
  have h := congrArg g he
  rw [hmul,fix q.num,show g den=den from fix q.den,← he] at h
  have hz : (g (f.app (scalar q))-f.app (scalar q))*den=0 := by grind
  have := (Field.of_mul_eq_zero hz).resolve_right dn
  grind

theorem action_on_bottom_of_generators (f : Embedding F) (g : F → F) (s t : Bool)
    (hadd : ∀ x y, g (x+y)=g x+g y) (hmul : ∀ x y, g (x*y)=g x*g y)
    (hq : ∀ q, g (f.app (scalar q))=f.app (scalar q))
    (h3 : g (f.app gen3)=f.app (fieldAction s t gen3))
    (h23 : g (f.app gen23)=f.app (fieldAction s t gen23)) (z : Biquad) :
    g (f.app z)=f.app (fieldAction s t z) := by
  obtain ⟨⟨a,b⟩,c,d⟩ := z
  rw [← basis_expansion]
  have ha := field_action_end s t
  simp only [ha.onAdd,ha.onMul,ha.onScalar,f.add,f.mul,hadd,hmul,hq,h3,h23]

/-- The ambient endomorphism sends each radical of rational square to one of its two signs. -/
theorem radical_image_sign (f : Embedding F) (g : F → F)
    (hmul : ∀ x y, g (x*y)=g x*g y) (fix : ∀ q, g (f.app (scalar q))=f.app (scalar q))
    (x : Biquad) (q : Rat) (hx : bm x x=scalar q) :
    ∃ s : Bool, g (f.app x)=if s then -(f.app x) else f.app x := by
  have sq : g (f.app x)*g (f.app x)=f.app x*f.app x := by
    rw [← hmul,← f.mul,hx,fix]
  have hz : (g (f.app x)-f.app x)*(g (f.app x)+f.app x)=0 := by grind
  rcases Field.of_mul_eq_zero hz with hp | hm
  · exact ⟨false,by simp; grind⟩
  · exact ⟨true,by simp; grind⟩

/-- The sign of √−23 determines the exchanging sign on the whole bottom field. -/
theorem bottom_sign_at_gen23 (f : Embedding F) (g : F → F) (t : Bool)
    (h0 : g 0=0) (h1 : g 1=1) (hadd : ∀ x y, g (x+y)=g x+g y)
    (hmul : ∀ x y, g (x*y)=g x*g y)
    (h23 : g (f.app gen23)=if t then -(f.app gen23) else f.app gen23) :
    ∃ s : Bool, ∀ z : Biquad, g (f.app z)=f.app (fieldAction s t z) := by
  have fix := fixed_rationals f g h0 h1 hadd hmul
  obtain ⟨s,es⟩ := radical_image_sign f g hmul fix gen3 (-3) generator_squares.1
  apply Exists.intro s
  apply action_on_bottom_of_generators f g s t hadd hmul fix
  · rw [(actions_on_generators s t).1]
    cases s <;> simpa [Reimann.DyadicEmbeddedBase69.map_neg] using es
  · rw [(actions_on_generators s t).2]
    cases t <;> simpa [Reimann.DyadicEmbeddedBase69.map_neg] using h23

/-- To use an Artin lift B as the conjugator between the dyadic places,
its arithmetic sign on √−23 suffices. -/
theorem artin_place_exchange (f : Embedding F) (B : F → F) (V W : DyadicValue F)
    (h0 : B 0=0) (h1 : B 1=1) (hadd : ∀ x y, B (x+y)=B x+B y)
    (hmul : ∀ x y, B (x*y)=B x*B y) (h23 : B (f.app gen23)= -(f.app gen23))
    (i : Bool) (hi : Centered f V i) (pull : ∀ z : Biquad, W.val (f.app z)=V.val (B (f.app z))) :
    Centered f W (!i) ∧ ¬ Centered f W i := by
  obtain ⟨s,hs⟩ := bottom_sign_at_gen23 f B true h0 h1 hadd hmul h23
  have e := centered_sign_transport f V W s true i hi (fun z => (pull z).trans (congrArg V.val (hs z)))
  have ht : Bool.xor i true= !i := by cases i <;> rfl
  rw [ht] at e
  exact ⟨e,fun h => (by cases i <;> decide : (!i) ≠ i) (center_unique f W e h)⟩

/-- Exchange of the two places is equivalent to the nontrivial sign at √−23. -/
theorem exchange_iff_negates_gen23 (f : Embedding F) (B : F → F) (V W : DyadicValue F)
    (h0 : B 0=0) (h1 : B 1=1) (hadd : ∀ x y, B (x+y)=B x+B y)
    (hmul : ∀ x y, B (x*y)=B x*B y)
    (i : Bool) (hi : Centered f V i) (pull : ∀ z : Biquad, W.val (f.app z)=V.val (B (f.app z))) :
    Centered f W (!i) ↔ B (f.app gen23)= -(f.app gen23) := by
  constructor
  · intro move
    obtain ⟨t,ht⟩ := radical_image_sign f B hmul (fixed_rationals f B h0 h1 hadd hmul)
      gen23 (-23) generator_squares.2
    cases t with
    | true => exact ht
    | false =>
      obtain ⟨s,hs⟩ := bottom_sign_at_gen23 f B false h0 h1 hadd hmul ht
      have fixed := centered_sign_transport f V W s false i hi (fun z => (pull z).trans (congrArg V.val (hs z)))
      rw [show Bool.xor i false=i by cases i <;> rfl] at fixed
      exact False.elim ((by cases i <;> decide : (!i) ≠ i) (center_unique f W move fixed))
  · intro ht
    exact (artin_place_exchange f B V W h0 h1 hadd hmul ht i hi pull).1

end Reimann.DyadicPrimeExchange69
