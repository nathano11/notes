import Reimann.CircularPolynomialField69
import Reimann.CircularFieldReduction69

/-! Evaluation at two primitive roots defines mutually inverse maps on their generated fields. -/
namespace Reimann.CircularSubstitution69

set_option linter.unusedSectionVars false

open Lean.Grind Lean.Grind.Field.NormNum CircularPolynomialField69 CircularFieldReduction69
  CircularRelationEval69 CircularNormalForm69 CircularMonomial69 CircularIndependence69

variable {R S T : Type} [Field R] [Field S] [Field T]
variable [IsCharP R 0] [IsCharP S 0] [IsCharP T 0]

abbrev Carrier {A : Type} [Field A] (x : A) := {u : A // Generated x u}

def Corresponds (x : R) (z : S) (u : R) (v : S) : Prop :=
  ∃ p, Represents x p u ∧ Represents z p v

theorem same_remainder (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z)
    {u : R} {v : S} (h : Corresponds x z u v) :
    ∃ r, Bounded r 44 ∧ evalAt x r 44 = u ∧ evalAt z r 44 = v := by
  obtain ⟨p,hp,hq⟩ := h
  obtain ⟨m,bp,ep⟩ := hp
  let V (f : Nat → Rat) := Represents x f u ∧ Represents z f v
  have vp : V p := ⟨⟨m,bp,ep⟩,hq⟩
  have closed (f : Nat → Rat) (s : Nat) (a : Rat) (hf : V f) :
      V (fun k => f k - shift s a phiQ k) := by
    exact ⟨same_value_subtract_root x u f _ hf.1
      (vanishes_shift x phiQ s a (primitive_vanishes x hx.order69 hx.not23 hx.not3)),
      same_value_subtract_root z v f _ hf.2
      (vanishes_shift z phiQ s a (primitive_vanishes z hz.order69 hz.not23 hz.not3))⟩
  obtain ⟨_,r,_,br,vr,_⟩ := division_preserving phiQ 44 phiQ_bounded phiQ_monic V closed m p bp vp
  exact ⟨r,br,value_at_bound x r u vr.1 44 br,value_at_bound z r v vr.2 44 br⟩

theorem correspondence_unique {x : R} {z : S} (hx : Primitive69 x) (hz : Primitive69 z)
    {u : R} {v w : S} (hv : Corresponds x z u v) (hw : Corresponds x z u w) : v = w := by
  obtain ⟨r,br,rx,rz⟩ := same_remainder x z hx hz hv
  obtain ⟨s,bs,sx,sz⟩ := same_remainder x z hx hz hw
  have eqn := unique_at_degree x 44 (primitive_monomials_independent x hx.order69 hx.not23 hx.not3)
    r s br bs (rx.trans sx.symm)
  exact rz.symm.trans (eqn ▸ sz : evalAt z r 44 = w)

theorem correspondence_exists (x : R) (z : S) (u : Carrier x) :
    ∃ v : Carrier z, Corresponds x z u.val v.val := by
  obtain ⟨p,m,bp,ep⟩ := u.property
  exact ⟨⟨evalAt z p m,p,m,bp,rfl⟩,p,⟨m,bp,ep⟩,m,bp,rfl⟩

noncomputable def substitute (x : R) (z : S) (u : Carrier x) : Carrier z :=
  Classical.choose (correspondence_exists x z u)

theorem substitute_spec (x : R) (z : S) (u : Carrier x) :
    Corresponds x z u.val (substitute x z u).val :=
  Classical.choose_spec (correspondence_exists x z u)

theorem substitute_eq {x : R} {z : S} (hx : Primitive69 x) (hz : Primitive69 z)
    (u : Carrier x) {v : S} (hv : Corresponds x z u.val v) : (substitute x z u).val = v :=
  correspondence_unique hx hz (substitute_spec x z u) hv

theorem substitute_eval {x : R} {z : S} (hx : Primitive69 x) (hz : Primitive69 z)
    (u : Carrier x) (p : Nat → Rat) (m : Nat) (bp : Bounded p m)
    (ep : evalAt x p m = u.val) : (substitute x z u).val = evalAt z p m :=
  substitute_eq hx hz u ⟨p,⟨m,bp,ep⟩,m,bp,rfl⟩

theorem substitute_self (x : R) (hx : Primitive69 x) (u : Carrier x) : substitute x x u = u := by
  obtain ⟨p,hp⟩ := u.property
  exact Subtype.ext (substitute_eq hx hx u ⟨p,hp,hp⟩)

theorem substitute_comp (x : R) (z : S) (w : T) (hx : Primitive69 x) (hz : Primitive69 z)
    (hw : Primitive69 w) (u : Carrier x) : substitute z w (substitute x z u) = substitute x w u := by
  obtain ⟨p,m,bp,ep⟩ := u.property
  apply Subtype.ext
  exact (substitute_eval hz hw _ p m bp (substitute_eval hx hz u p m bp ep).symm).trans
    (substitute_eval hx hw u p m bp ep).symm

theorem substitute_roundtrip (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z)
    (u : Carrier x) : substitute z x (substitute x z u) = u :=
  (substitute_comp x z x hx hz hx u).trans (substitute_self x hx u)

def constant (x : R) (q : Rat) : Carrier x := ⟨ofRat q, generated_rational x q⟩

def generator (x : R) : Carrier x := ⟨x,generated_root x⟩

def plus (x : R) (u v : Carrier x) : Carrier x := ⟨u.val+v.val,generated_add x _ _ u.2 v.2⟩

def times (x : R) (u v : Carrier x) : Carrier x := ⟨u.val*v.val,generated_mul x _ _ u.2 v.2⟩

def inverse (x : R) (hx : Primitive69 x) (u : Carrier x) : Carrier x := by
  refine ⟨u.val⁻¹,?_⟩
  by_cases hu : u.val = 0
  · rw [hu,Field.inv_zero]; exact generated_zero x
  · exact generated_inv x _ hx.order69 hx.not23 hx.not3 hu u.2

def power (x : R) (u : Carrier x) (n : Nat) : Carrier x := by
  refine ⟨u.val^n,?_⟩
  induction n with
  | zero => rw [Semiring.pow_zero]; exact generated_one x
  | succ n ih => rw [Semiring.pow_succ]; exact generated_mul x _ _ ih u.2

theorem corresponds_constant (x : R) (z : S) (a : Rat) :
    Corresponds x z (ofRat a) (ofRat a) := ⟨_,represents_constant x a,represents_constant z a⟩

theorem corresponds_zero (x : R) (z : S) : Corresponds x z 0 0 := by
  simpa only [ofRat_zero] using corresponds_constant x z 0

theorem corresponds_shift {x : R} {z : S} {u : R} {v : S} (s : Nat) (a : Rat)
    (h : Corresponds x z u v) : Corresponds x z ((ofRat a * x^s)*u) ((ofRat a * z^s)*v) := by
  obtain ⟨p,hp,hq⟩ := h
  exact ⟨_,represents_shift x u p s a hp,represents_shift z v p s a hq⟩

theorem corresponds_root (x : R) (z : S) : Corresponds x z x z := by
  simpa only [ofRat_one,Semiring.one_mul,Semiring.pow_one,Semiring.mul_one] using
    corresponds_shift 1 1 (corresponds_constant x z 1)

theorem corresponds_sub {x : R} {z : S} {u u' : R} {v v' : S}
    (h : Corresponds x z u v) (h' : Corresponds x z u' v') : Corresponds x z (u-u') (v-v') := by
  obtain ⟨p,px,pz⟩ := h
  obtain ⟨q,qx,qz⟩ := h'
  exact ⟨_,represents_sub x _ _ p q px qx,represents_sub z _ _ p q pz qz⟩

theorem corresponds_add {x : R} {z : S} {u u' : R} {v v' : S}
    (h : Corresponds x z u v) (h' : Corresponds x z u' v') : Corresponds x z (u+u') (v+v') := by
  have he := corresponds_sub h (corresponds_sub (corresponds_zero x z) h')
  rwa [show u-(0-u')=u+u' by grind only, show v-(0-v')=v+v' by grind only] at he

theorem corresponds_eval_mul {x : R} {z : S} {u : R} {v : S} (h : Corresponds x z u v)
    (p : Nat → Rat) (m : Nat) : Corresponds x z (evalAt x p m * u) (evalAt z p m * v) := by
  induction m with
  | zero =>
    change Corresponds x z (0*u) (0*v)
    simpa only [Semiring.zero_mul] using corresponds_zero x z
  | succ m ih =>
    rw [eval_succ,eval_succ,Semiring.right_distrib,Semiring.right_distrib]
    exact corresponds_add ih (corresponds_shift m (p m) h)

theorem corresponds_mul {x : R} {z : S} {u u' : R} {v v' : S}
    (h : Corresponds x z u v) (h' : Corresponds x z u' v') : Corresponds x z (u*u') (v*v') := by
  obtain ⟨p,⟨m,bp,ep⟩,hz⟩ := h
  rw [← ep,← value_at_bound z p v hz m bp]
  exact corresponds_eval_mul h' p m

theorem substitute_constant (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z) (q : Rat) :
    substitute x z (constant x q) = constant z q :=
  Subtype.ext (substitute_eq hx hz _ (corresponds_constant x z q))

theorem substitute_root (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z) :
    substitute x z (generator x) = generator z :=
  Subtype.ext (substitute_eq hx hz _ (corresponds_root x z))

theorem substitute_plus (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z)
    (u v : Carrier x) : substitute x z (plus x u v) = plus z (substitute x z u) (substitute x z v) :=
  Subtype.ext (substitute_eq hx hz _ (corresponds_add (substitute_spec x z u) (substitute_spec x z v)))

theorem substitute_mul (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z)
    (u v : Carrier x) : substitute x z (times x u v) = times z (substitute x z u) (substitute x z v) :=
  Subtype.ext (substitute_eq hx hz _ (corresponds_mul (substitute_spec x z u) (substitute_spec x z v)))

theorem map_inverse_of (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z)
    (f : Carrier x → Carrier z) (hc : ∀ a, f (constant x a) = constant z a)
    (hm : ∀ u v, f (times x u v) = times z (f u) (f v)) (u : Carrier x) :
    f (inverse x hx u) = inverse z hz (f u) := by
  apply Subtype.ext
  by_cases h : u.val = 0
  · have eu : u = constant x 0 := Subtype.ext (h.trans ofRat_zero.symm)
    have ei : inverse x hx u = constant x 0 := by
      apply Subtype.ext
      change u.val⁻¹ = ofRat 0
      rw [h,Field.inv_zero,ofRat_zero]
    rw [ei,eu,hc]
    change ofRat 0 = (ofRat 0 : S)⁻¹
    rw [ofRat_zero,Field.inv_zero]
  · have e : times x (inverse x hx u) u = constant x 1 :=
      Subtype.ext ((Field.inv_mul_cancel h).trans ofRat_one.symm)
    have v := congrArg Subtype.val ((hm _ _).symm.trans ((congrArg f e).trans (hc 1)))
    change (f (inverse x hx u)).val * (f u).val = ofRat 1 at v
    rw [ofRat_one] at v
    have nonzero : (f u).val ≠ 0 := by
      intro zero
      rw [zero, Semiring.mul_zero] at v
      exact Field.zero_ne_one v
    have t := congrArg (fun b : S => b*(f u).val⁻¹) v
    rw [Semiring.mul_assoc,Field.mul_inv_cancel nonzero,Semiring.mul_one,Semiring.one_mul] at t
    exact t

theorem substitute_inverse (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z)
    (u : Carrier x) : substitute x z (inverse x hx u) = inverse z hz (substitute x z u) :=
  map_inverse_of x z hx hz (substitute x z) (substitute_constant x z hx hz)
    (substitute_mul x z hx hz) u

structure FieldIso (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z) where
  forward : Carrier x → Carrier z
  backward : Carrier z → Carrier x
  leftInv : ∀ u, backward (forward u) = u
  rightInv : ∀ v, forward (backward v) = v
  map_constant : ∀ a, forward (constant x a) = constant z a
  map_plus : ∀ u v, forward (plus x u v) = plus z (forward u) (forward v)
  map_times : ∀ u v, forward (times x u v) = times z (forward u) (forward v)
  map_inverse : ∀ u, forward (inverse x hx u) = inverse z hz (forward u)

noncomputable def substitutionIso (x : R) (z : S) (hx : Primitive69 x) (hz : Primitive69 z) :
    FieldIso x z hx hz where
  forward := substitute x z
  backward := substitute z x
  leftInv := substitute_roundtrip x z hx hz
  rightInv := substitute_roundtrip z x hz hx
  map_constant := substitute_constant x z hx hz
  map_plus := substitute_plus x z hx hz
  map_times := substitute_mul x z hx hz
  map_inverse := substitute_inverse x z hx hz

theorem map_power {x : R} {z : S} {hx : Primitive69 x} {hz : Primitive69 z}
    (e : FieldIso x z hx hz) (u : Carrier x) (n : Nat) :
    e.forward (power x u n) = power z (e.forward u) n := by
  induction n with
  | zero =>
    have eqn (a : R) (v : Carrier a) : power a v 0 = constant a 1 :=
      Subtype.ext ((Semiring.pow_zero v.val).trans ofRat_one.symm)
    rw [eqn, e.map_constant]
    exact Subtype.ext (ofRat_one.trans (Semiring.pow_zero _).symm)
  | succ n ih =>
    have eqn : power x u (n+1) = times x (power x u n) u := Subtype.ext (Semiring.pow_succ ..)
    rw [eqn,e.map_times,ih]
    exact Subtype.ext (Semiring.pow_succ ..).symm

def evalTerm (x : R) (u : Carrier x) (p : Nat → Rat) : Nat → Carrier x
  | 0 => constant x 0
  | n+1 => plus x (evalTerm x u p n) (times x (constant x (p n)) (power x u n))

theorem evalTerm_val (x : R) (u : Carrier x) (p : Nat → Rat) (m : Nat) :
    (evalTerm x u p m).val = evalAt u.val p m := by
  induction m with
  | zero => exact ofRat_zero
  | succ m ih =>
    change (evalTerm x u p m).val + ofRat (p m)*u.val^m = _
    rw [ih,eval_succ]

theorem map_evalTerm {x : R} {z : S} {hx : Primitive69 x} {hz : Primitive69 z}
    (e : FieldIso x z hx hz) (u : Carrier x) (p : Nat → Rat) (m : Nat) :
    e.forward (evalTerm x u p m) = evalTerm z (e.forward u) p m := by
  induction m with
  | zero => exact e.map_constant 0
  | succ m ih => rw [evalTerm,e.map_plus,e.map_times,e.map_constant,map_power,ih,evalTerm]

theorem map_eval {x : R} {z : S} {hx : Primitive69 x} {hz : Primitive69 z}
    (e : FieldIso x z hx hz) (u : Carrier x) (p : Nat → Rat) (m : Nat)
    (ep : evalAt x p m = u.val) : (e.forward u).val = evalAt (e.forward (generator x)).val p m := by
  have term : evalTerm x (generator x) p m = u := Subtype.ext ((evalTerm_val ..).trans ep)
  rw [← term, map_evalTerm, evalTerm_val]

theorem iso_forward_ext {x : R} {z : S} {hx : Primitive69 x} {hz : Primitive69 z}
    (e f : FieldIso x z hx hz) (h : e.forward (generator x) = f.forward (generator x)) :
    e.forward = f.forward := by
  funext u
  obtain ⟨p,m,_,ep⟩ := u.property
  exact Subtype.ext ((map_eval e u p m ep).trans (h ▸ (map_eval f u p m ep).symm))

theorem iso_ext_generator {x : R} {z : S} {hx : Primitive69 x} {hz : Primitive69 z}
    (e f : FieldIso x z hx hz) (h : e.forward (generator x) = f.forward (generator x)) : e = f := by
  have hf := iso_forward_ext e f h
  have hb : e.backward = f.backward := by
    funext u
    calc
      e.backward u = e.backward (f.forward (f.backward u)) := congrArg e.backward (f.rightInv u).symm
      _ = f.backward u := hf ▸ e.leftInv _
  cases e; cases f; cases hf; cases hb; rfl

end Reimann.CircularSubstitution69
