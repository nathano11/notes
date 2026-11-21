import Reimann.TameOrderFaithful277

namespace Reimann.TamePlaceRestriction277

open TameArithmetic277 TameRationalField277 TameOrderFaithful277
open TameBiquadratic277 TameOrderReduction277 TamePrimePowers277
open Lean.Grind

/-- Comparison of absolute values on E. The final law fixes its restriction
to the integer scalars at all positive and zero 277-adic radii. -/
structure PlaceOrder where
  le : Biquad → Biquad → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z
  total : ∀ x y, le x y ∨ le y x
  mul : ∀ {x y} z, le x y → le (bm x z) (bm y z)
  cancel : ∀ {x y z}, z ≠ scalar 0 → le (bm x z) (bm y z) → le x y
  add : ∀ {x y z}, le x z → le y z → le (ba x y) z
  integers : ∀ (n : Nat) (z : Int),
    le (scalar (z : Rat)) (scalar (((277 : Int)^n : Int) : Rat)) ↔ (277 : Int)^n ∣ z

theorem int_bounded (w : PlaceOrder) (z : Int) : w.le (scalar (z : Rat)) (scalar 1) := by
  have h := (w.integers 0 z).mpr (by simp)
  simpa using h

theorem one_mul_field (x : Biquad) : bm (scalar 1) x = x :=
  (mul_comm _ _).trans (mul_one x)

theorem product_le (w : PlaceOrder) {a b c d : Biquad} (h : w.le a b) (k : w.le c d) :
    w.le (bm a c) (bm b d) := by
  apply w.trans (w.mul c h)
  rw [mul_comm b c, mul_comm b d]
  exact w.mul b k

theorem bounded_product (w : PlaceOrder) {a b : Biquad}
    (h : w.le a (scalar 1)) (k : w.le b (scalar 1)) : w.le (bm a b) (scalar 1) := by
  simpa only [one_mul_field] using product_le w h k

theorem bounded_of_square (w : PlaceOrder) (x : Biquad) (h : w.le (bm x x) (scalar 1)) :
    w.le x (scalar 1) := by
  rcases w.total x (scalar 1) with h' | h'
  · exact h'
  · by_cases hz : x = scalar 0
    · subst x; exact int_bounded w 0
    · apply w.cancel hz
      rw [one_mul_field]
      exact w.trans h h'

theorem radicals_bounded (w : PlaceOrder) :
    w.le gen3 (scalar 1) ∧ w.le gen23 (scalar 1) := by
  constructor
  · apply bounded_of_square
    rw [generator_squares.1]
    exact int_bounded w (-3)
  · apply bounded_of_square
    rw [generator_squares.2]
    exact int_bounded w (-23)

theorem order_bounded (w : PlaceOrder) (v : OrderCoordinates) :
    w.le (rationalize v) (scalar 1) := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change w.le (((a:Rat),(b:Rat)),((c:Rat),(d:Rat))) (scalar 1)
  rw [← basis_expansion]
  obtain ⟨hi,hj⟩ := radicals_bounded w
  exact w.add (w.add (int_bounded w a) (bounded_product w (int_bounded w b) hi))
    (w.add (bounded_product w (int_bounded w c) hj)
      (bounded_product w (int_bounded w d) (bounded_product w hi hj)))

theorem rationalize_integer (z : Int) :
    rationalize (integerCoordinates z) = scalar (z : Rat) := rfl

theorem rationalize_add (u v : OrderCoordinates) :
    rationalize (componentAdd u v) = ba (rationalize u) (rationalize v) := by
  simp only [componentAdd,rationalize,ba,qa,Ring.intCast_add]

theorem rationalize_product (u v : OrderCoordinates) :
    rationalize (product (-3) (-23) u v) = bm (rationalize u) (rationalize v) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [product,rationalize,bm,qa,qm,qs,Ring.intCast_add,Ring.intCast_mul,Ring.intCast_neg] <;> grind

theorem strict_277 (w : PlaceOrder) : ¬ w.le (scalar 1) (scalar 277) := by
  have h := w.integers 1 1
  intro e
  exact (by decide : ¬ (277 : Int)^1 ∣ 1) (h.mp (by simpa using e))

theorem strict_zero (w : PlaceOrder) : ¬ w.le (scalar 1) (scalar 0) := by
  have h := (w.integers 1 0).mpr (by simp)
  exact fun e => strict_277 w (w.trans e (by simpa using h))

/-- The open unit ball of the place, restricted to the integral order. -/
def center (w : PlaceOrder) (v : OrderCoordinates) : Prop :=
  ¬ w.le (scalar 1) (rationalize v)

theorem center_prime (w : PlaceOrder) : TameOrderPrimes277.OrderPrime (center w) where
  zero := strict_zero w
  proper := fun h => h (w.refl _)
  add {x y} hx hy h := by
    change w.le (scalar 1) (rationalize (componentAdd x y)) at h
    rw [rationalize_add] at h
    rcases w.total (rationalize x) (rationalize y) with hxy | hyx
    · exact hy (w.trans h (w.add hxy (w.refl _)))
    · exact hx (w.trans h (w.add (w.refl _) hyx))
  absorb a {x} hx h := by
    change w.le (scalar 1) (rationalize (product (-3) (-23) a x)) at h
    rw [rationalize_product] at h
    have he := w.mul (rationalize x) (order_bounded w a)
    rw [one_mul_field] at he
    exact hx (w.trans h he)
  prime {x y} h := by
    by_cases hx : center w x
    · exact Or.inl hx
    · right
      intro hy
      have hh : w.le (scalar 1) (rationalize x) := Classical.not_not.mp hx
      have he := product_le w hh hy
      rw [one_mul_field, ← rationalize_product] at he
      exact h he

theorem unique_center (w : PlaceOrder) :
    ∃ s t : Bool, center w = primePlace s t ∧
      ∀ s' t', center w = primePlace s' t' → s = s' ∧ t = t' :=
  (TameLocalOrders277.all_order_primes _).mp ⟨center_prime w,strict_277 w⟩

/-- The idempotent coordinate vector with 1 only on the specified branch. -/
def signal {A : Type} [OfNat A 0] [OfNat A 1] (s t : Bool) : TameBiquadratic277.Quad A :=
  let row : A × A := if t then (0,1) else (1,0)
  if s then ((0,0),row) else (row,(0,0))

theorem signal_coordinate {A : Type} [OfNat A 0] [OfNat A 1] (s t : Bool) :
    coordinate s t (signal s t : TameBiquadratic277.Quad A) = 1 := by
  cases s <;> cases t <;> rfl

theorem signal_kills {A : Type} [CommRing A] (s t : Bool)
    (v : TameBiquadratic277.Quad A) (h : coordinate s t v = 0) :
    pointProduct (signal s t) v = ((0,0),(0,0)) := by
  cases s <;> cases t <;>
    simp only [signal,coordinate,ite_true,ite_false,Bool.false_eq_true,pointProduct] at * <;>
    apply Prod.ext <;> apply Prod.ext <;> grind

theorem images_zero (n : Nat) : images n (integerCoordinates 0) = ((0,0),(0,0)) := by
  unfold images
  change (finite_splitting277 n).evaluate ((0,0),(0,0)) = _
  exact (finite_splitting277 n).scalar 0

theorem signal_is_unit (w : PlaceOrder) (s t : Bool) (hw : center w = primePlace s t)
    (n : Nat) (e : OrderCoordinates) (he : images n e = signal s t) :
    w.le (scalar 1) (rationalize e) := by
  apply Classical.byContradiction
  intro h
  have hp : center w e := h
  rw [hw] at hp
  obtain ⟨k,hk⟩ := (same_prime_every_depth s t n e).mpr hp
  change coordinate s t (images n e) = 277*k at hk
  rw [he,signal_coordinate] at hk
  exact (by decide : ¬ (277 : Int) ∣ 1) ((finite_multiple_test n 1).mp ⟨k,hk⟩)

theorem rationalize_scale (p : Int) (v : OrderCoordinates) :
    rationalize (scale p v) = bm (scalar (p : Rat)) (rationalize v) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [rationalize,scale,scalar,bm,qa,qm,qs,Ring.intCast_mul] <;> grind

theorem modulus_bound (w : PlaceOrder) (p : Int) (v : OrderCoordinates) :
    w.le (rationalize (scale p v)) (scalar (p : Rat)) := by
  rw [rationalize_scale, mul_comm]
  have h := w.mul (scalar (p:Rat)) (order_bounded w v)
  simpa only [one_mul_field] using h

theorem order_cut_of_divides (w : PlaceOrder) (s t : Bool) (hw : center w = primePlace s t)
    (n : Nat) (v : OrderCoordinates) (h : (277 : Int)^(n+1) ∣ branchEval s t n v) :
    w.le (rationalize v) (scalar (((277 : Int)^(n+1) : Int) : Rat)) := by
  obtain ⟨e,he⟩ := images_surject n (signal s t)
  have hv := power_vanishes s t n v ((prime_power_iff s t n v).mpr h)
  have hz : images n (product (-3) (-23) e v) = images n (integerCoordinates 0) := by
    rw [images_product,he,signal_kills s t _ hv,images_zero]
  obtain ⟨u,hu⟩ := image_fibers n _ _ hz
  have hu' : product (-3) (-23) e v = scale ((277 : Int)^(n+1)) u := by
    simpa only [integerCoordinates,componentAdd,Int.zero_add] using hu
  have hunit := w.mul (rationalize v) (signal_is_unit w s t hw n e he)
  rw [one_mul_field, ← rationalize_product,hu'] at hunit
  exact w.trans hunit (modulus_bound w _ u)

theorem subtract_evaluation (s t : Bool) (n : Nat) (v : OrderCoordinates) :
    branchEval s t n (TameLocalOrders277.difference (integerCoordinates (branchEval s t n v)) v) = 0 := by
  rw [TameLocalOrders277.evaluation_difference,branchEval_integer,Int.sub_self]

theorem restore_evaluation (r : Int) (v : OrderCoordinates) :
    componentAdd v (TameLocalOrders277.difference (integerCoordinates r) v) = integerCoordinates r := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [TameLocalOrders277.difference,integerCoordinates,componentAdd,scale] <;> grind

/-- Every positive integral 277-adic radius at this place is the ordinary
prime-power radius of the uniquely determined sign pair. -/
theorem order_cut_iff (w : PlaceOrder) (s t : Bool) (hw : center w = primePlace s t)
    (n : Nat) (v : OrderCoordinates) :
    w.le (rationalize v) (scalar (((277 : Int)^(n+1) : Int) : Rat)) ↔
      (277 : Int)^(n+1) ∣ branchEval s t n v := by
  constructor
  · intro h
    have hd := order_cut_of_divides w s t hw n
      (TameLocalOrders277.difference (integerCoordinates (branchEval s t n v)) v)
      (by rw [subtract_evaluation]; simp)
    have ha := w.add h hd
    rw [← rationalize_add,restore_evaluation,rationalize_integer] at ha
    exact (w.integers (n+1) _).mp ha
  · exact order_cut_of_divides w s t hw n v

theorem unit_integer (w : PlaceOrder) (s t : Bool) (hw : center w = primePlace s t)
    (u : Int) (hu : ¬ (277 : Int) ∣ u) : w.le (scalar 1) (scalar (u:Rat)) := by
  apply Classical.byContradiction
  intro h
  have hc : center w (integerCoordinates u) := h
  rw [hw] at hc
  exact hu (by simpa only [primePlace,branchEval_integer] using hc)

theorem factor_positive (d : Nat) (hd : 0 < d) :
    ∃ n u : Nat, d = 277^n*u ∧ ¬277∣u := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hp : 277∣d
    · obtain ⟨k,hk⟩ := hp
      have hk0 : 0<k := by omega
      obtain ⟨n,u,hn,hu⟩ := ih k (by omega) hk0
      refine ⟨n+1,u,?_,hu⟩
      rw [hk,hn,Nat.pow_succ]; ac_rfl
    · exact ⟨0,d,by simp,hp⟩

theorem radius_of_factor (w : PlaceOrder) (s t : Bool) (hw : center w = primePlace s t)
    (n : Nat) (u : Int) (hu : ¬ (277 : Int) ∣ u) (x : Biquad) :
    w.le x (scalar (((277^n*u : Int)) : Rat)) ↔
    w.le x (scalar (((277^n : Int)) : Rat)) := by
  let q : Biquad := scalar (((277^n : Int)) : Rat)
  have eqmul : bm (scalar (u:Rat)) q = scalar (((277^n*u:Int)) : Rat) := by
    rw [(scalar_embedding _ _).2.2,Rat.intCast_mul]
    apply congrArg scalar
    grind
  have hl := w.mul q (int_bounded w u)
  have hr := w.mul q (unit_integer w s t hw u hu)
  rw [one_mul_field,eqmul] at hl hr
  exact ⟨fun h => w.trans h hl, fun h => w.trans h hr⟩

theorem radius_agrees (w v : PlaceOrder) (s t : Bool)
    (hw : center w = primePlace s t) (hv : center v = primePlace s t)
    (k : Nat) (a : OrderCoordinates) :
    w.le (rationalize a) (scalar (((277^k : Int)) : Rat)) ↔
    v.le (rationalize a) (scalar (((277^k : Int)) : Rat)) := by
  cases k with
  | zero => simpa using (show w.le (rationalize a) (scalar 1) ↔ v.le (rationalize a) (scalar 1)
      from ⟨fun _ => order_bounded v a,fun _ => order_bounded w a⟩)
  | succ n => exact (order_cut_iff w s t hw n a).trans (order_cut_iff v s t hv n a).symm

theorem denominator_radius_agrees (w v : PlaceOrder) (s t : Bool)
    (hw : center w = primePlace s t) (hv : center v = primePlace s t)
    (d : Nat) (hd : 0<d) (a : OrderCoordinates) :
    w.le (rationalize a) (scalar ((d : Int) : Rat)) ↔
    v.le (rationalize a) (scalar ((d : Int) : Rat)) := by
  obtain ⟨k,u,hk,hu⟩ := factor_positive d hd
  have hu' : ¬(277 : Int)∣(u:Int) := fun h => hu (Int.ofNat_dvd.mp h)
  have de : (d : Int) = 277^k*(u:Int) := by rw [hk,Int.natCast_mul,Int.natCast_pow]; rfl
  rw [de,radius_of_factor w s t hw _ _ hu',radius_of_factor v s t hv _ _ hu']
  exact radius_agrees w v s t hw hv k a

/-- Clear all four rational coefficients in the polynomial basis by one
positive integer. The scalar numerator identity is shared with the field construction. -/
theorem common_denominator (x : Biquad) :
    ∃ d : Nat, 0<d ∧ ∃ a : OrderCoordinates,
      bm x (scalar ((d:Int):Rat)) = rationalize a := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  let m := a.den*(b.den*(c.den*d.den))
  have clear (z : Rat) (b : Nat) :
      z*(((z.den*b:Nat):Int):Rat) = ((((b:Int)*z.num:Int)):Rat) := by
    have h := rational_numerator z
    simp only [Int.natCast_mul,Rat.intCast_mul]
    grind
  have hb : m=b.den*(a.den*(c.den*d.den)) := by dsimp [m]; ac_rfl
  have hc : m=c.den*(a.den*(b.den*d.den)) := by dsimp [m]; ac_rfl
  have hd : m=d.den*(a.den*(b.den*c.den)) := by dsimp [m]; ac_rfl
  refine ⟨m,Nat.mul_pos a.den_pos (Nat.mul_pos b.den_pos (Nat.mul_pos c.den_pos d.den_pos)),
    ((↑(b.den*(c.den*d.den))*a.num,↑(a.den*(c.den*d.den))*b.num),
    (↑(a.den*(b.den*d.den))*c.num,↑(a.den*(b.den*c.den))*d.num)),?_⟩
  have ha := clear a (b.den*(c.den*d.den))
  change a*(((m:Int)):Rat) = _ at ha
  have h₂ := hb.symm ▸ clear b (a.den*(c.den*d.den))
  have h₃ := hc.symm ▸ clear c (a.den*(b.den*d.den))
  have h₄ := hd.symm ▸ clear d (a.den*(b.den*c.den))
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,qm,qa,qs,scalar,rationalize] <;> grind

theorem clear_unit_ball (w : PlaceOrder) (x : Biquad) (d : Nat) (hd : 0<d)
    (a : OrderCoordinates) (ha : bm x (scalar ((d:Int):Rat)) = rationalize a) :
    w.le x (scalar 1) ↔ w.le (rationalize a) (scalar ((d:Int):Rat)) := by
  have hn : scalar ((d:Int):Rat) ≠ scalar 0 := by
    intro he
    have h := (scalar_embedding _ _).1.mp he
    have : (d:Int) = 0 := Rat.intCast_inj.mp (show (((d:Int)):Rat) = ((0:Int):Rat) from h)
    omega
  rw [← ha]
  constructor
  · intro h
    simpa only [one_mul_field] using w.mul (scalar ((d:Int):Rat)) h
  · intro h
    apply w.cancel hn
    simpa only [one_mul_field] using h

theorem unit_ball_agrees (w v : PlaceOrder) (s t : Bool)
    (hw : center w = primePlace s t) (hv : center v = primePlace s t) (x : Biquad) :
    w.le x (scalar 1) ↔ v.le x (scalar 1) := by
  obtain ⟨d,hd,a,ha⟩ := common_denominator x
  rw [clear_unit_ball w x d hd a ha,clear_unit_ball v x d hd a ha]
  exact denominator_radius_agrees w v s t hw hv d hd a

theorem zero_mul_field (x : Biquad) : bm (scalar 0) x = scalar 0 := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [scalar,bm,qa,qm,qs] <;> grind

theorem at_zero_iff (w : PlaceOrder) (x : Biquad) : w.le x (scalar 0) ↔ x=scalar 0 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hx
    apply strict_zero w
    apply w.cancel hx
    rwa [one_mul_field,zero_mul_field]
  · rintro rfl; exact w.refl _

theorem inverse_nonzero (y : Biquad) (hy : y ≠ scalar 0) : bi y ≠ scalar 0 := by
  intro he
  have h := biquad_mul_inverse y hy
  rw [he,mul_comm,zero_mul_field] at h
  exact (by decide : scalar 0 ≠ scalar 1) h

theorem relative_unit_ball (w : PlaceOrder) (x y : Biquad) (hy : y ≠ scalar 0) :
    w.le x y ↔ w.le (bm x (bi y)) (scalar 1) := by
  have he : bm y (bi y) = scalar 1 := biquad_mul_inverse y hy
  rw [← he]
  exact ⟨w.mul (bi y), w.cancel (inverse_nonzero _ hy)⟩

/-- Agreement of the first-level center forces agreement of the complete
valuation comparisons on all rational elements of the biquadratic field. -/
theorem place_order_ext (w v : PlaceOrder) (h : center w = center v) : w=v := by
  obtain ⟨s,t,hw,_⟩ := unique_center w
  have hv := h.symm.trans hw
  have he : w.le = v.le := by
    funext x y
    apply propext
    by_cases hy : y=scalar 0
    · subst y
      rw [at_zero_iff,at_zero_iff]
    · rw [relative_unit_ball w x y hy,relative_unit_ball v x y hy]
      exact unit_ball_agrees w v s t hw hv _
  cases w; cases v
  congr

noncomputable def test_sign (w : PlaceOrder) (v : OrderCoordinates) : Bool := by
  classical
  exact if center w v then false else true

theorem test_sign_false (w : PlaceOrder) (v : OrderCoordinates) :
    test_sign w v = false ↔ center w v := by
  classical
  simp [test_sign]

/-- Detect the two signs using X−44 and Y−114 in the open unit ball. -/
noncomputable def signs (w : PlaceOrder) : Bool × Bool :=
  (test_sign w ((-44,1),(0,0)),test_sign w ((-114,0),(1,0)))

theorem signs_of_center (w : PlaceOrder) (s t : Bool) (h : center w = primePlace s t) :
    signs w = (s,t) := by
  have h₁ := (test_sign_false w ((-44,1),(0,0))).trans
    ((congrArg (fun P : OrderCoordinates → Prop => P ((-44,1),(0,0))) h).to_iff.trans
      (kernel_detects_signs s t).1)
  have h₂ := (test_sign_false w ((-114,0),(1,0))).trans
    ((congrArg (fun P : OrderCoordinates → Prop => P ((-114,0),(1,0))) h).to_iff.trans
      (kernel_detects_signs s t).2)
  apply Prod.ext
  · change test_sign w ((-44,1),(0,0)) = s
    cases s <;> cases ht : test_sign w ((-44,1),(0,0)) <;> simp_all
  · change test_sign w ((-114,0),(1,0)) = t
    cases t <;> cases ht : test_sign w ((-114,0),(1,0)) <;> simp_all

theorem center_at_signs (w : PlaceOrder) :
    center w = primePlace (signs w).1 (signs w).2 := by
  obtain ⟨s,t,h,_⟩ := unique_center w
  rw [signs_of_center w s t h]
  exact h

theorem signs_injective (w v : PlaceOrder) (h : signs w = signs v) : w = v := by
  apply place_order_ext
  rw [center_at_signs w,center_at_signs v,h]

/-- To enumerate the field places it suffices to construct four absolute-value
comparisons realizing the two sign tests. All other field comparisons then follow. -/
theorem field_orders_of_signed_places (candidate : Bool × Bool → PlaceOrder)
    (local_tests : ∀ b, signs (candidate b) = b) :
    (∀ w : PlaceOrder, candidate (signs w) = w) ∧
    (∀ b c : Bool × Bool, candidate b = candidate c ↔ b=c) := by
  constructor
  · intro w; exact signs_injective _ _ (local_tests _)
  · intro b c; constructor
    · intro h; exact (local_tests b).symm.trans ((congrArg signs h).trans (local_tests c))
    · intro h; exact congrArg candidate h

end Reimann.TamePlaceRestriction277

