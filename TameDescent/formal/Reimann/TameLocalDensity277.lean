import Reimann.TamePlaceRestriction277

namespace Reimann.TameLocalDensity277

open TamePlaceRestriction277 TameOrderFaithful277 TameRationalField277 TameArithmetic277
open TameBiquadratic277 TameLocalOrders277 TameLimit277 Lean.Grind

/-- Integer approximation of an order element at its selected signed prime. -/
theorem approximate_order (w : PlaceOrder) (s t : Bool) (hw : center w = TamePrimePowers277.primePlace s t)
    (m : Nat) (a : OrderCoordinates) :
    w.le (rationalize (TameLocalOrders277.difference a (integerCoordinates (branchEval s t m a))))
      (scalar (((277 : Int)^(m+1) : Int) : Rat)) := by
  apply (order_cut_iff w s t hw _ _).mpr
  rw [evaluation_difference,branchEval_integer,Int.sub_self]
  simp

theorem scalar_nat_ne_zero (d : Nat) (hd : 0 < d) : scalar ((d:Int):Rat) ≠ scalar 0 := by
  intro e
  have h := (scalar_embedding _ _).1.mp e
  have : (d : Int)=0 := Rat.intCast_inj.mp (show ((d:Int):Rat)=((0:Int):Rat) from h)
  omega

theorem shift_radius (w : PlaceOrder) (s t : Bool) (hw : center w = TamePrimePowers277.primePlace s t)
    (d k u : Nat) (hd : 0<d) (hd' : d=277^k*u) (hu : ¬277∣u) (m : Nat) (y : Biquad)
    (hy : w.le (bm y (scalar ((d:Int):Rat))) (scalar (((277 : Int)^(m+k) : Int) : Rat))) :
    w.le y (scalar (((277 : Int)^m : Int) : Rat)) := by
  apply w.cancel (scalar_nat_ne_zero d hd)
  have he : bm (scalar (((277:Int)^m:Int):Rat)) (scalar ((d:Int):Rat)) =
      scalar (((277^(m+k)*(u:Int):Int)):Rat) := by
    rw [(scalar_embedding _ _).2.2,← Rat.intCast_mul]
    apply congrArg scalar
    apply congrArg (fun a : Int => (a : Rat))
    rw [hd',Int.natCast_mul,Int.natCast_pow,Int.pow_add]
    change 277^m*(277^k*(u:Int)) = 277^m*277^k*(u:Int)
    exact (Int.mul_assoc _ _ _).symm
  rw [he]
  exact (radius_of_factor w s t hw (m+k) (u:Int) (fun h => hu (Int.ofNat_dvd.mp h)) _).mpr hy

theorem scale_error (x : Biquad) (d z : Int) (q : Rat) (a : OrderCoordinates)
    (ha : bm x (scalar (d:Rat)) = rationalize a) (hq : q*(d:Rat)=(z:Rat)) :
    bm (ba x (bn (scalar q))) (scalar (d:Rat)) =
      rationalize (TameLocalOrders277.difference a (integerCoordinates z)) := by
  rw [mul_comm,distributive,mul_comm (scalar (d:Rat)) x,ha]
  have he : bm (scalar (d:Rat)) (bn (scalar q)) = bn (scalar (z:Rat)) := by
    apply Prod.ext <;> apply Prod.ext <;> simp only [scalar,bm,qa,qm,qs,bn] <;> grind
  rw [he]
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [TameLocalOrders277.difference,componentAdd,TameOrderReduction277.scale,
      rationalize,integerCoordinates,scalar,bn,ba,qa,qs,Ring.intCast_add,Ring.intCast_mul] <;> grind

/-- Every element of the global field has a rational approximation at
each prescribed power of 277. Its numerator is the selected signed evaluation
of the cleared integral coordinates at the precision adjusted for the denominator. -/
theorem approximation_at_precision (w : PlaceOrder) (x : Biquad) (n : Nat) :
    ∃ q : Rat, w.le (ba x (bn (scalar q))) (scalar (((277 : Int)^(n+1) : Int) : Rat)) := by
  obtain ⟨s,t,hw,_⟩ := unique_center w
  obtain ⟨d,hd,a,ha⟩ := common_denominator x
  obtain ⟨k,u,hdu,hu⟩ := factor_positive d hd
  let z := branchEval s t (n+k) a
  let q := (z:Rat)/((d:Int):Rat)
  have hn : ((d:Int):Rat) ≠ 0 := fun h => scalar_nat_ne_zero d hd (congrArg scalar h)
  have hq : q*((d:Int):Rat) = (z:Rat) := Rat.div_mul_cancel hn
  refine ⟨q,shift_radius w s t hw d k u hd hdu hu (n+1) _ ?_⟩
  rw [scale_error x (d:Int) z q a ha hq,show n+1+k=n+k+1 by omega]
  exact approximate_order w s t hw (n+k) a

theorem nonzero_order_detected (s t : Bool) (a : OrderCoordinates)
    (ha : a ≠ integerCoordinates 0) :
    ∃ n : Nat, ¬ (277 : Int)^(n+1) ∣ branchEval s t n a := by
  apply Classical.byContradiction
  intro hn
  apply ha
  apply orderImage_zero_kernel s t
  apply equal_of_residues
  intro n
  have hd : (277 : Int)^(n+1) ∣ branchEval s t n a :=
    Classical.byContradiction (fun h => hn ⟨n,h⟩)
  rw [orderImage_residue]
  change branchEval s t n a % ((277 : Int)^(n+1)) = 0 % ((277 : Int)^(n+1))
  rw [Int.emod_eq_zero_of_dvd hd,Int.zero_emod]

theorem nonzero_cleared (y : Biquad) (hy : y ≠ scalar 0) (d : Nat) (hd : 0<d)
    (a : OrderCoordinates) (ha : bm y (scalar ((d:Int):Rat)) = rationalize a) :
    a ≠ integerCoordinates 0 := by
  intro hz
  rw [hz,rationalize_integer] at ha
  have he := congrArg (fun v => bm v (bi (scalar ((d:Int):Rat)))) ha
  rw [mul_assoc,biquad_mul_inverse _ (scalar_nat_ne_zero d hd),mul_one] at he
  exact hy (he.trans (zero_mul_field _))

/-- No nonzero element of the global field has value below every integer power of 277. -/
theorem radii_cofinal (w : PlaceOrder) (y : Biquad) (hy : y ≠ scalar 0) :
    ∃ n : Nat, ¬ w.le y (scalar (((277:Int)^(n+1):Int):Rat)) := by
  obtain ⟨d,hd,a,ha⟩ := common_denominator y
  obtain ⟨s,t,hw,_⟩ := unique_center w
  obtain ⟨n,hn⟩ := nonzero_order_detected s t a (nonzero_cleared y hy d hd a ha)
  refine ⟨n,fun h => hn ((order_cut_iff w s t hw n a).mp ?_)⟩
  have he := w.mul y (int_bounded w (d:Int))
  rw [one_mul_field,mul_comm,ha] at he
  exact w.trans he h

/-- Every open valuation ball about a global field element, of arbitrary
nonzero field radius, contains a rational scalar. -/
theorem rational_dense_at_every_place (w : PlaceOrder) (x y : Biquad) (hy : y ≠ scalar 0) :
    ∃ q : Rat, ¬ w.le y (ba x (bn (scalar q))) := by
  obtain ⟨n,hn⟩ := radii_cofinal w y hy
  obtain ⟨q,hq⟩ := approximation_at_precision w x n
  exact ⟨q,fun h => hn (w.trans h hq)⟩

end Reimann.TameLocalDensity277
