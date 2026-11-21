import Reimann.TameCauchy277
import Reimann.TameAdicDomain277

namespace Reimann.TameRationalCauchy277

open TameLimit277

def scale (k : Nat) : Rat := ((277 : Int)^k : Int)

/-- Membership in 277^k ℤ_(277) for an actual rational q. -/
def Small (k : Nat) (q : Rat) : Prop :=
  ∃ a b : Int, ¬ (277 : Int) ∣ b ∧ q * (b : Rat) = scale k * (a : Rat)

def Close (k : Nat) (x y : Rat) : Prop := Small k (x-y)

theorem scale_add (k d : Nat) : scale (k+d) = scale k * scale d := by
  unfold scale
  rw [Int.pow_add,Rat.intCast_mul]

theorem unit_product {b d : Int} (hb : ¬ (277 : Int) ∣ b) (hd : ¬ (277 : Int) ∣ d) :
    ¬ (277 : Int) ∣ b*d := by
  intro h
  exact hd (TameAdicDomain277.cancel_nonzero_digit b d hb 1 (by simpa using h))

theorem small_zero (k : Nat) : Small k 0 :=
  ⟨0,1,by decide,by simp⟩

theorem small_add {k : Nat} {x y : Rat} (hx : Small k x) (hy : Small k y) :
    Small k (x+y) := by
  obtain ⟨a,b,hb,hx⟩ := hx
  obtain ⟨c,d,hd,hy⟩ := hy
  refine ⟨a*d+c*b,b*d,unit_product hb hd, ?_⟩
  simp only [Rat.intCast_add,Rat.intCast_mul]
  calc
    _ = (x*(b:Rat))*(d:Rat) + (y*(d:Rat))*(b:Rat) := by grind
    _ = _ := by rw [hx,hy]; grind

theorem small_neg {k : Nat} {x : Rat} (hx : Small k x) : Small k (-x) := by
  obtain ⟨a,b,hb,hx⟩ := hx
  refine ⟨-a,b,hb,?_⟩
  simp only [Rat.intCast_neg]
  grind

theorem small_drop {k m : Nat} (hkm : k ≤ m) {x : Rat} (hx : Small m x) : Small k x := by
  obtain ⟨a,b,hb,hx⟩ := hx
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hkm
  refine ⟨(277 : Int)^d*a,b,hb,?_⟩
  rw [hx,scale_add,Rat.intCast_mul]
  change scale k * scale d * (a:Rat) = scale k * (scale d * (a:Rat))
  grind

theorem small_int_iff (k : Nat) (z : Int) :
    Small k (z : Rat) ↔ (277 : Int)^k ∣ z := by
  constructor
  · rintro ⟨a,b,hb,he⟩
    have h : z*b = (277 : Int)^k*a := Rat.intCast_inj.mp (by
      simpa only [Rat.intCast_mul,scale] using he)
    exact TameAdicDomain277.cancel_nonzero_digit b z hb k ⟨a,by rw [Int.mul_comm b z,h]⟩
  · rintro ⟨a,rfl⟩
    refine ⟨a,1,by decide,?_⟩
    simp [Rat.intCast_mul,scale]

theorem close_refl (k : Nat) (x : Rat) : Close k x x := by
  change Small k (x-x)
  rw [Rat.sub_self]
  exact small_zero k

theorem close_symm {k : Nat} {x y : Rat} (h : Close k x y) : Close k y x := by
  change Small k (y-x)
  rw [show y-x= -(x-y) by grind]
  exact small_neg h

theorem close_trans {k : Nat} {x y z : Rat} (hxy : Close k x y) (hyz : Close k y z) :
    Close k x z := by
  change Small k (x-z)
  rw [show x-z = (x-y)+(y-z) by grind]
  exact small_add hxy hyz

theorem affine_close_iff (k : Nat) (c : Rat) (a b : Int) :
    Close k (c+(a:Rat)) (c+(b:Rat)) ↔ (277 : Int)^k ∣ a-b := by
  change Small k ((c+(a:Rat))-(c+(b:Rat))) ↔ _
  rw [show (c+(a:Rat))-(c+(b:Rat)) = ((a-b : Int) : Rat) by rw [Rat.intCast_sub]; grind]
  exact small_int_iff k (a-b)

/-- A rational with unit denominator admits an integer approximation at any precision. -/
theorem integer_approximation {q : Rat} (hq : Small 0 q) (k : Nat) :
    ∃ z : Int, Close k q (z : Rat) := by
  obtain ⟨a,b,hb,hq⟩ := hq
  have hnum : q*(b:Rat) = (a:Rat) := by simpa [scale] using hq
  obtain ⟨i,j,hij⟩ := TameAdicDomain277.unit_at_all_depths b hb k
  have hbez : 1-b*i = (277 : Int)^k*j := by omega
  have hz : a-(a*i)*b = (277 : Int)^k*(a*j) := calc
    _ = a*(1-b*i) := by grind
    _ = _ := by rw [hbez]; grind
  refine ⟨a*i,a*j,b,hb,?_⟩
  have hcast := congrArg (fun v : Int => (v : Rat)) hz
  simp only [Rat.intCast_sub,Rat.intCast_mul] at hcast ⊢
  calc
    _ = (a:Rat) - ((a:Rat)*(i:Rat))*(b:Rat) := by grind
    _ = _ := hcast

/-- Cauchy sequences for the ordinary 277-adic topology on ℚ. -/
def RatCauchy (s : Nat → Rat) : Prop :=
  ∀ k, ∃ N, ∀ i ≥ N, ∀ j ≥ N, Close k (s i) (s j)

def Equivalent (s t : Nat → Rat) : Prop :=
  ∀ k, ∃ N, ∀ i ≥ N, Close k (s i) (t i)

theorem equivalent_refl (s : Nat → Rat) : Equivalent s s :=
  fun k => ⟨0,fun i _ => close_refl k (s i)⟩

theorem equivalent_symm {s t : Nat → Rat} (h : Equivalent s t) : Equivalent t s := by
  intro k
  obtain ⟨N,hN⟩ := h k
  exact ⟨N,fun i hi => close_symm (hN i hi)⟩

theorem equivalent_trans {s t u : Nat → Rat} (hst : Equivalent s t) (htu : Equivalent t u) :
    Equivalent s u := by
  intro k
  obtain ⟨N,hN⟩ := hst k
  obtain ⟨M,hM⟩ := htu k
  exact ⟨max N M,fun i hi => close_trans (hN i (Nat.le_trans (Nat.le_max_left _ _) hi))
    (hM i (Nat.le_trans (Nat.le_max_right _ _) hi))⟩

theorem cauchy_transfer {s t : Nat → Rat} (hs : RatCauchy s) (hst : Equivalent s t) :
    RatCauchy t := by
  intro k
  obtain ⟨N,hN⟩ := hs k
  obtain ⟨M,hM⟩ := hst k
  refine ⟨max N M,fun i hi j hj => ?_⟩
  exact close_trans (close_symm (hM i (Nat.le_trans (Nat.le_max_right _ _) hi)))
    (close_trans (hN i (Nat.le_trans (Nat.le_max_left _ _) hi)
        j (Nat.le_trans (Nat.le_max_left _ _) hj))
      (hM j (Nat.le_trans (Nat.le_max_right _ _) hj)))

theorem affine_cauchy_iff (c : Rat) (z : Nat → Int) :
    RatCauchy (fun i => c+(z i : Rat)) ↔ TameCauchy277.IsCauchy z := by
  rw [TameCauchy277.cauchy_divisibility_iff]
  constructor
  · intro h k
    obtain ⟨N,hN⟩ := h k
    exact ⟨N,fun i hi j hj => (affine_close_iff k c _ _).mp (hN i hi j hj)⟩
  · intro h k
    obtain ⟨N,hN⟩ := h k
    exact ⟨N,fun i hi j hj => (affine_close_iff k c _ _).mpr (hN i hi j hj)⟩

theorem tail_approximation (s : Nat → Rat) (N : Nat)
    (h : ∀ i ≥ N, Small 0 (s i-s N)) :
    ∃ z : Nat → Int, ∀ i ≥ N, Close i (s i) (s N + (z i : Rat)) := by
  classical
  let z : Nat → Int := fun i => if hi : N ≤ i
    then Classical.choose (integer_approximation (h i hi) i) else 0
  refine ⟨z,fun i hi => ?_⟩
  have hclose := Classical.choose_spec (integer_approximation (h i hi) i)
  change Small i (s i - (s N + (z i:Rat)))
  rw [show s i - (s N + (z i:Rat)) = (s i-s N) - (z i:Rat) by grind]
  simpa only [z,dif_pos hi,Close] using hclose

theorem equivalent_of_increasing_precision {s t : Nat → Rat} {N : Nat}
    (h : ∀ i ≥ N, Close i (s i) (t i)) : Equivalent s t := by
  intro k
  refine ⟨max N k,fun i hi => ?_⟩
  exact small_drop (Nat.le_trans (Nat.le_max_right _ _) hi)
    (h i (Nat.le_trans (Nat.le_max_left _ _) hi))

/-- Every rational Cauchy sequence has a fixed rational translate whose tail
is equivalent, to all precisions, to a genuinely integral Cauchy sequence. -/
theorem rational_cauchy_integer_tail (s : Nat → Rat) (hs : RatCauchy s) :
    ∃ c : Rat, ∃ z : TameCauchy277.CauchySeq, Equivalent s (fun i => c+(z.term i : Rat)) := by
  obtain ⟨N,hN⟩ := hs 0
  obtain ⟨z,hz⟩ := tail_approximation s N (fun i hi => hN i hi N (Nat.le_refl N))
  have he : Equivalent s (fun i => s N+(z i:Rat)) := equivalent_of_increasing_precision hz
  have hc := (affine_cauchy_iff (s N) z).mp (cauchy_transfer hs he)
  exact ⟨s N,⟨z,hc⟩,he⟩

structure RationalSeq where
  term : Nat → Rat
  cauchy : RatCauchy term

def Rel (s t : RationalSeq) : Prop := Equivalent s.term t.term

def RationalCompletion := Quot Rel

theorem quot_eq_iff (s t : RationalSeq) : Quot.mk Rel s = Quot.mk Rel t ↔ Rel s t := by
  let S : Setoid RationalSeq :=
    ⟨Rel,⟨fun x => equivalent_refl x.term, fun h => equivalent_symm h,
      fun h g => equivalent_trans h g⟩⟩
  exact ⟨fun h => @Quotient.exact _ S _ _ h, Quot.sound⟩

def affineSeq (c : Rat) (s : TameCauchy277.CauchySeq) : RationalSeq :=
  ⟨fun i => c+(s.term i:Rat),(affine_cauchy_iff c s.term).mpr s.cauchy⟩

theorem affine_rel_iff (c : Rat) (s t : TameCauchy277.CauchySeq) :
    Rel (affineSeq c s) (affineSeq c t) ↔ TameCauchy277.Same s t := by
  rw [TameCauchy277.same_divisibility_iff]
  constructor
  · intro h k
    obtain ⟨N,hN⟩ := h k
    exact ⟨N,fun i hi => (affine_close_iff k c _ _).mp (hN i hi)⟩
  · intro h k
    obtain ⟨N,hN⟩ := h k
    exact ⟨N,fun i hi => (affine_close_iff k c _ _).mpr (hN i hi)⟩

/-- Translation by a fixed rational of the embedded completed integers. -/
def affine (c : Rat) : TameCauchy277.Completion → RationalCompletion :=
  Quot.lift (fun s => Quot.mk Rel (affineSeq c s))
    (fun s t h => Quot.sound ((affine_rel_iff c s t).mpr h))

theorem affine_injective (c : Rat) (X Y : TameCauchy277.Completion) :
    affine c X = affine c Y → X = Y := by
  induction X using Quot.ind with
  | mk s =>
    induction Y using Quot.ind with
    | mk t =>
      intro h
      exact Quot.sound ((affine_rel_iff c s t).mp ((quot_eq_iff _ _).mp h))

theorem affine_cover (X : RationalCompletion) :
    ∃ c : Rat, ∃ z : Integer277, affine c (TameCauchy277.ofInteger z) = X := by
  induction X using Quot.ind with
  | mk s =>
    obtain ⟨c,t,he⟩ := rational_cauchy_integer_tail s.term s.cauchy
    let T : TameCauchy277.Completion := Quot.mk _ t
    refine ⟨c,TameCauchy277.toInteger T,?_⟩
    rw [TameCauchy277.ofInteger_toInteger]
    exact Quot.sound (equivalent_symm he)

/-- Each rational translate is a copy of the inverse-limit integers, and these
translates cover all Cauchy classes of rationals. -/
theorem affine_coordinates :
    (∀ c : Rat, ∀ x y : Integer277, affine c (TameCauchy277.ofInteger x) =
      affine c (TameCauchy277.ofInteger y) → x=y) ∧
    (∀ X : RationalCompletion, ∃ c : Rat, ∃ z : Integer277,
      affine c (TameCauchy277.ofInteger z) = X) := by
  refine ⟨?_,affine_cover⟩
  intro c x y h
  have e := congrArg TameCauchy277.toInteger (affine_injective c _ _ h)
  simpa only [TameCauchy277.toInteger_ofInteger] using e

theorem overlap_integral {c d : Rat} {s t : TameCauchy277.CauchySeq}
    (h : Rel (affineSeq c s) (affineSeq d t)) : Small 0 (c-d) := by
  obtain ⟨N,hN⟩ := h 0
  have hs : Small 0 ((c+(s.term N:Rat))-(d+(t.term N:Rat))) := hN N (Nat.le_refl N)
  have hi : Small 0 (((t.term N - s.term N : Int)) : Rat) :=
    (small_int_iff 0 _).mpr (by simp)
  have he : c-d = ((c+(s.term N:Rat))-(d+(t.term N:Rat))) +
      (((t.term N - s.term N : Int)) : Rat) := by rw [Rat.intCast_sub]; grind
  rw [he]
  exact small_add hs hi

theorem overlap_of_integral {c d : Rat} (h : Small 0 (c-d)) :
    ∃ t : TameCauchy277.CauchySeq,
      Rel (affineSeq c (TameCauchy277.constantSeq 0)) (affineSeq d t) := by
  let z : Nat → Int := fun i => Classical.choose (integer_approximation h i)
  have ha : ∀ i, Close i c (d+(z i:Rat)) := by
    intro i
    change Small i (c-(d+(z i:Rat)))
    rw [show c-(d+(z i:Rat)) = (c-d)-(z i:Rat) by grind]
    exact Classical.choose_spec (integer_approximation h i)
  have he : Equivalent (fun _ => c) (fun i => d+(z i:Rat)) :=
    equivalent_of_increasing_precision (N:=0) (fun i _ => ha i)
  have hc : RatCauchy (fun _ => c) := fun k => ⟨0,fun _ _ _ _ => close_refl k c⟩
  have hz := (affine_cauchy_iff d z).mp (cauchy_transfer hc he)
  refine ⟨⟨z,hz⟩,?_⟩
  change Equivalent (fun _ => c+((0:Int):Rat)) (fun i => d+(z i:Rat))
  simpa only [Rat.intCast_zero, Rat.add_zero] using he

/-- Two translated copies of the completed integers intersect precisely when
their rational centers differ by a rational with denominator prime to 277. -/
theorem affine_overlap_iff (c d : Rat) :
    (∃ X Y : TameCauchy277.Completion, affine c X = affine d Y) ↔ Small 0 (c-d) := by
  constructor
  · rintro ⟨X,Y,h⟩
    induction X using Quot.ind with
    | mk s =>
      induction Y using Quot.ind with
      | mk t => exact overlap_integral ((quot_eq_iff _ _).mp h)
  · intro h
    obtain ⟨t,ht⟩ := overlap_of_integral h
    exact ⟨Quot.mk _ (TameCauchy277.constantSeq 0),Quot.mk _ t,Quot.sound ht⟩

end Reimann.TameRationalCauchy277
