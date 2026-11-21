import Reimann.DyadicRealLayer

/-! Valuations on the compositum with a dyadic cyclotomic field. We use
rational additive values normalized by v(2)=1 and assign v(0)=0 only
as a convention. All multiplicative and unequal-value laws exclude zero. -/
namespace Reimann.DyadicDecomposition69

open Lean.Grind

structure DyadicValue (F : Type) [Field F] where
  val : F → Rat
  zero : val 0 = 0
  two_ne : (2 : F) ≠ 0
  two : val 2 = 1
  mul : ∀ {x y : F}, x ≠ 0 → y ≠ 0 → val (x*y) = val x + val y
  smaller : ∀ {x y : F}, x ≠ 0 → y ≠ 0 → val x < val y →
    x+y ≠ 0 ∧ val (x+y) = val x

variable {F : Type} [Field F]

/-- If u+v=2 and v(uv)≤1, the two factors have equal additive value. -/
theorem equal_at_halving (V : DyadicValue F) {u v : F} (hu : u≠0) (hv : v≠0)
    (hs : u+v=2) (hp : V.val (u*v) ≤ 1) : V.val u = V.val v := by
  have hsum : V.val (u+v) = 1 := hs ▸ V.two
  rw [V.mul hu hv] at hp
  by_cases h : V.val u < V.val v
  · have lo := (V.smaller hu hv h).2
    rw [hsum] at lo
    grind
  · by_cases k : V.val v < V.val u
    · have lo := (V.smaller hv hu k).2
      rw [AddCommMonoid.add_comm v u,hsum] at lo
      grind
    · grind

/-- Exact value at every dyadic place of an actual primitive dyadic root,
including z=-1. It follows just from (1-z)(1+z)=1-z². -/
theorem cyclotomic_uniformizer_value (V : DyadicValue F) (n : Nat) (z : F)
    (hz : z^(2^n : Nat) = -1) :
    1-z ≠ 0 ∧ V.val (1-z) ≤ 1 ∧ ((2^n : Nat) : Rat) * V.val (1-z) = 1 := by
  induction n generalizing z with
  | zero =>
    have he : z = -1 := by simpa only [Nat.pow_zero,Semiring.pow_one] using hz
    rw [he,show (1 : F) - -1 = 2 by grind only,V.two]
    exact ⟨V.two_ne,by decide,by simp⟩
  | succ n ih =>
    have hsq : (z*z)^(2^n : Nat) = -1 := by
      rw [CommSemiring.mul_pow]
      exact (DyadicRealLayer.square_power z n).symm.trans hz
    obtain ⟨hn,hlo,hm⟩ := ih (z*z) hsq
    have hp : (1-z)*(1+z) = 1-z*z := by grind only
    have hu : 1-z ≠ 0 := by intro h; rw [← hp,h,Semiring.zero_mul] at hn; exact hn rfl
    have hv : 1+z ≠ 0 := by intro h; rw [← hp,h,Semiring.mul_zero] at hn; exact hn rfl
    have hvv := equal_at_halving V hu hv (by grind only) (hp ▸ hlo)
    have he := V.mul hu hv
    rw [hp,←hvv] at he
    refine ⟨hu,by grind,?_⟩
    rw [Nat.pow_succ,Rat.natCast_mul]
    grind

/-- v is congruent to j/N modulo the integers, expressed without division. -/
def Digit (N j : Nat) (v : Rat) : Prop :=
  ∃ k : Int, (N : Rat)*v = (((N : Int)*k+(j : Int) : Int) : Rat)

theorem integer_digit (N : Nat) (k : Int) : Digit N 0 (k : Rat) := by
  refine ⟨k,?_⟩
  simp [Rat.intCast_mul,Rat.intCast_natCast]

theorem shift_digit {N j : Nat} {u v : Rat} (hu : (N:Rat)*u=1) (h : Digit N j v) :
    Digit N (j+1) (u+v) := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Rat.intCast_add,Rat.intCast_mul,Rat.intCast_one] at *
  grind

theorem digit_nonintegral {N j : Nat} {v : Rat} (hj : 0 < j) (hlt : j<N)
    (hv : Digit N j v) (a : Int) : v ≠ (a : Rat) := by
  rintro rfl
  obtain ⟨b,h⟩ := hv
  have eq : (N:Int)*a = (N:Int)*b+j := by
    apply Rat.intCast_inj.mp
    simpa only [Rat.intCast_mul,Rat.intCast_natCast] using h
  have hd : (N:Int) ∣ (j:Int) := ⟨a-b,by grind⟩
  have ha := Int.ofNat_dvd.mp hd
  exact (Nat.not_dvd_of_pos_of_lt hj hlt) ha

/-- For a coefficient, the two valuations are the same integer. -/
def AgreeIntegral (V W : DyadicValue F) (c : F) : Prop :=
  c=0 ∨ ∃ k : Int, V.val c = (k : Rat) ∧ W.val c = (k : Rat)

def Detected (V W : DyadicValue F) (N j : Nat) (x : F) : Prop :=
  x ≠ 0 ∧ V.val x = W.val x ∧ Digit N j (V.val x)

theorem take_smaller (V W : DyadicValue F) {x y : F} {N i j : Nat}
    (hx : Detected V W N i x) (hy : Detected V W N j y) (hlt : V.val x < V.val y) :
    Detected V W N i (x+y) := by
  obtain ⟨nx,ex,dx⟩ := hx
  obtain ⟨ny,ey,_⟩ := hy
  obtain ⟨hn,hv⟩ := V.smaller nx ny hlt
  have hw := (W.smaller nx ny (ex ▸ ey ▸ hlt)).2
  exact ⟨hn,hv.trans (ex.trans hw.symm),hv ▸ dx⟩

def horner (x : F) : List F → F
  | [] => 0
  | c::cs => c+x*horner x cs

/-- The distinct fractional parts ensure that no two live terms cancel below degree N. -/
theorem leading_term (V W : DyadicValue F) (N : Nat) (u : F)
    (hu : u ≠ 0) (hval : V.val u = W.val u) (huv : (N : Rat)*V.val u=1)
    (cs : List F) (hN : cs.length ≤ N) (hc : ∀ c ∈ cs, AgreeIntegral V W c) :
    horner u cs=0 ∨ ∃ j < cs.length, Detected V W N j (horner u cs) := by
  induction cs with
  | nil => exact Or.inl rfl
  | cons c cs ih =>
    have hlen : cs.length+1≤N := hN
    have hc' := hc c (by simp)
    have cf (nz : c≠0) : Detected V W N 0 c := by
      obtain ⟨k,hv,hw⟩ := hc'.resolve_left nz
      exact ⟨nz,hv.trans hw.symm,hv ▸ integer_digit N k⟩
    rcases ih (by omega) (fun t ht => hc t (by simp [ht])) with h | ⟨j,hj,nz,eq,dig⟩
    · simp only [horner,h,Semiring.mul_zero,AddCommMonoid.add_zero,List.length_cons]
      by_cases hz : c=0
      · exact Or.inl hz
      · exact Or.inr ⟨0,by omega,cf hz⟩
    · have py : u*horner u cs ≠ 0 := fun h => (Field.of_mul_eq_zero h).elim hu nz
      have vv := V.mul hu nz
      have ww := W.mul hu nz
      have pd : Detected V W N (j+1) (u*horner u cs) :=
        ⟨py,by rw [vv,ww,hval,eq],vv ▸ shift_digit huv dig⟩
      apply Or.inr
      by_cases cz : c=0
      · exact ⟨j+1,by simp; omega,by simpa only [horner,cz,AddCommMonoid.zero_add] using pd⟩
      · obtain ⟨k,hv,_⟩ := hc'.resolve_left cz
        have ne : V.val (u*horner u cs) ≠ V.val c := by
          rw [hv]
          exact digit_nonintegral (by omega) (by omega) pd.2.2 k
        by_cases lt : V.val c < V.val (u*horner u cs)
        · exact ⟨0,by simp,take_smaller V W (cf cz) pd lt⟩
        · have hlt : V.val (u*horner u cs) < V.val c := by grind
          refine ⟨j+1,by simp; omega,?_⟩
          rw [horner,AddCommMonoid.add_comm c (u*horner u cs)]
          exact take_smaller V W pd (cf cz) hlt

theorem bounded_place_unique (V W : DyadicValue F) (n : Nat) (z : F)
    (hz : z^(2^n : Nat) = -1) (cs : List F) (hlen : cs.length ≤ 2^n)
    (hc : ∀ c ∈ cs, AgreeIntegral V W c) :
    V.val (horner (1-z) cs) = W.val (horner (1-z) cs) := by
  obtain ⟨hn,_,hv⟩ := cyclotomic_uniformizer_value V n z hz
  obtain ⟨_,_,hw⟩ := cyclotomic_uniformizer_value W n z hz
  have pos : (0 : Rat) < ((2^n : Nat) : Rat) := Rat.natCast_pos.mpr (Nat.pow_pos (by decide))
  have eq : V.val (1-z) = W.val (1-z) := by
    have h : ((2^n : Nat) : Rat)*(V.val (1-z)-W.val (1-z)) = 0 := by grind only
    rcases Rat.mul_eq_zero.mp h with a|b <;> grind
  rcases leading_term V W (2^n) (1-z) hn eq hv cs hlen hc with h|⟨_,_,hd⟩
  · rw [h,V.zero,W.zero]
  · exact hd.2.1

/-- Agreement on coefficient values determines the place on every quotient of
bounded cyclotomic expansions; the nonzero denominator need not be a unit. -/
theorem cyclotomic_place_unique (V W : DyadicValue F) (n : Nat) (z x : F)
    (hz : z^(2^n : Nat) = -1) (p q : List F) (hp : p.length ≤ 2^n) (hq : q.length ≤ 2^n)
    (cp : ∀ c ∈ p, AgreeIntegral V W c) (cq : ∀ c ∈ q, AgreeIntegral V W c)
    (dn : horner (1-z) q ≠ 0) (frac : x*horner (1-z) q = horner (1-z) p) :
    V.val x = W.val x := by
  by_cases nx : x = 0
  · rw [nx,V.zero,W.zero]
  · have vp := bounded_place_unique V W n z hz p hp cp
    have vq := bounded_place_unique V W n z hz q hq cq
    rw [← frac,V.mul nx dn,W.mul nx dn,vq] at vp
    grind only

end Reimann.DyadicDecomposition69
