import Reimann.TameSplitting277
import Reimann.CyclicBoundary

namespace Reimann.TameRootExhaustion277

open Reimann.TameSplitting277

/-- The sum of roots agreeing initially has the same unit residue as a simple derivative. -/
theorem sum_unit_of_agreement (p x y d : Int) (h : p ∣ x-y)
    (hd : p ∣ 2*y*d-1) : ∃ c : Int, (x+y)*d = 1+p*c := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨v,hv⟩ := hd
  exact ⟨k*d+v, by grind⟩

/-- Two square roots at precision p^k with the same first digit coincide
there whenever the derivative of one of them is invertible at p. -/
theorem simple_root_unique (p a x y d : Int) (k : Nat) (hx : p^k ∣ x^2-a)
    (hy : p^k ∣ y^2-a) (h : p ∣ x-y) (hd : p ∣ 2*y*d-1) : p^k ∣ x-y := by
  obtain ⟨c,hc⟩ := sum_unit_of_agreement p x y d h hd
  apply (CyclicBoundary.cancel_unit_factor p c (x-y) k).mp
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := hy
  refine ⟨(u-v)*d, ?_⟩
  rw [← hc]
  grind

/-- false chooses the positive seed and true its negative. -/
def signed (negative : Bool) (x : Int) : Int := if negative then -x else x

theorem base_divides (p : Int) (n : Nat) : p ∣ p^(n+1) :=
  ⟨p^n, by rw [Int.pow_succ, Int.mul_comm]⟩

/-- Compatibility at adjacent levels preserves the initial residue. -/
theorem first_digit (p : Int) (z : Nat → Int)
    (hz : ∀ n, p^(n+1) ∣ z (n+1)-z n) (k : Nat) : p ∣ z k-z 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨x,hx⟩ := Int.dvd_trans (base_divides p k) (hz k)
    obtain ⟨y,hy⟩ := ih
    exact ⟨x+y, by grind⟩

theorem signed_data (a x d : Int) (n : Nat) (hs : SignedLevel a x d n) (b : Bool) :
    ((277 : Int)^(n+1) ∣ (signed b (liftPair a x d n).1)^2-a) ∧
    ((277 : Int)^(n+1) ∣ 2*(signed b (liftPair a x d n).1)*(signed b (liftPair a x d n).2)-1) ∧
    ((277 : Int)^(n+1) ∣ signed b (liftPair a x d (n+1)).1-signed b (liftPair a x d n).1) := by
  cases b with
  | false => exact ⟨hs.positive,hs.positiveSimple,hs.positiveCompatible⟩
  | true => exact ⟨hs.negative,hs.negativeSimple,hs.negativeCompatible⟩

/-- A root with a specified initial signed digit is exactly that Hensel lift at
the full precision. The converse will follow from the same root equations. -/
theorem root_with_given_digit (a x d : Int) (hs : ∀ n, SignedLevel a x d n)
    (b : Bool) (n : Nat) (z : Int) (hz : (277 : Int)^(n+1) ∣ z^2-a)
    (hseed : (277 : Int) ∣ z - signed b x) :
    (277 : Int)^(n+1) ∣ z - signed b (liftPair a x d n).1 := by
  let y := fun k => signed b (liftPair a x d k).1
  have hfirst := first_digit 277 y (fun k => (signed_data a x d k (hs k) b).2.2) n
  change (277 : Int) ∣ signed b (liftPair a x d n).1 - signed b x at hfirst
  obtain ⟨i,hi⟩ := hseed
  obtain ⟨j,hj⟩ := hfirst
  apply simple_root_unique 277 a z _ (signed b (liftPair a x d n).2) (n+1) hz
    (signed_data a x d n (hs n) b).1
  · exact ⟨i-j, by grind⟩
  · exact Int.dvd_trans (base_divides 277 n) (signed_data a x d n (hs n) b).2.1

theorem digit_representative (z : Int) :
    ∃ j : Fin 277, (277 : Int) ∣ z-(j.val : Int) := by
  let j : Fin 277 := ⟨(z%277).toNat, by omega⟩
  refine ⟨j,z/277,?_⟩
  change z - (((z%277).toNat : Nat) : Int) = _
  omega

theorem transport_square (m a x z : Int) (hr : m ∣ x^2-a) (hc : m ∣ z-x) :
    m ∣ z^2-a := by
  obtain ⟨i,hi⟩ := hr
  obtain ⟨j,hj⟩ := hc
  exact ⟨i+j*(z+x), by grind⟩

/-- Transfer the already enumerated finite-residue tests to integer roots. -/
theorem seed_test (k : Nat) (s : Int)
    (hfinite : ∀ j : Fin 277, (j.val^2+k)%277 = 0 →
      ∃ b : Bool, (277 : Int) ∣ (j.val : Int) - signed b s)
    (z : Int) (hz : (277 : Int) ∣ z^2-(-(k : Int))) :
    ∃ b : Bool, (277 : Int) ∣ z-signed b s := by
  obtain ⟨j,u,hu⟩ := digit_representative z
  have hj := transport_square 277 (-(k : Int)) z (j.val : Int) hz ⟨-u,by grind⟩
  have hd : (277 : Nat) ∣ j.val^2+k := by
    apply Int.ofNat_dvd.mp
    change (277 : Int) ∣ ((j.val^2+k : Nat) : Int)
    simpa only [Int.natCast_add,Int.natCast_pow,Int.sub_neg] using hj
  obtain ⟨b,v,hv⟩ := hfinite j (Nat.mod_eq_zero_of_dvd hd)
  exact ⟨b,u+v,by grind⟩

theorem both_seed_tests (z : Int) :
    ((277 : Int) ∣ z^2-(-3) → ∃ b, (277 : Int) ∣ z-signed b 44) ∧
    ((277 : Int) ∣ z^2-(-23) → ∃ b, (277 : Int) ∣ z-signed b 114) := by
  constructor
  · apply seed_test 3 44
    intro j hj
    rcases ((all_seed_residues j).1.mp hj) with h | h
    · exact ⟨false,by rw [h]; decide⟩
    · exact ⟨true,by rw [h]; decide⟩
  · apply seed_test 23 114
    intro j hj
    rcases ((all_seed_residues j).2.mp hj) with h | h
    · exact ⟨false,by rw [h]; decide⟩
    · exact ⟨true,by rw [h]; decide⟩

/-- At a fixed level the two choices of sign are distinct. -/
theorem sign_unique (m z y : Int) (hsep : ¬ m ∣ y-(-y)) (b c : Bool)
    (hb : m ∣ z-signed b y) (hc : m ∣ z-signed c y) : b = c := by
  obtain ⟨i,hi⟩ := hb
  obtain ⟨j,hj⟩ := hc
  cases b <;> cases c
  · rfl
  · exact False.elim (hsep ⟨j-i,by simp [signed] at hi hj; grind⟩)
  · exact False.elim (hsep ⟨i-j,by simp [signed] at hi hj; grind⟩)
  · rfl

/-- Exhaustion and uniqueness at a finite level, including the converse. -/
theorem root_at_level_iff (a x d : Int) (hs : ∀ n, SignedLevel a x d n)
    (seeds : ∀ z : Int, (277 : Int) ∣ z^2-a → ∃ b, (277 : Int) ∣ z-signed b x)
    (n : Nat) (z : Int) :
    ((277 : Int)^(n+1) ∣ z^2-a) ↔
    ∃ b, ((277 : Int)^(n+1) ∣ z-signed b (liftPair a x d n).1) ∧
      ∀ c, ((277 : Int)^(n+1) ∣ z-signed c (liftPair a x d n).1) → c=b := by
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := seeds z (Int.dvd_trans (base_divides 277 n) hz)
    have hfull := root_with_given_digit a x d hs b n z hz hb
    exact ⟨b,hfull,fun c hc => sign_unique _ _ _ (hs n).distinct c b hc hfull⟩
  · rintro ⟨b,hb,_⟩
    exact transport_square _ _ _ _ (signed_data a x d n (hs n) b).1 hb

/-- One sign works at every positive precision and it is unique. -/
theorem coherent_root_iff (a x d : Int) (hs : ∀ n, SignedLevel a x d n)
    (seeds : ∀ z : Int, (277 : Int) ∣ z^2-a → ∃ b, (277 : Int) ∣ z-signed b x)
    (z : Nat → Int) (hcoh : ∀ n, (277 : Int)^(n+1) ∣ z (n+1)-z n) :
    (∀ n, (277 : Int)^(n+1) ∣ (z n)^2-a) ↔
    ∃ b, (∀ n, (277 : Int)^(n+1) ∣ z n-signed b (liftPair a x d n).1) ∧
      (∀ c, ((277 : Int) ∣ z 0-signed c x) → c=b) := by
  constructor
  · intro hz
    have hzero : (277 : Int) ∣ (z 0)^2-a := by simpa using hz 0
    obtain ⟨b,hb⟩ := seeds (z 0) hzero
    refine ⟨b,fun n => ?_,fun c hc => ?_⟩
    · apply root_with_given_digit a x d hs b n (z n) (hz n)
      obtain ⟨i,hi⟩ := first_digit 277 z hcoh n
      obtain ⟨j,hj⟩ := hb
      exact ⟨i+j,by grind⟩
    · have hsep : ¬ (277 : Int) ∣ x-(-x) := by simpa [liftPair] using (hs 0).distinct
      exact sign_unique 277 (z 0) x hsep c b hc hb
  · rintro ⟨b,hb,_⟩ n
    exact transport_square _ _ _ _ (signed_data a x d n (hs n) b).1 (hb n)

def Matches (a x d : Int) (z : Nat → Int) (b : Bool) : Prop :=
  ∀ n, (277 : Int)^(n+1) ∣ z n-signed b (liftPair a x d n).1

/-- The simultaneous solutions in the inverse limit have exactly four
possible pairs of signs. Each solution's pair is fixed by its two first digits. -/
theorem four_signs_iff (z w : Nat → Int)
    (hz : ∀ n, (277 : Int)^(n+1) ∣ z (n+1)-z n)
    (hw : ∀ n, (277 : Int)^(n+1) ∣ w (n+1)-w n) :
    (∀ n, ((277 : Int)^(n+1) ∣ (z n)^2-(-3)) ∧
      ((277 : Int)^(n+1) ∣ (w n)^2-(-23))) ↔
    ∃ s : Bool × Bool, Matches (-3) 44 85 z s.1 ∧ Matches (-23) 114 130 w s.2 ∧
      ∀ t : Bool × Bool, ((277 : Int) ∣ z 0-signed t.1 44) →
        ((277 : Int) ∣ w 0-signed t.2 114) → t=s := by
  have h1 := coherent_root_iff (-3) 44 85 (fun n => (split_both_277 n).1)
    (fun x => (both_seed_tests x).1) z hz
  have h2 := coherent_root_iff (-23) 114 130 (fun n => (split_both_277 n).2)
    (fun x => (both_seed_tests x).2) w hw
  constructor
  · intro h
    obtain ⟨b,hb,hbu⟩ := h1.mp (fun n => (h n).1)
    obtain ⟨c,hc,hcu⟩ := h2.mp (fun n => (h n).2)
    exact ⟨(b,c),hb,hc,fun t ht kt => Prod.ext (hbu t.1 ht) (hcu t.2 kt)⟩
  · rintro ⟨s,hs,ks,_⟩ n
    exact ⟨transport_square _ _ _ _ (signed_data _ _ _ n (split_both_277 n).1 s.1).1 (hs n),
      transport_square _ _ _ _ (signed_data _ _ _ n (split_both_277 n).2 s.2).1 (ks n)⟩

/-- Each of the four labels actually occurs, as witnessed by signed Newton sequences. -/
theorem every_sign_pair_occurs (s : Bool × Bool) :
    ∃ z w : Nat → Int, Matches (-3) 44 85 z s.1 ∧ Matches (-23) 114 130 w s.2 ∧
      ∀ n, ((277 : Int)^(n+1) ∣ z (n+1)-z n) ∧
        ((277 : Int)^(n+1) ∣ w (n+1)-w n) ∧
        ((277 : Int)^(n+1) ∣ (z n)^2-(-3)) ∧ ((277 : Int)^(n+1) ∣ (w n)^2-(-23)) := by
  refine ⟨fun n => signed s.1 (liftPair (-3) 44 85 n).1,
    fun n => signed s.2 (liftPair (-23) 114 130 n).1,?_,?_,fun n => ?_⟩
  · intro n; simp
  · intro n; simp
  · obtain ⟨z,_,cz⟩ := signed_data _ _ _ n (split_both_277 n).1 s.1
    obtain ⟨w,_,cw⟩ := signed_data _ _ _ n (split_both_277 n).2 s.2
    exact ⟨cz,cw,z,w⟩

end Reimann.TameRootExhaustion277
