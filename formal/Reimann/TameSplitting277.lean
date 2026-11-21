import Std

namespace Reimann.TameSplitting277

/-- A Newton step for the quadratic with an integral inverse representative. -/
def rootStep (a x d : Int) : Int := x-d*(x^2-a)

theorem root_error (a x d : Int) :
    (rootStep a x d)^2-a = (x^2-a)*(-(2*x*d-1)+d^2*(x^2-a)) := by
  unfold rootStep
  grind

theorem derivative_error (a x d : Int) :
    2*(rootStep a x d)*d-1 = (2*x*d-1)-2*d^2*(x^2-a) := by
  unfold rootStep
  grind

def inverseStep (y d : Int) : Int := d*(2-2*y*d)

theorem inverse_error (y d : Int) :
    2*y*inverseStep y d-1 = -(2*y*d-1)^2 := by unfold inverseStep; grind

/-- Both the root and its derivative inverse lift from modulus m to m². -/
theorem newton_precision (a x d m : Int) (hx : m ∣ x^2-a) (hd : m ∣ 2*x*d-1) :
    (m*m ∣ (rootStep a x d)^2-a) ∧
    (m*m ∣ 2*(rootStep a x d)*inverseStep (rootStep a x d) d-1) := by
  obtain ⟨e,he⟩ := hx
  obtain ⟨v,hv⟩ := hd
  constructor
  · rw [root_error,he,hv]
    exact ⟨e*(-v+d^2*e), by grind⟩
  · rw [inverse_error,derivative_error,he,hv]
    exact ⟨-(v-2*d^2*e)^2, by grind⟩

theorem quadratic_to_successor (p : Int) (n : Nat) :
    p^(n+2) ∣ p^(n+1)*p^(n+1) := by
  refine ⟨p^n, ?_⟩
  rw [Int.pow_succ p (n+1), Int.pow_succ p n]
  grind

/-- At depth n the pair represents a root and its derivative inverse modulo
    p^(n+1). The update itself works over the integers. -/
def liftPair (a x d : Int) : Nat → Int × Int
  | 0 => (x,d)
  | n+1 =>
    let s := liftPair a x d n
    let y := rootStep a s.1 s.2
    (y, inverseStep y s.2)

theorem liftPair_precision (p a x d : Int) (hx : p ∣ x^2-a) (hd : p ∣ 2*x*d-1) (n : Nat) :
    (p^(n+1) ∣ (liftPair a x d n).1^2-a) ∧
    (p^(n+1) ∣ 2*(liftPair a x d n).1*(liftPair a x d n).2-1) := by
  induction n with
  | zero => simpa [liftPair, Int.pow_one] using And.intro hx hd
  | succ n ih =>
    obtain ⟨h1,h2⟩ := newton_precision _ _ _ _ ih.1 ih.2
    exact ⟨Int.dvd_trans (quadratic_to_successor p n) h1,
      Int.dvd_trans (quadratic_to_successor p n) h2⟩

/-- Consecutive roots and consecutive inverse derivatives agree at the old precision. -/
theorem liftPair_coherent (p a x d : Int) (hx : p ∣ x^2-a) (hd : p ∣ 2*x*d-1) (n : Nat) :
    (p^(n+1) ∣ (liftPair a x d (n+1)).1-(liftPair a x d n).1) ∧
    (p^(n+1) ∣ (liftPair a x d (n+1)).2-(liftPair a x d n).2) := by
  let s := liftPair a x d n
  obtain ⟨⟨e,he⟩,⟨v,hv⟩⟩ := liftPair_precision p a x d hx hd n
  change s.1^2-a = _ at he
  change 2*s.1*s.2-1 = _ at hv
  change (_ ∣ rootStep a s.1 s.2-s.1) ∧ (_ ∣ inverseStep (rootStep a s.1 s.2) s.2-s.2)
  constructor
  · refine ⟨-s.2*e, ?_⟩
    unfold rootStep
    rw [he]
    grind
  · have hv' := derivative_error a s.1 s.2
    rw [he,hv] at hv'
    refine ⟨-s.2*(v-2*s.2^2*e), ?_⟩
    unfold inverseStep
    grind

/-- For the four signed roots, the negative inverse is obtained by the same sign. -/
theorem simple_seeds :
    ((277 : Int) ∣ 44^2-(-3)) ∧ ((277 : Int) ∣ 2*44*85-1) ∧
    ((277 : Int) ∣ 114^2-(-23)) ∧ ((277 : Int) ∣ 2*114*130-1) ∧
    (-44 : Int)%277 = 233 ∧ (-114 : Int)%277 = 163 := by decide +kernel

/-- Exhaust all residue representatives at the initial level. -/
theorem all_seed_residues : ∀ j : Fin 277,
    ((j.val^2+3)%277 = 0 ↔ j.val = 44 ∨ j.val = 233) ∧
    ((j.val^2+23)%277 = 0 ↔ j.val = 114 ∨ j.val = 163) := by
  decide +kernel

/-- Invertibility of the derivative prevents the two signed roots from agreeing. -/
theorem signed_distinct (m y d : Int) (hm : ¬ m ∣ 1) (hd : m ∣ 2*y*d-1) :
    ¬ m ∣ y-(-y) := by
  rintro ⟨k,hk⟩
  obtain ⟨j,hj⟩ := hd
  exact hm ⟨k*d-j, by grind⟩

theorem precision_nonunit (n : Nat) : ¬ (277 : Int)^(n+1) ∣ 1 := by
  intro hh
  have hd : (277 : Int) ∣ (277 : Int)^(n+1) := ⟨277^n, by rw [Int.pow_succ, Int.mul_comm]⟩
  exact (by decide : ¬ (277 : Int) ∣ 1) (Int.dvd_trans hd hh)

/-- Signed roots, inverse derivatives, separation and compatibility at one
    finite level. The integer recurrences fix representatives across levels. -/
structure SignedLevel (a x d : Int) (n : Nat) : Prop where
  positive : (277 : Int)^(n+1) ∣ (liftPair a x d n).1^2-a
  negative : (277 : Int)^(n+1) ∣ (-(liftPair a x d n).1)^2-a
  positiveSimple : (277 : Int)^(n+1) ∣ 2*(liftPair a x d n).1*(liftPair a x d n).2-1
  negativeSimple : (277 : Int)^(n+1) ∣ 2*(-(liftPair a x d n).1)*(-(liftPair a x d n).2)-1
  distinct : ¬ (277 : Int)^(n+1) ∣ (liftPair a x d n).1-(-(liftPair a x d n).1)
  positiveCompatible : (277 : Int)^(n+1) ∣ (liftPair a x d (n+1)).1-(liftPair a x d n).1
  negativeCompatible : (277 : Int)^(n+1) ∣ (-(liftPair a x d (n+1)).1)-(-(liftPair a x d n).1)

theorem signed_tower (a x d : Int) (hx : 277 ∣ x^2-a) (hd : 277 ∣ 2*x*d-1) (n : Nat) :
    SignedLevel a x d n := by
  obtain ⟨h1,h2⟩ := liftPair_precision 277 a x d hx hd n
  obtain ⟨h3,_⟩ := liftPair_coherent 277 a x d hx hd n
  refine ⟨h1, ?_, h2, ?_, signed_distinct _ _ _ (precision_nonunit n) h2, h3, ?_⟩
  · have eqn : (-(liftPair a x d n).1)^2 = (liftPair a x d n).1^2 := by grind
    rwa [eqn]
  · have eqn : 2*(-(liftPair a x d n).1)*(-(liftPair a x d n).2) =
        2*(liftPair a x d n).1*(liftPair a x d n).2 := by grind
    rwa [eqn]
  · obtain ⟨k,hk⟩ := h3
    exact ⟨-k, by grind⟩

/-- The two generating quadratics each split into distinct simple roots,
    with the same two signs compatible through all positive 277-power levels. -/
theorem split_both_277 (n : Nat) :
    SignedLevel (-3) 44 85 n ∧ SignedLevel (-23) 114 130 n :=
  ⟨signed_tower _ _ _ simple_seeds.1 simple_seeds.2.1 n,
   signed_tower _ _ _ simple_seeds.2.2.1 simple_seeds.2.2.2.1 n⟩

end Reimann.TameSplitting277
