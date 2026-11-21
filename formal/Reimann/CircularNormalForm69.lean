import Reimann.CircularRelationEval69

/-! Reduction of any finite rational polynomial preserves its value at a root. -/

namespace Reimann.CircularNormalForm69

open Lean.Grind CircularGauss69 CircularMonomial69 CircularRelationEval69

def Represents {R : Type} [Field R] (x : R) (p : Nat → Rat) (y : R) : Prop :=
  ∃ m, Bounded p m ∧ evalAt x p m = y

theorem value_at_bound {R : Type} [Field R] (x : R) (p : Nat → Rat) (y : R)
    (hv : Represents x p y) (m : Nat) (hb : Bounded p m) : evalAt x p m = y := by
  obtain ⟨n,hn,he⟩ := hv
  exact (eval_extend x p m (max m n) hb (Nat.le_max_left ..)).symm.trans
    ((eval_extend x p n (max m n) hn (Nat.le_max_right ..)).trans he)

theorem same_value_subtract_root {R : Type} [Field R] [IsCharP R 0]
    (x y : R) (f g : Nat → Rat) (hf : Represents x f y) (hg : Vanishes x g) :
    Represents x (fun i => f i - g i) y := by
  obtain ⟨m,bf,ef⟩ := hf
  obtain ⟨n,bg,eg⟩ := hg
  refine ⟨max m n, ?_, ?_⟩
  · intro k hk
    change f k - g k = 0
    rw [bf k (by omega), bg k (by omega), Rat.sub_self]
  · rw [eval_sub, eval_extend x f m _ bf (Nat.le_max_left ..),
      eval_extend x g n _ bg (Nat.le_max_right ..), ef, eg]
    grind only

theorem normal_form_at_root {R : Type} [Field R] [IsCharP R 0] (x : R)
    (D : Nat → Rat) (d : Nat) (hD : Bounded D (d+1)) (hm : D d = 1) (hv : Vanishes x D)
    (p : Nat → Rat) (m : Nat) (hp : Bounded p m) :
    ∃ r, Bounded r d ∧ evalAt x r d = evalAt x p m := by
  let y := evalAt x p m
  obtain ⟨_,r,_,br,vr,_⟩ := division_preserving D d hD hm (fun f => Represents x f y)
    (fun f s a hf => same_value_subtract_root x y f _ hf (vanishes_shift x D s a hv))
    m p hp ⟨m,hp,rfl⟩
  exact ⟨r,br,value_at_bound x r y vr d br⟩

theorem unique_at_degree {R : Type} [Field R] [IsCharP R 0] (x : R) (d : Nat)
    (indep : ∀ f, Bounded f d → evalAt x f d = 0 → ∀ i, f i = 0)
    (p q : Nat → Rat) (bp : Bounded p d) (bq : Bounded q d)
    (h : evalAt x p d = evalAt x q d) : p = q := by
  have b : Bounded (fun k => p k - q k) d := by
    intro k hk; change p k - q k = 0; rw [bp k hk, bq k hk, Rat.sub_self]
  have he : evalAt x (fun k => p k - q k) d = 0 := by rw [eval_sub, h]; grind only
  funext i
  have hi := indep _ b he i
  change p i - q i = 0 at hi
  grind

end Reimann.CircularNormalForm69
