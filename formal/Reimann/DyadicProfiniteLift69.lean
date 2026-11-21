import Std

/-! Compactness for a countable inverse system of finite sets of admissible lifts. -/
namespace Reimann.DyadicProfiniteLift69

universe u
variable {X : Nat → Type u}

/-- Some candidate in a finite list survives every depth whenever one
survives each finite depth and the tests decrease with depth. -/
theorem finite_survivor {T : Type u} (candidates : List T) (test : T → Nat → Prop)
    (weaken : ∀ x m n, m ≤ n → test x n → test x m)
    (cover : ∀ n, ∃ x ∈ candidates, test x n) : ∃ x ∈ candidates, ∀ n, test x n := by
  classical
  induction candidates with
  | nil => obtain ⟨x,hx,_⟩ := cover 0; simp at hx
  | cons a l ih =>
    by_cases ha : ∀ n, test a n
    · exact ⟨a,by simp,ha⟩
    · obtain ⟨k,hk⟩ := Classical.not_forall.mp ha
      have tail (n : Nat) : ∃ x ∈ l, test x n := by
        obtain ⟨x,hx,ht⟩ := cover (max n k)
        rcases List.mem_cons.mp hx with e | h
        · subst x
          exact False.elim (hk (weaken a k _ (Nat.le_max_right ..) ht))
        · exact ⟨x,h,weaken x n _ (Nat.le_max_left ..) ht⟩
      obtain ⟨x,hx,ht⟩ := ih tail
      exact ⟨x,List.mem_cons_of_mem a hx,ht⟩

/-- A finite chain of adjacent restrictions, with the first step visible. -/
inductive Descends (down : (n : Nat) → X (n+1) → X n) :
    {n m : Nat} → X n → X m → Prop
  | refl {n} (x : X n) : Descends down x x
  | step {n m} (y : X (n+1)) {z : X m} (tail : Descends down y z) :
      Descends down (down n y) z

theorem descend_trans {down : (n : Nat) → X (n+1) → X n} {i j k : Nat}
    {x : X i} {y : X j} {z : X k} (h : Descends down x y) (g : Descends down y z) :
    Descends down x z := by
  induction h with
  | refl => exact g
  | step v _ ih => exact .step v (ih g)

theorem ancestor_at (down : (n : Nat) → X (n+1) → X n) {m : Nat} (z : X m)
    (n : Nat) (hn : n ≤ m) : ∃ x : X n, Descends down x z := by
  induction m with
  | zero =>
    obtain rfl : n=0 := by omega
    exact ⟨z,.refl _⟩
  | succ m ih =>
    by_cases eq : n=m+1
    · subst n; exact ⟨z,.refl _⟩
    · obtain ⟨v,hv⟩ := ih (down m z) (by omega)
      exact ⟨v,descend_trans hv (.step z (.refl _))⟩

theorem ancestor_mem {down : (n : Nat) → X (n+1) → X n} (L : (n : Nat) → List (X n))
    (closed : ∀ n x, x ∈ L (n+1) → down n x ∈ L n) {n m : Nat} {x : X n} {z : X m}
    (h : Descends down x z) (hz : z ∈ L m) : x ∈ L n := by
  induction h with
  | refl => exact hz
  | step y _ ih => exact closed _ y (ih hz)

def Reaches (down : (n : Nat) → X (n+1) → X n) (L : (n : Nat) → List (X n))
    {n : Nat} (x : X n) (k : Nat) : Prop :=
  ∃ m, k ≤ m ∧ ∃ z ∈ L m, Descends down x z

theorem reaches_weaken {down : (n : Nat) → X (n+1) → X n} {L : (n : Nat) → List (X n)}
    {n : Nat} (x : X n) {j k : Nat} (h : j ≤ k) (hk : Reaches down L x k) :
    Reaches down L x j := by
  obtain ⟨m,hm,z,hz,e⟩ := hk
  exact ⟨m,Nat.le_trans h hm,z,hz,e⟩

theorem first_child {down : (n : Nat) → X (n+1) → X n} {n m : Nat} {x : X n} {z : X m}
    (h : Descends down x z) (hlen : n < m) :
    ∃ y : X (n+1), down n y = x ∧ Descends down y z := by
  cases h with
  | refl => omega
  | step y tail => exact ⟨y,rfl,tail⟩

theorem root_survives (down : (n : Nat) → X (n+1) → X n) (L : (n : Nat) → List (X n))
    (closed : ∀ n x, x ∈ L (n+1) → down n x ∈ L n) (nonempty : ∀ n, ∃ x, x ∈ L n) :
    ∃ x ∈ L 0, ∀ k, Reaches down L x k := by
  apply finite_survivor (L 0) (fun x k => Reaches down L x k)
    (fun x _ _ h => reaches_weaken x h)
  intro k
  obtain ⟨z,hz⟩ := nonempty k
  obtain ⟨x,hx⟩ := ancestor_at down z 0 (Nat.zero_le _)
  exact ⟨x,ancestor_mem L closed hx hz,k,Nat.le_refl _,z,hz,hx⟩

theorem surviving_child (down : (n : Nat) → X (n+1) → X n) (L : (n : Nat) → List (X n))
    (closed : ∀ n x, x ∈ L (n+1) → down n x ∈ L n) {n : Nat} (x : X n)
    (live : ∀ k, Reaches down L x k) :
    ∃ y ∈ L (n+1), down n y=x ∧ ∀ k, Reaches down L y k := by
  let test (y : X (n+1)) (k : Nat) := down n y=x ∧ Reaches down L y k
  have cover (k : Nat) : ∃ y ∈ L (n+1), test y k := by
    obtain ⟨m,hm,z,hz,hxz⟩ := live (max k (n+1))
    obtain ⟨y,hy,hyz⟩ := first_child hxz (by omega)
    exact ⟨y,ancestor_mem L closed hyz hz,hy,m,by omega,z,hz,hyz⟩
  obtain ⟨y,hy,h⟩ := finite_survivor _ test
    (fun y _ _ h e => ⟨e.1,reaches_weaken y h e.2⟩) cover
  exact ⟨y,hy,(h 0).1,fun k => (h k).2⟩

/-- Countable finite inverse systems have coherent lifts even when the maps
are not surjective. The lists may use different ambient types at each level. -/
theorem coherent_lifts (down : (n : Nat) → X (n+1) → X n) (L : (n : Nat) → List (X n))
    (closed : ∀ n x, x ∈ L (n+1) → down n x ∈ L n) (nonempty : ∀ n, ∃ x, x ∈ L n) :
    ∃ s : (n : Nat) → X n, (∀ n, s n ∈ L n) ∧ ∀ n, down n (s (n+1)) = s n := by
  classical
  let Live (n : Nat) := {x : X n // x ∈ L n ∧ ∀ k, Reaches down L x k}
  obtain ⟨x,hx,hl⟩ := root_survives down L closed nonempty
  have extend (n : Nat) (x : Live n) : ∃ y : Live (n+1), down n y.val=x.val := by
    obtain ⟨y,hy,he,hv⟩ := surviving_child down L closed x.val x.property.2
    exact ⟨⟨y,hy,hv⟩,he⟩
  let seq : (n : Nat) → Live n := Nat.rec (motive := Live) ⟨x,hx,hl⟩
    (fun n v => Classical.choose (extend n v))
  exact ⟨fun n => (seq n).val,fun n => (seq n).property.1,
    fun n => Classical.choose_spec (extend n (seq n))⟩

/-- A compatible family of automorphisms with a prescribed image, all
stabilizing the selected prime, from the corresponding finite lifting tests. -/
theorem prescribed_prime_lifts {Y : Nat → Type u} (all : (n : Nat) → List (X n))
    (enumerates : ∀ n (x : X n), x ∈ all n) (down : (n : Nat) → X (n+1) → X n)
    (image : (n : Nat) → X n → Y n) (target : (n : Nat) → Y n)
    (stabilizes : (n : Nat) → X n → Prop)
    (finiteLift : ∀ n, ∃ x : X n, image n x=target n ∧ stabilizes n x)
    (restricts : ∀ n x, image (n+1) x=target (n+1) → stabilizes (n+1) x →
      image n (down n x)=target n ∧ stabilizes n (down n x)) :
    ∃ s : (n : Nat) → X n, (∀ n, image n (s n)=target n ∧ stabilizes n (s n)) ∧
      ∀ n, down n (s (n+1))=s n := by
  classical
  let L (n : Nat) := (all n).filter (fun x => decide (image n x=target n ∧ stabilizes n x))
  have mem (n : Nat) (x : X n) : x ∈ L n ↔ image n x=target n ∧ stabilizes n x := by
    simp [L,enumerates]
  obtain ⟨s,hs,hd⟩ := coherent_lifts down L (by
    intro n x hx
    obtain ⟨hi,hp⟩ := (mem (n+1) x).mp hx
    exact (mem n _).mpr (restricts n x hi hp)) (by
    intro n
    obtain ⟨x,hx⟩ := finiteLift n
    exact ⟨x,(mem n x).mpr hx⟩)
  exact ⟨s,fun n => (mem n (s n)).mp (hs n),hd⟩

end Reimann.DyadicProfiniteLift69
