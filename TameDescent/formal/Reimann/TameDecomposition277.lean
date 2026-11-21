import Reimann.TameOrderFaithful277
import Reimann.TameEmbeddings277

namespace Reimann.TameDecomposition277

open TameRationalField277 TameArithmetic277 TamePrimePowers277

abbrev Signs := Bool × Bool

def change (s t : Signs) : Signs := (s.1.xor t.1,s.2.xor t.2)

def signed {A : Type} [Neg A] (s : Bool) (x : A) : A := if s then -x else x

/-- Conjugation on the coordinates 1, X, Y, XY of the rational field or integral order. -/
def conjugate {A : Type} [Neg A] (s : Signs) (v : (A × A) × (A × A)) :
    (A × A) × (A × A) :=
  ((v.1.1,signed s.1 v.1.2),(signed s.2 v.2.1,signed (s.1.xor s.2) v.2.2))

theorem sign_action (s t : Signs) (x : Biquad) :
    conjugate s (conjugate t x) = conjugate (change s t) x := by
  rcases s with ⟨a,b⟩
  rcases t with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [change,conjugate,signed,Bool.xor]

theorem sign_involution (s : Signs) (x : Biquad) : conjugate s (conjugate s x) = x := by
  rw [sign_action]
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem preserves_scalars (s : Signs) (a : Rat) : conjugate s (scalar a) = scalar a := by
  rcases s with ⟨sx,sy⟩
  cases sx <;> cases sy <;> simp [conjugate,scalar,signed,Bool.xor]

theorem preserves_add (s : Signs) (x y : Biquad) :
    conjugate s (ba x y) = ba (conjugate s x) (conjugate s y) := by
  rcases s with ⟨sx,sy⟩
  cases sx <;> cases sy <;> apply Prod.ext <;> apply Prod.ext <;>
    simp only [ba,qa,conjugate,signed,Bool.xor] <;> grind

theorem preserves_mul (s : Signs) (x y : Biquad) :
    conjugate s (bm x y) = bm (conjugate s x) (conjugate s y) := by
  rcases s with ⟨sx,sy⟩
  cases sx <;> cases sy <;> apply Prod.ext <;> apply Prod.ext <;>
    simp only [bm,qm,qa,qs,conjugate,signed,Bool.xor] <;> grind

/-- The original integral coordinates are carried into themselves by these field automorphisms. -/
theorem integral_restriction (s : Signs) (v : OrderCoordinates) :
    TameOrderFaithful277.rationalize (conjugate s v) =
    conjugate s (TameOrderFaithful277.rationalize v) := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;>
    simp [TameOrderFaithful277.rationalize,conjugate,signed,Bool.xor]

theorem conjugate_evaluation (s t : Signs) (n : Nat) (v : OrderCoordinates) :
    branchEval t.1 t.2 n (conjugate s v) = branchEval (change s t).1 (change s t).2 n v := by
  rcases s with ⟨a,b⟩
  rcases t with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [branchEval,evalAt,rootAt,change,conjugate,signed,Bool.xor] <;> grind

theorem conjugate_prime (s t : Signs) (v : OrderCoordinates) :
    primePlace t.1 t.2 (conjugate s v) ↔ primePlace (change s t).1 (change s t).2 v := by
  unfold primePlace
  rw [conjugate_evaluation]

theorem conjugate_prime_power (s t : Signs) (n : Nat) (v : OrderCoordinates) :
    primePower t.1 t.2 (n+1) (conjugate s v) ↔ primePower (change s t).1 (change s t).2 (n+1) v := by
  rw [prime_power_iff,prime_power_iff,conjugate_evaluation]

theorem times_zero (x : Biquad) : bm x (scalar 0) = scalar 0 := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,scalar,qa,qs,qm] <;> grind

theorem product_eq_zero (x y : Biquad) (h : bm x y = scalar 0) :
    x = scalar 0 ∨ y = scalar 0 := by
  by_cases hx : x = scalar 0
  · exact Or.inl hx
  · right
    have he := congrArg (bm (bi x)) h
    rw [← mul_assoc, mul_comm (bi x) x, biquad_mul_inverse x hx,
      mul_comm _ y, mul_one, times_zero] at he
    exact he

theorem difference_of_squares (x y : Biquad) :
    bm (ba x (bn y)) (ba x y) = ba (bm x x) (bn (bm y y)) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,ba,bn,qa,qs,qm] <;> grind

theorem sum_eq_zero (x y : Biquad) (h : ba x y = scalar 0) : x = bn y := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,k⟩⟩
  simp only [ba,qa,scalar,Prod.mk.injEq] at h
  apply Prod.ext <;> apply Prod.ext <;> simp only [bn,qs] <;> grind

theorem double_negative (x : Biquad) : bn (bn x) = x := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bn,qs] <;> grind

theorem only_two_roots (x y : Biquad) (h : bm x x = bm y y) :
    x = y ∨ x = bn y := by
  have e := difference_of_squares x y
  rw [h,(add_group_laws (bm y y) (bm y y) (bm y y)).2.2.2] at e
  rcases product_eq_zero _ _ e with ha | hb
  · exact Or.inl ((sum_eq_zero _ _ ha).trans (double_negative y))
  · exact Or.inr (sum_eq_zero _ _ hb)

/-- Unital rational algebra endomorphisms in the checked four-coordinate field. -/
structure EndMap where
  app : Biquad → Biquad
  onRat : ∀ r, app (scalar r) = scalar r
  onAdd : ∀ x y, app (ba x y) = ba (app x) (app y)
  onMul : ∀ x y, app (bm x y) = bm (app x) (app y)

def automorphism (s : Signs) : EndMap :=
  ⟨conjugate s,preserves_scalars s,preserves_add s,preserves_mul s⟩

theorem determined_by_roots (f g : EndMap) (h3 : f.app gen3 = g.app gen3)
    (h23 : f.app gen23 = g.app gen23) : f = g := by
  have h : f.app = g.app := by
    funext x
    rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
    rw [← basis_expansion a b c d]
    simp only [f.onAdd,f.onMul,f.onRat,g.onAdd,g.onMul,g.onRat,h3,h23]
  cases f
  cases g
  cases h
  rfl

theorem images_of_roots (f : EndMap) :
    (f.app gen3 = gen3 ∨ f.app gen3 = bn gen3) ∧
    (f.app gen23 = gen23 ∨ f.app gen23 = bn gen23) := by
  constructor
  · apply only_two_roots
    rw [← f.onMul,generator_squares.1,f.onRat]
  · apply only_two_roots
    rw [← f.onMul,generator_squares.2,f.onRat]

theorem automorphism_roots (a b : Bool) :
    (automorphism (a,b)).app gen3 = (if a then bn gen3 else gen3) ∧
    (automorphism (a,b)).app gen23 = (if b then bn gen23 else gen23) := by
  cases a <;> cases b <;> decide +kernel

theorem every_automorphism (f : EndMap) : ∃ s : Signs, f = automorphism s := by
  rcases images_of_roots f with ⟨h₁,h₂⟩
  have select (z u : Biquad) (h : z = u ∨ z = bn u) :
      ∃ s : Bool, z = if s then bn u else u := by
    rcases h with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨a,ha⟩ := select _ _ h₁
  obtain ⟨b,hb⟩ := select _ _ h₂
  exact ⟨(a,b), determined_by_roots _ _ (ha.trans (automorphism_roots a b).1.symm)
    (hb.trans (automorphism_roots a b).2.symm)⟩

theorem rationalize_injective {v w : OrderCoordinates}
    (h : TameOrderFaithful277.rationalize v = TameOrderFaithful277.rationalize w) : v = w := by
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases w with ⟨⟨e,f⟩,⟨g,k⟩⟩
  simpa [TameOrderFaithful277.rationalize] using h

theorem kernel_labels (p q : Signs)
    (h : ∀ v, primePlace p.1 p.2 v ↔ primePlace q.1 q.2 v) : p = q := by
  have hx := (kernel_detects_signs p.1 p.2).1.symm.trans
    ((h ((-44,1),(0,0))).trans (kernel_detects_signs q.1 q.2).1)
  have hy := (kernel_detects_signs p.1 p.2).2.symm.trans
    ((h ((-114,0),(1,0))).trans (kernel_detects_signs q.1 q.2).2)
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- The forward action takes the ideal labelled p onto the ideal labelled q. All
rational endomorphisms preserve the integral order by their signed description. -/
def CarriesPrime (f : EndMap) (p q : Signs) : Prop :=
  ∀ (v w : OrderCoordinates), f.app (TameOrderFaithful277.rationalize v) =
    TameOrderFaithful277.rationalize w → (primePlace p.1 p.2 v ↔ primePlace q.1 q.2 w)

theorem change_solve (s p q : Signs) : change s q = p ↔ s = change p q := by
  rcases s with ⟨a,b⟩
  rcases p with ⟨c,d⟩
  rcases q with ⟨e,f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem automorphism_carries (s p q : Signs) :
    CarriesPrime (automorphism s) p q ↔ s = change p q := by
  rw [← change_solve]
  constructor
  · intro h
    apply kernel_labels
    intro v
    have hp := h v (conjugate s v) (integral_restriction s v).symm
    exact (conjugate_prime s q v).symm.trans hp.symm
  · intro he v w hw
    have eq : conjugate s v = w := rationalize_injective ((integral_restriction s v).trans hw)
    rw [← eq,conjugate_prime,he]

/-- Every rational endomorphism is invertible; its inverse is itself. -/
theorem all_involutive (f : EndMap) (x : Biquad) : f.app (f.app x) = x := by
  obtain ⟨s,rfl⟩ := every_automorphism f
  exact sign_involution s x

theorem distinct_automorphisms (s t : Signs) (h : automorphism s = automorphism t) : s=t := by
  have e : change s (false,false) = s := by
    rcases s with ⟨i,j⟩
    cases i <;> cases j <;> rfl
  have transported := (automorphism_carries s s (false,false)).mpr e.symm
  rw [h] at transported
  exact ((automorphism_carries t s (false,false)).mp transported |>.trans e).symm

/-- There is a unique global field automorphism carrying one specified ordinary
prime above 277 to another; the element is the coordinatewise difference of the sign labels. -/
theorem simply_transitive (p q : Signs) :
    CarriesPrime (automorphism (change p q)) p q ∧
    ∀ f : EndMap, CarriesPrime f p q → f = automorphism (change p q) := by
  refine ⟨(automorphism_carries _ _ _).mpr rfl, ?_⟩
  intro f hf
  obtain ⟨s,rfl⟩ := every_automorphism f
  exact congrArg automorphism ((automorphism_carries s p q).mp hf)

theorem self_change (p : Signs) : change p p = (false,false) := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem identity_map (x : Biquad) : (automorphism (false,false)).app x = x := rfl

/-- The decomposition subgroup of the bottom biquadratic extension at a signed
ordinary prime is trivial. -/
theorem decomposition_trivial (f : EndMap) (p : Signs) :
    CarriesPrime f p p ↔ f = automorphism (false,false) := by
  have h := simply_transitive p p
  rw [self_change] at h
  exact ⟨h.2 f,fun e => e.symm ▸ h.1⟩

theorem residue_frobenius (a : Fin 277) : a^277 = a := by
  revert a
  decide +kernel

/-- The residue-power criterion for an automorphism in the bottom decomposition subgroup. -/
def IsArithmeticFrobenius (f : EndMap) (p : Signs) : Prop :=
  CarriesPrime f p p ∧
  ∀ (v w : OrderCoordinates), f.app (TameOrderFaithful277.rationalize v) =
    TameOrderFaithful277.rationalize w →
    TameOrderPrimes277.red w (TameLocalOrders277.branchIndex p.1 p.2) =
      (TameOrderPrimes277.red v (TameLocalOrders277.branchIndex p.1 p.2)) ^ 277

theorem arithmetic_frobenius_identity (f : EndMap) (p : Signs) :
    IsArithmeticFrobenius f p ↔ f = automorphism (false,false) := by
  constructor
  · exact fun h => (decomposition_trivial f p).mp h.1
  · intro hf
    refine ⟨(decomposition_trivial f p).mpr hf, ?_⟩
    intro v w h
    rw [hf,identity_map] at h
    rw [rationalize_injective h, residue_frobenius]

/-- All ordinary primes of the polynomial order over 277 occur. This endpoint concerns
the signs in the bottom biquadratic field. -/
theorem all_bottom_decompositions (P : OrderCoordinates → Prop)
    (hp : TameOrderPrimes277.OrderPrime P) (h277 : P (integerCoordinates 277)) :
    ∃ s : Signs, P = primePlace s.1 s.2 ∧
      (∀ f : EndMap, CarriesPrime f s s ↔ f = automorphism (false,false)) ∧
      (∀ f : EndMap, IsArithmeticFrobenius f s ↔ f = automorphism (false,false)) ∧
      (∀ t : Signs, CarriesPrime (automorphism (change s t)) s t ∧
        ∀ f : EndMap, CarriesPrime f s t → f = automorphism (change s t)) := by
  obtain ⟨i,j,h,_⟩ := (TameLocalOrders277.all_order_primes P).mp ⟨hp,h277⟩
  exact ⟨(i,j),h,fun f => decomposition_trivial f (i,j),
    fun f => arithmetic_frobenius_identity f (i,j),simply_transitive (i,j)⟩

end Reimann.TameDecomposition277
