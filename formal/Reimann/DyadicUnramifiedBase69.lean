import Reimann.DyadicOrderCompletion69

/-! Unramified quadratic base change of a dyadic valuation ring with
binary residue field. The parameterized order has basis (1,e), e²=e−1.
The hypotheses identify the base ring's uniformizer, residue map and units.
-/

namespace Reimann.DyadicUnramifiedBase69

open Lean.Grind
open Reimann.DyadicOrderCompletion69 (pairProduct)

variable {R : Type} [CommRing R]

/-- Local data on the base ring. The last property is the discrete valuation
factorization of each nonzero scalar into a uniformizer power and a residue unit. -/
structure Base (R : Type) [CommRing R] where
  π : R
  red : R → BitVec 1
  red_zero : red 0 = 0
  red_one : red 1 = 1
  red_add : ∀ a b, red (a+b) = red a + red b
  red_mul : ∀ a b, red (a*b) = red a * red b
  red_neg : ∀ a, red (-a) = -red a
  red_pi : red π = 0
  cancel_pi : ∀ a, π*a = 0 → a=0
  unit : ∀ a, red a ≠ 0 → ∃ t, a*t=1
  factor : ∀ a, a ≠ 0 → ∃ n : Nat, ∃ t, a=π^n*t ∧ red t ≠ 0

def norm (x : R × R) : R := x.1*x.1+x.1*x.2+x.2*x.2

def conjugate (x : R × R) : R × R := (x.1+x.2,-x.2)

def residue (B : Base R) (x : R × R) : BitVec 1 × BitVec 1 := (B.red x.1,B.red x.2)

theorem norm_identity (x : R × R) : pairProduct x (conjugate x) = (norm x,0) := by
  apply Prod.ext <;> simp only [pairProduct,conjugate,norm] <;> grind

theorem norm_mul (x y : R × R) : norm (pairProduct x y)=norm x * norm y := by
  simp only [norm,pairProduct]; grind

theorem residue_product (B : Base R) (x y : R × R) :
    residue B (pairProduct x y) = DyadicInert.residueProduct (residue B x) (residue B y) := by
  simp [residue,pairProduct,DyadicInert.residueProduct,AddCommGroup.sub_eq_add_neg,
    B.red_add,B.red_neg,B.red_mul,BitVec.sub_eq_add_neg]

theorem residue_norm (B : Base R) (x : R × R) :
    B.red (norm x) = 1 ↔ residue B x ≠ (0,0) := by
  have h : ∀ a b : BitVec 1, a*a+a*b+b*b=1 ↔ (a,b) ≠ (0,0) := by decide
  simpa [norm,residue,B.red_add,B.red_mul] using h (B.red x.1) (B.red x.2)

/-- For nonzero reduction the inverse is the conjugate divided by the scalar norm. -/
theorem unit_of_primitive (B : Base R) (x : R × R) (hx : residue B x ≠ (0,0)) :
    ∃ y : R × R, pairProduct x y = (1,0) ∧ pairProduct y x = (1,0) := by
  have hr := (residue_norm B x).mpr hx
  obtain ⟨t,ht⟩ := B.unit (norm x) (by rw [hr]; decide)
  refine ⟨(t*(x.1+x.2),-t*x.2), ?_, ?_⟩ <;> apply Prod.ext <;>
    simp only [norm,pairProduct] at * <;> grind

theorem split_power (π : R) {i j : Nat} (h : i ≤ j) :
    π^j = π^i * π^(j-i) := by
  rw [← Semiring.pow_add,show i+(j-i) = j by omega]

/-- Remove the lesser of the two coordinate valuations, handling zero coordinates separately. -/
theorem common_power (B : Base R) (a b : R) (h : (a,b) ≠ (0,0)) :
    ∃ n : Nat, ∃ u v : R, a=B.π^n*u ∧ b=B.π^n*v ∧ (B.red u,B.red v) ≠ (0,0) := by
  by_cases ha : a=0
  · subst a
    obtain ⟨n,v,hv,hr⟩ := B.factor b (by intro hb; exact h (by rw [hb]))
    exact ⟨n,0,v,by grind,hv,fun he => hr (congrArg Prod.snd he)⟩
  obtain ⟨i,u,hu,hru⟩ := B.factor a ha
  by_cases hb : b=0
  · subst b
    exact ⟨i,u,0,hu,by grind,fun he => hru (congrArg Prod.fst he)⟩
  obtain ⟨j,v,hv,hrv⟩ := B.factor b hb
  by_cases hij : i ≤ j
  · exact ⟨i,u,B.π^(j-i)*v,hu,by rw [hv,split_power B.π hij]; grind,
      fun he => hru (congrArg Prod.fst he)⟩
  · exact ⟨j,B.π^(i-j)*u,v,by rw [hu,split_power B.π (show j≤i by omega)]; grind,hv,
      fun he => hrv (congrArg Prod.snd he)⟩

theorem cancel_uniformizer_power (B : Base R) (n : Nat) (a b : R)
    (he : B.π^n*a = B.π^n*b) : a=b := by
  induction n with
  | zero => simpa only [Semiring.pow_zero,Semiring.one_mul] using he
  | succ n ih =>
    have eq : B.π*(B.π^n*a-B.π^n*b)=0 := by rw [Semiring.pow_succ] at he; grind
    have e := B.cancel_pi _ eq
    exact ih (by grind)

theorem unit_not_deeper (B : Base R) (n : Nat) (a : R) (ha : B.red a ≠ 0) :
    ¬ ∃ b : R, B.π^n*a = B.π^(n+1)*b := by
  rintro ⟨b,hb⟩
  have he : B.π^n*a=B.π^n*(B.π*b) := by rw [Semiring.pow_succ] at hb; grind
  have eq := cancel_uniformizer_power B n _ _ he
  exact ha (by rw [eq,B.red_mul,B.red_pi]; simp)

/-- For x≠0, write its two coefficients as π^n times a primitive pair.
The norm has exact exponent 2n, so the extension's uniformizer stays π. -/
theorem norm_valuation (B : Base R) (x : R × R) (hx : x ≠ (0,0)) :
    ∃ n : Nat, ∃ u : R × R, x=(B.π^n*u.1,B.π^n*u.2) ∧
      residue B u ≠ (0,0) ∧ B.red (norm u)=1 ∧
      norm x=B.π^(n+n)*norm u ∧ ¬ ∃ t : R, norm x=B.π^((n+n)+1)*t := by
  obtain ⟨n,a,b,ha,hb,hr⟩ := common_power B x.1 x.2 hx
  let u : R × R := (a,b)
  have he : x=(B.π^n*u.1,B.π^n*u.2) := Prod.ext ha hb
  have hu := (residue_norm B u).mpr hr
  have hn : norm x=B.π^(n+n)*norm u := by rw [he,Semiring.pow_add]; simp only [norm]; grind
  refine ⟨n,u,he,hr,hu,hn,?_⟩
  rw [hn]
  exact unit_not_deeper B _ _ (by rw [hu]; decide)

theorem norm_nonzero (B : Base R) (x : R × R) (hx : x ≠ (0,0)) : norm x ≠ 0 := by
  obtain ⟨n,u,_,_,_,_,hd⟩ := norm_valuation B x hx
  intro hz
  exact hd ⟨0,by rw [hz]; grind⟩

theorem binary_irreducible (v : BitVec 1) : v*v-v+1 ≠ 0 := by
  revert v
  decide

theorem base_fraction_obstruction (B : Base R) (a b : R) (hb : b ≠ 0) :
    a*a-a*b+b*b ≠ 0 := by
  have h : (a,-b) ≠ (0,0) := by
    intro he
    have hb' := congrArg Prod.snd he
    change -b=0 at hb'
    exact hb (by grind)
  have hn := norm_nonzero B (a,-b) h
  simp only [norm] at hn
  intro hz
  apply hn
  grind

/-- Ring operations preserved by an embedding or a base automorphism. -/
structure RingMap (A C : Type) [CommRing A] [CommRing C] where
  app : A → C
  zero : app 0=0
  one : app 1=1
  add : ∀ a b, app (a+b)=app a+app b
  neg : ∀ a, app (-a) = -app a
  mul : ∀ a b, app (a*b)=app a*app b

/-- Irreducibility over the actual fraction field of R once the embedding and
its denominator-clearing property are given. Any root would yield a vanishing
binary norm on the base with nonzero denominator. -/
theorem fraction_field_no_root {K : Type} [Field K] (B : Base R) (inc : RingMap R K)
    (faithful : ∀ x, inc.app x=0 → x=0)
    (fractions : ∀ t : K, ∃ a b : R, b≠0 ∧ inc.app a = t*inc.app b) (t : K) :
    t*t-t+1 ≠ 0 := by
  obtain ⟨a,b,hb,h⟩ := fractions t
  intro ht
  apply base_fraction_obstruction B a b hb
  apply faithful
  simp only [AddCommGroup.sub_eq_add_neg,inc.add,inc.mul,inc.neg,h]
  have he := congrArg (fun s : K => s*inc.app b*inc.app b) ht
  grind

/-- In degree two the only possible nontrivial monic factorization has two
linear factors; coefficient comparison would make s a root. -/
theorem no_monic_linear_factors {K : Type} [Field K]
    (hr : ∀ t : K, t*t-t+1 ≠ 0) (s t : K) : ¬ (s+t=1 ∧ s*t=1) := by
  rintro ⟨hs,ht⟩
  apply hr s
  grind

theorem field_pair_inverse {K : Type} [Field K] (hr : ∀ t : K, t*t-t+1 ≠ 0)
    (x : K × K) (hx : x≠(0,0)) : ∃ y : K × K, pairProduct x y = (1,0) := by
  have hn : norm x ≠ 0 := by
    intro he
    unfold norm at he
    by_cases hb : x.2=0
    · have ha : x.1=0 := by
        by_cases hz : x.1=0
        · exact hz
        · have hi := Field.mul_inv_cancel hz
          rw [hb] at he
          grind
      exact hx (Prod.ext ha hb)
    · have hi := Field.mul_inv_cancel hb
      apply hr (-x.1*x.2⁻¹)
      grind
  let t := (norm x)⁻¹
  have ht : norm x*t=1 := Field.mul_inv_cancel hn
  refine ⟨(t*(x.1+x.2),-t*x.2),?_⟩
  apply Prod.ext <;> simp only [norm,pairProduct] at * <;> grind

theorem residue_surjective (B : Base R) (v : BitVec 1 × BitVec 1) :
    ∃ x : R × R, residue B x = v := by
  have bits : ∀ b : BitVec 1, b=0 ∨ b=1 := by decide
  have lift (b : BitVec 1) : ∃ a : R, B.red a=b := by
    rcases bits b with h|h
    · exact ⟨0,B.red_zero.trans h.symm⟩
    · exact ⟨1,B.red_one.trans h.symm⟩
  obtain ⟨a,ha⟩ := lift v.1
  obtain ⟨b,hb⟩ := lift v.2
  exact ⟨(a,b), Prod.ext ha hb⟩

theorem divisible_by_pi (B : Base R) (a : R) : B.red a = 0 ↔ ∃ b : R, a=B.π*b := by
  constructor
  · intro ha
    by_cases hz : a=0
    · exact ⟨0,by rw [hz]; grind⟩
    obtain ⟨n,u,hu,hr⟩ := B.factor a hz
    cases n with
    | zero =>
      have : a = u := by simpa only [Semiring.pow_zero,Semiring.one_mul] using hu
      exact False.elim (hr (this ▸ ha))
    | succ n =>
      exact ⟨B.π^n*u,by rw [hu,Semiring.pow_succ]; grind⟩
  · rintro ⟨b,rfl⟩
    rw [B.red_mul,B.red_pi]; simp

theorem extension_residue_kernel (B : Base R) (x : R × R) :
    residue B x = (0,0) ↔ ∃ y : R × R, x = pairProduct (B.π,0) y := by
  constructor
  · intro h
    obtain ⟨u,hu⟩ := (divisible_by_pi B x.1).mp (congrArg Prod.fst h)
    obtain ⟨v,hv⟩ := (divisible_by_pi B x.2).mp (congrArg Prod.snd h)
    exact ⟨(u,v),Prod.ext (by simp only [pairProduct]; grind) (by simp only [pairProduct]; grind)⟩
  · rintro ⟨y,rfl⟩
    rw [residue_product]
    simp [residue,DyadicInert.residueProduct,B.red_pi,B.red_zero]

theorem extension_prime (B : Base R) (x y : R × R) :
    residue B (pairProduct x y) = (0,0) ↔ residue B x=(0,0) ∨ residue B y=(0,0) := by
  have h : ∀ a b c d : BitVec 1, DyadicInert.residueProduct (a,b) (c,d) = (0,0) ↔
      (a,b)=(0,0) ∨ (c,d)=(0,0) := by decide
  rw [residue_product]
  exact h _ _ _ _

/-- Any proper ideal containing the base uniformizer is the residue kernel.
The preceding theorem proves that this kernel is prime, and residue_surjective
identifies its quotient with the four-element residue field. -/
theorem unique_prime_over_pi (B : Base R) (P : R × R → Prop)
    (proper : ¬ P (1,0)) (above : P (B.π,0))
    (absorb : ∀ x y, P x → P (pairProduct x y)) (x : R × R) :
    P x ↔ residue B x = (0,0) := by
  constructor
  · intro hp
    by_cases h : residue B x = (0,0)
    · exact h
    · obtain ⟨y,hy,_⟩ := unit_of_primitive B x h
      exact False.elim (proper (hy ▸ absorb x y hp))
  · intro h
    obtain ⟨y,hy⟩ := (extension_residue_kernel B x).mp h
    rw [hy]
    exact absorb _ _ above

def extend {S : Type} [CommRing S] (f : RingMap R S) (x : R × R) : S × S :=
  (f.app x.1,f.app x.2)

theorem extension_fixes_generator {S : Type} [CommRing S] (f : RingMap R S) :
    extend f (0,1) = (0,1) ∧ ∀ r : R, extend f (r,0)=(f.app r,0) := by
  simp [extend,f.zero,f.one]

theorem extension_laws {S : Type} [CommRing S] (f : RingMap R S) (x y : R × R) :
    extend f (x.1+y.1,x.2+y.2) = ((extend f x).1+(extend f y).1,(extend f x).2+(extend f y).2) ∧
    extend f (pairProduct x y) = pairProduct (extend f x) (extend f y) := by
  simp [extend,pairProduct,AddCommGroup.sub_eq_add_neg,f.add,f.mul,f.neg]

theorem extension_inverse {S : Type} [CommRing S] (f : RingMap R S) (g : RingMap S R)
    (left : ∀ x, g.app (f.app x) = x) (right : ∀ y, f.app (g.app y) = y) :
    (∀ x : R × R, extend g (extend f x)=x) ∧ (∀ y : S × S, extend f (extend g y)=y) := by
  simp [extend,left,right]

/-- At the bottom base Z₂ the full inverse-limit multiplication from
DyadicInert agrees in each finite precision with the generic quadratic order.
Each of the two completed factors at q=3 therefore has this multiplication. -/
theorem base_completion_coordinates (x y : DyadicInert.Pair) (n : Nat) :
    let z := DyadicInert.product (DyadicLattice.natScalar 1) x y
    (z.1.residue n,z.2.residue n) = pairProduct (x.1.residue n,x.2.residue n) (y.1.residue n,y.2.residue n) := by
  simp only [DyadicInert.product,DyadicLattice.natScalar,DyadicLattice.add,DyadicLattice.mul,
    DyadicLattice.neg,pairProduct]; apply Prod.ext <;> grind

/-- The kernel of the binary pair projection contains zero, excludes one,
and is closed under addition, negation and multiplication by arbitrary elements. -/
theorem residue_prime_ideal (B : Base R) :
    residue B (0,0)=(0,0) ∧ residue B (1,0)≠(0,0) ∧
    (∀ x y : R × R, residue B x=(0,0) → residue B y=(0,0) →
      residue B (x.1+y.1,x.2+y.2)=(0,0)) ∧
    (∀ x : R × R, residue B x=(0,0) → residue B (-x.1,-x.2)=(0,0)) ∧
    (∀ x y : R × R, residue B x=(0,0) → residue B (pairProduct x y)=(0,0)) := by
  refine ⟨Prod.ext B.red_zero B.red_zero, ?_, ?_, ?_, ?_⟩
  · simp [residue,B.red_one,B.red_zero]
  · intro x y hx hy
    have hx₁ := congrArg Prod.fst hx; have hx₂ := congrArg Prod.snd hx
    have hy₁ := congrArg Prod.fst hy; have hy₂ := congrArg Prod.snd hy
    simp only [residue] at *
    rw [B.red_add,B.red_add,hx₁,hx₂,hy₁,hy₂]; decide
  · intro x hx
    have hx₁ := congrArg Prod.fst hx; have hx₂ := congrArg Prod.snd hx
    simp only [residue] at *
    rw [B.red_neg,B.red_neg,hx₁,hx₂]; decide
  · intro x y hx; exact (extension_prime B x y).mpr (.inl hx)

/-- A map fixing e and acting by f on the base is forced on all coefficients.
This identifies the full subgroup fixing e in the base changed field. -/
theorem lift_unique_fixing_e {S : Type} [CommRing S] (f : RingMap R S)
    (g : R × R → S × S)
    (ha : ∀ x y : R × R, g (x.1+y.1,x.2+y.2) = ((g x).1+(g y).1,(g x).2+(g y).2))
    (hm : ∀ x y, g (pairProduct x y) = pairProduct (g x) (g y))
    (hb : ∀ r, g (r,0)=(f.app r,0)) (he : g (0,1) = (0,1)) (x : R × R) :
    g x = extend f x := by
  have expand (r : R) : pairProduct (r,0) (0,1)=(0,r) := by
    apply Prod.ext <;> simp only [pairProduct] <;> grind
  have hs : g (0,x.2)=(0,f.app x.2) := by
    rw [← expand,hm,hb,he]
    apply Prod.ext <;> simp only [pairProduct] <;> grind
  have hadd := ha (x.1,0) (0,x.2)
  rw [hb,hs] at hadd
  simpa only [AddCommMonoid.add_zero,AddCommMonoid.zero_add,extend] using hadd

end Reimann.DyadicUnramifiedBase69
