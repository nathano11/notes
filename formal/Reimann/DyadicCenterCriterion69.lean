import Reimann.DyadicLocalRestriction69

/-! A valuation above 2 is centered at a labelled bottom prime as soon as
the second generator of that prime belongs to its support. -/
namespace Reimann.DyadicCenterCriterion69

open Lean.Grind Reimann.DyadicDecomposition69 Reimann.DyadicLocalRestriction69
open Reimann.DyadicBottomValue69 Reimann.DyadicEmbeddedBase69 Reimann.DyadicArithmetic69
open Reimann.TameRationalField277 Reimann.DyadicIntegralCriterion69
attribute [local instance] Ring.intCast Semiring.natCast

variable {F : Type} [Field F] (V : DyadicValue F)

theorem one : V.val 1 = 0 := by
  have ne : (1:F) ≠ 0 := by intro h; apply V.two_ne; grind
  have e := V.mul ne ne
  rw [Semiring.one_mul] at e
  grind

theorem negation (x : F) : V.val (-x) = V.val x := by
  by_cases hx : x=0
  · simp only [hx,AddCommGroup.neg_zero]
  have hn : -x≠0 := by grind
  have e := V.mul hn hn
  rw [show (-x)*(-x)=x*x by grind,V.mul hx hx] at e
  grind

theorem sum_bound (q : Rat) (x y : F) (hx : x=0 ∨ q≤V.val x) (hy : y=0 ∨ q≤V.val y) :
    x+y=0 ∨ q≤V.val (x+y) := by
  rcases hx with rfl|hx
  · simpa only [AddCommMonoid.zero_add] using hy
  rcases hy with rfl|hy
  · simp only [AddCommMonoid.add_zero]; exact .inr hx
  by_cases hs : x+y=0
  · exact .inl hs
  right
  apply Classical.byContradiction
  intro h
  by_cases hz : y=0
  · rw [hz,AddCommMonoid.add_zero] at h; exact h hx
  have hn : -y≠0 := by grind
  have lo : V.val (x+y)<V.val (-y) := by rw [negation]; grind
  have e := (V.smaller hs hn lo).2
  rw [show x+y+(-y)=x by grind] at e
  grind

theorem nat_nonneg (n : Nat) : 0≤V.val (n:F) := by
  induction n with
  | zero => simpa only [Semiring.natCast_zero,V.zero] using (show (0:Rat)≤0 by decide)
  | succ n ih =>
    have h := sum_bound V 0 (n:F) 1 (.inr ih) (.inr (by rw [one]; decide))
    rw [Semiring.natCast_succ]
    rcases h with h|h
    · rw [h,V.zero]; decide
    · exact h

theorem int_nonneg (n : Int) : 0≤V.val (n:F) := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast,Ring.intCast_natCast]
    exact nat_nonneg V k
  | negSucc k =>
    have e : ((Int.negSucc k : Int):F) = -((k+1:Nat):F) := by
      change ((-((k+1:Nat):Int):Int):F) = _
      rw [Ring.intCast_neg,Ring.intCast_natCast]
    rw [e,negation]; exact nat_nonneg V _

theorem odd_unit (k : Int) : ((1+2*k : Int):F)≠0 ∧ V.val ((1+2*k : Int):F)=0 := by
  have equiv : ((1+2*k : Int):F) = 1+(2:F)*(k:F) := by grind
  rw [equiv]
  have ho : (1:F)≠0 := by intro h; apply V.two_ne; grind
  by_cases hz : (k:F)=0
  · simp only [hz,Semiring.mul_zero,AddCommMonoid.add_zero]
    exact ⟨ho,one V⟩
  have hn : (2:F)*(k:F)≠0 := fun h => (Field.of_mul_eq_zero h).elim V.two_ne hz
  have lower : V.val 1<V.val ((2:F)*(k:F)) := by
    rw [one,V.mul V.two_ne hz,V.two]
    have h := int_nonneg V k
    grind
  obtain ⟨ne,e⟩ := V.smaller ho hn lower
  exact ⟨ne,e.trans (one V)⟩

theorem monic_at_negative (f : Embedding F) (z : Biquad) (hz : V.val (f.app z)<0)
    (cs : List Int) : f.app (monicAt z cs)≠0 ∧ V.val (f.app (monicAt z cs))≤0 := by
  have nz : f.app z≠0 := by intro h; rw [h,V.zero] at hz; grind
  induction cs with
  | nil =>
    change f.app (scalar 1)≠0 ∧ V.val (f.app (scalar 1))≤0
    rw [(map_zero_one f).2,one V]
    constructor
    · intro h; apply V.two_ne; grind
    · decide
  | cons c cs ih =>
    change f.app (ba (bm z (monicAt z cs)) (scalar (c:Rat)))≠0 ∧ _
    simp only [monicAt,f.add,f.mul,f.scalar_int]
    let u := f.app z * f.app (monicAt z cs)
    have nu : u≠0 := fun h => (Field.of_mul_eq_zero h).elim nz ih.1
    have vu : V.val u<0 := by
      dsimp only [u]; rw [V.mul nz ih.1]; have he := ih.2; grind
    by_cases nc : (c:F)=0
    · simp only [nc,AddCommMonoid.add_zero]; exact ⟨nu,by change V.val u≤0; grind⟩
    have lt : V.val u < V.val (c:F) := by have hc := int_nonneg V c; grind
    obtain ⟨ne,eq⟩ := V.smaller nu nc lt
    exact ⟨ne,by change V.val (u+(c:F))≤0; rw [eq]; grind⟩

theorem local_nonneg (f : Embedding F) (x : LocalIntegers) : 0≤V.val (f.app x.val) := by
  obtain ⟨k,cs,hcs⟩ := x.property
  let d := ((1+2*k:Int):F)
  let z := dilate (1+2*k) x.val
  have he : f.app z=d*f.app x.val := by unfold z d dilate; rw [f.mul,f.scalar_int]
  have hzero : f.app (monicAt z cs) = 0 := (congrArg f.app hcs).trans (map_zero_one f).1
  have nd := odd_unit V k
  apply Classical.byContradiction
  intro h
  have nx : f.app x.val≠0 := by intro e; rw [e,V.zero] at h; grind
  have lt : V.val (f.app z)<0 := by rw [he,V.mul nd.1 nx,nd.2]; grind
  exact (monic_at_negative V f z lt cs).1 hzero

theorem support_add {x y : F} (hx : Supports V x) (hy : Supports V y) : Supports V (x+y) := by
  rcases hx with rfl|hx
  · simpa only [AddCommMonoid.zero_add] using hy
  rcases hy with rfl|hy
  · simpa only [AddCommMonoid.add_zero] using (show Supports V x from .inr hx)
  by_cases le : V.val x ≤ V.val y
  · rcases sum_bound V (V.val x) x y (.inr (by grind)) (.inr le) with e|h
    · exact .inl e
    · exact .inr (by grind)
  · rcases sum_bound V (V.val y) x y (.inr (by grind)) (.inr (by grind)) with e|h
    · exact .inl e
    · exact .inr (by grind)

theorem support_prime (f : Embedding F) :
    DyadicFiberDescent.IsPrime residueMap (fun x => Supports V (f.app x.val)) where
  zero := .inl (map_zero_one f).1
  proper := by
    change ¬Supports V (f.app (scalar 1))
    rw [(map_zero_one f).2]
    rintro (e|h)
    · apply V.two_ne; grind
    · rw [one V] at h; grind
  add_mem x y hx hy := by
    change Supports V (f.app (ba x.val y.val))
    rw [f.add]; exact support_add V hx hy
  absorb x y hx := by
    change Supports V (f.app (bm x.val y.val))
    rw [f.mul]
    by_cases nx : f.app x.val=0
    · exact .inl (by rw [nx,Semiring.zero_mul])
    by_cases ny : f.app y.val=0
    · exact .inl (by rw [ny,Semiring.mul_zero])
    have hpos := hx.resolve_left nx
    have hy := local_nonneg V f y
    exact .inr (by rw [V.mul nx ny]; grind)
  prime x y h := by
    change Supports V (f.app (bm x.val y.val)) at h
    rw [f.mul] at h
    by_cases nx : f.app x.val=0
    · exact .inl (.inl nx)
    by_cases ny : f.app y.val=0
    · exact .inr (.inl ny)
    rcases h with h|h
    · exact False.elim ((Field.of_mul_eq_zero h).elim nx ny)
    · rw [V.mul nx ny] at h
      by_cases hx : 0<V.val (f.app x.val)
      · exact .inl (.inr hx)
      · exact .inr (.inr (by grind))

/-- The entire center is forced by the single labelled prime generator. -/
theorem centered_of_generator (f : Embedding F) (i : Bool)
    (generator : Supports V (f.app (primeGenerator i).val)) : Centered f V i := by
  let P := fun x : LocalIntegers => Supports V (f.app x.val)
  have two_mem : P (DyadicPrimeClassification69.two localized_integer_order) := by
    change Supports V (f.app (scalar 2))
    have he : f.app (scalar 2)=(2:F) := by have e := f.scalar_int 2; grind
    exact .inr (by rw [he,V.two]; decide)
  have labels := (primes_above_two P).mp ⟨support_prime V f,two_mem⟩
  have wrong : ¬DyadicFiberDescent.coordinateKernel residueMap (!i) (primeGenerator i) := by
    simpa only [Bool.not_not] using other_generator_outside (!i)
  have he : P=DyadicFiberDescent.coordinateKernel residueMap i := by
    have hm : P (primeGenerator i) := generator
    cases i <;> rcases labels with h|h <;> first | exact h | exact False.elim (wrong (h ▸ hm))
  exact ⟨local_nonneg V f,fun x => Iff.of_eq (congrFun he x).symm⟩

end Reimann.DyadicCenterCriterion69
