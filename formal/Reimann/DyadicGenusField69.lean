import Reimann.DyadicEmbeddedBase69

/-! Equality of the two descriptions of the genus-field cyclotomic tower for
the bottom pair (3,23). All field expressions are evaluated in the same
ambient field. The subfield with just rational constants can be expressed
by taking the starting family B empty. -/

namespace Reimann.DyadicGenusField69

open Lean.Grind
open Reimann.DyadicCyclotomicSpan69

variable {F : Type u} [Field F]

def realTrace (z : F) : F := z+z⁻¹

theorem radical_squares (i x y : F) (hi : i*i= -1) (hx : x*x= -3) (hy : y*y= -23) :
    (i*x)*(i*x)=3 ∧ (i*y)*(i*y)=23 ∧ (i*x*y)*(i*x*y)= -69 := by grind

/-- For k₀=i x y, X=i x and Y=i y, one has k₀=−i X Y. -/
theorem recover_i (i x y : F) (hi : i*i= -1) (nx : x≠0) (ny : y≠0) :
    -(i*x*y)*((i*x)*(i*y))⁻¹=i := by
  have ni : i ≠ 0 := by intro h; rw [h] at hi; grind
  have nprod : (i*x)*(i*y) ≠ 0 := fun h => (Field.of_mul_eq_zero h).elim
    (fun h' => (Field.of_mul_eq_zero h').elim ni nx) (fun h' => (Field.of_mul_eq_zero h').elim ni ny)
  have h : -(i*x*y)=i*((i*x)*(i*y)) := by grind
  rw [h,Semiring.mul_assoc,Field.mul_inv_cancel nprod,Semiring.mul_one]

theorem recover_bottom (i x y : F) (hi : i*i= -1) :
    -(i*(i*x))=x ∧ -(i*(i*y))=y := by grind

/-- The Chebyshev recurrence for traces of powers of a root of unity. -/
theorem trace_power_step (z : F) (nz : z ≠ 0) (n : Nat) :
    realTrace (z^(n+2)) = realTrace z * realTrace (z^(n+1)) - realTrace (z^n) := by
  have hi := Field.mul_inv_cancel nz
  simp only [realTrace,Field.inv_pow,Semiring.pow_succ,Field.inv_mul]
  grind

theorem traces_of_powers {C : F → Prop} (c : Subfield C) (z : F) (nz : z≠0)
    (hz : C (realTrace z)) (n : Nat) : C (realTrace (z^n)) := by
  have base : C (realTrace (z^0)) := by simpa only [realTrace,Semiring.pow_zero,Field.inv_one] using c.add c.one c.one
  have h₁ : C (realTrace (z^1)) := by simpa only [Semiring.pow_one] using hz
  have step : ∀ k : Nat, C (realTrace (z^k)) ∧ C (realTrace (z^(k+1))) := by
    intro k
    induction k with
    | zero => exact ⟨base,h₁⟩
    | succ k ih =>
      refine ⟨ih.2,?_⟩
      rw [trace_power_step z nz k,AddCommGroup.sub_eq_add_neg]
      exact c.add (c.mul hz ih.2) (c.neg ih.1)
  exact (step n).1

theorem rotated_trace (i z : F) (hi : i*i= -1) :
    realTrace z - i*realTrace (i*z)=2*z := by
  have ni : i≠0 := by intro h; rw [h] at hi; grind
  have h := Field.mul_inv_cancel ni
  simp only [realTrace,Field.inv_mul]
  grind

theorem root_from_traces [IsCharP F 0] {C : F → Prop} (c : Subfield C) (i z : F)
    (hi : i*i= -1) (ci : C i) (hz : C (realTrace z)) (hr : C (realTrace (i*z))) : C z := by
  have two : C (2:F) := (show (1:F)+1=2 by grind) ▸ c.add c.one c.one
  have nt : (2:F) ≠ 0 := by grind
  have raw := c.add hz (c.neg (c.mul ci hr))
  rw [← AddCommGroup.sub_eq_add_neg,rotated_trace i z hi] at raw
  have q := c.mul raw (c.inv two)
  rw [show (2:F)*z*(2:F)⁻¹=z by have h := Field.mul_inv_cancel nt; grind] at q
  exact q

theorem square_roots_agree_up_to_sign (u v : F) (h : u*u=v*v) : u=v ∨ u= -v := by
  have h' : (u-v)*(u+v)=0 := by grind
  exact (Field.of_mul_eq_zero h').elim (fun e => Or.inl (by grind)) (fun e => Or.inr (by grind))

theorem quarter_power (z : F) (n : Nat) (hz : z^(2^(n+1) : Nat)= -1) :
    z^(2^n : Nat)*z^(2^n : Nat)= -1 := by
  rwa [Nat.pow_succ,Nat.mul_two,Semiring.pow_add] at hz

/-- In every primitive layer of order at least four, adjoining its generator
is equivalent to adjoining its real trace and a fixed fourth root of unity. -/
theorem finite_generators_iff [IsCharP F 0] {C : F → Prop} (c : Subfield C)
    (i z : F) (n : Nat) (hi : i*i= -1) (hz : z^(2^(n+1) : Nat)= -1) :
    C z ↔ C (realTrace z) ∧ C i := by
  let j := z^(2^n : Nat)
  have hj : j*j= -1 := quarter_power z n hz
  have signs := square_roots_agree_up_to_sign j i (hj.trans hi.symm)
  have nz : z≠0 := by
    intro e
    have p : 0 < 2^(n+1) := Nat.pow_pos (by decide)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show 2^(n+1)≠0 by omega)
    rw [hk,Semiring.pow_succ,e,Semiring.mul_zero] at hz
    grind
  constructor
  · intro cz
    have cj : C j := subfield_pow c cz _
    exact ⟨c.add cz (c.inv cz),signs.elim (fun e => e ▸ cj) (fun e => (show -j=i by grind) ▸ c.neg cj)⟩
  · rintro ⟨ct,ci⟩
    have cj : C j := signs.elim (fun e => e.symm ▸ ci) (fun e => e.symm ▸ c.neg ci)
    have cr := traces_of_powers c z nz ct (2^n+1)
    rw [Semiring.pow_succ] at cr
    exact root_from_traces c j z hj cj ct cr

def DyadicRoot (z : F) : Prop := ∃ n : Nat, z^(2^n : Nat)=1

theorem root_level_raise (z : F) (n : Nat) (h : z^(2^n : Nat)=1) (m : Nat) :
    z^(2^(n+m) : Nat)=1 := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [Nat.add_succ,Nat.pow_succ,Nat.mul_two,Semiring.pow_add,ih,Semiring.one_mul]

theorem dyadic_root_mul {x y : F} (hx : DyadicRoot x) (hy : DyadicRoot y) : DyadicRoot (x*y) := by
  obtain ⟨n,hn⟩ := hx
  obtain ⟨m,hm⟩ := hy
  refine ⟨n+m,?_⟩
  have hy' := root_level_raise y m hm n
  rw [Nat.add_comm m n] at hy'
  rw [CommSemiring.mul_pow,root_level_raise x n hn m,hy',Semiring.one_mul]

theorem dyadic_fourth_root (i : F) (hi : i*i= -1) : DyadicRoot i := by
  refine ⟨2,?_⟩
  change i^(4:Nat)=1
  simp only [Semiring.pow_succ,Semiring.pow_zero]
  grind

/-- A common subfield contains the bottom field and all dyadic roots precisely
when it contains the imaginary quadratic generator, both positive radicals
and all real dyadic traces. -/
theorem subfield_generators_iff [IsCharP F 0] {C : F → Prop} (c : Subfield C)
    (i x y : F) (hi : i*i= -1) (hx : x*x= -3) (hy : y*y= -23) :
    (C x ∧ C y ∧ ∀ z, DyadicRoot z → C z) ↔
    (C (i*x*y) ∧ C (i*x) ∧ C (i*y) ∧ ∀ z, DyadicRoot z → C (realTrace z)) := by
  have hr := dyadic_fourth_root i hi
  constructor
  · rintro ⟨cx,cy,roots⟩
    have ci := roots i hr
    exact ⟨c.mul (c.mul ci cx) cy,c.mul ci cx,c.mul ci cy,fun z h => c.add (roots z h) (c.inv (roots z h))⟩
  · rintro ⟨ck,cX,cY,traces⟩
    have nx : x≠0 := by intro e; rw [e] at hx; grind
    have ny : y≠0 := by intro e; rw [e] at hy; grind
    have ci : C i := recover_i i x y hi nx ny ▸ c.mul (c.neg ck) (c.inv (c.mul cX cY))
    have back := recover_bottom i x y hi
    exact ⟨back.1 ▸ c.neg (c.mul ci cX),back.2 ▸ c.neg (c.mul ci cY),
      fun z h => root_from_traces c i z hi ci (traces z h) (traces (i*z) (dyadic_root_mul hr h))⟩

/-- The least subfield containing B, both imaginary radicals, and μ₂∞. -/
def bottomTower (B : F → Prop) (x y t : F) : Prop :=
  ∀ C : F → Prop, Subfield C → (∀ s, B s → C s) →
    (C x ∧ C y ∧ ∀ z, DyadicRoot z → C z) → C t

/-- The least subfield containing B, the genus radicals and the real tower. -/
def genusTower (B : F → Prop) (i x y t : F) : Prop :=
  ∀ C : F → Prop, Subfield C → (∀ s, B s → C s) →
    (C (i*x*y) ∧ C (i*x) ∧ C (i*y) ∧ ∀ z, DyadicRoot z → C (realTrace z)) → C t

/-- Taking B empty gives the equality over the prime field Q in characteristic zero. -/
theorem genus_field_equality [IsCharP F 0] (B : F → Prop) (i x y : F)
    (hi : i*i= -1) (hx : x*x= -3) (hy : y*y= -23) :
    bottomTower B x y = genusTower B i x y := by
  funext t
  apply propext
  constructor
  · intro h C c base rhs
    exact h C c base ((subfield_generators_iff c i x y hi hx hy).mpr rhs)
  · intro h C c base lhs
    exact h C c base ((subfield_generators_iff c i x y hi hx hy).mp lhs)

theorem successor_power_square (z : F) (n : Nat) :
    (z*z)^(2^n : Nat)=z^(2^(n+1) : Nat) := by
  rw [CommSemiring.mul_pow,Nat.pow_succ,Nat.mul_two,Semiring.pow_add]

/-- An arbitrary root of unity of order dividing 2^(n+1) is a power of
any root whose 2^n-th power is minus one. -/
theorem powers_exhaust_roots (n : Nat) (z t : F)
    (hz : z^(2^n : Nat)= -1) (ht : t^(2^(n+1) : Nat)=1) : ∃ k : Nat, t=z^k := by
  induction n generalizing z t with
  | zero =>
    have ez : z= -1 := by simpa only [Nat.pow_zero,Semiring.pow_one] using hz
    have et : t*t=1*1 := by
      rw [← successor_power_square] at ht
      simpa only [Nat.pow_zero,Semiring.pow_one,Semiring.one_mul] using ht
    rcases square_roots_agree_up_to_sign t 1 et with e | e
    · exact ⟨0,by rw [Semiring.pow_zero,e]⟩
    · exact ⟨1,by rw [Semiring.pow_one,ez,e]⟩
  | succ n ih =>
    obtain ⟨k,hk⟩ := ih (z*z) (t*t) ((successor_power_square z n).trans hz)
      ((successor_power_square t (n+1)).trans ht)
    rw [CommSemiring.mul_pow] at hk
    rcases square_roots_agree_up_to_sign t (z^k) hk with e | e
    · exact ⟨k,e⟩
    · exact ⟨k+2^(n+1),by rw [Semiring.pow_add,hz,e]; grind⟩

theorem primitive_is_dyadic (z : F) (n : Nat) (h : z^(2^n : Nat)= -1) : DyadicRoot z := by
  refine ⟨n+1,?_⟩
  rw [← successor_power_square,CommSemiring.mul_pow,h]
  grind

theorem dyadic_ne_zero {z : F} (h : DyadicRoot z) : z≠0 := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<2) (n:=n)))
  intro e
  rw [hk,Semiring.pow_succ,e,Semiring.mul_zero] at hn
  grind

/-- One trace at each primitive level generates the traces of every dyadic
root. No compatibility of the choices at successive levels is required. -/
theorem real_tower_generators {C : F → Prop} (c : Subfield C) (ζ : Nat → F)
    (prim : ∀ n, (ζ n)^(2^(n+1) : Nat)= -1) :
    (∀ t, DyadicRoot t → C (realTrace t)) ↔ ∀ n, C (realTrace (ζ n)) := by
  constructor
  · intro h n
    exact h _ (primitive_is_dyadic _ _ (prim n))
  · intro h t ht
    obtain ⟨n,hn⟩ := ht
    obtain ⟨k,hk⟩ := powers_exhaust_roots (n+1) (ζ n) t (prim n) (root_level_raise t n hn 2)
    rw [hk]
    exact traces_of_powers c _ (dyadic_ne_zero (primitive_is_dyadic _ _ (prim n))) (h n) k

def genusFieldByLayers (B : F → Prop) (i x y : F) (ζ : Nat → F) (t : F) : Prop :=
  ∀ C : F → Prop, Subfield C → (∀ s, B s → C s) →
    (C (i*x*y) ∧ C (i*x) ∧ C (i*y) ∧ ∀ n, C (realTrace (ζ n))) → C t

/-- With B empty, the left side is E_a(μ₂∞) for E_a=Q(x,y,ζₐ+ζₐ⁻¹).
The right side is Q(√−69,√3,√23) times the real cyclotomic tower. -/
theorem mizusawa_field_change [IsCharP F 0] (B : F → Prop) (i x y : F)
    (hi : i*i= -1) (hx : x*x= -3) (hy : y*y= -23) (ζ : Nat → F)
    (prim : ∀ n, (ζ n)^(2^(n+1) : Nat)= -1) (a : Nat) :
    bottomTower (fun s => B s ∨ s=realTrace (ζ a)) x y = genusFieldByLayers B i x y ζ := by
  funext t
  apply propext
  constructor
  · intro h C c base rhs
    obtain ⟨ck,cX,cY,layers⟩ := rhs
    have all := (real_tower_generators c ζ prim).mpr layers
    apply h C c (fun s hs => hs.elim (base s) (fun e => e ▸ layers a))
    exact (subfield_generators_iff c i x y hi hx hy).mpr ⟨ck,cX,cY,all⟩
  · intro h C c base lhs
    obtain ⟨ck,cX,cY,all⟩ := (subfield_generators_iff c i x y hi hx hy).mp lhs
    exact h C c (fun s hb => base s (Or.inl hb)) ⟨ck,cX,cY,(real_tower_generators c ζ prim).mp all⟩

open Reimann.TameRationalField277 Reimann.DyadicEmbeddedBase69
open Reimann.DyadicBottomValue69 (Embedding)
attribute [local instance] Ring.intCast Semiring.natCast
variable {K : Type} [Field K]

theorem subfield_integers {C : K → Prop} (c : Subfield C) (m : Int) : C (m:K) := by
  have hn (n : Nat) : C (n:K) := by
    induction n with
    | zero => simpa only [Semiring.natCast_zero] using c.zero
    | succ k ih => rw [Semiring.natCast_succ]; exact c.add ih c.one
  cases m with
  | ofNat n =>
    change C (((n:Int):K))
    rw [Ring.intCast_natCast]
    exact hn n
  | negSucc n =>
    rw [Int.negSucc_eq,Ring.intCast_neg,Ring.intCast_add,Ring.intCast_natCast,Ring.intCast_one]
    exact c.neg (c.add (hn n) c.one)

theorem subfield_rationals {C : K → Prop} (c : Subfield C) (f : Embedding K) (q : Rat) :
    C (f.app (scalar q)) := by
  have h (m : Int) : C (f.app (scalar (m:Rat))) := by rw [f.scalar_int]; exact subfield_integers c m
  let den := f.app (scalar ((q.den:Int):Rat))
  have nden : den≠0 := DyadicBottomValue69.positive_integer_nonzero f q.den q.den_pos
  have num : f.app (scalar q)*den=f.app (scalar (q.num:Rat)) := by
    rw [← f.mul,(scalar_embedding _ _).2.2,rational_numerator]
  have one := Field.mul_inv_cancel nden
  have qr : f.app (scalar (q.num:Rat))*den⁻¹ = f.app (scalar q) := by
    rw [← num,Semiring.mul_assoc,one,Semiring.mul_one]
  exact qr ▸ c.mul (h q.num) (c.inv (h (q.den:Int)))

/-- An ambient subfield contains the embedded E₀ exactly when it contains
its two concrete radicals. Rational coefficients are automatic. -/
theorem bottom_image_iff {C : K → Prop} (c : Subfield C) (f : Embedding K) :
    (∀ z, baseImage f z → C z) ↔ C (f.app gen3) ∧ C (f.app gen23) := by
  constructor
  · exact fun h => ⟨h _ ⟨gen3,rfl⟩,h _ ⟨gen23,rfl⟩⟩
  · rintro ⟨hx,hy⟩ _ ⟨⟨⟨a,b⟩,⟨p,q⟩⟩,rfl⟩
    rw [← basis_expansion]
    simp only [f.add,f.mul]
    have h := subfield_rationals c f
    exact c.add (c.add (h a) (c.mul (h b) hx)) (c.add (c.mul (h p) hy) (c.mul (h q) (c.mul hx hy)))

theorem embedded_radical_squares (f : Embedding K) :
    f.app gen3*f.app gen3= -3 ∧ f.app gen23*f.app gen23= -23 := by
  constructor
  · rw [← f.mul,generator_squares.1]
    have h := f.scalar_int (-3)
    grind
  · rw [← f.mul,generator_squares.2]
    have h := f.scalar_int (-23)
    grind

/-- The compositum Eₐ(μ₂∞) formed from the image of the concrete bottom field. -/
def embeddedTower (f : Embedding K) (r t : K) : Prop :=
  ∀ C : K → Prop, Subfield C → (∀ z, baseImage f z → C z) →
    C r → (∀ z, DyadicRoot z → C z) → C t

theorem embedded_bottom_presentation (f : Embedding K) (r : K) :
    embeddedTower f r = bottomTower (fun z => False ∨ z=r) (f.app gen3) (f.app gen23) := by
  funext t
  apply propext
  constructor
  · intro h C c base hgens
    exact h C c ((bottom_image_iff c f).mpr ⟨hgens.1,hgens.2.1⟩) (base r (Or.inr rfl)) hgens.2.2
  · intro h C c base hr roots
    obtain ⟨hx,hy⟩ := (bottom_image_iff c f).mp base
    exact h C c (fun _ e => e.elim False.elim (fun he => he ▸ hr)) ⟨hx,hy,roots⟩

theorem embedded_mizusawa_field_change [IsCharP K 0] (f : Embedding K) (i : K)
    (hi : i*i= -1) (ζ : Nat → K) (prim : ∀ n, (ζ n)^(2^(n+1) : Nat)= -1) (a : Nat) :
    embeddedTower f (realTrace (ζ a)) =
    genusFieldByLayers (fun _ => False) i (f.app gen3) (f.app gen23) ζ := by
  rw [embedded_bottom_presentation]
  obtain ⟨hx,hy⟩ := embedded_radical_squares f
  exact mizusawa_field_change _ _ _ _ hi hx hy ζ prim a

end Reimann.DyadicGenusField69
