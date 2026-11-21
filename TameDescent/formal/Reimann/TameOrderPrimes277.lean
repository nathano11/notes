import Reimann.TameFiber277
import Reimann.TameBiquadratic277

namespace Reimann.TameOrderPrimes277

open TameFiber277 TameBiquadratic277 Lean.Grind Fin.IntCast

/-- The integral order Z[X,Y]/(X²+3,Y²+23), in its four-coefficient presentation. -/
abbrev Order := Quad Int

def mapQuad (f : A → B) (v : Quad A) : Quad B :=
  ((f v.1.1,f v.1.2),(f v.2.1,f v.2.2))

def unpack (v : Quad A) (i : Fin 4) : A :=
  if i=0 then v.1.1 else if i=1 then v.1.2 else if i=2 then v.2.1 else v.2.2

def pack (v : Fin 4 → A) : Quad A := ((v 0,v 1),(v 2,v 3))

theorem pack_unpack (v : Quad A) : pack (unpack v) = v := by rfl

theorem unpack_pack (v : Fin 4 → A) : unpack (pack v) = v := by
  funext i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 :=
    (by decide +kernel : ∀ j : Fin 4, j=0 ∨ j=1 ∨ j=2 ∨ j=3) i
  rcases h with h|h|h|h <;> subst i <;> rfl

def castQ (x : Order) : Quad F := mapQuad (fun z : Int => (z : F)) x

theorem castQ_add (x y : Order) :
    castQ (componentAdd x y) = componentAdd (castQ x) (castQ y) := by
  simp only [castQ,mapQuad,componentAdd,Ring.intCast_add]

theorem castQ_mul (x y : Order) :
    castQ (product (-3) (-23) x y) = product (-3) (-23) (castQ x) (castQ y) := by
  simp only [castQ,mapQuad,product,Ring.intCast_add,Ring.intCast_mul,Ring.intCast_neg]
  rfl

def liftQ (v : Quad F) : Order := mapQuad (fun z : F => (z.val : Int)) v

theorem castQ_lift (v : Quad F) : castQ (liftQ v) = v := by
  have he (a : F) : ((a.val : Int) : F) = a := by
    apply Fin.eq_of_val_eq
    rw [Lean.Grind.Fin.val_intCast,Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.isLt)]
    rfl
  simp [castQ,liftQ,mapQuad,he]

/-- Evaluation in the four residue branches in ++,+−,−+,−− order. -/
def red (x : Order) : Fiber := unpack ((finite_splitting277 0).evaluate (castQ x))

theorem red_surjective (v : Fiber) : ∃ x, red x=v := by
  let e := finite_splitting277 0
  refine ⟨liftQ (e.interpolate (pack v)),?_⟩
  unfold red
  rw [castQ_lift,e.realize,unpack_pack]

theorem unpack_add (x y : Quad F) :
    unpack (componentAdd x y) = fun i => unpack x i + unpack y i := by
  funext i
  unfold unpack
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> simp [h0,h1,h2,componentAdd]

theorem unpack_mul (x y : Quad F) :
    unpack (pointProduct x y) = fun i => unpack x i * unpack y i := by
  funext i
  unfold unpack
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> simp [h0,h1,h2,pointProduct]

theorem red_add (x y : Order) :
    red (componentAdd x y) = fun i => red x i+red y i := by
  unfold red
  rw [castQ_add,(finite_splitting277 0).add,unpack_add]

theorem red_mul (x y : Order) :
    red (product (-3) (-23) x y) = fun i => red x i*red y i := by
  unfold red
  rw [castQ_mul,(finite_splitting277 0).mul,unpack_mul]

def scalar (a : Int) : Order := ((a,0),(0,0))

theorem red_scalar (a : Int) : red (scalar a) = fun _ => (a : F) := by
  unfold red
  change unpack ((finite_splitting277 0).evaluate (((a : F),0),(0,0))) = _
  rw [(finite_splitting277 0).scalar]
  funext i
  simp [unpack]

theorem red_eq_castQ {x y : Order} (h : red x=red y) : castQ x=castQ y := by
  have H := congrArg (fun v => (finite_splitting277 0).interpolate (pack v)) h
  simpa only [red,pack_unpack,(finite_splitting277 0).reconstruct] using H

theorem cast_eq_translate {a b : Int} (h : (a : F) = (b : F)) :
    ∃ z : Int, a=b+277*z := by
  have H := congrArg Fin.val h
  rw [Lean.Grind.Fin.val_intCast,Lean.Grind.Fin.val_intCast] at H
  have hh : a%277=b%277 := by omega
  obtain ⟨z,hz⟩ := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hh)
  exact ⟨z,by omega⟩

theorem translate {x y : Order} (h : red x=red y) :
    ∃ z : Order, x=componentAdd y (product (-3) (-23) z (scalar 277)) := by
  have H := red_eq_castQ h
  obtain ⟨a,ha⟩ := cast_eq_translate (congrArg (fun s => s.1.1) H)
  obtain ⟨b,hb⟩ := cast_eq_translate (congrArg (fun s => s.1.2) H)
  obtain ⟨c,hc⟩ := cast_eq_translate (congrArg (fun s => s.2.1) H)
  obtain ⟨d,hd⟩ := cast_eq_translate (congrArg (fun s => s.2.2) H)
  refine ⟨((a,b),(c,d)),?_⟩
  apply Prod.ext <;> apply Prod.ext <;> simp [componentAdd,product,scalar] <;> grind

/-- Proper prime ideal predicate on the four-coefficient order. -/
structure OrderPrime (P : Order → Prop) : Prop where
  zero : P (scalar 0)
  proper : ¬ P (scalar 1)
  add : ∀ {x y}, P x → P y → P (componentAdd x y)
  absorb : ∀ a {x}, P x → P (product (-3) (-23) a x)
  prime : ∀ {x y}, P (product (-3) (-23) x y) → P x ∨ P y

theorem saturated {P : Order → Prop} (hp : OrderPrime P) (h277 : P (scalar 277))
    {x y : Order} (h : red x=red y) : P x ↔ P y := by
  have direction {a b : Order} (eq : red a=red b) (mem : P b) : P a := by
    obtain ⟨z,hz⟩ := translate eq
    rw [hz]
    exact hp.add mem (hp.absorb z h277)
  exact ⟨direction h.symm,direction h⟩

def image (P : Order → Prop) (v : Fiber) : Prop := ∃ x, red x=v ∧ P x

theorem image_red {P : Order → Prop} (hp : OrderPrime P) (h277 : P (scalar 277))
    (x : Order) : image P (red x) ↔ P x := by
  constructor
  · rintro ⟨y,hy,mem⟩
    exact (saturated hp h277 hy).mp mem
  · intro mem
    exact ⟨x,rfl,mem⟩

theorem prime_image {P : Order → Prop} (hp : OrderPrime P) (h277 : P (scalar 277)) :
    IsPrime (image P) := by
  constructor
  · exact ⟨scalar 0,red_scalar 0,hp.zero⟩
  · intro h
    apply hp.proper
    apply (image_red hp h277 (scalar 1)).mp
    rw [red_scalar]
    exact h
  · rintro a b ⟨x,rfl,hx⟩ ⟨y,rfl,hy⟩
    exact ⟨componentAdd x y,red_add x y,hp.add hx hy⟩
  · rintro a b ⟨y,rfl,hy⟩
    obtain ⟨x,rfl⟩ := red_surjective a
    exact ⟨product (-3) (-23) x y,red_mul x y,hp.absorb x hy⟩
  · intro a b h
    obtain ⟨x,rfl⟩ := red_surjective a
    obtain ⟨y,rfl⟩ := red_surjective b
    rw [← red_mul] at h
    rcases hp.prime ((image_red hp h277 _).mp h) with hx|hy
    · exact Or.inl ((image_red hp h277 _).mpr hx)
    · exact Or.inr ((image_red hp h277 _).mpr hy)

def coordinateKernel (i : Fin 4) (x : Order) : Prop := kernel i (red x)

theorem coordinate_prime (i : Fin 4) : OrderPrime (coordinateKernel i) := by
  have h := kernel_prime i
  constructor
  · change kernel i (red (scalar 0))
    rw [red_scalar]
    exact h.zero
  · change ¬kernel i (red (scalar 1))
    rw [red_scalar]
    exact h.proper
  · intro x y hx hy
    change kernel i (red (componentAdd x y))
    rw [red_add]
    exact h.add hx hy
  · intro a x hx
    change kernel i (red (product (-3) (-23) a x))
    rw [red_mul]
    exact h.absorb _ hx
  · intro x y hxy
    change kernel i (red (product (-3) (-23) x y)) at hxy
    rw [red_mul] at hxy
    exact h.prime hxy

theorem coordinate_above (i : Fin 4) : coordinateKernel i (scalar 277) := by
  change kernel i (red (scalar 277))
  rw [red_scalar]
  rfl

theorem coordinate_injective {i j : Fin 4} (h : coordinateKernel i = coordinateKernel j) : i=j := by
  apply kernel_injective
  funext v
  obtain ⟨x,rfl⟩ := red_surjective v
  exact congrFun h x

/-- Each prime ideal of the integral coordinate order containing 277 is one
of the four signed kernels, and each of the four occurs exactly once. -/
theorem four_primes_above_277 (P : Order → Prop) :
    (OrderPrime P ∧ P (scalar 277)) ↔
      ∃ i, P=coordinateKernel i ∧ ∀ j, P=coordinateKernel j → j=i := by
  constructor
  · rintro ⟨hp,h277⟩
    obtain ⟨i,hi⟩ := (prime_iff_coordinate (image P)).mp (prime_image hp h277)
    have eq : P=coordinateKernel i := by
      funext x
      apply propext
      change P x ↔ kernel i (red x)
      rw [← hi, image_red hp h277]
    exact ⟨i,eq,fun _ hj => coordinate_injective (hj.symm.trans eq)⟩
  · rintro ⟨i,rfl,_⟩
    exact ⟨coordinate_prime i,coordinate_above i⟩

/-- Each coordinate prime contracts to exactly (277) in the scalar integers. -/
theorem contraction (i : Fin 4) (a : Int) : coordinateKernel i (scalar a) ↔ 277 ∣ a := by
  unfold coordinateKernel kernel
  rw [red_scalar]
  change ((a : F)=0) ↔ 277 ∣ a
  constructor
  · intro ha
    obtain ⟨z,hz⟩ := cast_eq_translate (b := 0) ha
    exact ⟨z,by omega⟩
  · intro ha
    exact cast_difference a 0 (by simpa using ha)

/-- The signed evaluation at any one coordinate is onto the full residue field. -/
theorem residue_surjective (i : Fin 4) (a : F) : ∃ x : Order, red x i = a := by
  obtain ⟨x,hx⟩ := red_surjective (fun _ => a)
  exact ⟨x,congrFun hx i⟩

end Reimann.TameOrderPrimes277
