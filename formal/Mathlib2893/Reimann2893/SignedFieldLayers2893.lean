import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Rat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The imaginary quadratic bottom field and its tower of real dyadic traces.
The quadratic norm of either 2 plus or 2 minus a new trace is 2 minus the old trace. -/
noncomputable section
namespace Reimann.SignedFieldLayers2893

abbrev Bottom := QuadraticAlgebra ℚ (-2893) 0

theorem negative_nonsquare : ¬ IsSquare (-2893 : ℚ) := by
  rintro ⟨r, hr⟩
  nlinarith [sq_nonneg r]

instance bottomNonsquare : Fact (¬ IsSquare (-2893 : ℚ)) := ⟨negative_nonsquare⟩

theorem rational_two_nonsquare : ¬ IsSquare (2 : ℚ) := by
  rintro ⟨r,hr⟩
  have h := (Rat.exists_mul_self 2).mp ⟨r, hr.symm⟩
  rw [Rat.sqrt_ofNat] at h
  norm_num at h

theorem bottom_two_nonsquare : ¬ IsSquare (2 : Bottom) := by
  rintro ⟨z, hz⟩
  have h₀ := congrArg QuadraticAlgebra.re hz
  have h₁ := congrArg QuadraticAlgebra.im hz
  change (2 : ℚ) = z.re * z.re + (-2893) * z.im * z.im at h₀
  change (0 : ℚ) = z.re * z.im + z.im * z.re + 0 * z.im * z.im at h₁
  have hz' : z.re * z.im = 0 := by linarith [mul_comm z.im z.re]
  rcases mul_eq_zero.mp hz' with hr | hi
  · rw [hr] at h₀
    nlinarith [sq_nonneg z.im]
  · exact rational_two_nonsquare ⟨z.re, by simpa [hi] using h₀⟩

def fifth {K : Type*} [CommRing K] (x : K) : K := x^5 - 5*x^3 + 5*x

def omega {K : Type*} [CommRing K] (d : K) : QuadraticAlgebra K d 0 := ⟨0,1⟩

theorem omega_squared {K : Type*} [CommRing K] (d : K) :
    (omega d)^2 = algebraMap K (QuadraticAlgebra K d 0) d := by
  ext <;> simp [omega, pow_two]

theorem norm_shift_plus {K : Type*} [Field K] (x : K) :
    QuadraticAlgebra.norm (2 + omega (2+x)) = 2-x := by
  simp [QuadraticAlgebra.norm_def, omega, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

theorem norm_shift_minus {K : Type*} [Field K] (x : K) :
    QuadraticAlgebra.norm (2 - omega (2+x)) = 2-x := by
  simp [QuadraticAlgebra.norm_def, omega, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

theorem nonsquare_of_norm {K : Type*} [Field K] {d : K}
    (z : QuadraticAlgebra K d 0) (h : ¬ IsSquare (QuadraticAlgebra.norm z)) :
    ¬ IsSquare z := by
  rintro ⟨u,rfl⟩
  exact h ⟨u.norm, map_mul _ _ _⟩

/-- The coefficient of the new trace in the expression for its fifth-power image. -/
def multiplier {K : Type*} [CommRing K] (x : K) : K := x^2-x-1

theorem fifth_extension {K : Type*} [CommRing K] (x : K) :
    2+fifth x = (2+x)*(multiplier x)^2 := by
  unfold fifth multiplier
  ring

theorem fifth_omega {K : Type*} [Field K] (x : K) :
    fifth (omega (2+x)) = (⟨0,multiplier x⟩ : QuadraticAlgebra K (2+x) 0) := by
  ext <;> simp [fifth,omega,multiplier,pow_succ,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;> ring

/-- Extend a field automorphism to the quadratic layer by the weighted image of the root. -/
def extend {K : Type*} [Field K] (d v : K) (s : K ≃+* K)
    (h : s d = d*v^2) (hv : v ≠ 0) :
    QuadraticAlgebra K d 0 ≃+* QuadraticAlgebra K d 0 where
  toFun z := ⟨s z.re,v*s z.im⟩
  invFun z := ⟨s.symm z.re,s.symm (z.im/v)⟩
  left_inv z := by
    ext
    · exact s.symm_apply_apply _
    · change s.symm (v * s z.im / v) = z.im
      rw [mul_div_cancel_left₀ _ hv, s.symm_apply_apply]
  right_inv z := by
    ext
    · exact s.apply_symm_apply _
    · change v * s (s.symm (z.im/v)) = z.im
      rw [s.apply_symm_apply, mul_div_cancel₀ _ hv]
  map_add' z w := by ext <;> simp <;> ring
  map_mul' z w := by ext <;> simp [h] <;> ring

structure Stage where
  carrier : Type
  [field : Field carrier]
  [charZero : CharZero carrier]
  root : carrier
  plus : ¬ IsSquare (2+root)
  minus : ¬ IsSquare (2-root)
  action : carrier ≃+* carrier
  power_five : action root = fifth root

attribute [instance] Stage.field Stage.charZero

def bottomStage : Stage where
  carrier := Bottom
  root := 0
  plus := by simpa using bottom_two_nonsquare
  minus := by simpa using bottom_two_nonsquare
  action := RingEquiv.refl _
  power_five := by simp [fifth]

theorem radicand_ne_zero (s : Stage) : 2+s.root ≠ 0 := by
  intro h
  exact s.plus ⟨0, by simp [h]⟩

theorem action_radicand (s : Stage) :
    s.action (2+s.root) = (2+s.root)*(multiplier s.root)^2 := by
  rw [map_add, map_ofNat, s.power_five, fifth_extension]

theorem multiplier_nonzero (s : Stage) : multiplier s.root ≠ 0 := by
  intro h
  have eqn := action_radicand s
  rw [h] at eqn
  exact radicand_ne_zero s (s.action.injective (by simpa using eqn))

instance stepNonsquare (s : Stage) : Fact (¬ IsSquare (2+s.root)) := ⟨s.plus⟩

def next (s : Stage) : Stage where
  carrier := QuadraticAlgebra s.carrier (2+s.root) 0
  root := omega (2+s.root)
  plus := nonsquare_of_norm _ (by rw [norm_shift_plus]; exact s.minus)
  minus := nonsquare_of_norm _ (by rw [norm_shift_minus]; exact s.minus)
  action := extend _ _ s.action (action_radicand s) (multiplier_nonzero s)
  power_five := by
    rw [fifth_omega]
    change (⟨s.action 0, multiplier s.root * s.action 1⟩ : QuadraticAlgebra s.carrier (2+s.root) 0) = _
    simp

def tower : Nat → Stage
  | 0 => bottomStage
  | n+1 => next (tower n)

abbrev Layer (n : Nat) := (tower n).carrier

def traceRoot (n : Nat) : Layer n := (tower n).root

def forward (n : Nat) : Layer n ≃+* Layer n := (tower n).action

def includeNext (n : Nat) : Layer n →+* Layer (n+1) :=
  algebraMap (Layer n) (QuadraticAlgebra (Layer n) (2+(tower n).root) 0)

theorem traceRoot_zero : traceRoot 0 = 0 := rfl

theorem traceRoot_succ_sq (n : Nat) :
    traceRoot (n+1)^2 = includeNext n (2+traceRoot n) := omega_squared _

theorem forward_include (n : Nat) (x : Layer n) :
    forward (n+1) (includeNext n x) = includeNext n (forward n x) := by
  change (⟨(forward n) x, multiplier (traceRoot n) * (forward n) 0⟩ :
    QuadraticAlgebra (Layer n) (2+traceRoot n) 0) = ⟨(forward n) x, 0⟩
  simp

theorem forward_five (n : Nat) :
    forward n (traceRoot n) = (traceRoot n)^5-5*(traceRoot n)^3+5*traceRoot n :=
  (tower n).power_five

instance layerAlgebra (n : Nat) : Algebra (Layer n) (Layer (n+1)) :=
  inferInstanceAs (Algebra (Layer n) (QuadraticAlgebra (Layer n) (2+traceRoot n) 0))

theorem includeNext_eq_algebraMap (n : Nat) :
    includeNext n = algebraMap (Layer n) (Layer (n+1)) := rfl

instance finiteStep (n : Nat) : Module.Finite (Layer n) (Layer (n+1)) :=
  inferInstanceAs (Module.Finite (Layer n) (QuadraticAlgebra (Layer n) (2+traceRoot n) 0))

instance layerScalarTower (n : Nat) : IsScalarTower ℚ (Layer n) (Layer (n+1)) :=
  inferInstanceAs (IsScalarTower ℚ (Layer n) (QuadraticAlgebra (Layer n) (2+traceRoot n) 0))

instance finiteOverRat (n : Nat) : Module.Finite ℚ (Layer n) := by
  induction n with
  | zero => exact inferInstanceAs (Module.Finite ℚ Bottom)
  | succ n ih =>
    letI := ih
    exact Module.Finite.trans (Layer n) (Layer (n+1))

/-- Extension of a scalar homomorphism with a prescribed image of the square root. -/
def evaluateQuadratic {K L : Type*} [Field K] [Field L] (d : K) (i : K →+* L)
    (u : L) (hu : u^2 = i d) : QuadraticAlgebra K d 0 →+* L where
  toFun z := i z.re + i z.im * u
  map_one' := by change i 1 + i 0 * u = 1; simp
  map_zero' := by change i 0 + i 0 * u = 0; simp
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      map_zero, zero_mul, add_zero]
    rw [← hu]
    ring

def bottomRadical : Layer 0 := omega (-2893 : ℚ)

theorem bottomRadical_sq : bottomRadical^2 = (-2893 : Layer 0) := by
  have h : (omega (-2893 : ℚ))^2 = (-2893 : Bottom) := by
    ext <;> norm_num [omega,pow_two,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
  exact h

def liftBottom {L : Type*} [Field L] [CharZero L] (s : L) (hs : s^2 = -2893) :
    Layer 0 →+* L :=
  evaluateQuadratic (-2893 : ℚ) (algebraMap ℚ L) s (by simpa using hs)

theorem liftBottom_radical {L : Type*} [Field L] [CharZero L] (s : L) (hs : s^2 = -2893) :
    liftBottom s hs bottomRadical = s := by
  change algebraMap ℚ L 0 + algebraMap ℚ L 1 * s = s
  simp

def liftNext (n : Nat) {L : Type*} [Field L] (i : Layer n →+* L)
    (u : L) (hu : u^2 = i (2+traceRoot n)) : Layer (n+1) →+* L :=
  evaluateQuadratic (2+traceRoot n) i u hu

theorem liftNext_root (n : Nat) {L : Type*} [Field L] (i : Layer n →+* L)
    (u : L) (hu : u^2 = i (2+traceRoot n)) :
    liftNext n i u hu (traceRoot (n+1)) = u := by
  change i 0 + i 1 * u = u
  simp

theorem liftNext_include (n : Nat) {L : Type*} [Field L] (i : Layer n →+* L)
    (u : L) (hu : u^2 = i (2+traceRoot n)) (x : Layer n) :
    liftNext n i u hu (includeNext n x) = i x := by
  change i x + i 0 * u = i x
  simp

theorem span_quadratic {K : Type*} [Field K] (d : K) (z : QuadraticAlgebra K d 0) :
    z = QuadraticAlgebra.C z.re + QuadraticAlgebra.C z.im * omega d := by
  ext <;> simp [omega, -QuadraticAlgebra.C_eq_algebraMap]

theorem span_next (n : Nat) (z : Layer (n+1)) :
    ∃ a b : Layer n, z = includeNext n a + includeNext n b * traceRoot (n+1) := by
  let y : QuadraticAlgebra (Layer n) (2+traceRoot n) 0 := z
  exact ⟨y.re,y.im,span_quadratic _ y⟩

def embedBottom : (n : Nat) → Bottom →+* Layer n
  | 0 => RingHom.id _
  | n+1 => (includeNext n).comp (embedBottom n)

theorem forward_fixes_bottom (n : Nat) (x : Bottom) :
    forward n (embedBottom n x) = embedBottom n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change forward (n+1) (includeNext n (embedBottom n x)) = includeNext n (embedBottom n x)
    rw [forward_include, ih]

theorem bottom_degree_two : Module.finrank ℚ (Layer 0) = 2 :=
  QuadraticAlgebra.finrank_eq_two (-2893 : ℚ) 0

theorem step_degree_two (n : Nat) : Module.finrank (Layer n) (Layer (n+1)) = 2 :=
  QuadraticAlgebra.finrank_eq_two (2+traceRoot n) 0

end Reimann.SignedFieldLayers2893
