import Std
import Reimann.CircularPolynomial69

/-! Evaluation at a primitive cube root in integral coordinates. -/
namespace Reimann.CircularEisenstein69

open Lean.Grind
attribute [local instance] Ring.intCast
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def padd {R : Type} [Add R] : List R → List R → List R
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a+b) :: padd p q

def pmul {R : Type} [CommRing R] : List R → List R → List R
  | [], _ => []
  | a :: p, q => padd (q.map (fun b => a*b)) (0 :: pmul p q)

def pPow {R : Type} [CommRing R] (p : List R) : Nat → List R
  | 0 => [1]
  | n+1 => pmul p (pPow p n)

def omegaMul {R : Type} [CommRing R] (x y : R × R) : R × R :=
  (x.1*y.1 - x.2*y.2, x.1*y.2 + x.2*y.1 - x.2*y.2)

def omegaEval {R : Type} [CommRing R] : List R → R × R
  | [] => (0,0)
  | c :: p => (c-(omegaEval p).2, (omegaEval p).1-(omegaEval p).2)

def omegaNorm {R : Type} [CommRing R] (x : R × R) : R :=
  x.1*x.1 - x.1*x.2 + x.2*x.2

theorem omegaNorm_mul {R : Type} [CommRing R] (x y : R × R) :
    omegaNorm (omegaMul x y) = omegaNorm x * omegaNorm y := by
  simp only [omegaNorm, omegaMul]
  grind only

theorem finite_norm_zero (x : Fin 23 × Fin 23)
    (h : omegaNorm x = 0) : x = (0,0) := by
  have table : ∀ a b : Fin 23, omegaNorm (a,b) = 0 → (a,b) = (0,0) := by decide +kernel
  exact table x.1 x.2 h

theorem finite_product_zero : ∀ a b : Fin 23,
    a*b = 0 → a = 0 ∨ b = 0 := by decide +kernel

theorem finite_pair_no_zero_divisors (x y : Fin 23 × Fin 23)
    (h : omegaMul x y = (0,0)) : x = (0,0) ∨ y = (0,0) := by
  have hprod : omegaNorm x * omegaNorm y = 0 := by
    rw [← omegaNorm_mul, h]
    decide
  exact (finite_product_zero _ _ hprod).imp (finite_norm_zero _) (finite_norm_zero _)

theorem omegaEval_add {R : Type} [CommRing R] (p q : List R) :
    omegaEval (padd p q) =
      ((omegaEval p).1+(omegaEval q).1, (omegaEval p).2+(omegaEval q).2) := by
  induction p generalizing q with
  | nil => simp [omegaEval, padd, AddCommMonoid.zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [omegaEval, padd, AddCommMonoid.add_zero]
    | cons b q =>
      simp only [padd, omegaEval, ih, Prod.mk.injEq]
      constructor <;> grind only

theorem omegaEval_scale {R : Type} [CommRing R] (a : R) (q : List R) :
    omegaEval (q.map (fun b => a*b)) =
      (a*(omegaEval q).1, a*(omegaEval q).2) := by
  induction q with
  | nil => simp [omegaEval] <;> grind only
  | cons b q ih =>
    simp only [List.map_cons, omegaEval, ih, Prod.mk.injEq]
    constructor <;> grind only

theorem omegaEval_mul {R : Type} [CommRing R] (p q : List R) :
    omegaEval (pmul p q) = omegaMul (omegaEval p) (omegaEval q) := by
  induction p with
  | nil => simp [pmul, omegaEval, omegaMul] <;> grind only
  | cons a p ih =>
    simp only [pmul, omegaEval_add, omegaEval_scale, omegaEval, ih, omegaMul, Prod.mk.injEq]
    constructor <;> grind only

def reduce23 (z : Int) : Fin 23 := Int.cast z

theorem reduce23_add (x y : Int) : reduce23 (x+y) = reduce23 x + reduce23 y :=
  Ring.intCast_add x y

theorem reduce23_mul (x y : Int) : reduce23 (x*y) = reduce23 x * reduce23 y :=
  Ring.intCast_mul x y

theorem reduce23_sub (x y : Int) : reduce23 (x-y) = reduce23 x - reduce23 y :=
  Ring.intCast_sub x y

theorem omegaEval_reduce (p : List Int) :
    omegaEval (p.map reduce23) = (reduce23 (omegaEval p).1, reduce23 (omegaEval p).2) := by
  induction p with
  | nil => decide
  | cons a p ih => simp only [List.map_cons, omegaEval, ih, reduce23_sub]

theorem phi_omegaEval : omegaEval CircularPolynomial69.phi = (0,-23) := by decide +kernel

theorem phi_reduce : CircularPolynomial69.phi.map reduce23 = pPow [1,1,1] 22 := by decide +kernel

theorem reduce23_zero_dvd (z : Int) (h : reduce23 z = 0) : 23 ∣ z := by
  change Fin.intCast z = (0 : Fin 23) at h
  cases z with
  | ofNat n =>
    have hv := congrArg Fin.val h
    change n % 23 = 0 at hv
    obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero hv
    refine ⟨(k : Int), ?_⟩
    change (n : Int) = 23 * (k : Int)
    omega
  | negSucc n =>
    have hn := congrArg Neg.neg h
    change -(-(Fin.ofNat 23 (n+1))) = -(0 : Fin 23) at hn
    have hc : Fin.ofNat 23 (n+1) = (0 : Fin 23) := by grind only
    have hv := congrArg Fin.val hc
    change (n+1) % 23 = 0 at hv
    obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero hv
    refine ⟨-(k : Int), ?_⟩
    change -(↑n + 1 : Int) = 23 * -(k : Int)
    omega

theorem second_coordinate_dvd (x y : Int × Int)
    (hx : 23 ∣ x.1 ∧ 23 ∣ x.2) (hy : 23 ∣ y.1 ∧ 23 ∣ y.2) :
    529 ∣ (omegaMul x y).2 := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hx
  obtain ⟨⟨c,hc⟩,⟨d,hd⟩⟩ := hy
  refine ⟨a*d+b*c-b*d, ?_⟩
  simp only [omegaMul, ha, hb, hc, hd]
  grind only

theorem phi_factor_obstruction (p q : List Int) (h : pmul p q = CircularPolynomial69.phi)
    (hp : omegaEval (p.map reduce23) = (0,0)) (hq : omegaEval (q.map reduce23) = (0,0)) :
    False := by
  rw [omegaEval_reduce, Prod.mk.injEq] at hp hq
  have d := second_coordinate_dvd (omegaEval p) (omegaEval q)
    ⟨reduce23_zero_dvd _ hp.1, reduce23_zero_dvd _ hp.2⟩
    ⟨reduce23_zero_dvd _ hq.1, reduce23_zero_dvd _ hq.2⟩
  rw [← omegaEval_mul, h, phi_omegaEval] at d
  exact (by decide : ¬ (529 : Int) ∣ -23) d

theorem reduce23_padd (p q : List Int) :
    (padd p q).map reduce23 = padd (p.map reduce23) (q.map reduce23) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q => simp only [padd, List.map_cons, reduce23_add, ih]

theorem reduce23_scale (a : Int) (q : List Int) :
    (q.map (fun b => a*b)).map reduce23 =
      (q.map reduce23).map (fun b => reduce23 a*b) := by
  induction q with
  | nil => rfl
  | cons b q ih => simp only [List.map_cons, reduce23_mul, ih]

theorem reduce23_pmul (p q : List Int) :
    (pmul p q).map reduce23 = pmul (p.map reduce23) (q.map reduce23) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons, pmul, reduce23_padd, reduce23_scale, ih]
    rfl

end Reimann.CircularEisenstein69
