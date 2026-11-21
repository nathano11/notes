import Reimann.CircularReduction69

/-! Bounded Horner reduction in the integral order at conductor 69. Each
degree-44 cancellation exhibits the integer multiple of the monic relation. -/
namespace Reimann.CircularIntegralNormal69

open Lean.Grind CircularPolynomial69 CircularReduction69
attribute [local instance] Ring.intCast

theorem add_length (p q : List Int) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons c p ih =>
    cases q with
    | nil => simp [add]
    | cons a q => simp only [add,List.length_cons,ih]; omega

theorem eval_append_last {R : Type} [CommRing R] (x : R) (p : List Int) (a : Int) :
    eval x (p ++ [a]) = eval x p + x^p.length * Int.cast a := by
  induction p with
  | nil =>
    simp only [List.nil_append,eval,List.length_nil,Semiring.pow_zero,Semiring.one_mul]
    grind only
  | cons c p ih =>
    simp only [List.cons_append,eval,ih,List.length_cons,Semiring.pow_succ]
    grind only

theorem phi_lower_length : phi.dropLast.length = 44 := by decide +kernel

theorem phi_append_leading : phi.dropLast ++ [1] = phi := by decide +kernel

theorem phi_leading_identity {R : Type} [CommRing R] (x : R) :
    eval x phi = eval x phi.dropLast + x^44 := by
  calc
    eval x phi = eval x (phi.dropLast ++ [1]) := congrArg (eval x) phi_append_leading.symm
    _ = _ := by rw [eval_append_last,phi_lower_length,Ring.intCast_one,Semiring.mul_one]

def cancelLeading (p : List Int) (a : Int) : List Int :=
  add p (phi.dropLast.map (fun b => -a * b))

theorem cancelLeading_length (p : List Int) (a : Int) (h : p.length = 44) :
    (cancelLeading p a).length = 44 := by
  rw [cancelLeading,add_length,List.length_map,phi_lower_length,h]
  decide

theorem cancelLeading_congruent (p : List Int) (a : Int) (h : p.length = 44) :
    Congruent (p ++ [a]) (cancelLeading p a) := by
  refine ⟨[a],?_⟩
  intro R _ x
  rw [eval_append_last,h,cancelLeading,eval_add,eval_scale,Ring.intCast_neg,phi_leading_identity]
  simp only [eval,Semiring.mul_zero,Semiring.add_zero]
  grind only

theorem congruent_cons (c : Int) {p q : List Int} (h : Congruent p q) :
    Congruent (c :: p) (c :: q) := by
  obtain ⟨k,hk⟩ := h
  refine ⟨0 :: k,?_⟩
  intro R _ x
  simp only [eval,hk R x,Ring.intCast_zero]
  grind only

def hornerStep (c : Int) (r : List Int) : List Int :=
  if r.length = 44 then
    cancelLeading (c :: r).dropLast ((c :: r).getLast (by simp))
  else c :: r

theorem hornerStep_length (c : Int) (r : List Int) (h : r.length ≤ 44) :
    (hornerStep c r).length ≤ 44 := by
  by_cases e : r.length = 44
  · simp only [hornerStep,e,ite_true]
    rw [cancelLeading_length _ _ (by simpa using e)]
    exact Nat.le_refl _
  · simp only [hornerStep,e,ite_false,List.length_cons]
    omega

theorem hornerStep_congruent (c : Int) (r : List Int) :
    Congruent (c :: r) (hornerStep c r) := by
  by_cases e : r.length = 44
  · simp only [hornerStep,e,ite_true]
    have h := cancelLeading_congruent (c :: r).dropLast ((c :: r).getLast (by simp)) (by simpa using e)
    rwa [List.dropLast_concat_getLast] at h
  · simp only [hornerStep,e,ite_false]
    exact congruent_refl _

def normalForm : List Int → List Int
  | [] => []
  | c :: p => hornerStep c (normalForm p)

theorem normalForm_length (p : List Int) : (normalForm p).length ≤ 44 := by
  induction p with
  | nil => decide
  | cons c p ih => exact hornerStep_length c _ ih

theorem normalForm_congruent (p : List Int) : Congruent p (normalForm p) := by
  induction p with
  | nil => exact congruent_refl []
  | cons c p ih => exact congruent_trans (congruent_cons c ih) (hornerStep_congruent c _)

theorem integral_normal_form (p : List Int) : ∃ q : List Int, q.length ≤ 44 ∧ Congruent p q :=
  ⟨normalForm p,normalForm_length p,normalForm_congruent p⟩

end Reimann.CircularIntegralNormal69
