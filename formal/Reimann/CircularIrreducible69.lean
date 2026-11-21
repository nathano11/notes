import Reimann.CircularGauss69
import Reimann.CircularAbsolute69

/-! Transfer the integral factor obstruction to finitely supported rational coefficients. -/
namespace Reimann.CircularIrreducible69

open CircularGauss69

def truncation (q : Nat → Rat) (d : Nat) : List Rat :=
  List.ofFn (fun i : Fin (d+1) => q i.val)

theorem truncation_length (q : Nat → Rat) (d : Nat) : (truncation q d).length = d+1 :=
  List.length_ofFn

theorem truncation_coeff (q : Nat → Rat) (d : Nat) (tail : ∀ i, d+1 ≤ i → q i = 0) :
    coeff (truncation q d) = q := by
  funext i
  simp only [coeff, truncation, List.getElem?_ofFn]
  split
  · rfl
  · exact (tail i (by omega)).symm

theorem truncation_last (q : Nat → Rat) (d : Nat) :
    (truncation q d).getLast? = some (q d) := by
  rw [List.getLast?_eq_getElem?, truncation_length]
  simp only [Nat.add_sub_cancel, truncation, List.getElem?_ofFn]
  split
  · rfl
  · omega

theorem lift_length (A : List Int) (q : Nat → Rat) (d : Nat)
    (h : A.map (fun z : Int => (z : Rat)) = truncation q d) : A.length = d+1 := by
  simpa only [List.length_map, truncation_length] using congrArg List.length h

theorem lift_last (A : List Int) (q : Nat → Rat) (d : Nat)
    (h : A.map (fun z : Int => (z : Rat)) = truncation q d) (monic : q d = 1) :
    A.getLast? = some 1 := by
  have eqn := congrArg List.getLast? h
  rw [List.getLast?_map, truncation_last, monic] at eqn
  cases hx : A.getLast? with
  | none => simp [hx] at eqn
  | some a =>
    have ea : (a : Rat) = ((1 : Int) : Rat) := by simpa [hx] using eqn
    rw [Rat.intCast_inj.mp ea]

theorem integral_lifts (d e : Nat) (q D : Nat → Rat)
    (hq : ∀ i, e+1 ≤ i → q i = 0) (hD : ∀ i, d+1 ≤ i → D i = 0)
    (mq : q e = 1) (mD : D d = 1)
    (hmul : ∀ k, convolution q D k = ((coeff CircularPolynomial69.phi k : Int) : Rat)) :
    ∃ A B : List Int, A.length = e+1 ∧ B.length = d+1 ∧
      A.getLast? = some 1 ∧ B.getLast? = some 1 ∧
      ∀ n, convolution (coeff A) (coeff B) n = coeff CircularPolynomial69.phi n := by
  have topq := (truncation_last q e).trans (congrArg some mq)
  have topD := (truncation_last D d).trans (congrArg some mD)
  obtain ⟨A,B,hA,hB,prod⟩ := monic_factorization_descends CircularPolynomial69.phi
    (truncation q e) (truncation D d) (List.mem_of_getLast? topq) (List.mem_of_getLast? topD)
    (by simpa only [truncation_coeff q e hq, truncation_coeff D d hD] using hmul)
  exact ⟨A,B,lift_length A q e hA,lift_length B D d hB,lift_last A q e hA mq,
    lift_last B D d hB mD,prod⟩

theorem no_rational_split (d e : Nat) (hd : 0 < d) (he : 0 < e) (hdeg : d+e = 44)
    (q D : Nat → Rat) (hq : ∀ i, e+1 ≤ i → q i = 0) (hD : ∀ i, d+1 ≤ i → D i = 0)
    (mq : q e = 1) (mD : D d = 1)
    (hmul : ∀ k, convolution q D k = ((coeff CircularPolynomial69.phi k : Int) : Rat)) :
    False := by
  obtain ⟨A,B,lenA,lenB,endA,endB,prod⟩ := integral_lifts d e q D hq hD mq mD hmul
  exact CircularAbsolute69.no_monic_integer_factorization A B e d he hd (by omega)
    lenA lenB endA endB prod

end Reimann.CircularIrreducible69
