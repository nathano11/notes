import ReimannNative69.DyadicIntegerPrime69
import Reimann.DyadicEmbeddedBase69
import Mathlib.Algebra.Polynomial.Monic

/-! Transport the monic equations of the explicit 69 order into mathlib's
actual integral closure of the integers in an ambient field. -/
namespace Reimann.DyadicEmbeddedIntegers69

open Polynomial DyadicBottomValue69 DyadicIntegralCriterion69
variable {K : Type} [Field K]

noncomputable def monicPolynomial : List ℤ → ℤ[X]
  | [] => 1
  | a :: t => X * monicPolynomial t + C a

theorem monic_polynomial (c : List ℤ) : (monicPolynomial c).Monic := by
  induction c with
  | nil => exact monic_one
  | cons a c ih =>
    apply (monic_X.mul ih).add_of_left
    apply lt_of_le_of_lt (degree_C_le : (C a).degree ≤ 0)
    rw [degree_eq_natDegree (mul_ne_zero X_ne_zero ih.ne_zero),natDegree_X_mul ih.ne_zero]
    exact_mod_cast Nat.succ_pos _

theorem evaluate_monic (f : Embedding K) (z : TameRationalField277.Biquad) (c : List ℤ) :
    aeval (f.app z) (monicPolynomial c) = f.app (monicAt z c) := by
  induction c with
  | nil => simpa only [monicPolynomial,monicAt,map_one] using (DyadicEmbeddedBase69.map_zero_one f).2.symm
  | cons a c ih =>
    simp only [monicPolynomial,monicAt,map_add,map_mul,aeval_X,aeval_C,ih,f.add,f.mul,f.scalar_int]
    rfl

theorem isIntegral_of_monic (f : Embedding K) {z : TameRationalField277.Biquad}
    (hz : DyadicIntegralCriterion69.IsIntegral z) : _root_.IsIntegral ℤ (f.app z) := by
  obtain ⟨c,hc⟩ := hz
  exact ⟨monicPolynomial c,monic_polynomial c,(evaluate_monic f z c).trans
    ((congrArg f.app hc).trans (DyadicEmbeddedBase69.map_zero_one f).1)⟩

def orderNumerator (f : Embedding K) (p : Dyadic.Matrix) : DyadicIntegerPrime69.integerRing K :=
  ⟨f.app (DyadicFieldTrace69.embed p),isIntegral_of_monic f (DyadicOrderIntegral69.order_is_integral p)⟩

end Reimann.DyadicEmbeddedIntegers69

