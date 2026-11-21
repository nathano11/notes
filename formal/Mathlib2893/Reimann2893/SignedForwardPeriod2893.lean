import Reimann2893.SignedFieldLayers2893

/-! Period of the forward field automorphism on each finite cyclotomic layer. -/
namespace Reimann.SignedForwardPeriod2893

open SignedFieldLayers2893

theorem pow_include (n j : Nat) (x : Layer n) :
    (forward (n+1)^j) (includeNext n x) = includeNext n ((forward n^j) x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ', RingAut.mul_apply, RingAut.mul_apply, ih, forward_include]

theorem root_fixed_or_negated (n : Nat) (σ : Layer (n+1) ≃+* Layer (n+1))
    (fixed : ∀ a : Layer n, σ (includeNext n a) = includeNext n a) :
    σ (traceRoot (n+1)) = traceRoot (n+1) ∨ σ (traceRoot (n+1)) = -traceRoot (n+1) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, traceRoot_succ_sq, fixed]

theorem quadratic_square_trivial (n : Nat) (σ : Layer (n+1) ≃+* Layer (n+1))
    (fixed : ∀ a : Layer n, σ (includeNext n a) = includeNext n a) : σ^2 = 1 := by
  have twice : σ (σ (traceRoot (n+1))) = traceRoot (n+1) := by
    rcases root_fixed_or_negated n σ fixed with hp | hm
    · rw [hp,hp]
    · rw [hm,map_neg,hm,neg_neg]
  apply RingEquiv.ext
  intro z
  obtain ⟨a,b,rfl⟩ := span_next n z
  simp only [pow_two, RingAut.mul_apply, map_add, map_mul, fixed, twice, RingAut.one_apply]

/-- The period bound is proved on every element of the actual field. -/
theorem forward_period (n : Nat) : (forward n)^(2^n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ 2 n, pow_mul]
    apply quadratic_square_trivial
    intro a
    rw [pow_include,ih, RingAut.one_apply]

end Reimann.SignedForwardPeriod2893
