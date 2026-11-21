import Reimann277.AbsoluteFrobeniusLift
import Reimann277.ArithmeticSymbol

namespace Reimann.TameArithmeticSymbol277

open NumberField TameInertia277 TameArtin277 TameCyclotomicLocal277

theorem residueSize_at_prolongation {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal)
    (P : Ideal ClosureIntegers) (hP : Prolongs J P) :
    residueSize J = Nat.card (CutIntegers r n ⧸ P.comap (integralInclusion r n)) := by
  rw [hP.contraction, residueSize_contracted J hJ]

theorem prolongation_contraction_nonzero {r n : ℕ} (J : IntegralIdeals r n)
    (P : Ideal ClosureIntegers) (hP : Prolongs J P) : P.comap (integralInclusion r n) ≠ 0 := by
  rw [hP.contraction]
  exact contracted_ne_zero J

/-- Every prolongation of a surviving finite prime has an absolute arithmetic
Frobenius lift in the actual finite-twist kernel. -/
theorem exists_frobeniusAt {r n : ℕ} (J : IntegralIdeals r n) (hJ : J.val.IsMaximal)
    (P : Ideal ClosureIntegers) (hP : Prolongs J P) :
    ∃ x : globalKernel r n, FrobeniusAt J P x := by
  obtain ⟨g,hg⟩ := TameAbsoluteFrobenius277.exists_frobenius (K := cutField r n) (L := Closure)
    P hP.maximal.isPrime (prolongation_contraction_nonzero J P hP)
  obtain ⟨x,rfl⟩ := (kernelAutEquiv r n).surjective g
  refine ⟨x,?_⟩
  unfold FrobeniusAt
  rw [residueSize_at_prolongation J hJ P hP]
  exact hg

end Reimann.TameArithmeticSymbol277
