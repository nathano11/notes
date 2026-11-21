import Reimann277.IdealAction
import Reimann277.QuotientTransport

namespace Reimann.TameQuotientConjugation277

open TameCyclotomicLocal277 TameArtin277 TameIdealAction277

noncomputable def kernelEquiv (r n : ℕ) (g : Global) : globalKernel r n ≃* globalKernel r n where
  toFun := conjugateKernel g
  invFun := conjugateKernel g⁻¹
  left_inv x := by
    apply Subtype.ext
    change g⁻¹*(g*x.val*g⁻¹)*(g⁻¹)⁻¹ = x.val
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    change g*(g⁻¹*x.val*(g⁻¹)⁻¹)*g⁻¹ = x.val
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    change g*(x.val*y.val)*g⁻¹ = (g*x.val*g⁻¹)*(g*y.val*g⁻¹)
    simp [mul_assoc]

theorem kernelEquiv_continuous (r n : ℕ) (g : Global) : Continuous (kernelEquiv r n g) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

theorem atPlaces_conjugate (r n : ℕ) (g : Global) (x : globalKernel r n) (hx : x ∈ atPlaces r n) :
    conjugateKernel g x ∈ atPlaces r n := by
  obtain ⟨s,a,y,rfl⟩ := hx
  refine ⟨s,g*a,y,?_⟩
  apply Subtype.ext
  change g*(a*restriction s y.val*a⁻¹)*g⁻¹ = (g*a)*restriction s y.val*(g*a)⁻¹
  simp [mul_assoc]

theorem localRelations_conjugate (r n : ℕ) (g : Global) (x : globalKernel r n)
    (hx : x ∈ localRelations r n) : conjugateKernel g x ∈ localRelations r n := by
  rcases hx with h | h
  · exact Or.inl (TameQuotientTransport277.away_conjugate (asAut g) x h
      ((globalKernelNormal r n).conj_mem _ x.property g))
  · exact Or.inr (atPlaces_conjugate r n g x h)

theorem localRelations_conjugate_iff (r n : ℕ) (g : Global) (x : globalKernel r n) :
    x ∈ localRelations r n ↔ kernelEquiv r n g x ∈ localRelations r n := by
  constructor
  · exact localRelations_conjugate r n g x
  · intro h
    have hy := localRelations_conjugate r n g⁻¹ _ h
    change (kernelEquiv r n g).symm (kernelEquiv r n g x) ∈ localRelations r n at hy
    simpa only [MulEquiv.symm_apply_apply] using hy

/-- The global automorphism acts on the concrete unramified, 277-split quotient. -/
noncomputable def onQuotient (r n : ℕ) (g : Global) :
    UnramifiedSplitQuotient r n ≃* UnramifiedSplitQuotient r n :=
  TameQuotientTransport277.descendEquiv _ (kernelEquiv r n g) (kernelEquiv_continuous r n g)
    (kernelEquiv_continuous r n g⁻¹) (localRelations_conjugate_iff r n g)

theorem onQuotient_project (r n : ℕ) (g : Global) (x : globalKernel r n) :
    onQuotient r n g (project r n x) = project r n (conjugateKernel g x) := rfl

theorem onQuotient_continuous (r n : ℕ) (g : Global) : Continuous (onQuotient r n g) :=
  TameQuotientTransport277.descendEquiv_continuous _ _ _ _ _

theorem onQuotient_one (r n : ℕ) (a : UnramifiedSplitQuotient r n) :
    onQuotient r n 1 a = a := by
  obtain ⟨x,rfl⟩ := project_surjective r n a
  rw [onQuotient_project]
  apply congrArg (project r n)
  apply Subtype.ext
  change 1*x.val*(1 : Global)⁻¹ = x.val
  simp

theorem onQuotient_mul (r n : ℕ) (g h : Global) (a : UnramifiedSplitQuotient r n) :
    onQuotient r n (g*h) a = onQuotient r n g (onQuotient r n h a) := by
  obtain ⟨x,rfl⟩ := project_surjective r n a
  simp only [onQuotient_project]
  apply congrArg (project r n)
  apply Subtype.ext
  change (g*h)*x.val*(g*h)⁻¹ = g*(h*x.val*h⁻¹)*g⁻¹
  simp [mul_assoc]

/-- Conjugation by the upstairs kernel is already trivial on its abelian quotient. -/
theorem onQuotient_kernel (r n : ℕ) (h : globalKernel r n) (a : UnramifiedSplitQuotient r n) :
    onQuotient r n h.val a = a := by
  obtain ⟨x,rfl⟩ := project_surjective r n a
  rw [onQuotient_project]
  change project r n (h*x*h⁻¹) = project r n x
  rw [map_mul,map_mul,map_inv,quotient_commutes r n (project r n h) (project r n x),mul_inv_cancel_right]

end Reimann.TameQuotientConjugation277
