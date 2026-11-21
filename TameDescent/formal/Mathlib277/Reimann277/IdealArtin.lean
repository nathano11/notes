import Mathlib.RingTheory.ClassGroup.Basic

namespace Reimann.TameIdealArtin277

open scoped nonZeroDivisors

variable (R : Type*) [CommRing R] [IsDomain R]

abbrev InvertibleIdeals := (FractionalIdeal R⁰ (FractionRing R))ˣ

variable {G : Type*} [Group G]

/-- Ideal-theoretic inputs to global reciprocity for a chosen Galois quotient. -/
structure IdealSymbol where
  symbol : InvertibleIdeals R →* G
  onto : Function.Surjective symbol
  principal_kernel : symbol.ker = (toPrincipalIdeal R (FractionRing R)).range

variable {R}

noncomputable def classToGalois (a : IdealSymbol R (G := G)) : ClassGroup R ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq a.principal_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective a.symbol a.onto)

theorem classToGalois_mk (a : IdealSymbol R (G := G)) (I : InvertibleIdeals R) :
    classToGalois a (ClassGroup.mk (FractionRing R) I) = a.symbol I :=
  congrArg (classToGalois a) (ClassGroup.Quot_mk_eq_mk I).symm

theorem galoisToClass_symbol (a : IdealSymbol R (G := G)) (I : InvertibleIdeals R) :
    (classToGalois a).symm (a.symbol I) = ClassGroup.mk (FractionRing R) I :=
  (classToGalois a).symm_apply_eq.mpr (classToGalois_mk a I).symm

theorem principal_ideal_iff (a : IdealSymbol R (G := G)) (I : InvertibleIdeals R) :
    a.symbol I = 1 ↔ ∃ x : (FractionRing R)ˣ, toPrincipalIdeal R (FractionRing R) x = I := by
  change I ∈ a.symbol.ker ↔ _
  rw [a.principal_kernel]
  exact MonoidHom.mem_range

end Reimann.TameIdealArtin277
