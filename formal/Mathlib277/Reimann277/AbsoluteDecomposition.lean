import Reimann277.PadicEmbeddings
import Mathlib.FieldTheory.AbsoluteGaloisGroup

namespace Reimann.TameCyclotomicLocal277

open TameBiquadraticField277 TamePadicEmbeddings277

local instance absolutePrime : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

abbrev Global := Field.absoluteGaloisGroup Biquadratic

abbrev Local := Field.absoluteGaloisGroup ℚ_[277]

abbrev asAut {K : Type*} [Field K] (g : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g

/-- Each field embedding gives a continuous restriction after mathlib's choice
of a compatible embedding of algebraic closures. -/
noncomputable def restriction (s : Bool × Bool) : Local →ₜ* Global :=
  Field.absoluteGaloisGroup.map (embedding s).toRingHom

/-- Use exactly the closure embedding chosen by absoluteGaloisGroup.map. -/
noncomputable def closureEmbedding (s : Bool × Bool) :
    AlgebraicClosure Biquadratic →+* AlgebraicClosure ℚ_[277] :=
  letI : Algebra Biquadratic ℚ_[277] := (embedding s).toRingHom.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure Biquadratic →ₐ[Biquadratic] AlgebraicClosure ℚ_[277]).toRingHom

theorem closureEmbedding_on_base (s : Bool × Bool) (x : Biquadratic) :
    closureEmbedding s (algebraMap Biquadratic (AlgebraicClosure Biquadratic) x) =
      algebraMap ℚ_[277] (AlgebraicClosure ℚ_[277]) (embedding s x) := by
  letI : Algebra Biquadratic ℚ_[277] := (embedding s).toRingHom.toAlgebra
  let j : AlgebraicClosure Biquadratic →ₐ[Biquadratic] AlgebraicClosure ℚ_[277] := IsAlgClosed.lift
  exact j.commutes x

theorem restriction_commutes (s : Bool × Bool) (g : Local) (z : AlgebraicClosure Biquadratic) :
    closureEmbedding s (asAut (restriction s g) z) = asAut g (closureEmbedding s z) := by
  letI : Algebra Biquadratic ℚ_[277] := (embedding s).toRingHom.toAlgebra
  let f : AlgebraicClosure Biquadratic →ₐ[Biquadratic] AlgebraicClosure ℚ_[277] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure Biquadratic) (AlgebraicClosure ℚ_[277]) := f.toAlgebra
  exact ((asAut g).restrictScalars Biquadratic).restrictNormal_commutes (AlgebraicClosure Biquadratic) z

theorem restriction_root_action (s : Bool × Bool) (n e : Nat) (g : Local)
    (h : ∀ ζ : AlgebraicClosure ℚ_[277], ζ^277^(n+1) = 1 → asAut g ζ = ζ^e)
    (z : AlgebraicClosure Biquadratic) (hz : z^277^(n+1) = 1) :
    asAut (restriction s g) z = z^e := by
  apply (closureEmbedding s).injective
  rw [restriction_commutes,map_pow]
  apply h
  rw [← map_pow,hz,map_one]

end Reimann.TameCyclotomicLocal277
