import Reimann.TameBiquadratic277

/-! Coordinate comparison for the two teams working on E₀. The tame
calculation uses X,Y; the dyadic integral order uses e,w with X=2e-1,
Y=2w-1. Coefficients are ordered (1,e,w,ew) or (1,X,Y,XY). -/

namespace Reimann.DyadicBasisComparison

open Lean.Grind Reimann.TameBiquadratic277

variable {R : Type} [CommRing R]

def toIntegral (z : Quad R) : Quad R :=
  ((z.1.1-z.1.2-z.2.1+z.2.2, 2*(z.1.2-z.2.2)),(2*(z.2.1-z.2.2),4*z.2.2))

theorem evaluation_comparison (e w : R) (z : Quad R) :
    let a := toIntegral z
    (a.1.1+a.1.2*e)+(a.2.1+a.2.2*e)*w =
      (z.1.1+z.1.2*(2*e-1))+(z.2.1+z.2.2*(2*e-1))*(2*w-1) := by
  simp only [toIntegral]
  grind

def fromIntegral (half : R) (z : Quad R) : Quad R :=
  let t := half*half*z.2.2
  ((z.1.1+half*z.1.2+half*z.2.1+t,half*z.1.2+t),(half*z.2.1+t,t))

theorem inverses_at_odd_prime (half : R) (h : 2*half=1) (z : Quad R) :
    fromIntegral half (toIntegral z) = z ∧ toIntegral (fromIntegral half z) = z := by
  constructor <;> apply Prod.ext <;> apply Prod.ext <;> simp only [fromIntegral,toIntegral] <;> grind

/-- The three independent congruences describe the sublattice integrally;
there are two choices of parity twice and four choices in the ew slot. -/
theorem integer_image (z : Quad Int) :
    (∃ x, toIntegral x = z) ↔ (2 ∣ z.1.2) ∧ (2 ∣ z.2.1) ∧ (4 ∣ z.2.2) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨⟨_,rfl⟩,⟨_,rfl⟩,⟨_,rfl⟩⟩
  · rintro ⟨⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩
    refine ⟨((z.1.1+b+c+d,b+d),(c+d,d)), ?_⟩
    apply Prod.ext <;> apply Prod.ext <;> simp only [toIntegral] <;> grind

theorem basis_comparison_277 (n : Nat) :
    ∃ half : Residue n, 2*half=1 ∧ ∀ z : Quad (Residue n),
      fromIntegral half (toIntegral z) = z ∧ toIntegral (fromIntegral half z) = z := by
  obtain ⟨h,_⟩ := TameSplitting277.split_both_277 n
  obtain ⟨_,hd⟩ := lifted_equations _ _ _ _ h
  let half := liftedRoot (-3) 44 85 n * liftedInverse (-3) 44 85 n
  have hh : 2*half = 1 := by unfold half; grind
  exact ⟨half, hh, inverses_at_odd_prime half hh⟩

def cosetIndex (z : Quad Int) : Fin 16 :=
  let v := 8*(z.1.2%2)+4*(z.2.1%2)+z.2.2%4
  ⟨v.toNat, by dsimp [v]; omega⟩

theorem same_coset_iff (x y : Quad Int) :
    (∃ v, toIntegral v = ((x.1.1-y.1.1,x.1.2-y.1.2),(x.2.1-y.2.1,x.2.2-y.2.2))) ↔
    cosetIndex x = cosetIndex y := by
  rw [integer_image, Fin.ext_iff]
  simp only [cosetIndex]
  omega

theorem sixteen_cosets (i : Fin 16) : ∃ z : Quad Int, cosetIndex z = i := by
  let k := (i.val : Int)
  refine ⟨((0,k/8),((k/4)%2,k%4)), Fin.ext ?_⟩
  simp only [cosetIndex,k]
  have := i.isLt
  omega

end Reimann.DyadicBasisComparison
