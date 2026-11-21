import ReimannNative69.DyadicUnramifiedClosure69
import ReimannNative69.DyadicBottomPrime69
import Reimann.DyadicGenusSwitcher69

/-! Finite-place inertia of the marked quadratic genus field over the real cyclotomic tower. -/
namespace Reimann.DyadicGenusInertia69

open DyadicUnramifiedClosure69
open scoped Pointwise

variable {Ω : Type} [Field Ω] [CharZero Ω]

/-- A root of the monic quadratic U²−U−c is an algebraic integer. -/
theorem quadratic_integer (u : Ω) (c : ℤ) (h : u*u = u + (c : Ω)) : IsIntegral ℤ u := by
  let f : QuadraticAlgebra ℤ c 1 →ₐ[ℤ] Ω :=
    QuadraticAlgebra.lift ⟨u,by simpa [zsmul_eq_mul,add_comm] using h⟩
  have integ : IsIntegral ℤ (QuadraticAlgebra.omega : QuadraticAlgebra ℤ c 1) :=
    Algebra.IsIntegral.isIntegral _
  simpa [f,QuadraticAlgebra.lift_apply_apply] using integ.map f

/-- For discriminants −3 and −23 the integral quadratic generator is (1+r)/2. -/
theorem integral_half_radical (r : Ω) (c : ℤ) (h : r^2 = 1 + 4*(c : Ω)) :
    IsIntegral ℤ ((1+r)/2) := by
  apply quadratic_integer _ c
  field_simp
  linear_combination h

/-- Flipping the quadratic generator by inertia forces the rational discriminant into the prime. -/
theorem half_flip_forces_discriminant (P : Ideal (integralClosure ℤ Ω)) (g : Ω ≃ₐ[ℚ] Ω)
    (res : ∀ u : integralClosure ℤ Ω, g • u - u ∈ P) (r : Ω) (n : ℕ)
    (half : IsIntegral ℤ ((1+r)/2)) (hs : r^2 = -(n : Ω)) (flip : g r = -r) :
    (n : integralClosure ℤ Ω) ∈ P := by
  let u : integralClosure ℤ Ω := ⟨(1+r)/2,half⟩
  let b := g • u - u
  have hb : (b : Ω) = -r := by
    change g ((1+r)/2) - (1+r)/2 = -r
    rw [map_div₀,map_add,map_one,map_ofNat,flip]
    ring
  have eq : -(b*b) = (n : integralClosure ℤ Ω) := by
    apply Subtype.ext
    change -((b : Ω) * (b : Ω)) = (n : Ω)
    rw [hb]
    linear_combination -hs
  exact eq ▸ P.neg_mem (P.mul_mem_left b (res u))

/-- Flipping i forces the rational prime 2 into the inertia prime. -/
theorem i_flip_forces_two (P : Ideal (integralClosure ℤ Ω)) (g : Ω ≃ₐ[ℚ] Ω)
    (res : ∀ u : integralClosure ℤ Ω, g • u - u ∈ P) (i : Ω)
    (hi : i^2 = -1) (flip : g i = -i) : (2 : integralClosure ℤ Ω) ∈ P := by
  have integ : IsIntegral ℤ i := IsIntegral.of_pow (n := 2) (by decide) (by
    rw [hi]
    exact isIntegral_one.neg)
  let u : integralClosure ℤ Ω := ⟨i,integ⟩
  have eq : u * (g • u - u) = (2 : integralClosure ℤ Ω) := by
    apply Subtype.ext
    change i*(g i-i)=2
    rw [flip]
    linear_combination -2*hi
  exact eq ▸ P.mul_mem_left u (res u)

/-- Bézout's identity excludes simultaneous membership for coprime rational primes. -/
theorem exclude_coprime {R : Type*} [CommRing R] (P : Ideal R) (hP : P.IsPrime)
    {a b : R} (coprime : IsCoprime a b) (ha : a ∈ P) (hb : b ∈ P) : False := by
  obtain ⟨m,n,eq⟩ := coprime
  exact hP.one_notMem (eq ▸ P.add_mem (P.mul_mem_left m ha) (P.mul_mem_left n hb))

/-- Fixation of the product ixy rules out a single sign flip. Two simultaneous sign
flips would put two of 2, 3, 23 in the same prime of the algebraic integers. -/
theorem inertia_fixes_three_radicals (g : Ω ≃ₐ[ℚ] Ω) (i x y : Ω)
    (hi : i^2 = -1) (hx : x^2 = -3) (hy : y^2 = -23)
    (hd : g (i*x*y) = i*x*y) (inert : finiteInertia (integralClosure ℤ Ω) g) :
    g i = i ∧ g x = x ∧ g y = y := by
  obtain ⟨P,hP,_,_,res⟩ := inert
  have si := sq_eq_sq_iff_eq_or_eq_neg.mp (show (g i)^2 = i^2 by rw [← map_pow,hi]; simp)
  have sx := sq_eq_sq_iff_eq_or_eq_neg.mp (show (g x)^2 = x^2 by rw [← map_pow,hx,map_neg,map_ofNat])
  have sy := sq_eq_sq_iff_eq_or_eq_neg.mp (show (g y)^2 = y^2 by rw [← map_pow,hy,map_neg,map_ofNat])
  have ix := integral_half_radical x (-1) (by norm_num; exact hx)
  have iy := integral_half_radical y (-6) (by norm_num; exact hy)
  have three (h : g x = -x) : (3 : integralClosure ℤ Ω) ∈ P :=
    half_flip_forces_discriminant P g res x 3 ix hx h
  have twentythree (h : g y = -y) : (23 : integralClosure ℤ Ω) ∈ P :=
    half_flip_forces_discriminant P g res y 23 iy hy h
  have ni : i ≠ 0 := by rintro rfl; norm_num at hi
  have nx : x ≠ 0 := by rintro rfl; norm_num at hx
  have ny : y ≠ 0 := by rintro rfl; norm_num at hy
  rw [map_mul,map_mul] at hd
  have fi : g i = i := by
    by_contra e
    have two := i_flip_forces_two P g res i hi (si.resolve_left e)
    have fx := sx.resolve_right (fun h => exclude_coprime P hP ⟨-1,1,by norm_num⟩ two (three h))
    have fy := sy.resolve_right (fun h => exclude_coprime P hP ⟨-11,1,by norm_num⟩ two (twentythree h))
    rw [fx,fy] at hd
    exact e (mul_right_cancel₀ nx (mul_right_cancel₀ ny hd))
  have fx : g x = x := by
    by_contra e
    have hp := three (sx.resolve_left e)
    have fy := sy.resolve_right (fun h => exclude_coprime P hP ⟨8,-1,by norm_num⟩ hp (twentythree h))
    rw [fi,fy] at hd
    exact e (mul_left_cancel₀ ni (mul_right_cancel₀ ny hd))
  rw [fi,fx] at hd
  exact ⟨fi,fx,mul_left_cancel₀ (mul_ne_zero ni nx) hd⟩

/-- Inertia over k∞ fixes both imaginary quadratic generators and every root
in the dyadic cyclotomic tower. -/
theorem inertia_fixes_marked_genus (Ω : Type) [Field Ω] [CharZero Ω] [IsGalois ℚ Ω]
    (x y : Ω) (ζ : ℕ → Ω) (hx : x^2 = -3) (hy : y^2 = -23)
    (hz : ∀ n, (ζ n)^(2^(n+1) : ℕ) = -1) (g : Ω ≃ₐ[ℚ] Ω)
    (hk : g ∈ (cyclotomicBase Ω (ζ 0*x*y) ζ).fixingSubgroup)
    (inert : finiteInertia (integralClosure ℤ Ω) g) :
    g x = x ∧ g y = y ∧ ∀ n, g (ζ n) = ζ n := by
  have fix := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hk
  have d : g (ζ 0*x*y) = ζ 0*x*y := fix _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _))
  have hi : (ζ 0)^2 = -1 := by simpa using hz 0
  obtain ⟨fi,fx,fy⟩ := inertia_fixes_three_radicals g (ζ 0) x y hi hx hy d inert
  refine ⟨fx,fy,fun n => ?_⟩
  have tr : g (ζ n+(ζ n)⁻¹) = ζ n+(ζ n)⁻¹ :=
    fix _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ (Set.mem_range_self n)))
  let a : DyadicLocalRestriction69.Automorphism Ω :=
    ⟨g,g.injective,g.surjective,map_zero g,map_one g,map_add g,map_mul g⟩
  exact (DyadicGenusField69.finite_generators_iff (DyadicGenusSwitcher69.fixed_subfield a)
    (ζ 0) (ζ n) n (by simpa only [pow_two] using hi) (hz n)).mpr ⟨tr,fi⟩

end Reimann.DyadicGenusInertia69
