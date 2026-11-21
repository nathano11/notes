import ReimannNative69.DyadicIntegerPrime69
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Two distinct primes of the full algebraic integers above two, separated by the
two roots of X²−X+6 modulo two. The argument needs no choice of integral basis. -/
namespace Reimann.DyadicBottomPrime69

open DyadicNativePrime69 DyadicIntegerPrime69

abbrev quadraticOrder := QuadraticAlgebra ℤ (-6) 1

theorem positive_norm_kernel (z : quadraticOrder) (h : QuadraticAlgebra.norm z=0) : z=0 := by
  have hz : z.re*z.re + z.re*z.im + 6*z.im*z.im=0 := by
    simpa [QuadraticAlgebra.norm_def] using h
  have hsum : (2*z.re+z.im)^2 + 23*z.im^2=0 := by nlinarith only [hz]
  have hi : z.im^2=0 := by nlinarith only [hsum,sq_nonneg (2*z.re+z.im),sq_nonneg z.im]
  have hzi : z.im=0 := by simpa using hi
  have hr : z.re*z.re=0 := by simpa [hzi] using hz
  exact QuadraticAlgebra.ext (mul_self_eq_zero.mp hr) hzi

noncomputable def evaluate {A : Type*} [CommRing A] (w : A) (hw : w*w=w-6) : quadraticOrder →+* A :=
  (QuadraticAlgebra.lift (a:=(-6:ℤ)) (b:=1) ⟨w,by simpa [zsmul_eq_mul,sub_eq_add_neg,add_comm] using hw⟩).toRingHom

theorem evaluate_generator {A : Type*} [CommRing A] (w : A) (hw : w*w=w-6) :
    evaluate w hw QuadraticAlgebra.omega=w := by simp [evaluate,QuadraticAlgebra.lift_apply_apply]

theorem evaluate_injective {K : Type*} [Field K] [CharZero K] (w : K) (hw : w*w=w-6) :
    Function.Injective (evaluate w hw) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  apply positive_norm_kernel
  have h : ((QuadraticAlgebra.norm z : ℤ) : K) = 0 := by
    calc
      _ = evaluate w hw (algebraMap ℤ quadraticOrder (QuadraticAlgebra.norm z)) := by simp
      _ = 0 := by rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star,map_mul,hz,zero_mul]
  exact_mod_cast h

def integerGenerator : integerRing quadraticOrder :=
  ⟨QuadraticAlgebra.omega,Algebra.IsIntegral.isIntegral _⟩

noncomputable def residue (r : ZMod 2) (hr : r*r=r-6) :
    integerRing quadraticOrder →+* ZMod 2 :=
  (evaluate r hr).comp (integerRing quadraticOrder).subtype

theorem residue_generator (r : ZMod 2) (hr : r*r=r-6) :
    residue r hr integerGenerator=r := evaluate_generator r hr

theorem residue_maximal (r : ZMod 2) (hr : r*r=r-6) : (RingHom.ker (residue r hr)).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro x
  obtain ⟨n,rfl⟩ := ZMod.intCast_surjective x
  exact ⟨n,map_intCast _ _⟩

theorem prolong_residue {K : Type*} [Field K] [CharZero K] (w : K) (hw : w*w=w-6)
    (r : ZMod 2) (hr : r*r=r-6) :
    ∃ P : Ideal (integerRing K), P.IsMaximal ∧
      ∀ z : integerRing quadraticOrder, integersMap (evaluate w hw) z ∈ P ↔ residue r hr z=0 := by
  obtain ⟨P,hP,hc⟩ := prolong_integer_prime (evaluate w hw) (evaluate_injective w hw)
    (RingHom.ker (residue r hr)) (residue_maximal r hr)
  refine ⟨P,hP,fun z => ?_⟩
  change z∈contraction (integersMap (evaluate w hw)) P ↔ _
  rw [hc]
  rfl

/-- The actual full integer ring has distinct maximal ideals at the two residue roots.
The integral element u represents w in these two ideals. -/
theorem two_dyadic_primes {K : Type*} [Field K] [CharZero K] (w : K) (hw : w*w=w-6) :
    ∃ u : integerRing K, u.val=w ∧ ∃ P Q : Ideal (integerRing K),
      P.IsMaximal ∧ Q.IsMaximal ∧ (2:integerRing K)∈P ∧ (2:integerRing K)∈Q ∧
      u∈P ∧ (1-u)∈Q ∧ u∉Q ∧ P≠Q := by
  let u := integersMap (evaluate w hw) integerGenerator
  have h0 : (0:ZMod 2)*0=0-6 := by decide
  have h1 : (1:ZMod 2)*1=1-6 := by decide
  obtain ⟨P,hP,hcP⟩ := prolong_residue w hw 0 h0
  obtain ⟨Q,hQ,hcQ⟩ := prolong_residue w hw 1 h1
  have htwo (r : ZMod 2) (hr : r*r=r-6) : residue r hr (2:integerRing quadraticOrder)=0 := by
    rw [map_ofNat]; decide
  have h2P := (hcP 2).mpr (htwo 0 h0)
  have h2Q := (hcQ 2).mpr (htwo 1 h1)
  have huP : u∈P := (hcP integerGenerator).mpr (residue_generator 0 h0)
  have huQ : u∉Q := fun hu => one_ne_zero ((residue_generator 1 h1).symm.trans ((hcQ _).mp hu))
  have hvQ := (hcQ (1-integerGenerator)).mpr (by simp [map_sub,residue_generator])
  exact ⟨u,evaluate_generator w hw,P,Q,hP,hQ,by simpa only [map_ofNat] using h2P,by simpa only [map_ofNat] using h2Q,
    huP,by simpa [u] using hvQ,huQ,fun he => huQ (he ▸ huP)⟩

/-- For the specified imaginary quadratic generator the two bottoms are indexed by
w=(1+sqrt(-23))/2 and its conjugate 1−w. -/
theorem half_generator_relation {K : Type*} [Field K] [CharZero K] (δ : K) (hδ : δ^2 = -23) :
    ((1+δ)/2)*((1+δ)/2)=(1+δ)/2-6 := by
  field_simp
  rw [add_sq,hδ]
  ring

theorem two_primes_at_sqrt_neg23 {K : Type*} [Field K] [CharZero K] (δ : K) (hδ : δ^2 = -23) :
    ∃ u : integerRing K, u.val=(1+δ)/2 ∧ ∃ P Q : Ideal (integerRing K),
      P.IsMaximal ∧ Q.IsMaximal ∧ (2:integerRing K)∈P ∧ (2:integerRing K)∈Q ∧
      u∈P ∧ (1-u)∈Q ∧ u∉Q ∧ P≠Q :=
  two_dyadic_primes _ (half_generator_relation δ hδ)

/-- At every prime of the integer ring over two, exactly one of the two roots vanishes. -/
theorem center_dichotomy {K : Type*} [Field K] (u : integerRing K) (hu : u*u=u-6)
    (P : Ideal (integerRing K)) (hP : P.IsPrime) (two : (2:integerRing K)∈P) :
    (u∈P ∧ 1-u∉P) ∨ (1-u∈P ∧ u∉P) := by
  have h6 : (6:integerRing K)∈P := by simpa only [show (3:integerRing K)*2=6 by norm_num] using P.mul_mem_left 3 two
  have hprod : u*(1-u)∈P := by rwa [mul_sub,mul_one,hu,sub_sub_cancel]
  have excl (huP : u∈P) (hvP : 1-u∈P) : False := hP.one_notMem (by simpa using P.add_mem hvP huP)
  rcases hP.mem_or_mem hprod with h | h
  · exact Or.inl ⟨h,excl h⟩
  · exact Or.inr ⟨h,fun t => excl t h⟩

/-- Any prime of the full ring of algebraic integers lying above two is maximal,
also when the field is an infinite algebraic extension. -/
theorem prime_containing_two_maximal {K : Type*} [Field K] (P : Ideal (integerRing K))
    (hP : P.IsPrime) (two : (2:integerRing K)∈P) : P.IsMaximal := by
  letI : P.IsPrime := hP
  haveI : Algebra.IsIntegral ℤ (integerRing K) := ⟨fun x =>
    (isIntegral_algHom_iff (integerRing K).subtype.toIntAlgHom Subtype.val_injective).mp x.property⟩
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R:=ℤ)
  apply IsPrime.to_maximal_ideal
  intro h
  have ht : (2:ℤ)∈P.under ℤ := by simpa only [Ideal.mem_comap,map_ofNat] using two
  rw [h] at ht
  exact (by decide : (2:ℤ)≠0) ht

end Reimann.DyadicBottomPrime69
