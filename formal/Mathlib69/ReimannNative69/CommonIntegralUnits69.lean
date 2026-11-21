import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import ReimannNative69.CommonRealPart69
import ReimannNative69.CircularSubgroup69

/-! A unit in the integral closure of the integers in the real compositum.
The integral closure is allowed to have its own carrier and embedding.
Mathlib's standard integer ring has precisely the required instance. -/

namespace Reimann.CommonIntegralUnits69

open CircularFieldReduction69 CircularPolynomial69 CircularRealUnit69 CircularSinnott69
  CircularSubgroup69

variable {R : Type} [Field R]

def integerEmbedding (E : Subfield R) (O : Type*) [CommRing O] [Algebra O E] : O →+* R :=
  E.subtype.comp (algebraMap O E)

def standardCircularUnits (E : Subfield R) (O : Type*) [CommRing O] [Algebra O E]
    (D : Subgroup Rˣ) : Subgroup Oˣ :=
  D.comap (Units.map (integerEmbedding E O).toMonoidHom)

theorem lift_integral_element {E : Type*} [Field E] (O : Type*) [CommRing O] [Algebra O E]
    [IsIntegralClosure O ℤ E] (e : E) (he : IsIntegral ℤ e) :
    ∃ a : O, algebraMap O E a = e :=
  IsIntegralClosure.isIntegral_iff.mp he

theorem lift_integral_unit {E : Type*} [Field E] (O : Type*) [CommRing O] [Algebra O E]
    [IsIntegralClosure O ℤ E] (e f : E) (he : IsIntegral ℤ e) (hf : IsIntegral ℤ f)
    (hinv : e*f = 1) :
    ∃ w : Oˣ, algebraMap O E w.val = e ∧ algebraMap O E (w⁻¹).val = f := by
  obtain ⟨a,ha⟩ := lift_integral_element O e he
  obtain ⟨b,hb⟩ := lift_integral_element O f hf
  have hab : a*b = 1 := by
    apply IsIntegralClosure.algebraMap_injective O ℤ E
    rw [map_mul,ha,hb,_root_.map_one,hinv]
  let w : Oˣ := ⟨a,b,hab,(mul_comm b a).trans hab⟩
  exact ⟨w,ha,hb⟩

theorem quadratic_integral_in_subfield (E : Subfield R) (e : E)
    (he : (e : R)^2-25*(e : R)+1 = 0) : IsIntegral ℤ e :=
  integral_of_quadratic e (Subtype.ext he)

variable [CharZero R]

/-- The returned unit and its inverse belong to the actual units of any
standard integral closure in E. Their images in the ambient field belong
to the specified circular numbers. -/
theorem positive_and_inverse (x u v : R) (hx : Primitive69 x)
    (hu : u^2 = -3) (hv : v^2 = -23) (c : Conjugation R) (hc : Compatible c u v)
    (E : Subfield R) (hE : ∀ t : R, t ∈ E ↔ RealPart c u v t)
    (O : Type*) [CommRing O] [Algebra O E] [IsIntegralClosure O ℤ E]
    (D : Subgroup Rˣ) (hD : normGenerators x hx (RealPart c u v) ⊆ D) :
    ∃ w : Oˣ, integerEmbedding E O w.val = signedProduct x 1 ∧
      integerEmbedding E O (w⁻¹).val = 25-signedProduct x 1 ∧
      w ∈ standardCircularUnits E O D ∧ w⁻¹ ∈ standardCircularUnits E O D := by
  obtain ⟨⟨ss,hs,hprod⟩,hrE,hrF,hinv,hquadE,hquadF⟩ :=
    real_circular_unit x u v hx hu hv c hc
  let e : E := ⟨signedProduct x 1,(hE _).mpr hrE⟩
  let f : E := ⟨25-signedProduct x 1,(hE _).mpr hrF⟩
  obtain ⟨w,hw,hi⟩ := lift_integral_unit O e f
    (quadratic_integral_in_subfield E e hquadE) (quadratic_integral_in_subfield E f hquadF)
    (Subtype.ext hinv)
  have hw' : integerEmbedding E O w.val = signedProduct x 1 := congrArg Subtype.val hw
  have hi' : integerEmbedding E O (w⁻¹).val = 25-signedProduct x 1 := congrArg Subtype.val hi
  let z := Units.map (integerEmbedding E O).toMonoidHom w
  have hz : (z : R) = signedProduct x 1 := hw'
  have hnum := positive_mem_numbers x hx (RealPart c u v) ss hs z (hz.trans hprod)
  have hmem : w ∈ standardCircularUnits E O D := (conductorNumbers_le _ _ _ _).mpr hD hnum
  exact ⟨w,hw',hi',hmem,(standardCircularUnits E O D).inv_mem hmem⟩

end Reimann.CommonIntegralUnits69
