import ReimannNative69.CircularCommonField69

/-! Two explicit subfield witnesses for the conductor comparison.
The quadratic witness uses the same orientation as the circular norm. -/

namespace Reimann.CircularConductorWitness69

open CircularCommonField69 CircularRealUnit69 CircularRational69 CircularRationalPeriod69

noncomputable abbrev period : K := CircularFactor69.periodTheta x

theorem period_equation : period^2 = period + 17 :=
  CircularFactor69.period_theta_quadratic x (CircularPrimitive69.phi_vanishes_of_order69 x
    CommonAmbient69.x_primitive.order69 CommonAmbient69.x_primitive.not23 CommonAmbient69.x_primitive.not3)

theorem radical_square_value : (u*v)^2 = 69 :=
  product_square u v radical_values.1 radical_values.2.1

theorem radical_in_real_field : u*v ∈ realField := by
  apply (real_membership _).mpr
  have hs := compositum_subfield u v
  exact ⟨hs.mul _ _ hs.root (compositum_generators u v).1,
    product_fixed c u v CommonConjugation69.compatible.first CommonConjugation69.compatible.second⟩

noncomputable def realRadical : realField := ⟨u*v, radical_in_real_field⟩

theorem realRadical_square : realRadical^2 = 69 := Subtype.ext radical_square_value

theorem radical_ne_rational (q : ℚ) : u*v ≠ algebraMap ℚ K q := by
  intro h
  apply rat_square_ne_69 q
  apply (algebraMap ℚ K).injective
  simpa only [map_pow, map_ofNat, ← h] using radical_square_value

theorem period_from_product : period = (1+u*v)/2 := by
  apply (eq_div_iff (two_ne_zero' K)).mpr
  rw [radical_values.2.2]
  ring

theorem quadratic_embedding_injective : Function.Injective (evaluate period) :=
  fun _ _ h => primitive_period_injective x CommonAmbient69.x_primitive.order69
    CommonAmbient69.x_primitive.not23 CommonAmbient69.x_primitive.not3 h

noncomputable def periodField : Subfield K where
  carrier := Set.range (evaluate period)
  zero_mem' := ⟨scalar 0, eval_zero period⟩
  one_mem' := ⟨scalar 1, eval_one period⟩
  add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨plus a b, by rw [eval_add, ha, hb]⟩
  neg_mem' := fun ⟨a, ha⟩ => ⟨negative a, by rw [eval_negative, ha]⟩
  mul_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨times a b, by rw [eval_mul _ period_equation, ha, hb]⟩
  inv_mem' := fun {_} ⟨a, ha⟩ => ⟨inverse a, by rw [eval_inverse _ period_equation, ha]⟩

theorem period_mem_image : period ∈ periodField := ⟨theta, eval_theta period⟩

theorem radical_mem_image : u*v ∈ periodField := by
  rw [radical_values.2.2]
  exact periodField.sub_mem (periodField.mul_mem (natCast_mem periodField 2) period_mem_image)
    periodField.one_mem

theorem quadratic_image_eq_radical_field : periodField = Subfield.closure ({u*v} : Set K) := by
  let S := Subfield.closure ({u*v} : Set K)
  have hrad : u*v ∈ S := Subfield.subset_closure (Set.mem_singleton _)
  have ht : period ∈ S := by
    rw [period_from_product]
    exact S.div_mem (S.add_mem S.one_mem hrad) (natCast_mem S 2)
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    exact S.add_mem (CommonRealPart69.rat_mem S a.a)
      (S.mul_mem (CommonRealPart69.rat_mem S a.b) ht)
  · apply Subfield.closure_le.mpr
    intro w hw
    exact (Set.mem_singleton_iff.mp hw) ▸ radical_mem_image

theorem quadratic_image_real : periodField ≤ realField := by
  rw [quadratic_image_eq_radical_field]
  exact Subfield.closure_le.mpr (Set.singleton_subset_iff.mpr radical_in_real_field)

theorem root_trace_in_compositum :
    Compositum u v (CommonAmbient69.z + CommonAmbient69.z⁻¹) := by
  let z := CommonAmbient69.z
  have hz := (compositum_generators u v).2 z CommonAmbient69.z_order
  have hn : z ≠ 0 := by
    intro hz0
    have bad := CommonAmbient69.z_order
    change z^277 = 1 at bad
    simp [hz0] at bad
  exact (compositum_subfield u v).add _ _ hz ((compositum_subfield u v).inv _ hn hz)

theorem root_trace_fixed :
    c.app (CommonAmbient69.z + CommonAmbient69.z⁻¹) = CommonAmbient69.z + CommonAmbient69.z⁻¹ := by
  rw [c.add, c.inv, CommonConjugation69.conjugate_z, inv_inv, add_comm]

theorem root_trace_in_real_field : CommonAmbient69.z + CommonAmbient69.z⁻¹ ∈ realField :=
  (real_membership _).mpr ⟨root_trace_in_compositum, root_trace_fixed⟩

end Reimann.CircularConductorWitness69
