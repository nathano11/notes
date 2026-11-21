import Reimann.CircularRelativeGalois69
import Reimann.CircularRealUnit69
import Reimann.CircularCosets69

/-! The conductor-69 contribution to circular numbers, using the norm
operator (the product over automorphisms fixing the field intersection). -/

namespace Reimann.CircularSinnott69

open Lean.Grind CircularSubstitution69 CircularPowerSubstitution69 CircularRelativeGalois69
  CircularGalois69 CircularPolynomial69 CircularFieldReduction69 CircularCosets69
  CircularRealUnit69 CircularFactor69

variable {R : Type} [Field R] [IsCharP R 0]

def FixesIntersection {x : R} {hx : Primitive69 x} (K : R → Prop) (e : FieldIso x x hx hx) : Prop :=
  ∀ y : Carrier x, K y.val → e.forward y = y

def intersectionLabels (x : R) (hx : Primitive69 x) (K : R → Prop) (a : Fin 69) : Prop :=
  ∃ ha : Nat.Coprime a.val 69, FixesIntersection K (power_automorphism x hx a ha)

theorem intersection_one (x : R) (hx : Primitive69 x) (K : R → Prop) :
    intersectionLabels x hx K 1 :=
  ⟨by decide, fun y _ => power_one_apply x hx y⟩

theorem intersection_mul (x : R) (hx : Primitive69 x) (K : R → Prop) (a b : Fin 69)
    (ha : intersectionLabels x hx K a) (hb : intersectionLabels x hx K b) :
    intersectionLabels x hx K (a*b) := by
  obtain ⟨ua,fa⟩ := ha
  obtain ⟨ub,fb⟩ := hb
  refine ⟨unit_product a b ua ub, ?_⟩
  intro y hy
  rw [power_product_apply x hx a b ua ub y, fb y hy, fa y hy]

theorem intersection_positive (x : R) (hx : Primitive69 x) (K : R → Prop)
    (hF : ∀ c, K (coefficient x hx c).val) (a : Fin 69) (ha : intersectionLabels x hx K a) :
    eta a.val = 1 := by
  obtain ⟨ua,fa⟩ := ha
  have fixes : FixesQuadratic (power_automorphism x hx a ua) := fun c => fa _ (hF c)
  have h := (fixes_iff_label _).mp fixes
  rwa [power_label] at h

theorem automorphism_of_label {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) :
    power_automorphism x hx (label e) (label_spec e).2.1 = e := by
  apply iso_ext_generator
  exact Subtype.ext ((power_generator x hx _ _).trans (label_spec e).1.symm)

/-- The labels enumerate precisely the automorphisms fixing every element
of the actual intersection of K with the generated cyclotomic field. -/
theorem intersection_exact {x : R} {hx : Primitive69 x} (K : R → Prop) (e : FieldIso x x hx hx) :
    intersectionLabels x hx K (label e) ↔ FixesIntersection K e := by
  constructor
  · rintro ⟨_,hf⟩
    rwa [automorphism_of_label e] at hf
  · intro hf
    exact ⟨(label_spec e).2.1, (automorphism_of_label e).symm ▸ hf⟩

def factor (x : R) (a : Fin 69) : Carrier x :=
  plus x (constant x 1) (times x (constant x (-1)) (power x (generator x) a.val))

theorem factor_at_image {x : R} {hx : Primitive69 x} (e : FieldIso x x hx hx) (a : Fin 69) :
    (e.forward (factor x a)).val = 1-(generatorImage e)^a.val := by
  unfold factor
  rw [e.map_plus, e.map_times, e.map_constant, e.map_constant, CircularSubstitution69.map_power]
  change Field.NormNum.ofRat 1 + Field.NormNum.ofRat (-1) * (generatorImage e)^a.val = _
  have hn := CircularRationalPeriod69.cast_int (R := R) (-1)
  change (Field.NormNum.ofRat (-1) : R) = _ at hn
  rw [CircularRelationEval69.ofRat_one, hn]
  simp only [Ring.intCast_neg, Ring.intCast_one]
  grind only

theorem factor_value (x : R) (hx : Primitive69 x) (a : Fin 69) :
    (factor x a).val = 1-x^a.val :=
  factor_at_image (identityIso x hx) a

noncomputable def action (x : R) (hx : Primitive69 x) (s : Fin 69) (y : Carrier x) : Carrier x :=
  if hs : Nat.Coprime s.val 69 then (power_automorphism x hx s hs).forward y else y

/-- Multiplicative norm operator over every generated-field automorphism
that fixes K intersected with the conductor field, once each. -/
noncomputable def normOperator (x : R) (hx : Primitive69 x) (K : R → Prop) (y : Carrier x) : R := by
  classical
  exact (labels (intersectionLabels x hx K)).foldr (fun s z => (action x hx s y).val * z) 1

theorem intersection_labels_nodup (x : R) (hx : Primitive69 x) (K : R → Prop) :
    (@labels (intersectionLabels x hx K) (fun _ => Classical.propDecidable _)).Nodup := by
  classical
  exact (List.nodup_finRange 69).filter _

theorem factor_orbit (x : R) (hx : Primitive69 x) (K : R → Prop) (a : Fin 69) :
    normOperator x hx K (factor x a) =
      @orbitProduct R _ x (intersectionLabels x hx K) (fun _ => Classical.propDecidable _) a := by
  classical
  unfold normOperator
  rw [orbit_as_power_product x hx.order69]
  let S := intersectionLabels x hx K
  have aux (ss : List (Fin 69)) (hs : ∀ s ∈ ss, S s) :
      ss.foldr (fun s z => (action x hx s (factor x a)).val*z) 1 =
      ss.foldr (fun s z => (1-(x^a.val)^s.val)*z) 1 := by
    induction ss with
    | nil => rfl
    | cons s ss ih =>
      obtain ⟨hu,_⟩ := hs s List.mem_cons_self
      simp only [List.foldr_cons]
      rw [ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))]
      have hhead : (action x hx s (factor x a)).val = 1-(x^a.val)^s.val := by
        unfold action
        split
        · rw [factor_at_image, power_generator, power_commutes x s.val a.val]
        · contradiction
      rw [hhead]
  exact aux _ (fun s h => (labels_mem S s).mp h)

theorem positive_norm_product (x : R) (hx : Primitive69 x) (K : R → Prop)
    (hF : ∀ c, K (coefficient x hx c).val) :
    ∃ reps : List (Fin 69), (∀ a ∈ reps, eta a.val = 1) ∧
      signedProduct x 1 = reps.foldr (fun a z => normOperator x hx K (factor x a) * z) 1 := by
  classical
  let S := intersectionLabels x hx K
  obtain ⟨reps,hr,_,he⟩ := signed_product_over_cosets x S (intersection_one x hx K)
    (intersection_mul x hx K) (intersection_positive x hx K hF)
  refine ⟨reps,hr,?_⟩
  simpa only [factor_orbit] using he

/-- Explicit conductor-69 norm-operator factors, an inverse in the real
compositum and monic integer equations for the unit and its inverse. -/
theorem real_circular_unit (x u v : R) (hx : Primitive69 x) (hu : u^2 = -3) (hv : v^2 = -23)
    (c : Conjugation R) (hc : Compatible c u v) :
    let K := RealPart c u v
    let e := signedProduct x 1
    (∃ reps : List (Fin 69), (∀ a ∈ reps, eta a.val = 1) ∧
      e = reps.foldr (fun a z => normOperator x hx K (factor x a) * z) 1) ∧
    K e ∧ K (25-e) ∧ e*(25-e) = 1 ∧ e^2-25*e+1 = 0 ∧ (25-e)^2-25*(25-e)+1 = 0 := by
  dsimp only
  exact ⟨positive_norm_product x hx _ (compatible_real_embedding x u v hx.order69 hx.not23 hx.not3
    hu hv c hc).1, signed_real_units x u v hx.order69 hx.not23 hx.not3 hu hv c hc.first hc.second⟩

end Reimann.CircularSinnott69
