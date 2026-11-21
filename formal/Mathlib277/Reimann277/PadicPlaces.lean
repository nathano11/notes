import Reimann277.PadicEmbeddings
import Reimann277.Completion
import Reimann.TamePlaceRestriction277

namespace Reimann.TamePadicPlaces277

open TameRationalField277 TameBiquadraticField277 TamePadicEmbeddings277
open TamePlaceRestriction277 TameOrderFaithful277

local instance fact277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

noncomputable def value (s : Bool × Bool) (x : Biquad) : ℚ_[277] := embedding s ⟨x⟩

theorem value_int (s : Bool × Bool) (a : ℤ) : value s (scalar (a : ℚ)) = (a : ℚ_[277]) := by
  change embedding s ⟨scalar (a : ℚ)⟩ = _
  rw [← coefficientHom_apply, (embedding s).commutes, map_intCast]

theorem value_mul (s : Bool × Bool) (x y : Biquad) :
    value s (bm x y) = value s x * value s y :=
  (embedding s).map_mul (Biquadratic.mk x) (Biquadratic.mk y)

theorem value_add (s : Bool × Bool) (x y : Biquad) :
    value s (ba x y) = value s x + value s y :=
  (embedding s).map_add (Biquadratic.mk x) (Biquadratic.mk y)

theorem value_nonzero (s : Bool × Bool) {x : Biquad} (hx : x ≠ scalar 0) : value s x ≠ 0 := by
  intro h
  exact hx (congrArg Biquadratic.coord ((embedding s).injective (h.trans (map_zero _).symm)))

theorem integer_radii (s : Bool × Bool) (n : ℕ) (a : ℤ) :
    ‖value s (scalar (a : ℚ))‖ ≤ ‖value s (scalar (((277 : ℤ)^n : ℤ) : ℚ))‖ ↔
      (277 : ℤ)^n ∣ a := by
  rw [value_int,value_int,Int.cast_pow]
  change ‖(a : ℚ_[277])‖ ≤ ‖((277 : ℕ) : ℚ_[277])^n‖ ↔ _
  rw [Padic.norm_p_pow (p := 277) n]
  exact Padic.norm_int_le_pow_iff_dvd (p := 277) a n

/-- Pull back the ordinary norm of the standard p-adic field. -/
noncomputable def order (s : Bool × Bool) : PlaceOrder where
  le x y := ‖value s x‖ ≤ ‖value s y‖
  refl _ := le_rfl
  trans := le_trans
  total _ _ := le_total _ _
  mul z h := by
    rw [value_mul,value_mul,norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  cancel hz h := by
    rw [value_mul,value_mul,norm_mul,norm_mul] at h
    exact le_of_mul_le_mul_right h (norm_pos_iff.mpr (value_nonzero s hz))
  add h k := by
    rw [value_add]
    exact (Padic.nonarchimedean _ _).trans (max_le h k)
  integers := integer_radii s

theorem center_eq (s : Bool × Bool) :
    center (order s) = TamePrimePowers277.primePlace s.1 s.2 := by
  funext x
  apply propext
  change (¬ ‖value s (scalar 1)‖ ≤ ‖value s (rationalize x)‖) ↔ _
  have h1 : value s (scalar 1) = 1 := (embedding s).map_one
  rw [h1,norm_one,not_le]
  exact norm_lt_one_iff_prime s x

theorem signs_order (s : Bool × Bool) : signs (order s) = s :=
  signs_of_center _ _ _ (center_eq s)

noncomputable def equiv : (Bool × Bool) ≃ PlaceOrder where
  toFun := order
  invFun := signs
  left_inv := signs_order
  right_inv := (field_orders_of_signed_places order signs_order).1

/-- The representative norm for this class of valuations extends the usual p-adic
norm of the rationals via its unique signed field embedding. -/
noncomputable abbrev normedAt (w : PlaceOrder) : NormedField Biquadratic :=
  NormedField.induced Biquadratic ℚ_[277] (embedding (signs w)) (embedding (signs w)).injective

theorem norm_comparison (w : PlaceOrder) (x y : Biquad) :
    w.le x y ↔ ‖value (signs w) x‖ ≤ ‖value (signs w) y‖ := by
  conv_lhs => rw [← equiv.apply_symm_apply w]
  rfl

theorem embedding_isometry (w : PlaceOrder) :
    letI := normedAt w
    Isometry (embedding (signs w)) := by
  letI := normedAt w
  intro x y
  rfl

/-- The metric completion for every extending valuation class. The equivalence
extends the unique signed field embedding and preserves distances in both directions. -/
theorem completion_at (w : PlaceOrder) :
    letI := normedAt w
    ∃ e : UniformSpace.Completion Biquadratic ≃+* ℚ_[277],
      (∀ x : Biquadratic, e (x : UniformSpace.Completion Biquadratic) = embedding (signs w) x) ∧
      (∀ x y, dist (e x) (e y) = dist x y) ∧
      (∀ x y, dist (e.symm x) (e.symm y) = dist x y) := by
  letI := normedAt w
  exact TameMetricCompletion277.completion_of_padic_embedding (embedding (signs w)).toRingHom
    (embedding_isometry w)

end Reimann.TamePadicPlaces277
