import Mathlib.RingTheory.Ideal.Quotient.Operations
import Reimann277.PrimeFactorization

namespace Reimann.TamePrimeCRT277

open NumberField TamePrimeFactorization277 TameFinitePlaces277 TameBiquadraticField277
open TamePadicEmbeddings277 TameArithmetic277 TameRationalField277 TameOrderFaithful277
open scoped NumberField

theorem principal_eq_intersection : principal = ⨅ s : Sign, signedIdeal s :=
  prime_factorization_277.trans product_is_intersection

noncomputable def crt_on_ideals : (O ⧸ principal) ≃+* (∀ s : Sign, O ⧸ signedIdeal s) :=
  (Ideal.quotEquivOfEq principal_eq_intersection).trans
    (Ideal.quotientInfRingEquivPiQuotient signedIdeal
      (fun _ _ h => TamePrimeFactorization277.pairwise_coprime h))

theorem crt_on_representatives (a : O) (s : Sign) :
    crt_on_ideals (Ideal.Quotient.mk _ a) s = Ideal.Quotient.mk (signedIdeal s) a := rfl

/-- Chinese remaindering on the full ring of integers, labelled by the two radical signs. -/
noncomputable def residue_product_277 : (O ⧸ principal) ≃+* (Sign → ZMod 277) :=
  crt_on_ideals.trans (RingEquiv.piCongrRight (fun s => residue_equiv (embedding s)))

theorem residue_coordinate (a : O) (s : Sign) :
    residue_product_277 (Ideal.Quotient.mk _ a) s =
      residue_equiv (embedding s) (Ideal.Quotient.mk (signedIdeal s) a) := rfl

theorem residue_coordinate_of_congruent (a : O) (s : Sign) (m : ℤ)
    (h : a - (m : O) ∈ signedIdeal s) :
    residue_product_277 (Ideal.Quotient.mk _ a) s = (m : ZMod 277) := by
  rw [residue_coordinate, (Ideal.Quotient.eq.mpr h)]
  simp only [map_intCast]

def signedInt (b : Bool) (m : ℤ) : ℤ := if b then -m else m

def radicalX : O := ⟨Biquadratic.mk gen3,integral_radicals.1⟩

def radicalY : O := ⟨Biquadratic.mk gen23,integral_radicals.2⟩

def subtractX (b : Bool) : OrderCoordinates := ((-signedInt b 44,1),(0,0))

def subtractY (b : Bool) : OrderCoordinates := ((-signedInt b 114,0),(1,0))

theorem subtractX_coe (b : Bool) :
    ((radicalX - (signedInt b 44 : O) : O) : Biquadratic) = ⟨rationalize (subtractX b)⟩ := by
  cases b <;> decide +kernel

theorem subtractY_coe (b : Bool) :
    ((radicalY - (signedInt b 114 : O) : O) : Biquadratic) = ⟨rationalize (subtractY b)⟩ := by
  cases b <;> decide +kernel

theorem shifted_radicals_on_order (s : Sign) :
    TamePrimePowers277.primePlace s.1 s.2 (subtractX s.1) ∧
    TamePrimePowers277.primePlace s.1 s.2 (subtractY s.2) := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> decide +kernel

theorem shifted_radicals_in_prime (s : Sign) :
    radicalX - (signedInt s.1 44 : O) ∈ signedIdeal s ∧
    radicalY - (signedInt s.2 114 : O) ∈ signedIdeal s := by
  constructor
  · apply (mem_embeddingIdeal_iff (embedding s) _).mpr
    rw [subtractX_coe, norm_lt_one_iff_prime]
    exact (shifted_radicals_on_order s).1
  · apply (mem_embeddingIdeal_iff (embedding s) _).mpr
    rw [subtractY_coe, norm_lt_one_iff_prime]
    exact (shifted_radicals_on_order s).2

theorem residue_radical_pair (s : Sign) :
    residue_product_277 (Ideal.Quotient.mk _ radicalX) s = (signedInt s.1 44 : ZMod 277) ∧
    residue_product_277 (Ideal.Quotient.mk _ radicalY) s = (signedInt s.2 114 : ZMod 277) :=
  ⟨residue_coordinate_of_congruent _ _ _ (shifted_radicals_in_prime s).1,
   residue_coordinate_of_congruent _ _ _ (shifted_radicals_in_prime s).2⟩

end Reimann.TamePrimeCRT277
