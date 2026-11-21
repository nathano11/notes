import Reimann.CircularIntersection69
import Reimann.CircularFactor69

/-! The conductor-3 and conductor-23 quadratic Gauss sums in powers of a
primitive 69th root. Their product determines the sign of the quadratic
period used by the signed circular unit. -/
namespace Reimann.CircularRadicals69

open Lean.Grind CircularPolynomial69 CircularKernel69 CircularIntersection69 CircularFactor69
attribute [local instance] Ring.intCast
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def labels23 (s : Nat) : List Nat :=
  ((List.range 23).filter (fun u => chi23 u == s)).map (fun u => 3*u)

theorem label_counts : (labels23 1).length = 11 ∧ (labels23 276).length = 11 := by decide +kernel

def signedPeriod {R : Type} [CommRing R] (x : R) (p n : List Nat) : R :=
  periodSum x p - periodSum x n

def radical3 {R : Type} [CommRing R] (x : R) : R := signedPeriod x [23] [46]

def radical23 {R : Type} [CommRing R] (x : R) : R := signedPeriod x (labels23 1) (labels23 276)

theorem radical3_formula {R : Type} [CommRing R] (x : R) : radical3 x = x^23 - x^46 := by
  simp [radical3,signedPeriod,periodSum,Semiring.add_zero]

def signedPoly (p n : List Nat) : List Int :=
  add (powerSum p) ((powerSum n).map (fun c => (-1 : Int)*c))

theorem eval_signedPoly {R : Type} [CommRing R] (x : R) (p n : List Nat) :
    eval x (signedPoly p n) = signedPeriod x p n := by
  rw [signedPoly,eval_add,eval_scale,eval_powerSum,eval_powerSum]
  simp only [signedPeriod,periodSum,Ring.intCast_neg,Ring.intCast_one]
  grind only

def squareRelation (p : List Int) (d : Int) : List Int := add (mulInt p p) [d]

theorem squareRelation_sound {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0)
    (p : List Int) (d : Int) (h : strip ((squareRelation p d).length - 44) (squareRelation p d) =
      List.replicate 44 0) : (eval x p)^2 = -Int.cast d := by
  have hz := eval_of_zero_remainder x hx _ h
  simp only [squareRelation,eval_add,eval_mulInt,eval,Semiring.mul_zero,Semiring.add_zero] at hz
  grind only

theorem radical3_remainder :
    let p := squareRelation (signedPoly [23] [46]) 3
    strip (p.length - 44) p = List.replicate 44 0 := by decide +kernel

theorem radical23_remainder :
    let p := squareRelation (signedPoly (labels23 1) (labels23 276)) 23
    strip (p.length - 44) p = List.replicate 44 0 := by decide +kernel

theorem radical3_square {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    (radical3 x)^2 = -3 := by
  have h := squareRelation_sound x hx _ 3 radical3_remainder
  rw [eval_signedPoly,Ring.intCast_ofNat] at h
  exact h

theorem radical23_square {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    (radical23 x)^2 = -23 := by
  have h := squareRelation_sound x hx _ 23 radical23_remainder
  rw [eval_signedPoly,Ring.intCast_ofNat] at h
  exact h

def productRelation : List Int :=
  add (mulInt (signedPoly [23] [46]) (signedPoly (labels23 1) (labels23 276)))
    (add (periodPoly.map (fun c => (-2 : Int)*c)) [1])

theorem product_remainder : strip (productRelation.length - 44) productRelation = List.replicate 44 0 := by
  decide +kernel

theorem radical_product {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    radical3 x * radical23 x = 2 * periodTheta x - 1 := by
  have h := eval_of_zero_remainder x hx _ product_remainder
  simp only [productRelation,eval_add,eval_mulInt,eval_signedPoly,eval_scale,eval,
    Ring.intCast_one,Ring.intCast_neg,Semiring.mul_zero,Semiring.add_zero] at h
  change signedPeriod x [23] [46] * signedPeriod x (labels23 1) (labels23 276) = 2 * eval x periodPoly - 1
  grind only

def SignedPermutation (a s : Nat) (p n : List Nat) : Prop :=
  if s = 1 then (translate a p).Perm p ∧ (translate a n).Perm n
  else (translate a p).Perm n ∧ (translate a n).Perm p

theorem chi3_permutations : ∀ a : Fin 69, Nat.Coprime a.val 69 →
    SignedPermutation a.val (chi3 a.val) [23] [46] := by
  unfold SignedPermutation
  decide +kernel

theorem chi23_permutations : ∀ a : Fin 69, Nat.Coprime a.val 69 →
    SignedPermutation a.val (chi23 a.val) (labels23 1) (labels23 276) := by
  unfold SignedPermutation
  decide +kernel

theorem signedPeriod_action {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (a s : Nat) (p n : List Nat) (h : SignedPermutation a s p n) :
    signedPeriod (x^a) p n = if s = 1 then signedPeriod x p n else -signedPeriod x p n := by
  simp only [signedPeriod,period_at_power x h69]
  by_cases e : s = 1
  · simp only [SignedPermutation,e,ite_true] at h
    simp only [e,ite_true,period_permutation x h.1,period_permutation x h.2]
  · simp only [SignedPermutation,e,ite_false] at h
    simp only [e,ite_false,period_permutation x h.1,period_permutation x h.2]
    grind only

theorem radical3_action {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (a : Fin 69) (hu : Nat.Coprime a.val 69) :
    radical3 (x^a.val) = if chi3 a.val = 1 then radical3 x else -radical3 x :=
  signedPeriod_action x h69 _ _ _ _ (chi3_permutations a hu)

theorem radical23_action {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1)
    (a : Fin 69) (hu : Nat.Coprime a.val 69) :
    radical23 (x^a.val) = if chi23 a.val = 1 then radical23 x else -radical23 x :=
  signedPeriod_action x h69 _ _ _ _ (chi23_permutations a hu)

theorem simultaneous_conjugation {R : Type} [CommRing R] (x : R) (h69 : x^69 = 1) :
    radical3 (x^68) = -radical3 x ∧ radical23 (x^68) = -radical23 x := by
  have h3 := radical3_action x h69 (68 : Fin 69) (by decide)
  have h23 := radical23_action x h69 (68 : Fin 69) (by decide)
  exact ⟨h3,h23⟩

theorem primitive_radicals {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    (radical3 x)^2 = -3 ∧ (radical23 x)^2 = -23 ∧ radical3 x * radical23 x = 2 * periodTheta x - 1 := by
  have hx := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  exact ⟨radical3_square x hx,radical23_square x hx,radical_product x hx⟩

theorem radical_product_square {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    (radical3 x * radical23 x)^2 = 69 := by
  have h3 := radical3_square x hx
  have h23 := radical23_square x hx
  have eqn : (radical3 x * radical23 x)^2 = (radical3 x)^2 * (radical23 x)^2 := by grind only
  rw [eqn,h3,h23]
  grind only

theorem period_from_radicals {R : Type} [Field R] (x : R) (hx : eval x phi = 0)
    (two : (2 : R) ≠ 0) :
    periodTheta x = (radical3 x * radical23 x + 1) / 2 := by
  rw [radical_product x hx]
  have eqn : 2 * periodTheta x - 1 + 1 = periodTheta x * 2 := by grind only
  rw [eqn,Field.div_eq_mul_inv,Semiring.mul_assoc,Field.mul_inv_cancel two,Semiring.mul_one]

theorem positive_unit_radicals {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    2 * signedProduct x 1 = 25 + 3 * (radical3 x * radical23 x) := by
  rw [positive_signed_value x hx,radical_product x hx]
  grind only

theorem conjugate_unit_radicals {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    2 * signedProduct x 276 = 25 - 3 * (radical3 x * radical23 x) := by
  rw [negative_signed_value x hx,radical_product x hx]
  grind only

end Reimann.CircularRadicals69
