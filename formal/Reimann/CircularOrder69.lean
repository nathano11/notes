import Reimann.CircularPrimitive69

/-! Exact order of a root of the conductor polynomial in characteristic zero.
At a cube root, a three-term Horner step computes the remainder modulo X³−1. -/
namespace Reimann.CircularOrder69

open Lean.Grind CircularPolynomial69 CircularPrimitive69
attribute [local instance] Ring.intCast

theorem phi_geometric_zero {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) :
    1 + x^23 + x^46 = 0 := by
  rw [← phi_factorization x,hx,Semiring.zero_mul]

theorem phi_power69 {R : Type} [CommRing R] (x : R) (hx : eval x phi = 0) : x^69 = 1 := by
  have h := conductor_factor_identity x
  rw [phi_geometric_zero x hx,Semiring.mul_zero] at h
  grind only

theorem char_zero_numeral {R : Type} [Field R] [IsCharP R 0] (n : Nat) (hn : n ≠ 0) :
    (OfNat.ofNat n : R) ≠ 0 := by
  intro h
  have e := (IsCharP.ofNat_eq_zero_iff 0 n).mp h
  exact hn (by simpa using e)

theorem phi_power23_ne {R : Type} [Field R] [IsCharP R 0] (x : R) (hx : eval x phi = 0) :
    x^23 ≠ 1 := by
  intro e
  have h := phi_geometric_zero x hx
  rw [show 46 = 23+23 by decide,Semiring.pow_add,e,Semiring.one_mul] at h
  exact char_zero_numeral 3 (by decide) (by grind only : (3 : R) = 0)

theorem cube_horner_block {R : Type} [CommRing R] (x : R) (hx : x^3 = 1)
    (a b c : Int) (p : List Int) :
    eval x (a :: b :: c :: p) = Int.cast a + x * Int.cast b + x^2 * Int.cast c + eval x p := by
  simp only [eval]
  have he : x*(x*(x*eval x p)) = eval x p := by
    calc
      _ = x^3 * eval x p := by grind only
      _ = _ := by rw [hx,Semiring.one_mul]
  grind only

theorem phi_at_cube {R : Type} [CommRing R] (x : R) (hx : x^3 = 1) :
    eval x phi = 8*(1+x+x^2) - 23*x := by
  simp only [phi,phiTail,cube_horner_block x hx,eval,Ring.intCast_one,Ring.intCast_neg,Ring.intCast_zero]
  grind only

theorem phi_power3_ne {R : Type} [Field R] [IsCharP R 0] (x : R) (hx : eval x phi = 0) :
    x^3 ≠ 1 := by
  intro e
  have hp := (phi_at_cube x e).symm.trans hx
  have hc := cubic_factor_identity x
  rw [e] at hc
  have prod : (x-1)*(1+x+x^2) = 0 := by grind only
  rcases Field.of_mul_eq_zero prod with z | z
  · have xone : x = 1 := by grind only
    rw [xone] at hp
    exact char_zero_numeral 1 (by decide) (by grind only : (1 : R) = 0)
  · rw [z,Semiring.mul_zero] at hp
    have mult : (23 : R)*x = 0 := by grind only
    rcases Field.of_mul_eq_zero mult with bad | zero
    · exact char_zero_numeral 23 (by decide) bad
    · rw [zero] at e
      exact Field.zero_ne_one (by grind only : (0 : R) = 1)

theorem primitive_of_phi {R : Type} [Field R] [IsCharP R 0] (x : R) (hx : eval x phi = 0) :
    x^69 = 1 ∧ x^23 ≠ 1 ∧ x^3 ≠ 1 :=
  ⟨phi_power69 x hx,phi_power23_ne x hx,phi_power3_ne x hx⟩

end Reimann.CircularOrder69
