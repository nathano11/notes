import Reimann.Dyadic

/-!
# The two real samples for the field with q = 3 and d = 23

The finite sums use the common modulus 1104 and omit even residues, which
depletes the Euler factor at 2. Their denominator 24 times 1104 includes
division of the resulting Bernoulli value by two. The
arithmetic input for this module is reduction of Mizusawa's identity
L₂(s, ψ) = 2 Φ(5^s - 1) and of (P) = (Φ) to the two real samples at s = -1.
The even character ψ belongs to ℚ(√69). The second sample uses the even
quadratic character of conductor 8 with value -1 at 5.
-/

namespace Reimann.DyadicMoments

open Reimann.Dyadic

/-- The trivial and quadratic components of the half-normalized weight-one sum. -/
def realMoments : Int × Int :=
  ((weightOneNumerators 3 23).trivial / (24 * 1104),
   (weightOneNumerators 3 23).quadratic / (24 * 1104))

/-- Extract the two real specializations from the denominator-cleared computation. -/
theorem normalized_real_moments_3_23 : realMoments = (-36, -308) := by
  unfold realMoments
  rw [values_3_23]
  decide

/-- If s represents 1/5, the arguments s-1 and -s-1 reduce to 4 and 2. -/
theorem inverse_five_arguments (s : Int) (hs : (5*s) % 8 = 1) :
    (s-1) % 8 = 4 ∧ (-s-1) % 8 = 2 := by
  omega

/-- The units relating P to Φ can differ at the two arguments. -/
theorem unit_scaled_moment_residues (u v : Int) (hu : u % 2 = 1) (hv : v % 2 = 1) :
    (u*realMoments.1) % 8 = 4 ∧ (v*realMoments.2) % 8 = 4 := by
  rw [normalized_real_moments_3_23]
  change (u*(-36)) % 8 = 4 ∧ (v*(-308)) % 8 = 4
  omega

/-- Horner evaluation of an integer representative of T² + C₁ T + C₀. -/
def quadraticSample (c0 c1 t : Int) : Int := (t+c1)*t+c0

/-- The sampled polynomial uses Mizusawa's generator and the convention T = γ-1. -/
theorem sample_is_companion_determinant (c0 c1 t : Int) :
    quadraticSample c0 c1 t = det (shift (companion c0 c1) (-(1+t))) := by
  rw [determinant_specialization]
  unfold quadraticSample characteristic
  grind

/-- Polynomial evaluation commutes with reducing the argument modulo eight. -/
theorem sample_reduce_argument (c0 c1 t : Int) :
    quadraticSample c0 c1 t % 8 = quadraticSample c0 c1 (t%8) % 8 := by
  unfold quadraticSample
  rw [Int.add_emod ((t+c1)*t) c0, Int.add_emod ((t%8+c1)*(t%8)) c0,
    Int.mul_emod (t+c1) t, Int.mul_emod (t%8+c1) (t%8),
    Int.add_emod t c1, Int.add_emod (t%8) c1]
  simp

/-- The two samples force both residues, even without assuming a coefficient is even. -/
theorem coefficients_of_two_residues (c0 c1 : Int)
    (hPlus : quadraticSample c0 c1 4 % 8 = 4)
    (hMinus : quadraticSample c0 c1 2 % 8 = 4) :
    c0 % 8 = 4 ∧ c1 % 4 = 2 := by
  unfold quadraticSample at hPlus hMinus
  omega

/-- The remaining field-specific input consists of the two displayed specialization
congruences for the actual P of ℚ(√(-69)) over its cyclotomic ℤ₂-extension.
Here u and v represent the evaluated units P/Φ at the two arguments.
Bernoulli interpolation for ψ and ψχ₈ identifies Φ at those arguments with
the finite half-normalized moments. -/
theorem coefficient_residues_of_mizusawa_samples (c0 c1 s u v : Int)
    (hs : (5*s) % 8 = 1) (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hPlus : quadraticSample c0 c1 (s-1) % 8 = (u*realMoments.1) % 8)
    (hMinus : quadraticSample c0 c1 (-s-1) % 8 = (v*realMoments.2) % 8) :
    c0 % 8 = 4 ∧ c1 % 4 = 2 := by
  obtain ⟨hArgPlus, hArgMinus⟩ := inverse_five_arguments s hs
  obtain ⟨hRealPlus, hRealMinus⟩ := unit_scaled_moment_residues u v hu hv
  rw [sample_reduce_argument c0 c1 (s-1), hArgPlus, hRealPlus] at hPlus
  rw [sample_reduce_argument c0 c1 (-s-1), hArgMinus, hRealMinus] at hMinus
  exact coefficients_of_two_residues c0 c1 hPlus hMinus

end Reimann.DyadicMoments
