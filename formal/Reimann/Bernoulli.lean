import Std

namespace Reimann.Bernoulli

/-- The reflected weight of the depth-one test. -/
def reflectedIndex (p r : Nat) : Nat := p - 1 - r

/-- Recover the original sum, check the range, and check the parity of the
    reflected Bernoulli index. The bounds agree with the arithmetic hypotheses. -/
theorem reflectedIndex_spec (p r t : Nat) (hr : 0 < r) (hrt : r < t)
    (hp : 2 * t + 1 < p) (hodd : p % 2 = 1) :
    reflectedIndex p r + r + 1 = p ∧
    2 ≤ reflectedIndex p r ∧ reflectedIndex p r < p ∧
    reflectedIndex p r % 2 = r % 2 := by
  unfold reflectedIndex
  omega

/-- Reduce the base before taking the power in the finite residue calculation. -/
def modularPower (a e p : Nat) : Nat := (a % p) ^ e % p

/-- The quadratic character modulo an odd prime f, represented in residues
    modulo p by 0, 1 and p-1 using Euler's criterion. -/
def quadraticValue (a f p : Nat) : Nat :=
  let v := modularPower a ((f - 1) / 2) f
  if v = 0 then 0 else if v = 1 then 1 else p - 1

/-- Coefficients of (b - σ_b)Θ in the basis σ_a⁻¹ are floor(b*a/(f*p)).
    At units the exponent p-2-r represents -(r+1) modulo p-1.
    Entries at p are skipped; the character value vanishes at multiples of f. -/
def smoothedResidue (f p r b : Nat) : Nat :=
  let m := f * p
  (List.range m).foldl (fun total a =>
    if a % p = 0 then total else
      (total + (b * a / m) * quadraticValue a f p *
        modularPower a (p - 2 - r) p) % p) 0

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
theorem conductor_three_residue : smoothedResidue 3 277 1 31 = 250 := by decide

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
theorem conductor_twenty_three_residue : smoothedResidue 23 277 1 24 = 184 := by decide

/-- Pure arithmetic consequence of the two residues for q=3,d=23, a=0. -/
theorem neither_residue_vanishes :
    smoothedResidue 3 277 1 31 ≠ 0 ∧ smoothedResidue 23 277 1 24 ≠ 0 := by
  rw [conductor_three_residue, conductor_twenty_three_residue]
  decide

/-- Integer polynomial equal to 6*f^5 times the fifth Bernoulli polynomial
    at a/f when f is nonzero. Its coefficients are explicit in this definition. -/
def scaledBernoulliFive (f a : Int) : Int :=
  6*a^5 - 15*f*a^4 + 10*f^2*a^3 - f^4*a

/-- The conductor-three signed sum is 6*3*(-10/3), with denominators cleared. -/
theorem fifth_signed_moment :
    scaledBernoulliFive 3 1 - scaledBernoulliFive 3 2 = -60 := by decide

/-- The p=7, r=1 residue and the reduction of -10/3 are separate numerical checks. -/
theorem small_check :
    smoothedResidue 3 7 1 31 = 4 ∧ (6 * (3 : Int) + 10) % 7 = 0 := by decide

end Reimann.Bernoulli
