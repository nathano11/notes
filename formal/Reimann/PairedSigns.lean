import Reimann.WeightClasses
import Reimann.Character2893

/-!
Joint low bits of the two signs. Section 8 of Dyadic_Window_Orders.md
gives weight-three valuations 5 and 7 for q=11, d=263. At precision 64
these are the residues 32 and 0. The polynomial coefficients below may
be any integral representatives at this precision. The comparison to the
arithmetic special values is a separate obligation in PROOF_STATUS.md.
-/
namespace Reimann.PairedSigns

open Reimann.SampleSpacing

/-- The two signs at a common weight have the same odd denominator a². -/
theorem sign_difference (c0 c1 a : Int) :
    numerator c0 c1 1 a - numerator c0 c1 (-1) a = 2 * a * (c1-2) := by
  unfold numerator
  grind

/-- Weight three has a=125. Only six bits of its two samples are required. -/
def WeightThree (c0 c1 : Int) : Prop :=
  numerator c0 c1 1 125 % 64 = 32 ∧ numerator c0 c1 (-1) 125 % 64 = 0

theorem linear_at_three (c0 c1 : Int) :
    numerator c0 c1 1 125 = 15376 - 15500*c1 + 15625*c0 ∧
    numerator c0 c1 (-1) 125 = 15876 - 15750*c1 + 15625*c0 := by
  unfold numerator
  constructor <;> grind

/-- Reducing the two weight-three equations removes the large coefficients. -/
theorem weight_three_linear_residues (c0 c1 : Int) (h : WeightThree c0 c1) :
    (16 - 12*c1 + 9*c0) % 64 = 32 ∧ (4 - 6*c1 + 9*c0) % 64 = 0 := by
  obtain ⟨hp, hm⟩ := h
  obtain ⟨ep, em⟩ := linear_at_three c0 c1
  rw [ep] at hp
  rw [em] at hm
  have a : 15376 - 15500*c1 + 15625*c0 =
      (16 - 12*c1 + 9*c0) + 64*(240 - 242*c1 + 244*c0) := by omega
  have b : 15876 - 15750*c1 + 15625*c0 =
      (4 - 6*c1 + 9*c0) + 64*(248 - 246*c1 + 244*c0) := by omega
  rw [a, Int.add_mul_emod_self_left] at hp
  rw [b, Int.add_mul_emod_self_left] at hm
  exact ⟨hp, hm⟩

theorem weight_three_linear_coefficient (c0 c1 : Int) (h : WeightThree c0 c1) :
    c1 % 32 = 18 := by
  obtain ⟨hp, hm⟩ := weight_three_linear_residues c0 c1 h
  have a := Int.emod_add_mul_ediv (16 - 12*c1 + 9*c0) 64
  have b := Int.emod_add_mul_ediv (4 - 6*c1 + 9*c0) 64
  rw [hp] at a
  rw [hm] at b
  let u := (4 - 6*c1 + 9*c0)/64 - (16 - 12*c1 + 9*c0)/64
  have hu : 3*c1+10 = 32*u := by dsimp [u]; omega
  have he : c1 = 18 + 32*(11*u-c1-4) := by omega
  exact (congrArg (fun z : Int => z%32) he).trans (by simp)

theorem weight_three_constant_coefficient (c0 c1 : Int) (h : WeightThree c0 c1) :
    c0 % 64 = 40 := by
  have hl := weight_three_linear_coefficient c0 c1 h
  have hc := Int.emod_add_mul_ediv c1 32
  rw [hl] at hc
  have hm := (weight_three_linear_residues c0 c1 h).2
  have eqn := Int.emod_add_mul_ediv (4-6*c1+9*c0) 64
  rw [hm] at eqn
  let u := (4-6*c1+9*c0)/64 + 3*(c1/32) + 1
  have hu : 9*c0 = 40 + 64*u := by dsimp [u]; omega
  have he : c0 = 40 + 64*(35 + 57*u-8*c0) := by omega
  exact (congrArg (fun z : Int => z%64) he).trans (by simp)

/-- Substituting coefficient representatives only uses c1 modulo 32,
because the signed numerator contains the even factor s−a. -/
theorem coefficient_reduction (c0 c1 s a : Int) (h : WeightThree c0 c1)
    (evenDiff : ∃ d : Int, s-a = 2*d) :
    numerator c0 c1 s a % 64 = numerator 40 18 s a % 64 := by
  obtain ⟨d, hd⟩ := evenDiff
  have h0 := Int.emod_add_mul_ediv c0 64
  have h1 := Int.emod_add_mul_ediv c1 32
  rw [weight_three_constant_coefficient c0 c1 h] at h0
  rw [weight_three_linear_coefficient c0 c1 h] at h1
  let x := c0/64
  let y := c1/32
  have hx : c0 = 40+64*x := h0.symm
  have hy : c1 = 18+32*y := h1.symm
  have he : numerator c0 c1 s a =
      numerator 40 18 s a + 64*(x*a^2+y*a*d) := by
    unfold numerator
    rw [hx, hy, hd]
    grind
  rw [he, Int.add_mul_emod_self_left]

/-- After coefficient reduction, the numerator modulo 64 depends on a modulo 32. -/
theorem argument_reduction (s a : Int) :
    numerator 40 18 s a % 64 = numerator 40 18 s (a%32) % 64 := by
  let b := a%32
  let k := a/32
  have ha : a = b+32*k := (Int.emod_add_mul_ediv a 32).symm
  have he : numerator 40 18 s a =
      numerator 40 18 s b + 64*k*(8*s + 23*b + 368*k) := by
    unfold numerator
    rw [ha]
    grind
  rw [he, Int.mul_assoc, Int.add_mul_emod_self_left]

theorem five_power_period_eight (r : Nat) :
    (5 : Int)^(r+8) % 32 = 5^r % 32 := by
  have h : (5:Int)^8 = 1+32*12207 := by decide
  rw [Int.pow_add, h]
  have he : (5:Int)^r * (1+32*12207) = 5^r + 32*(12207*5^r) := by grind
  rw [he, Int.add_mul_emod_self_left]

theorem five_power_mod_weight (r : Nat) : (5:Int)^r % 32 = 5^(r%8) % 32 := by
  have step (j n : Nat) : (5:Int)^(j+8*n) % 32 = 5^j % 32 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, ← Nat.add_assoc, five_power_period_eight, ih]
  have h := step (r%8) (r/8)
  rwa [Nat.mod_add_div] at h

theorem signed_sample_mod_weight (c0 c1 s : Int) (h : WeightThree c0 c1)
    (hs : s = 1 ∨ s = -1) (r : Nat) :
    numerator c0 c1 s (5^r) % 64 = numerator 40 18 s ((5:Int)^(r%8)%32) % 64 := by
  obtain ⟨z, hz⟩ := five_power_mod_four r
  have hd : ∃ d : Int, s-5^r = 2*d := by
    rcases hs with h | h
    · exact ⟨-2*z, by omega⟩
    · exact ⟨-1-2*z, by omega⟩
  rw [coefficient_reduction c0 c1 s _ h hd, argument_reduction, five_power_mod_weight]

/-- The four entries give residues of (plus numerator, minus numerator) modulo 64. -/
theorem representative_table :
    let residues := fun j : Nat =>
      (numerator 40 18 1 ((5:Int)^j%32) %64, numerator 40 18 (-1) ((5:Int)^j%32) %64)
    (residues 1 = (16,48)) ∧ (residues 3 = (32,0)) ∧
      (residues 5 = (48,16)) ∧ (residues 7 = (0,32)) := by decide

/-- At every odd weight, determine exactly which branch, if any, reaches depth six. -/
theorem all_odd_weights (c0 c1 : Int) (h : WeightThree c0 c1) (r : Nat) (hr : r%2=1) :
    let pair := (numerator c0 c1 1 (5^r) % 64, numerator c0 c1 (-1) (5^r) % 64)
    (r%8 = 1 ∧ pair = (16,48)) ∨ (r%8 = 3 ∧ pair = (32,0)) ∨
    (r%8 = 5 ∧ pair = (48,16)) ∨ (r%8 = 7 ∧ pair = (0,32)) := by
  dsimp only
  rw [signed_sample_mod_weight c0 c1 1 h (Or.inl rfl),
      signed_sample_mod_weight c0 c1 (-1) h (Or.inr rfl)]
  obtain ⟨h1,h3,h5,h7⟩ := representative_table
  have hs : r%8=1 ∨ r%8=3 ∨ r%8=5 ∨ r%8=7 := by omega
  rcases hs with hr | hr | hr | hr
  · exact Or.inl ⟨hr, hr ▸ h1⟩
  · exact Or.inr (Or.inl ⟨hr, hr ▸ h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, hr ▸ h5⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hr, hr ▸ h7⟩))

/-- Divide the checked weight-three Bernoulli numerators by their common scaling. -/
theorem normalized_third_residues :
    (Character2893.sums.weightThree / (240 * (Character2893.modulus : Int))) % 64 = 32 ∧
    (Character2893.sums.twistedThree / (240 * (Character2893.modulus : Int))) % 64 = 0 := by
  rw [Character2893.normalized_table, Character2893.modulus_value]
  decide

/-- The field-specific interpolation input needed at precision 64: each
normalized finite sum and its polynomial numerator differ by a unit modulo 64. -/
theorem weight_three_of_interpolation_mod64 (c0 c1 u v : Int) (oddPlus : u%2=1)
    (plus : numerator c0 c1 1 125 % 64 =
      (u*(Character2893.sums.weightThree/(240*(Character2893.modulus:Int))))%64)
    (minus : numerator c0 c1 (-1) 125 % 64 =
      (v*(Character2893.sums.twistedThree/(240*(Character2893.modulus:Int))))%64) :
    WeightThree c0 c1 := by
  obtain ⟨hp,hm⟩ := normalized_third_residues
  rw [Int.mul_emod, hp] at plus
  rw [Int.mul_emod, hm] at minus
  have lift := Int.emod_add_mul_ediv u 64
  have parity : u%64 = 1+2*((u%64)/2) := by omega
  rw [parity] at plus
  constructor <;> omega

theorem both_seeds (c0 c1 : Int) (h : WeightThree c0 c1) :
    WeightClasses.hit (WeightClasses.sample c0 c1 1) 0 0 ∧
    WeightClasses.hit (WeightClasses.sample c0 c1 (-1)) 0 0 := by
  apply (WeightClasses.two_seeds_iff c0 c1).mpr
  have h0 := weight_three_constant_coefficient c0 c1 h
  have h1 := weight_three_linear_coefficient c0 c1 h
  omega

/-- At depth k+4 the two root classes coincide exactly when the signed
difference is divisible to that depth. The power of five cancels. -/
theorem common_class_iff {c0 c1 : Int} {k i j : Nat}
    (hp : WeightClasses.RootAt (WeightClasses.sample c0 c1 1) k i)
    (hm : WeightClasses.RootAt (WeightClasses.sample c0 c1 (-1)) k j) :
    i=j ↔ (2:Int)^(k+4) ∣ 2*(c1-2) := by
  rw [WeightClasses.roots_equal_iff hp hm]
  unfold WeightClasses.sample
  rw [sign_difference, show 2 * (5:Int)^(1+2*i)*(c1-2) =
        5^(1+2*i)*(2*(c1-2)) by grind, WeightClasses.cancel_five_power]

theorem depth_cutoff (c0 c1 : Int) (h : WeightThree c0 c1) (k : Nat) :
    (2:Int)^(k+4) ∣ 2*(c1-2) ↔ k ≤ 1 := by
  have hc := weight_three_linear_coefficient c0 c1 h
  constructor
  · intro hd
    apply Classical.byContradiction
    intro hgt
    have he : k+4 = 6+(k-2) := by omega
    rw [he, Int.pow_add] at hd
    have h64 : (64:Int) ∣ 2*(c1-2) :=
      Int.dvd_trans (Int.dvd_mul_right (2^6) (2^(k-2))) hd
    omega
  · intro hk
    have cases' : k=0 ∨ k=1 := by omega
    rcases cases' with h | h <;> subst k
    · change (16:Int) ∣ 2*(c1-2)
      omega
    · change (32:Int) ∣ 2*(c1-2)
      omega

/-- Each sign has a unique root class at each depth. The classes are equal
through divisibility by 32 and distinct from divisibility by 64 onward. -/
theorem paired_root_classes (c0 c1 : Int) (h : WeightThree c0 c1) (k : Nat) :
    ∃ i j, WeightClasses.RootAt (WeightClasses.sample c0 c1 1) k i ∧
      WeightClasses.RootAt (WeightClasses.sample c0 c1 (-1)) k j ∧ (i=j ↔ k≤1) := by
  obtain ⟨p,m⟩ := both_seeds c0 c1 h
  obtain ⟨i,hi,_⟩ := WeightClasses.classes_from_two_seeds c0 c1 1 p m (Or.inl rfl) k
  obtain ⟨j,hj,_⟩ := WeightClasses.classes_from_two_seeds c0 c1 (-1) p m (Or.inr rfl) k
  exact ⟨i,j,hi,hj,(common_class_iff hi hj).trans (depth_cutoff c0 c1 h k)⟩

/-- Cleared numerator of P(+5^(-r)−1), the untwisted ψ branch. -/
def positiveBranch (c0 c1 : Int) (r : Nat) : Int := numerator c0 c1 1 (5^r)

/-- Cleared numerator of P(−5^(-r)−1), the ψχ₈ branch. -/
def negativeBranch (c0 c1 : Int) (r : Nat) : Int := numerator c0 c1 (-1) (5^r)

/-- The unscaled polynomial identity in its reciprocal argument u. -/
theorem reciprocal_sign_identity (c0 c1 u : Rat) :
    ((u-1)^2 + c1*(u-1) + c0) - ((-u-1)^2 + c1*(-u-1) + c0) =
      2*u*(c1-2) := by grind

theorem coefficient_minus_two_valuation (c0 c1 : Int) (h : WeightThree c0 c1) :
    Reimann.Dyadic.exactV (c1-2) 4 := by
  have hc := weight_three_linear_coefficient c0 c1 h
  have eqn := Int.emod_add_mul_ediv c1 32
  rw [hc] at eqn
  exact ⟨c1/32, by change c1-2=16*(2*(c1/32)+1); omega⟩

/-- The two branch numerators differ by exactly 2⁵ times an odd integer
at every weight. The denominator 5^(2r) is odd. -/
theorem signed_difference_valuation (c0 c1 : Int) (h : WeightThree c0 c1) (r : Nat) :
    Reimann.Dyadic.exactV (positiveBranch c0 c1 r - negativeBranch c0 c1 r) 5 := by
  unfold positiveBranch negativeBranch
  rw [sign_difference]
  obtain ⟨v,hv⟩ := five_power_mod_four r
  obtain ⟨z,hz⟩ := coefficient_minus_two_valuation c0 c1 h
  change c1-2=16*(2*z+1) at hz
  refine ⟨z+2*v*(2*z+1), ?_⟩
  change 2*(5:Int)^r*(c1-2)=32*(2*(z+2*v*(2*z+1))+1)
  rw [hv,hz]
  grind

end Reimann.PairedSigns
