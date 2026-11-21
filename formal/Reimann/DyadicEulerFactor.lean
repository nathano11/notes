import Reimann.Character2893

/-! The primitive quadratic character at conductor 2893 and the Euler factor at 2.
The sums below use the Bernoulli polynomial normalization of Character2893. -/

namespace Reimann.DyadicEulerFactor

open Reimann.Character2893 Reimann.Dyadic

/-- The primitive conductor is the product of the two odd prime conductors. -/
def conductor : Nat := 11 * 263

/-- Euler-criterion definition, including zero at nonunits of the conductor. -/
def quadraticCharacter (a : Nat) : Int := quadSymbol 11 a * quadSymbol 263 a

/-- The two local quadratic symbols give the sign at the removed prime. -/
theorem character_at_two : quadSymbol 11 2 = -1 ∧ quadSymbol 263 2 = 1 ∧
    quadraticCharacter 2 = -1 := by decide

/-- Summing the two lifts of a residue divides the period by two. The scaled
Bernoulli polynomials acquire the same factor 2 in degrees two and four. -/
theorem bernoulli_distribution_two (m b : Int) :
    scaledB2 (2*m) b + scaledB2 (2*m) (b+m) = 2 * scaledB2 m b ∧
    scaledB4 (2*m) b + scaledB4 (2*m) (b+m) = 2 * scaledB4 m b := by
  unfold scaledB2 scaledB4
  constructor <;> grind

/-- The even terms removed at period 2m have respective homogeneities 4 and 16. -/
theorem bernoulli_at_double (m b : Int) :
    scaledB2 (2*m) (2*b) = 4 * scaledB2 m b ∧
    scaledB4 (2*m) (2*b) = 16 * scaledB4 m b := by
  unfold scaledB2 scaledB4
  constructor <;> grind

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
/-- Exhaustive residue tests for doubling at 11 and 263. -/
theorem doubling_at_both_primes :
    (∀ a : Fin 11, quadSymbol 11 (2*a.val) = -quadSymbol 11 a.val) ∧
    (∀ a : Fin 263, quadSymbol 263 (2*a.val) = quadSymbol 263 a.val) := by
  decide

/-- Euler's criterion only uses the specified residue class. -/
theorem quadSymbol_of_congruent {p a b : Nat} (h : a%p = b%p) :
    quadSymbol p a = quadSymbol p b := by
  unfold quadSymbol
  rw [h]

theorem double_residue (a p : Nat) : (2*a)%p = (2*(a%p))%p := by
  rw [Nat.mul_mod 2 a p, Nat.mul_mod 2 (a%p) p, Nat.mod_mod]

/-- Doubling the argument reverses the primitive character for every residue. -/
theorem character_double (a : Nat) : quadraticCharacter (2*a) = -quadraticCharacter a := by
  have h11 := doubling_at_both_primes.1 ⟨a%11, Nat.mod_lt _ (by decide)⟩
  have h263 := doubling_at_both_primes.2 ⟨a%263, Nat.mod_lt _ (by decide)⟩
  unfold quadraticCharacter
  rw [quadSymbol_of_congruent (double_residue a 11),
      quadSymbol_of_congruent (double_residue a 263), h11, h263]
  unfold quadSymbol
  simp [Int.neg_mul]

theorem character_period (a : Nat) : quadraticCharacter (a+conductor) = quadraticCharacter a := by
  unfold quadraticCharacter
  change quadSymbol 11 (a+2893) * quadSymbol 263 (a+2893) = _
  rw [quadSymbol_of_congruent (p:=11) (a:=a+2893) (b:=a) (by omega),
      quadSymbol_of_congruent (p:=263) (a:=a+2893) (b:=a) (by omega)]

/-- After summing over a full period, the two lifted terms enumerate all
residues at 2m. Subtracting the separately indexed even term removes the
Euler contribution. The resulting raw multipliers are twice 3 and twice 9. -/
theorem removed_even_contribution (a : Nat) :
    let m : Int := conductor
    let b : Int := a
    let χ := quadraticCharacter a
    let χ' := quadraticCharacter (a+conductor)
    let χ₂ := quadraticCharacter (2*a)
    ((-χ)*scaledB2 (2*m) b + (-χ')*scaledB2 (2*m) (b+m)) -
      (-χ₂)*scaledB2 (2*m) (2*b) = 2*3*((-χ)*scaledB2 m b) ∧
    ((-χ)*scaledB4 (2*m) b + (-χ')*scaledB4 (2*m) (b+m)) -
      (-χ₂)*scaledB4 (2*m) (2*b) = 2*9*((-χ)*scaledB4 m b) := by
  dsimp only
  rw [character_period, character_double]
  obtain ⟨h2,h4⟩ := bernoulli_distribution_two (conductor : Int) a
  obtain ⟨d2,d4⟩ := bernoulli_at_double (conductor : Int) a
  rw [d2,d4]
  constructor <;> grind

/-- Sum over every residue represented by a natural number below n. -/
def sumBelow : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n+1, f => sumBelow n f + f n

theorem sumBelow_linear (n : Nat) (u v : Int) (f g : Nat → Int) :
    sumBelow n (fun a => u*f a + v*g a) = u*sumBelow n f + v*sumBelow n g := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp only [sumBelow, ih]; grind

theorem sumBelow_add (n k : Nat) (f : Nat → Int) :
    sumBelow (n+k) f = sumBelow n f + sumBelow k (fun a => f (a+n)) := by
  induction k with
  | zero => simp [sumBelow]
  | succ k ih => simp only [sumBelow, Nat.add_comm k n]; grind

theorem sumBelow_even_odd (n : Nat) (f : Nat → Int) :
    sumBelow (2*n) f = sumBelow n (fun a => f (2*a)) + sumBelow n (fun a => f (2*a+1)) := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega]
    simp only [sumBelow, ih]
    grind

theorem sumBelow_scale (n : Nat) (k : Int) (f : Nat → Int) :
    sumBelow n (fun a => k*f a) = k*sumBelow n f := by
  simpa using sumBelow_linear n k 0 f f

theorem sumBelow_pointwise_add (n : Nat) (f g : Nat → Int) :
    sumBelow n (fun a => f a + g a) = sumBelow n f + sumBelow n g := by
  simpa using sumBelow_linear n 1 1 f g

/-- The odd part of a period of length 2n is the two halves minus the evens. -/
theorem reindex_odd_sum (n : Nat) (f : Nat → Int) :
    sumBelow n (fun a => f (2*a+1)) =
      sumBelow n (fun a => (f a + f (a+n)) - f (2*a)) := by
  have allHalves := sumBelow_add n n f
  have allParity := sumBelow_even_odd n f
  rw [show 2*n=n+n by omega] at allParity
  have remove := sumBelow_linear n 1 (-1) (fun a => f a + f (a+n)) (fun a => f (2*a))
  simp only [Int.one_mul, Int.neg_mul, ← Int.sub_eq_add_neg] at remove
  rw [sumBelow_pointwise_add] at remove
  omega

/-- Signed raw numerator for the chosen scaled Bernoulli polynomial at period m. -/
def summand (B : Int → Int → Int) (m a : Nat) : Int :=
  -(quadraticCharacter a) * B m a

def primitiveRaw (B : Int → Int → Int) : Int :=
  sumBelow conductor (summand B conductor)

/-- Only odd residues 1,3,…,2n−1 occur at the even period 2n. -/
def oddRaw (B : Int → Int → Int) (n : Nat) : Int :=
  sumBelow n (fun a => summand B (2*n) (2*a+1))

theorem depletion_at_twice_conductor :
    oddRaw scaledB2 conductor = 2*3*primitiveRaw scaledB2 ∧
    oddRaw scaledB4 conductor = 2*9*primitiveRaw scaledB4 := by
  unfold oddRaw primitiveRaw
  constructor
  · rw [reindex_odd_sum, ← sumBelow_scale]
    apply congrArg (sumBelow conductor)
    funext a
    simpa [summand]
      using (removed_even_contribution a).1
  · rw [reindex_odd_sum, ← sumBelow_scale]
    apply congrArg (sumBelow conductor)
    funext a
    simpa [summand]
      using (removed_even_contribution a).2

theorem character_period_multiple (a k : Nat) :
    quadraticCharacter (a+k*conductor) = quadraticCharacter a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, character_period, ih]

/-- Once the period is even, its two lifts of an odd residue are both odd.
Another doubling therefore multiplies the raw numerator only by 2. -/
theorem oddRaw_double_period (B : Int → Int → Int) (n : Nat)
    (period : ∀ b, quadraticCharacter (b+2*n) = quadraticCharacter b)
    (dist : ∀ m b : Int, B (2*m) b + B (2*m) (b+m) = 2*B m b) :
    oddRaw B (2*n) = 2*oddRaw B n := by
  let f (a : Nat) := summand B (2*(2*n)) (2*a+1)
  change sumBelow (2*n) f = 2*sumBelow n _
  have halves := sumBelow_add n n f
  rw [show n+n=2*n by omega] at halves
  rw [halves, ← sumBelow_pointwise_add, ← sumBelow_scale]
  apply congrArg (sumBelow n)
  funext a
  dsimp only [f, summand]
  rw [show 2*(a+n)+1 = (2*a+1)+2*n by omega, period]
  have identity := dist (↑(2*n)) (↑(2*a+1))
  rw [Int.natCast_add, Int.natCast_mul 2 (2*n)]
  grind

/-- Raw numerators at 8 times the primitive conductor. -/
theorem depletion_at_common_period :
    oddRaw scaledB2 (4*conductor) = 8*3*primitiveRaw scaledB2 ∧
    oddRaw scaledB4 (4*conductor) = 8*9*primitiveRaw scaledB4 := by
  have twoPeriod (a : Nat) := character_period_multiple a 2
  have fourPeriod (a : Nat) : quadraticCharacter (a+2*(2*conductor)) = quadraticCharacter a :=
    character_period_multiple a 4
  have b2 (m b : Int) := (bernoulli_distribution_two m b).1
  have b4 (m b : Int) := (bernoulli_distribution_two m b).2
  obtain ⟨hw1,hw3⟩ := depletion_at_twice_conductor
  have x1 := oddRaw_double_period scaledB2 conductor twoPeriod b2
  have x3 := oddRaw_double_period scaledB4 conductor twoPeriod b4
  have y1 := oddRaw_double_period scaledB2 (2*conductor) fourPeriod b2
  have y3 := oddRaw_double_period scaledB4 (2*conductor) fourPeriod b4
  change oddRaw scaledB2 (2*(2*conductor)) = _ ∧ oddRaw scaledB4 (2*(2*conductor)) = _
  omega

/-- Partial sums of the original executable enumeration, before its final block. -/
def blockSums (n : Nat) : WeightedSums :=
  (List.range n).foldl residueBlock ⟨0,0,0,0⟩

theorem blockSums_succ (n : Nat) :
    blockSums (n+1) = residueBlock (blockSums n) n := by
  simp [blockSums, List.range_succ]

/-- Four successive odd raw summands are exactly the two untwisted components
of one transition of the original accumulator. -/
theorem untwisted_block_step (acc : WeightedSums) (n : Nat) :
    let step (B : Int → Int → Int) (z : Int) :=
      z + summand B modulus (8*n+1) + summand B modulus (8*n+3) +
      summand B modulus (8*n+5) + summand B modulus (8*n+7)
    (residueBlock acc n).weightOne = step scaledB2 acc.weightOne ∧
    (residueBlock acc n).weightThree = step scaledB4 acc.weightThree := by
  constructor <;> rfl

theorem sumBelow_four_next (n : Nat) (f : Nat → Int) :
    sumBelow (4*(n+1)) f =
      sumBelow (4*n) f + f (4*n) + f (4*n+1) + f (4*n+2) + f (4*n+3) := by
  rw [show 4*(n+1)=4*n+1+1+1+1 by omega]
  rfl

theorem untwisted_partial_sums (n : Nat) :
    (blockSums n).weightOne =
      sumBelow (4*n) (fun a => summand scaledB2 modulus (2*a+1)) ∧
    (blockSums n).weightThree =
      sumBelow (4*n) (fun a => summand scaledB4 modulus (2*a+1)) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    obtain ⟨hs2,hs4⟩ := untwisted_block_step (blockSums n) n
    rw [blockSums_succ, hs2, hs4, ih.1, ih.2, sumBelow_four_next, sumBelow_four_next]
    have ha : 2*(4*n)+1=8*n+1 := by omega
    have hb : 2*(4*n+1)+1=8*n+3 := by omega
    have hc : 2*(4*n+2)+1=8*n+5 := by omega
    have hd : 2*(4*n+3)+1=8*n+7 := by omega
    simp only [ha, hb, hc, hd, and_self]

theorem executable_odd_sums :
    sums.weightOne = oddRaw scaledB2 (4*conductor) ∧
    sums.weightThree = oddRaw scaledB4 (4*conductor) :=
  untwisted_partial_sums conductor

/-- The actual common-modulus sums have eight times the raw normalization,
and the two Euler factors 1-χ(2)2^r for r=1,3. -/
theorem raw_euler_factors :
    sums.weightOne = 8*3*primitiveRaw scaledB2 ∧
    sums.weightThree = 8*9*primitiveRaw scaledB4 :=
  ⟨executable_odd_sums.1.trans depletion_at_common_period.1,
   executable_odd_sums.2.trans depletion_at_common_period.2⟩

set_option maxRecDepth 131072 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 300 in
/-- Independent kernel computation directly over the 2893 primitive residues. -/
theorem primitive_raw_table :
    primitiveRaw scaledB2 = 24*(conductor : Int)*(-3472) ∧
    primitiveRaw scaledB4 = 240*(conductor : Int)*4771880864 := by
  decide

theorem normalized_primitive_moments :
    primitiveRaw scaledB2 / (24*(conductor : Int)) = -3472 ∧
    primitiveRaw scaledB4 / (240*(conductor : Int)) = 4771880864 := by
  rw [primitive_raw_table.1, primitive_raw_table.2]
  decide

/-- The common normalization cancels the increase from conductor m to 8m.
The normalized untwisted sums are exactly 3 and 9 times the primitive sums. -/
theorem normalized_euler_factors :
    sums.weightOne / (24*(modulus : Int)) =
      3*(primitiveRaw scaledB2 / (24*(conductor : Int))) ∧
    sums.weightThree / (240*(modulus : Int)) =
      9*(primitiveRaw scaledB4 / (240*(conductor : Int))) := by
  rw [raw_euler_factors.1, raw_euler_factors.2, primitive_raw_table.1, primitive_raw_table.2]
  decide

theorem depleted_values_from_primitive :
    sums.weightOne / (24*(modulus : Int)) = -10416 ∧
    sums.weightThree / (240*(modulus : Int)) = 42946927776 := by
  rw [normalized_euler_factors.1, normalized_euler_factors.2,
    normalized_primitive_moments.1, normalized_primitive_moments.2]
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- Exhaust the possible smaller conductor divisors of 11 times 263. -/
theorem proper_divisors :
    ∀ d : Fin conductor, d.val ∣ conductor → d.val=1 ∨ d.val=11 ∨ d.val=263 := by
  decide

/-- These units agree with 1 modulo 11 and 263 respectively, and have
opposite character to 1. Primitivity must be tested on units. -/
theorem incompatible_unit_residues :
    Nat.gcd 1 conductor = 1 ∧ Nat.gcd 45 conductor = 1 ∧ Nat.gcd 527 conductor = 1 ∧
    45%11 = 1 ∧ 527%263 = 1 ∧
    quadraticCharacter 1 = 1 ∧ quadraticCharacter 45 = -1 ∧
    quadraticCharacter 527 = -1 := by decide

/-- On units the character factors through no proper divisor of its modulus.
The putative inducing function is allowed to be arbitrary. -/
theorem no_descent_to_proper_divisor (d : Nat) (hd : d ∣ conductor) (hlt : d < conductor) :
    ¬ ∃ f : Nat → Int, ∀ a, Nat.gcd a conductor = 1 →
      quadraticCharacter a = f (a%d) := by
  rintro ⟨f,induced⟩
  obtain ⟨u,v,w,r11,r263,c1,c45,c527⟩ := incompatible_unit_residues
  have h1 := induced 1 u
  have h45 := induced 45 v
  have h527 := induced 527 w
  rw [c1] at h1
  rw [c45] at h45
  rw [c527] at h527
  rcases proper_divisors ⟨d,hlt⟩ hd with one | eleven | twoSixtyThree
  · change d=1 at one
    subst d
    simp at h1 h45
    omega
  · change d=11 at eleven
    subst d
    rw [r11] at h45
    change 1=f 1 at h1
    omega
  · change d=263 at twoSixtyThree
    subst d
    rw [r263] at h527
    change 1=f 1 at h1
    omega

end Reimann.DyadicEulerFactor
