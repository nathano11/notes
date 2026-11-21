import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.FundamentalDiscriminant
import Reimann.SignedCommonNormalization

/-! Arithmetic comparison of the signed Stickelberger character with the
quadratic residue symbol of the imaginary radicand and its discriminant. -/

namespace Reimann.SignedDiscriminant2893

/-- The least residues 0, 1 and p−1 decode to the three integer character values. -/
theorem signed_euler_decode (p t : Nat) (x : Int) (hp : 2<p) (ht : t=(x:ZMod p).val)
    (hx : x=0 ∨ x=1 ∨ x=-1) : (if t=p-1 then -1 else (t:Int)) = x := by
  have hm : (-1 : ZMod p).val = p-1 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
    exact ZMod.val_neg_one k
  rcases hx with rfl | rfl | rfl
  · rw [Int.cast_zero, ZMod.val_zero] at ht
    simp [ht,show 0 ≠ p-1 by omega]
  · rw [Int.cast_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1<p)] at ht
    simp [ht,show 1 ≠ p-1 by omega]
  · rw [Int.cast_neg, Int.cast_one, hm] at ht
    simp [ht]

theorem euler_word (p b : Nat) [Fact p.Prime] (hp : p%2=1) :
    ((jacobiSym (b : Int) p : Int) : ZMod p).val = (b%p)^((p-1)/2)%p := by
  have hpow : ((jacobiSym (b : Int) p : Int) : ZMod p) = (b : ZMod p)^(p/2) := by
    simp only [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow, Int.cast_natCast]
  calc
    _ = ((b : ZMod p)^(p/2)).val := congrArg ZMod.val hpow
    _ = b^(p/2)%p := by rw [← Nat.cast_pow, ZMod.val_natCast]
    _ = _ := by rw [show p/2=(p-1)/2 by omega, Nat.pow_mod]

/-- Decode the Euler-criterion word, including its zero at ramified arguments. -/
theorem quad_symbol_eq_jacobi (p b : Nat) [Fact p.Prime] (hp : p%2=1) :
    Dyadic.quadSymbol p b = jacobiSym b p := by
  have htwo := (Fact.out : p.Prime).two_le
  exact signed_euler_decode _ _ _ (by omega) (euler_word p b hp).symm
    (jacobiSym.trichotomy (b:Int) p)

set_option maxRecDepth 8192 in
theorem even_character_eq_jacobi (a : Nat) :
    SignedMeasure256.character a = jacobiSym a 2893 := by
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 263) := ⟨by decide +kernel⟩
  change Dyadic.quadSymbol 11 a * Dyadic.quadSymbol 263 a = jacobiSym a (11*263)
  rw [quad_symbol_eq_jacobi 11 a (by decide), quad_symbol_eq_jacobi 263 a (by decide),
    jacobiSym.mul_right' _ (by decide : 11≠0) (by decide : 263≠0)]

theorem mod_four_character (a : Nat) : SignedStickelberger.signFour a = ZMod.χ₄ a := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  unfold SignedStickelberger.signFour
  split_ifs <;> omega

theorem radicand_symbol (a : Nat) (ha : Odd a) :
    SignedCommonNormalization.character2893 a = jacobiSym (-2893) a := by
  unfold SignedCommonNormalization.character2893
  have qr : jacobiSym (2893:Int) a = jacobiSym a 2893 := by
    simpa using jacobiSym.quadratic_reciprocity_one_mod_four (a:=2893) (b:=a) (by decide) ha
  rw [even_character_eq_jacobi, mod_four_character, jacobiSym.neg (2893:Int) ha, qr, mul_comm]

theorem fundamental_discriminant : Int.IsFundamentalDiscr (-11572) := by
  change Int.IsFundamentalDiscr (4*(-2893))
  apply Int.isFundamentalDiscr_four_mul.mpr
  constructor
  · rw [← Int.squarefree_natAbs]
    change Squarefree (2893:Nat)
    decide +kernel
  · exact Or.inr (by decide)

/-- The finite inputs to Kida's rank formula for the two imaginary quadratic pairs.
The equality of these numerical expressions with an Iwasawa rank is an arithmetic theorem. -/
theorem kida_valuation_inputs :
    Dyadic.exactV (11^2-1) 3 ∧ Dyadic.exactV (263^2-1) 4 ∧
    Dyadic.exactV (3^2-1) 3 ∧ Dyadic.exactV (23^2-1) 4 ∧
    (-1 + 2^(3-3:Nat) + 2^(4-3:Nat) : Int) = 2 :=
  ⟨⟨7, by decide⟩, ⟨2161, by decide⟩, ⟨0, by decide⟩, ⟨16, by decide⟩, by decide⟩

/-- Equality on every odd input, including those divisible by either odd ramified prime. -/
theorem signed_character_eq_jacobi (a : Nat) (ha : Odd a) :
    SignedCommonNormalization.character2893 a = jacobiSym (-11572) a := by
  rw [show (-11572:Int) = 4*(-2893) by decide, jacobiSym.mul_left, jacobiSym.at_four ha, one_mul]
  exact radicand_symbol a ha

theorem even_zero (a : Nat) (ha : a%2=0) : SignedCommonNormalization.character2893 a = 0 := by
  unfold SignedCommonNormalization.character2893
  simp only [mod_four_character, ZMod.χ₄_nat_eq_if_mod_four, ha, reduceIte, mul_zero]

/-- The discriminant is even, so its quadratic character vanishes on even arguments. -/
theorem integer_character (a : Nat) :
    SignedCommonNormalization.character2893 a = if a%2=0 then 0 else jacobiSym (-11572) a := by
  split_ifs with h
  · exact even_zero a h
  · exact signed_character_eq_jacobi a (Nat.odd_iff.mpr (by omega))

theorem ramified_values (k : Nat) :
    SignedCommonNormalization.character2893 (2*k)=0 ∧
    SignedCommonNormalization.character2893 (11*k)=0 ∧
    SignedCommonNormalization.character2893 (263*k)=0 := by
  constructor
  · exact even_zero _ (by omega)
  · constructor <;> simp [SignedCommonNormalization.character2893, SignedMeasure256.character,
      Dyadic.quadSymbol, Nat.mul_mod_right]

/-- At an odd unramified prime the positive character sign is equivalent to
the quadratic defining polynomial having a residue-field root. -/
theorem good_prime_square (p : Nat) [Fact p.Prime] (hp : Odd p) (hg : (2893:ZMod p) ≠ 0) :
    SignedCommonNormalization.character2893 p = 1 ↔ IsSquare (-2893:ZMod p) := by
  rw [radicand_symbol p hp, ← jacobiSym.legendreSym.to_jacobiSym]
  have h : ((-2893:Int):ZMod p) ≠ 0 := by simpa using hg
  simpa using legendreSym.eq_one_iff p h

/-- The negative sign detects the absence of a square root at every odd prime. -/
theorem odd_prime_nonsquare (p : Nat) [Fact p.Prime] (hp : Odd p) :
    SignedCommonNormalization.character2893 p = -1 ↔ ¬ IsSquare (-2893:ZMod p) := by
  rw [radicand_symbol p hp]
  simpa using (ZMod.nonsquare_iff_jacobiSym_eq_neg_one (p:=p) (a:= -2893))

/-- For two odd primes of product 1 modulo four, twisting the two Euler
symbols by the mod-four sign gives the odd part of the discriminant character. -/
theorem two_prime_discriminant (p q a : Nat) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpodd : p%2=1) (hqodd : q%2=1) (hm : (p*q)%4=1) (ha : Odd a) :
    (Dyadic.quadSymbol p a * Dyadic.quadSymbol q a) * SignedStickelberger.signFour a =
      jacobiSym (4 * -((p*q:Nat):Int)) a := by
  rw [quad_symbol_eq_jacobi p a hpodd, quad_symbol_eq_jacobi q a hqodd,
    ← jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero, mod_four_character,
    jacobiSym.mul_left, jacobiSym.at_four ha, one_mul, jacobiSym.neg _ ha,
    jacobiSym.quadratic_reciprocity_one_mod_four hm ha, mul_comm]

theorem character69_eq_jacobi (a : Nat) (ha : Odd a) :
    DyadicZeroValues.chi276 a = jacobiSym (-276) a := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 23) := ⟨by decide⟩
  rw [show (-276:Int) = 4 * -((3*23:Nat):Int) by decide,
    ← two_prime_discriminant 3 23 a (by decide) (by decide) (by decide) ha]
  have hh := Nat.odd_iff.mp ha
  rcases (show a%4=1 ∨ a%4=3 by omega) with h | h <;>
    simp [DyadicZeroValues.chi276, SignedStickelberger.signFour, h]

end Reimann.SignedDiscriminant2893
