import Reimann.Dyadic

/-! Finite signed moments at s=0 for the two branches of the real quadratic
character of conductor 69. The interpolation at s=0 twists by the odd
character of conductor four. The field comparison is external. -/

namespace Reimann.DyadicZeroValues

open Reimann.Dyadic

/-- χ₆₉ multiplied by χ₋₄. Even arguments vanish. -/
def chi276 (b : Nat) : Int :=
  let quadratic := quadSymbol 3 b * quadSymbol 23 b
  match b % 4 with
  | 1 => quadratic
  | 3 => -quadratic
  | _ => 0

/-- The quadratic finite-order twist χ₈ multiplies the preceding character. -/
def chi552 (b : Nat) : Int :=
  match b % 8 with
  | 1 | 7 => chi276 b
  | 3 | 5 => -chi276 b
  | _ => 0

/-- Zeroth and first signed moments, based at b=1 through b=f inclusive. -/
def moments (f : Nat) (χ : Nat → Int) : Int × Int :=
  (List.range f).foldl (fun acc i =>
    let b := i+1
    let value := χ b
    (acc.1 + value, acc.2 + (b:Int)*value)) (0,0)

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem moments_276 : moments 276 chi276 = (0,-2208) := by decide

theorem moments_552 : moments 552 chi552 = (0,-4416) := by decide

/-- At s=0 the depleted factor is 1−χ(2) for each primitive twist. -/
theorem depletion_at_two : (1-chi276 2, 1-chi552 2) = (1,1) := by decide

/-- Numerator of the depleted −Σχ(b)B₁(b/f), with denominator 2f. -/
def depletedNumerator (f : Nat) (χ : Nat → Int) : Int :=
  let S := moments f χ
  (0 - (1-χ 2)) * (2*S.2-(f:Int)*S.1)

/-- The two depleted Bernoulli evaluations equal eight after restoring 2f. -/
theorem depleted_values_cleared :
    depletedNumerator 276 chi276 = (2*276:Int)*8 ∧
    depletedNumerator 552 chi552 = (2*552:Int)*8 := by
  have h₁ := congrArg Prod.fst depletion_at_two
  have h₂ := congrArg Prod.snd depletion_at_two
  change 1-chi276 2 = 1 at h₁
  change 1-chi552 2 = 1 at h₂
  simp [depletedNumerator, moments_276, moments_552, h₁,h₂]

/-- The additional factor two is Mizusawa's half-normalization. -/
def halfValue (f : Nat) (χ : Nat → Int) : Int :=
  depletedNumerator f χ / (4*(f:Int))

theorem half_values : (halfValue 276 chi276, halfValue 552 chi552) = (4,4) := by
  obtain ⟨h₁,h₂⟩ := depleted_values_cleared
  unfold halfValue
  rw [h₁,h₂]
  decide

/-- Necessary for a character at conductor f to be induced from modulus m. -/
def FactorsOnUnits (f m : Nat) (χ : Nat → Int) : Prop :=
  ∀ x y : Nat, Nat.gcd x f = 1 → Nat.gcd y f = 1 →
    x % m = y % m → χ x = χ y

/-- A unit b congruent to 1 modulo a multiple of m obstructs descent to m. -/
theorem unit_witness {f m q t : Nat} {χ : Nat → Int} (hm : m ∣ q)
    (hb : Nat.gcd (1+q*t) f = 1) (hs : χ 1 ≠ χ (1+q*t)) :
    ¬ FactorsOnUnits f m χ := by
  intro h
  obtain ⟨k,hk⟩ := hm
  have he : 1%m = (1+q*t)%m := by rw [hk, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  exact hs (h _ _ (by simp) hb he)

/-- Every proper conductor divisor divides one of f/2, f/3, f/23. -/
theorem proper_divisor_cover :
    (∀ m : Fin 276, m.val ∣ 276 → m.val ∣ 138 ∨ m.val ∣ 92 ∨ m.val ∣ 12) ∧
    (∀ m : Fin 552, m.val ∣ 552 → m.val ∣ 276 ∨ m.val ∣ 184 ∨ m.val ∣ 24) := by decide

/-- At modulus 276 the units 139,185,37 rule out all smaller conductor divisors. -/
theorem primitive_276 {m : Nat} (hlt : m < 276) (hm : m ∣ 276) :
    ¬ FactorsOnUnits 276 m chi276 := by
  rcases proper_divisor_cover.1 ⟨m,hlt⟩ hm with h | h | h
  · exact unit_witness (t:=1) h (by decide) (by decide)
  · exact unit_witness (t:=2) h (by decide) (by decide)
  · exact unit_witness (t:=3) h (by decide) (by decide)

/-- At modulus 552 the units 277,185,97 rule out all smaller conductor divisors. -/
theorem primitive_552 {m : Nat} (hlt : m < 552) (hm : m ∣ 552) :
    ¬ FactorsOnUnits 552 m chi552 := by
  rcases proper_divisor_cover.2 ⟨m,hlt⟩ hm with h | h | h
  · exact unit_witness (t:=1) h (by decide) (by decide)
  · exact unit_witness (t:=1) h (by decide) (by decide)
  · exact unit_witness (t:=4) h (by decide) (by decide)

/-- The residue class of −1 has value −1 in both characters. -/
theorem odd_characters : (chi276 275, chi552 551) = (-1,-1) := by decide

/-- The tables define functions on the displayed residue rings. -/
theorem reduce_at_conductors (b : Nat) :
    chi276 (b%276) = chi276 b ∧ chi552 (b%552) = chi552 b := by
  simp only [chi276, chi552, quadSymbol,
    Nat.mod_mod_of_dvd b (by decide : 4 ∣ 276), Nat.mod_mod_of_dvd b (by decide : 3 ∣ 276),
    Nat.mod_mod_of_dvd b (by decide : 23 ∣ 276), Nat.mod_mod_of_dvd b (by decide : 8 ∣ 552),
    Nat.mod_mod_of_dvd b (by decide : 4 ∣ 552), Nat.mod_mod_of_dvd b (by decide : 3 ∣ 552),
    Nat.mod_mod_of_dvd b (by decide : 23 ∣ 552), and_self]

/-- For the two branches, these are the local factors χ₋₄ and χ₋₈. -/
def oddFactor (quadraticTwist : Bool) (b : Nat) : Int :=
  match b % 8 with
  | 1 => 1
  | 3 => if quadraticTwist then 1 else -1
  | 5 => if quadraticTwist then -1 else 1
  | 7 => -1
  | _ => 0

theorem local_factorization (b : Nat) :
    chi276 b = quadSymbol 3 b * quadSymbol 23 b * oddFactor false b ∧
    chi552 b = quadSymbol 3 b * quadSymbol 23 b * oddFactor true b := by
  have h : b%4 = (b%8)%4 := (Nat.mod_mod_of_dvd b (by decide : 4 ∣ 8)).symm
  unfold chi552 chi276 oddFactor
  rw [h]
  have bounds := Nat.mod_lt b (by decide : 0 < 8)
  generalize b%8 = t at *
  have cases8 : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases cases8 with h|h|h|h|h|h|h|h <;> subst t <;> simp

theorem prime_factor_multiplicative (p : Nat) (hp : p=3 ∨ p=23) (a b : Nat) :
    quadSymbol p (a*b) = quadSymbol p a * quadSymbol p b := by
  have table : ∀ i j : Fin p, quadSymbol p (i.val*j.val) = quadSymbol p i.val * quadSymbol p j.val := by
    rcases hp with rfl | rfl <;> decide
  have pos : 0 < p := by omega
  have h := table ⟨a%p,Nat.mod_lt _ pos⟩ ⟨b%p,Nat.mod_lt _ pos⟩
  unfold quadSymbol at h ⊢
  simp only [Nat.mod_mod, ← Nat.mul_mod] at h
  exact h

theorem odd_factor_multiplicative (t : Bool) (a b : Nat) :
    oddFactor t (a*b) = oddFactor t a * oddFactor t b := by
  have table : ∀ u : Bool, ∀ i j : Fin 8,
      oddFactor u (i.val*j.val) = oddFactor u i.val * oddFactor u j.val := by decide
  have h := table t ⟨a%8,Nat.mod_lt _ (by decide)⟩ ⟨b%8,Nat.mod_lt _ (by decide)⟩
  unfold oddFactor at h ⊢
  simp only [Nat.mod_mod, ← Nat.mul_mod] at h
  exact h

theorem characters_multiplicative (a b : Nat) :
    chi276 (a*b) = chi276 a * chi276 b ∧ chi552 (a*b) = chi552 a * chi552 b := by
  obtain ⟨p₁,p₂⟩ := local_factorization (a*b)
  obtain ⟨a₁,a₂⟩ := local_factorization a
  obtain ⟨b₁,b₂⟩ := local_factorization b
  rw [p₁,p₂,a₁,a₂,b₁,b₂,prime_factor_multiplicative 3 (Or.inl rfl),
    prime_factor_multiplicative 23 (Or.inr rfl),odd_factor_multiplicative,odd_factor_multiplicative]
  constructor <;> grind

theorem support_on_units (b : Nat) :
    (chi276 b ≠ 0 ↔ Nat.gcd b 276 = 1) ∧ (chi552 b ≠ 0 ↔ Nat.gcd b 552 = 1) := by
  have table₁ : ∀ i : Fin 276, chi276 i.val ≠ 0 ↔ Nat.gcd i.val 276 = 1 := by decide
  have table₂ : ∀ i : Fin 552, chi552 i.val ≠ 0 ↔ Nat.gcd i.val 552 = 1 := by decide
  have h₁ := table₁ ⟨b%276, Nat.mod_lt _ (by decide)⟩
  have h₂ := table₂ ⟨b%552, Nat.mod_lt _ (by decide)⟩
  rw [(reduce_at_conductors b).1, ← Nat.gcd_rec, Nat.gcd_comm] at h₁
  rw [(reduce_at_conductors b).2, ← Nat.gcd_rec, Nat.gcd_comm] at h₂
  exact ⟨h₁,h₂⟩

end Reimann.DyadicZeroValues
