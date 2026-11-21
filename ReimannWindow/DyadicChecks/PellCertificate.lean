import Std

namespace ReimannWindow.PellCertificate

/-- The radicand of the real quadratic field obtained by adjoining
the square root of twice the product of the auxiliary primes. -/
def radicand : Nat := 641098

/-- Numerator and denominator of convergent 423 of the regular continued
fraction of the square root of the radicand, with the first index zero. -/
def pellX : Nat :=
  5483528512481796002932817388783300448702602025317638976164055091151016357200743701762140077205768601812289338444056006607390961749137637905744453646083383533943278301048998735798062531462269933550685914518807743

def pellY : Nat :=
  6848538396322087506059386495669389958255370805896335047636797958030601500379525998536364982767843382150527987810254606456228298099418805688612938691704757665131829945758948413325670624324749027177144451319576

theorem radicand_from_auxiliary_primes : radicand = 2 * 19 * 16871 := by
  decide
-- breakpoint radicand_from_auxiliary_primes

/-- The subtraction-free Pell identity proves that the algebraic integer
`pellX + pellY * sqrt(radicand)` has norm one. -/
theorem pell_norm_one : pellX ^ 2 = 1 + radicand * pellY ^ 2 := by
  decide
-- breakpoint pell_norm_one

theorem pell_coefficient_residues : (pellX % 9, pellY % 9) = (8, 3) := by
  decide
-- breakpoint pell_coefficient_residues

/-- All square roots of the radicand modulo nine, including their labels
as the two lifts of the distinct roots modulo three. -/
theorem roots_mod_nine :
    (∀ z : Fin 9, (z.val ^ 2) % 9 = radicand % 9 ↔ z.val = 1 ∨ z.val = 8) ∧
    ((1 : Nat) % 3, (8 : Nat) % 3) = (1, 2) := by
  decide
-- breakpoint roots_mod_nine

def unitAtRoot (z : Nat) : Nat := (pellX + pellY * z) % 9

theorem pell_local_residues : (unitAtRoot 1, unitAtRoot 8) = (2, 5) := by
  decide
-- breakpoint pell_local_residues

/-- The representative of a unit class modulo sign which is one modulo
three. The function is only used on units in the theorems below. -/
def principalRep (z : Nat) : Nat :=
  let r := z % 9
  if r % 3 = 1 then r else (9 - r) % 9

/-- The principal units modulo nine are the three powers of four.
Every unit modulo nine has a unique such exponent after its sign is removed. -/
theorem quotient_normal_form :
    ∀ z : Fin 9, z.val % 3 ≠ 0 →
      ∃ k : Fin 3, principalRep z.val = 4 ^ k.val % 9 ∧
        ∀ j : Fin 3, principalRep z.val = 4 ^ j.val % 9 → j = k := by
  decide
-- breakpoint quotient_normal_form

theorem pell_quotient_exponents :
    (principalRep (unitAtRoot 1), principalRep (unitAtRoot 8)) =
      (4 ^ 2 % 9, 4 ^ 1 % 9) := by
  have h₁ := congrArg Prod.fst pell_local_residues
  have h₂ := congrArg Prod.snd pell_local_residues
  change unitAtRoot 1 = 2 at h₁
  change unitAtRoot 8 = 5 at h₂
  rw [h₁, h₂] <;> decide
-- breakpoint pell_quotient_exponents

/-- Both local images have order three modulo sign, and they are inverses. -/
theorem pell_generates_mod_nine :
    let u := principalRep (unitAtRoot 1)
    let v := principalRep (unitAtRoot 8)
    u ≠ 1 ∧ v ≠ 1 ∧ u ^ 3 % 9 = 1 ∧ v ^ 3 % 9 = 1 ∧ (u * v) % 9 = 1 := by
  decide
-- breakpoint pell_generates_mod_nine

/-- Cubing a principal unit exposes one more factor of three. -/
theorem principal_cube_factor (c b : Nat) :
    (1 + 3 * c * b) ^ 3 =
      1 + 9 * c * (b * (1 + 3 * c * b + 3 * c * c * b ^ 2)) := by
  grind
-- breakpoint principal_cube_factor

/-- The remaining coefficient keeps exactly the same residue modulo three. -/
theorem principal_cube_coefficient (c b : Nat) :
    (b * (1 + 3 * c * b + 3 * c * c * b ^ 2)) % 3 = b % 3 := by
  have h : b * (1 + 3 * c * b + 3 * c * c * b ^ 2) =
      b + 3 * (c * b ^ 2 + c ^ 2 * b ^ 3) := by grind
  rw [h]
  omega
-- breakpoint principal_cube_coefficient

/-- The coefficient left after removing `3^(n+1)` has the same residue
as the starting coefficient, for every cyclotomic layer index. -/
theorem principal_cube_iterate (a n : Nat) :
    ∃ b : Nat, (1 + 3 * a) ^ (3 ^ n) = 1 + 3 ^ (n + 1) * b ∧
      b % 3 = a % 3 := by
  induction n with
  | zero => exact ⟨a, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨b, hb, hmod⟩ := ih
    let c := 3 ^ n
    refine ⟨b * (1 + 3 * c * b + 3 * c * c * b ^ 2), ?_,
      (principal_cube_coefficient c b).trans hmod⟩
    calc
      (1 + 3 * a) ^ (3 ^ (n + 1)) = ((1 + 3 * a) ^ (3 ^ n)) ^ 3 := by
        rw [Nat.pow_succ 3 n, Nat.pow_mul]
      _ = (1 + 3 * c * b) ^ 3 := by
        rw [hb, Nat.pow_succ]
        dsimp [c]
        grind
      _ = 1 + 9 * c * (b * (1 + 3 * c * b + 3 * c * c * b ^ 2)) :=
        principal_cube_factor c b
      _ = _ := by dsimp [c]; simp only [Nat.pow_succ]; grind
-- breakpoint principal_cube_iterate

/-- If the initial residue is nonzero, the exact power of three dividing
the difference at the `n`th step is `3^(n+1)`. -/
theorem principal_cube_exact_divisibility (a n : Nat) (ha : a % 3 ≠ 0) :
    3 ^ (n + 1) ∣ (1 + 3 * a) ^ (3 ^ n) - 1 ∧
    ¬ 3 ^ (n + 2) ∣ (1 + 3 * a) ^ (3 ^ n) - 1 := by
  obtain ⟨b, hb, hmod⟩ := principal_cube_iterate a n
  rw [hb, Nat.add_sub_cancel_left]
  refine ⟨Nat.dvd_mul_right _ _, ?_⟩
  intro h
  rw [Nat.pow_succ 3 (n + 1)] at h
  have hd : 3 ∣ b := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by decide)) h
  exact ha (hmod.symm.trans (Nat.mod_eq_zero_of_dvd hd))
-- breakpoint principal_cube_exact_divisibility

/-- Every natural number lifting either of the two sign-normalized Pell
residues has the same exact growth at every power-of-three exponent. -/
theorem pell_principal_lifts (u n : Nat)
    (hu : u % 9 = principalRep (unitAtRoot 1) ∨
      u % 9 = principalRep (unitAtRoot 8)) :
    3 ^ (n + 1) ∣ u ^ (3 ^ n) - 1 ∧ ¬ 3 ^ (n + 2) ∣ u ^ (3 ^ n) - 1 := by
  have h₁ := congrArg Prod.fst pell_quotient_exponents
  have h₂ := congrArg Prod.snd pell_quotient_exponents
  change principalRep (unitAtRoot 1) = 7 at h₁
  change principalRep (unitAtRoot 8) = 4 at h₂
  rw [h₁, h₂] at hu
  have hz : u = 1 + 3 * (u / 3) := by omega
  have ha : (u / 3) % 3 ≠ 0 := by omega
  simpa only [← hz] using principal_cube_exact_divisibility (u / 3) n ha
-- breakpoint pell_principal_lifts

end ReimannWindow.PellCertificate
