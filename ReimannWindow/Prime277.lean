import Std

/-!
Finite Stickelberger computations for the biquadratic field of conductor 69 at 277.
The statements in this file concern exact integers and finite lists. The number-field
interpretation uses the Kummer and Stickelberger arguments in the accompanying note.
-/
namespace ReimannWindow.Prime277

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def p : Nat := 277
private def b : Nat := 622

/-- Quadratic character modulo 3 with −1 represented by 276. -/
private def character3 (u : Nat) : Nat :=
  match u % 3 with
  | 0 => 0
  | 1 => 1
  | _ => 276

/-- Euler's criterion for the quadratic character of conductor 23. -/
private def character23 (u : Nat) : Nat :=
  match (u % 23) ^ 11 % 23 with
  | 0 => 0
  | 1 => 1
  | _ => 276

private def character (f u : Nat) : Nat :=
  ((if f % 3 = 0 then character3 u else 1) *
   (if f % 23 = 0 then character23 u else 1)) % p

/-- Collect all units u modulo 277 f with u ≡ v modulo 277. The quadratic
character vanishes at the nonunits among these representatives. -/
private def coefficient (f v : Nat) : Nat :=
  (List.range f).foldl (fun s k =>
    let u := v + p * k
    (s + (b * u / (f * p)) * character f u) % p) 0

/-- Entry j belongs to v = b^j modulo 277, with 0 ≤ j < 276. -/
def coefficients (f : Nat) : List Nat :=
  (List.range 276).map (fun j => coefficient f (b ^ j % p))

/-- Evaluate the character sum by Horner's rule. The exponent 275 − r
represents −r−1 modulo 276 for 1 ≤ r ≤ 275. -/
def residue (poly : List Nat) (r : Nat) : Nat :=
  let point := b ^ (275 - r) % p
  poly.foldr (fun c acc => (c + point * acc) % p) 0

/-- Count zeros and multiply all 137 residues of the specified parity. -/
def paritySummary (poly : List Nat) (first : Nat) : Nat × Nat :=
  (List.range 137).foldl (fun (acc : Nat × Nat) k =>
    let value := residue poly (first + 2 * k)
    (acc.1 + (if value = 0 then 1 else 0), (acc.2 * value) % p)) (0, 1)

/-- All divisors from 2 through 276 fail. The 276 powers of b exhaust
the units modulo 277, and b meets the auxiliary congruence modulo 69. -/
theorem prime_and_generator :
    (List.range 275).all (fun k => 277 % (k + 2) != 0) = true ∧
    b % 69 = 1 ∧ b ^ 276 % p = 1 ∧
    (List.range 275).all (fun k => b ^ (k + 1) % p != 1) = true := by
  decide +kernel

/-- The odd and even lists partition the weights 1 through 274. -/
theorem parity_coverage :
    ((List.range 137).map (fun k => (1 + 2*k, 2 + 2*k))).flatMap
      (fun pair => [pair.1, pair.2]) = (List.range 274).map (· + 1) := by
  decide +kernel

/- Each published coefficient list has its own proof from the defining sum.
This keeps verification of all the weights from repeating the character sums. -/
private def row1 : List Nat := [
  2, 152, 154, 83, 51, 124, 32, 44, 11, 259, 140, 133, 20, 248, 276, 121, 159, 267, 132, 23,
  2, 270, 5, 78, 91, 161, 142, 9, 106, 54, 50, 246, 123, 35, 76, 215, 75, 59, 234, 50,
  22, 5, 25, 208, 239, 10, 262, 172, 60, 113, 167, 100, 150, 1, 273, 36, 73, 184, 80, 243,
  38, 225, 61, 163, 18, 95, 190, 38, 107, 210, 168, 255, 59, 11, 141, 12, 138, 258, 143, 165,
  224, 64, 195, 222, 188, 109, 139, 136, 52, 175, 92, 40, 260, 19, 251, 30, 115, 43, 186, 233,
  53, 53, 0, 118, 127, 63, 39, 104, 178, 241, 163, 71, 255, 112, 170, 131, 145, 94, 193, 69,
  102, 26, 87, 80, 20, 130, 148, 125, 187, 230, 21, 127, 116, 199, 26, 34, 197, 97, 65, 192,
  190, 261, 16, 220, 35, 23, 56, 85, 204, 211, 47, 96, 68, 223, 185, 77, 212, 44, 65, 74,
  62, 266, 253, 183, 202, 58, 238, 13, 17, 98, 221, 32, 268, 129, 269, 8, 110, 17, 45, 62,
  42, 136, 105, 57, 82, 172, 7, 231, 177, 244, 194, 66, 71, 31, 271, 160, 264, 101, 29, 119,
  6, 181, 49, 249, 154, 29, 237, 134, 176, 89, 8, 56, 203, 55, 206, 86, 201, 179, 120, 3,
  149, 122, 156, 235, 205, 208, 15, 169, 252, 27, 84, 48, 93, 37, 229, 24, 158, 111, 14, 14,
  67, 226, 217, 4, 28, 240, 166, 103, 181, 273, 89, 232, 174, 213, 199, 250, 151, 275, 242, 41,
  257, 264, 47, 214, 196, 219, 157, 114, 46, 217, 228, 145, 41, 33, 147, 247]

private theorem coefficients_one : coefficients 1 = row1 := by
  decide +kernel

private def row3 : List Nat := [
  69, 138, 70, 69, 137, 138, 69, 138, 69, 138, 70, 70, 70, 70, 70, 69, 137, 137, 137, 137,
  138, 70, 69, 137, 138, 70, 69, 138, 70, 69, 137, 138, 70, 70, 70, 70, 70, 70, 69, 138,
  70, 70, 70, 69, 137, 138, 69, 138, 70, 70, 70, 70, 70, 69, 137, 138, 70, 70, 70, 70,
  69, 138, 70, 70, 70, 70, 69, 138, 70, 70, 70, 70, 69, 138, 70, 69, 138, 70, 69, 138,
  69, 138, 70, 70, 70, 69, 138, 70, 70, 69, 138, 69, 138, 70, 69, 138, 69, 137, 137, 138,
  70, 70, 69, 138, 69, 138, 69, 137, 138, 70, 69, 138, 69, 138, 69, 137, 138, 69, 138, 70,
  70, 70, 70, 70, 70, 70, 69, 138, 70, 70, 70, 70, 69, 138, 70, 70, 69, 138, 69, 138,
  70, 69, 137, 138, 69, 138, 69, 138, 70, 70, 70, 70, 70, 69, 137, 137, 137, 137, 138, 70,
  69, 137, 138, 70, 69, 138, 70, 69, 137, 138, 70, 70, 70, 70, 70, 70, 69, 138, 70, 70,
  70, 69, 137, 138, 69, 138, 70, 70, 70, 70, 70, 69, 137, 138, 70, 70, 70, 70, 69, 138,
  70, 70, 70, 70, 69, 138, 70, 70, 70, 70, 69, 138, 70, 69, 138, 70, 69, 138, 69, 138,
  70, 70, 70, 69, 138, 70, 70, 69, 138, 69, 138, 70, 69, 138, 69, 137, 137, 138, 70, 70,
  69, 138, 69, 138, 69, 137, 138, 70, 69, 138, 69, 138, 69, 137, 138, 69, 138, 70, 70, 70,
  70, 70, 70, 70, 69, 138, 70, 70, 70, 70, 69, 138, 70, 70, 69, 138]

private theorem coefficients_three : coefficients 3 = row3 := by
  decide +kernel

private def row23 : List Nat := [
  75, 141, 275, 139, 73, 0, 0, 2, 140, 70, 143, 142, 209, 0, 0, 2, 141, 276, 67, 68,
  275, 135, 68, 1, 210, 210, 210, 207, 136, 0, 1, 208, 71, 72, 68, 276, 68, 1, 209, 275,
  135, 67, 71, 76, 72, 70, 141, 0, 276, 66, 135, 69, 208, 67, 66, 136, 276, 67, 70, 140,
  67, 69, 209, 2, 140, 71, 72, 70, 139, 136, 2, 141, 276, 67, 66, 139, 76, 73, 276, 68,
  275, 136, 276, 67, 67, 68, 276, 67, 67, 68, 0, 3, 72, 68, 2, 139, 135, 66, 136, 276,
  71, 72, 67, 67, 70, 142, 208, 67, 71, 73, 276, 67, 68, 276, 69, 209, 276, 67, 68, 0,
  0, 0, 1, 208, 68, 0, 275, 139, 72, 68, 276, 68, 276, 68, 276, 67, 68, 3, 75, 141,
  275, 139, 73, 0, 0, 2, 140, 70, 143, 142, 209, 0, 0, 2, 141, 276, 67, 68, 275, 135,
  68, 1, 210, 210, 210, 207, 136, 0, 1, 208, 71, 72, 68, 276, 68, 1, 209, 275, 135, 67,
  71, 76, 72, 70, 141, 0, 276, 66, 135, 69, 208, 67, 66, 136, 276, 67, 70, 140, 67, 69,
  209, 2, 140, 71, 72, 70, 139, 136, 2, 141, 276, 67, 66, 139, 76, 73, 276, 68, 275, 136,
  276, 67, 67, 68, 276, 67, 67, 68, 0, 3, 72, 68, 2, 139, 135, 66, 136, 276, 71, 72,
  67, 67, 70, 142, 208, 67, 71, 73, 276, 67, 68, 276, 69, 209, 276, 67, 68, 0, 0, 0,
  1, 208, 68, 0, 275, 139, 72, 68, 276, 68, 276, 68, 276, 67, 68, 3]

private theorem coefficients_twentyThree : coefficients 23 = row23 := by
  decide +kernel

private def row69 : List Nat := [
  1, 211, 142, 206, 206, 143, 138, 207, 71, 140, 8, 77, 2, 206, 143, 140, 71, 72, 69, 211,
  142, 212, 73, 273, 272, 4, 9, 4, 70, 140, 64, 274, 141, 276, 65, 200, 272, 273, 273, 209,
  0, 4, 2, 201, 203, 72, 6, 206, 205, 209, 276, 68, 2, 144, 74, 205, 272, 1, 206, 204,
  274, 204, 0, 4, 2, 204, 274, 208, 5, 275, 139, 73, 276, 70, 141, 3, 76, 75, 140, 67,
  67, 64, 271, 66, 135, 69, 209, 2, 141, 2, 137, 275, 75, 144, 74, 210, 208, 67, 68, 0,
  274, 205, 211, 141, 1, 209, 275, 137, 206, 204, 275, 135, 71, 71, 140, 8, 76, 70, 203, 67,
  68, 1, 205, 272, 0, 0, 1, 209, 273, 274, 144, 77, 4, 68, 2, 137, 270, 136, 276, 66,
  135, 71, 71, 134, 139, 70, 206, 137, 269, 200, 275, 71, 134, 137, 206, 205, 208, 66, 135, 65,
  204, 4, 5, 273, 268, 273, 207, 137, 213, 3, 136, 1, 212, 77, 5, 4, 4, 68, 0, 273,
  275, 76, 74, 205, 271, 71, 72, 68, 1, 209, 275, 133, 203, 72, 5, 276, 71, 73, 3, 73,
  0, 273, 275, 73, 3, 69, 272, 2, 138, 204, 1, 207, 136, 274, 201, 202, 137, 210, 210, 213,
  6, 211, 142, 208, 68, 275, 136, 275, 140, 2, 202, 133, 203, 67, 69, 210, 209, 0, 3, 72,
  66, 136, 276, 68, 2, 140, 71, 73, 2, 142, 206, 206, 137, 269, 201, 207, 74, 210, 209, 276,
  72, 5, 0, 0, 276, 68, 4, 3, 133, 200, 273, 209, 275, 140, 7, 141]

private theorem coefficients_sixtyNine : coefficients 69 = row69 := by
  decide +kernel

/-- There are no zeros in any parity row. The second coordinate is the product
in the field with 277 elements. -/
theorem all_nonresonant_rows :
    paritySummary (coefficients 1) 2 = (0, 86) ∧
    paritySummary (coefficients 3) 1 = (0, 172) ∧
    paritySummary (coefficients 23) 1 = (0, 96) ∧
    paritySummary (coefficients 69) 2 = (0, 98) := by
  rw [coefficients_one, coefficients_three, coefficients_twentyThree, coefficients_sixtyNine]
  decide +kernel

/-- The two odd characters give zero in the remaining nontrivial tame residue.
That residue is treated by descent in the arithmetic proof. -/
theorem last_weight :
    residue (coefficients 3) 275 = 0 ∧ residue (coefficients 23) 275 = 0 := by
  rw [coefficients_three, coefficients_twentyThree]
  decide +kernel

/-- Two lifts of √69 and the associated norm-one unit (25+3√69)/2.
The opposite nonzero Fermat quotients are the local input at weight zero
modulo 276. -/
theorem local_unit :
    25 ^ 2 - 69 * 3 ^ 2 = (4 : Nat) ∧
    26839 ^ 2 % (p*p) = 69 ∧ 49890 ^ 2 % (p*p) = 69 ∧
    (26839 + 49890) % (p*p) = 0 ∧
    2 * 40271 % (p*p) = (25 + 3 * 26839) % (p*p) ∧
    2 * 36483 % (p*p) = (25 + 3 * 49890) % (p*p) ∧
    (40271 ^ 276 % (p*p) - 1) / p = 58 ∧
    (36483 ^ 276 % (p*p) - 1) / p = 219 ∧
    (58 + 219) % p = 0 := by
  decide +kernel

end ReimannWindow.Prime277

namespace ReimannWindow.Prime277

/-- A natural prime is at least two and its only positive divisors are one and itself. -/
def PrimeByDivisors (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- Test the divisors from two through the integer square root, inclusively. -/
def squareRootTrial (n : Nat) : Bool :=
  (List.range (n.sqrt - 1)).all (fun k => decide (¬ (k + 2) ∣ n))

/-- Every proper factorization has a factor at most the integer square root. -/
theorem primeByDivisors_of_squareRootTrial {n : Nat} (hn : 2 ≤ n)
    (ht : squareRootTrial n = true) : PrimeByDivisors n := by
  have noSmall (x : Nat) (hx : 2 ≤ x) (hbound : x ≤ n.sqrt) (hdvd : x ∣ n) : False := by
    have hindex : x - 2 ∈ List.range (n.sqrt - 1) := List.mem_range.mpr (by omega)
    have htest : ¬ (x - 2 + 2) ∣ n := of_decide_eq_true (List.all_eq_true.mp ht _ hindex)
    have heq : x - 2 + 2 = x := by omega
    exact htest (heq ▸ hdvd)
  refine ⟨hn, ?_⟩
  intro d hdvd
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  obtain ⟨e, hprod⟩ := hdvd
  by_cases he1 : e = 1
  · exact Or.inr (by simpa [he1] using hprod.symm)
  have hd0 : d ≠ 0 := by
    intro hd
    simp [hd] at hprod
    omega
  have he0 : e ≠ 0 := by
    intro he
    simp [he] at hprod
    omega
  by_cases hdsmall : d ≤ n.sqrt
  · exact False.elim (noSmall d (by omega) hdsmall ⟨e, hprod⟩)
  by_cases hesmall : e ≤ n.sqrt
  · exact False.elim (noSmall e (by omega) hesmall ⟨d, by rw [Nat.mul_comm]; exact hprod⟩)
  have hfloor : n.sqrt.succ * n.sqrt.succ ≤ d * e :=
    Nat.mul_le_mul (by omega) (by omega)
  have hceil := Nat.lt_succ_sqrt n
  omega

theorem prime_277 : PrimeByDivisors 277 :=
  primeByDivisors_of_squareRootTrial (by decide) (by decide +kernel)

theorem prime_114679 : PrimeByDivisors 114679 :=
  primeByDivisors_of_squareRootTrial (by decide) (by decide +kernel)

theorem prime_649843 : PrimeByDivisors 649843 :=
  primeByDivisors_of_squareRootTrial (by decide) (by decide +kernel)

end ReimannWindow.Prime277

