import Std

/-!
# Circular-unit reductions at 277

This file checks integer identities behind 551 character tests for the conductor-69
biquadratic example. The two auxiliary residue fields have orders 114679 and 649843.
All equalities are finite checks. The statements about units, class groups and
strict cohomology require the separate number-theoretic argument.
-/

namespace ReimannWindow.CircularUnits

set_option maxHeartbeats 0
set_option maxRecDepth 32768

private def p : Nat := 277

/-- Binary modular exponentiation. At most n+1 iterations suffice for exponent n. -/
private def powerLoop (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, n, acc =>
    if n = 0 then acc
    else powerLoop m fuel ((base * base) % m) (n / 2)
      (if n % 2 = 1 then (acc * base) % m else acc)

def power (a n m : Nat) : Nat := powerLoop m (n + 1) (a % m) n (1 % m)

/-- Trial division from 2 through bound inclusive. -/
def trial (n bound : Nat) : Bool :=
  (List.range (bound - 1)).all (fun k => n % (k + 2) != 0)

def generatorTest (g ell : Nat) (primeFactors : List Nat) : Bool :=
  power g (ell - 1) ell == 1 &&
    primeFactors.all (fun q => power g ((ell - 1) / q) ell != 1)

theorem prime_and_generator_arithmetic :
    trial 277 16 = true ∧ 277 < 17^2 ∧ 276 = 2^2*3*23 ∧
    generatorTest 5 277 [2, 3, 23] = true ∧
    trial 114679 338 = true ∧ 114679 < 339^2 ∧ 114678 = 2*3^2*23*277 ∧
    generatorTest 6 114679 [2, 3, 23, 277] = true ∧
    trial 649843 806 = true ∧ 649843 < 807^2 ∧ 649842 = 2*3*17*23*277 ∧
    generatorTest 2 649843 [2, 3, 17, 23, 277] = true := by
  decide +kernel

/-- The character has values 0, 1 or 276, the last representing -1. -/
def quadratic (f a : Nat) : Nat :=
  let c3 := if f % 3 = 0 then
    (match a % 3 with | 0 => 0 | 1 => 1 | _ => 276) else 1
  let c23 := if f % 23 = 0 then
    (match (a % 23)^11 % 23 with | 0 => 0 | 1 => 1 | _ => 276) else 1
  (c3 * c23) % p

/-- Products of 1-zeta^a for positive and negative character values.
The progression begins at first and increases by step. Its first power of zeta
is x, and multiplying it by jump advances to the next power. -/
private def products (ell f first step count x jump : Nat) : Nat × Nat :=
  let data := (List.range count).foldl (fun (st : Nat × Nat × Nat) k =>
    let term := (ell + 1 - st.2.2) % ell
    let next := (st.2.2 * jump) % ell
    match quadratic f (first + step * k) with
    | 1 => ((st.1 * term) % ell, st.2.1, next)
    | 276 => (st.1, (st.2.1 * term) % ell, next)
    | _ => (st.1, st.2.1, next)) (1, 1, x)
  (data.1, data.2.1)

structure Source where
  ell : Nat
  g : Nat
  f : Nat
  zeta : Nat
  jump : Nat
  h : Nat
  deriving Repr

/-- h generates the subgroup of order 277. zeta has order 277*f. -/
def sourceOK (w : Source) : Bool :=
  (w.ell - 1) % (p * w.f) == 0 &&
  w.zeta == power w.g ((w.ell - 1) / (p * w.f)) w.ell &&
  w.jump == power w.zeta p w.ell &&
  w.h == power w.g ((w.ell - 1) / p) w.ell

/-- Row position j collects all residues a congruent to 5^j modulo 277.
An entry d certifies log_h((positive/negative)^((ell-1)/277)) = d.
The equality is checked by exponentiation and cross multiplication. -/
def entryOK (w : Source) (j d : Nat) : Bool :=
  let v := power 5 j p
  let b := products w.ell w.f v p w.f (power w.zeta v w.ell) w.jump
  let n := (w.ell - 1) / p
  (b.1 != 0 && b.2 != 0) &&
    power b.1 n w.ell == (power w.h d w.ell * power b.2 n w.ell) % w.ell

def rowOK (w : Source) (row : List Nat) : Bool :=
  row.length == 276 &&
    ((List.range 276).zip row).all (fun jd => entryOK w jd.1 jd.2)

/-- Since a=5^j modulo 277, the s-character sum is this Fourier polynomial
evaluated at 5^s modulo 277, with coefficients in ascending j order. -/
def fourier (row : List Nat) (s : Nat) : Nat :=
  let point := power 5 s p
  row.foldr (fun coeff acc => (coeff + point * acc) % p) 0

def weights (odd : Bool) : List Nat :=
  if odd then (List.range 138).map (fun j => 2*j + 1)
  else (List.range 137).map (fun j => 2*j + 2)

def missing (odd : Bool) (row : List Nat) : List Nat :=
  (weights odd).filter (fun s => fourier row s == 0)

theorem parity_lists_cover :
    (weights true).length = 138 ∧ (weights false).length = 137 ∧
    (List.range 275).all (fun j =>
      (weights ((j + 1) % 2 == 1)).contains (j + 1)) = true := by
  decide +kernel

/-- Finite-field parameters at 114679 for the conductor factor 1. -/
def firstF1 : Source := ⟨114679, 6, 1, 49063, 1, 49063⟩

theorem firstF1_parameters : sourceOK firstF1 = true := by
  decide +kernel

def firstF1Row : List Nat := [
  97, 74, 125, 223, 2, 239, 248, 264, 195, 230, 65, 75, 5, 8, 42, 94, 271, 87, 261, 263, 0, 68, 89,
  167, 80, 260, 235, 91, 96, 56, 165, 192, 81, 88, 69, 239, 194, 112, 78, 257, 211, 130, 37, 91, 230, 94,
  5, 86, 137, 222, 13, 253, 131, 101, 89, 91, 104, 119, 229, 160, 203, 37, 196, 133, 31, 2, 46, 267, 105,
  109, 59, 176, 255, 111, 270, 200, 167, 14, 60, 220, 111, 232, 218, 228, 236, 109, 250, 272, 140, 60, 117, 156,
  131, 208, 192, 225, 216, 124, 109, 47, 113, 89, 128, 174, 64, 72, 222, 113, 70, 51, 81, 57, 92, 274, 89,
  192, 217, 263, 11, 168, 140, 268, 151, 230, 195, 168, 142, 225, 211, 157, 155, 168, 138, 234, 175, 200, 257, 166,
  237, 220, 24, 272, 247, 79, 2, 142, 139, 227, 50, 0, 184, 72, 85, 32, 238, 199, 267, 16, 150, 264, 238,
  81, 204, 49, 11, 79, 36, 33, 50, 171, 253, 117, 214, 133, 218, 232, 124, 210, 253, 63, 256, 78, 165, 46,
  42, 271, 231, 138, 147, 92, 157, 231, 185, 17, 11, 208, 120, 169, 248, 262, 213, 218, 179, 188, 145, 208, 87,
  19, 163, 142, 85, 92, 175, 2, 8, 50, 240, 12, 179, 18, 256, 141, 78, 150, 178, 189, 2, 201, 268, 80,
  28, 247, 110, 92, 105, 123, 104, 22, 265, 18, 50, 61, 53, 17, 224, 123, 120, 24, 223, 213, 41, 19, 199,
  188, 197, 163, 65, 161, 105, 93, 107, 10, 203, 208, 65, 117, 225, 227, 228, 256, 24, 218, 95, 77, 196, 138]

theorem firstF1_logarithms : rowOK firstF1 firstF1Row = true := by
  decide +kernel

/-- Finite-field parameters at 114679 for the conductor factor 3. -/
def firstF3 : Source := ⟨114679, 6, 3, 102884, 2370, 49063⟩

theorem firstF3_parameters : sourceOK firstF3 = true := by
  decide +kernel

def firstF3Row : List Nat := [
  269, 157, 49, 138, 56, 166, 215, 180, 141, 258, 149, 73, 216, 246, 107, 224, 23, 140, 217, 236, 47, 276, 256,
  123, 112, 207, 209, 182, 58, 197, 217, 4, 256, 255, 54, 98, 82, 245, 231, 175, 24, 113, 199, 4, 243, 125,
  38, 22, 199, 232, 263, 115, 177, 207, 215, 257, 60, 183, 100, 230, 247, 13, 227, 204, 204, 87, 231, 222, 203,
  16, 115, 157, 106, 253, 209, 181, 104, 103, 264, 91, 120, 116, 33, 232, 253, 118, 125, 150, 57, 105, 182, 99,
  270, 200, 31, 35, 103, 187, 9, 133, 197, 182, 63, 189, 207, 14, 70, 225, 35, 124, 198, 145, 170, 273, 52,
  158, 229, 206, 47, 147, 270, 229, 3, 182, 171, 75, 197, 228, 0, 34, 260, 259, 24, 270, 75, 88, 193, 225,
  8, 120, 228, 139, 221, 111, 62, 97, 136, 19, 128, 204, 61, 31, 170, 53, 254, 137, 60, 41, 230, 1, 21,
  154, 165, 70, 68, 95, 219, 80, 60, 273, 21, 22, 223, 179, 195, 32, 46, 102, 253, 164, 78, 273, 34, 152,
  239, 255, 78, 45, 14, 162, 100, 70, 62, 20, 217, 94, 177, 47, 30, 264, 50, 73, 73, 190, 46, 55, 74,
  261, 162, 120, 171, 24, 68, 96, 173, 174, 13, 186, 157, 161, 244, 45, 24, 159, 152, 127, 220, 172, 95, 178,
  7, 77, 246, 242, 174, 90, 268, 144, 80, 95, 214, 88, 70, 263, 207, 52, 242, 153, 79, 132, 107, 4, 225,
  119, 48, 71, 230, 130, 7, 48, 274, 95, 106, 202, 80, 49, 0, 243, 17, 18, 253, 7, 202, 189, 84, 52]

theorem firstF3_logarithms : rowOK firstF3 firstF3Row = true := by
  decide +kernel

/-- Finite-field parameters at 114679 for the conductor factor 23. -/
def firstF23 : Source := ⟨114679, 6, 23, 93898, 50842, 49063⟩

theorem firstF23_parameters : sourceOK firstF23 = true := by
  decide +kernel

def firstF23Row : List Nat := [
  133, 200, 249, 53, 192, 244, 144, 39, 36, 154, 142, 41, 97, 54, 116, 178, 94, 164, 273, 53, 2, 263, 249,
  3, 30, 148, 35, 87, 140, 17, 254, 95, 33, 37, 155, 227, 68, 223, 87, 146, 255, 6, 145, 17, 174, 164,
  158, 13, 267, 194, 157, 121, 93, 3, 102, 25, 220, 177, 61, 90, 38, 102, 171, 145, 1, 75, 156, 100, 102,
  184, 147, 97, 264, 269, 24, 21, 125, 168, 91, 272, 29, 62, 182, 83, 100, 38, 64, 44, 121, 148, 72, 183,
  197, 206, 150, 243, 74, 124, 179, 227, 46, 78, 180, 229, 236, 64, 97, 142, 66, 23, 95, 89, 42, 5, 127,
  123, 221, 262, 186, 58, 269, 198, 196, 157, 22, 118, 31, 252, 219, 97, 55, 253, 171, 63, 114, 260, 151, 160,
  144, 77, 28, 224, 85, 33, 133, 238, 241, 123, 135, 236, 180, 223, 161, 99, 183, 113, 4, 224, 275, 14, 28,
  274, 247, 129, 242, 190, 137, 260, 23, 182, 244, 240, 122, 50, 209, 54, 190, 131, 22, 271, 132, 260, 103, 113,
  119, 264, 10, 83, 120, 156, 184, 274, 175, 252, 57, 100, 216, 187, 239, 175, 106, 132, 276, 202, 121, 177, 175,
  93, 130, 180, 13, 8, 253, 256, 152, 109, 186, 5, 248, 215, 95, 194, 177, 239, 213, 233, 156, 129, 205, 94,
  80, 71, 127, 34, 203, 153, 98, 50, 231, 199, 97, 48, 41, 213, 180, 135, 211, 254, 182, 188, 235, 272, 150,
  154, 56, 15, 91, 219, 8, 79, 81, 120, 255, 159, 246, 25, 58, 180, 222, 24, 106, 214, 163, 17, 126, 117]

theorem firstF23_logarithms : rowOK firstF23 firstF23Row = true := by
  decide +kernel

/-- Finite-field parameters at 114679 for the conductor factor 69. -/
def firstF69 : Source := ⟨114679, 6, 69, 46656, 21767, 49063⟩

theorem firstF69_parameters : sourceOK firstF69 = true := by
  decide +kernel

def firstF69Row : List Nat := [
  229, 17, 211, 188, 186, 54, 159, 132, 275, 131, 140, 273, 90, 210, 51, 259, 85, 154, 192, 233, 262, 198, 70,
  137, 128, 111, 65, 88, 110, 215, 27, 66, 5, 185, 234, 276, 9, 216, 241, 41, 170, 255, 74, 51, 168, 140,
  206, 218, 125, 74, 239, 261, 122, 77, 126, 63, 129, 122, 165, 231, 80, 25, 99, 1, 11, 82, 65, 215, 128,
  120, 122, 209, 210, 144, 70, 263, 170, 163, 177, 144, 109, 194, 253, 55, 87, 253, 142, 112, 40, 267, 250, 71,
  141, 252, 193, 63, 73, 8, 121, 6, 90, 195, 69, 48, 157, 80, 150, 234, 180, 48, 169, 10, 1, 146, 260,
  70, 248, 256, 159, 94, 202, 158, 254, 176, 0, 14, 98, 220, 68, 222, 240, 182, 237, 267, 60, 36, 209, 203,
  229, 17, 211, 188, 186, 54, 159, 132, 275, 131, 140, 273, 90, 210, 51, 259, 85, 154, 192, 233, 262, 198, 70,
  137, 128, 111, 65, 88, 110, 215, 27, 66, 5, 185, 234, 276, 9, 216, 241, 41, 170, 255, 74, 51, 168, 140,
  206, 218, 125, 74, 239, 261, 122, 77, 126, 63, 129, 122, 165, 231, 80, 25, 99, 1, 11, 82, 65, 215, 128,
  120, 122, 209, 210, 144, 70, 263, 170, 163, 177, 144, 109, 194, 253, 55, 87, 253, 142, 112, 40, 267, 250, 71,
  141, 252, 193, 63, 73, 8, 121, 6, 90, 195, 69, 48, 157, 80, 150, 234, 180, 48, 169, 10, 1, 146, 260,
  70, 248, 256, 159, 94, 202, 158, 254, 176, 0, 14, 98, 220, 68, 222, 240, 182, 237, 267, 60, 36, 209, 203]

theorem firstF69_logarithms : rowOK firstF69 firstF69Row = true := by
  decide +kernel

/-- Finite-field parameters at 649843 for the conductor factor 3. -/
def secondF3 : Source := ⟨649843, 2, 3, 19495, 305637, 94892⟩

theorem secondF3_parameters : sourceOK secondF3 = true := by
  decide +kernel

def secondF3Row : List Nat := [
  19, 231, 165, 240, 101, 133, 187, 179, 13, 254, 227, 246, 33, 65, 22, 158, 265, 227, 77, 217, 115, 98, 67,
  163, 0, 136, 36, 124, 240, 6, 179, 115, 67, 218, 209, 25, 225, 214, 269, 54, 24, 19, 132, 253, 23, 144,
  258, 134, 203, 140, 177, 246, 1, 21, 212, 73, 49, 27, 158, 213, 42, 152, 108, 220, 10, 98, 194, 243, 21,
  132, 221, 159, 68, 141, 136, 253, 92, 231, 225, 118, 215, 110, 14, 58, 196, 109, 147, 109, 238, 199, 146, 253,
  165, 106, 124, 69, 102, 114, 195, 21, 191, 28, 192, 110, 182, 127, 197, 139, 54, 72, 147, 180, 263, 126, 84,
  120, 259, 45, 97, 190, 96, 210, 114, 173, 29, 22, 77, 226, 151, 89, 218, 75, 137, 37, 151, 158, 200, 55,
  258, 46, 112, 37, 176, 144, 90, 98, 264, 23, 50, 31, 244, 212, 255, 119, 12, 50, 200, 60, 162, 179, 210,
  114, 0, 141, 241, 153, 37, 271, 98, 162, 210, 59, 68, 252, 52, 63, 8, 223, 253, 258, 145, 24, 254, 133,
  19, 143, 74, 137, 100, 31, 276, 256, 65, 204, 228, 250, 119, 64, 235, 125, 169, 57, 267, 179, 83, 34, 256,
  145, 56, 118, 209, 136, 141, 24, 185, 46, 52, 159, 62, 167, 263, 219, 81, 168, 130, 168, 39, 78, 131, 24,
  112, 171, 153, 208, 175, 163, 82, 256, 86, 249, 85, 167, 95, 150, 80, 138, 223, 205, 130, 97, 14, 151, 193,
  157, 18, 232, 180, 87, 181, 67, 163, 104, 248, 255, 200, 51, 126, 188, 59, 202, 140, 240, 126, 119, 77, 222]

theorem secondF3_logarithms : rowOK secondF3 secondF3Row = true := by
  decide +kernel

/-- Finite-field parameters at 649843 for the conductor factor 23. -/
def secondF23 : Source := ⟨649843, 2, 23, 643757, 121828, 94892⟩

theorem secondF23_parameters : sourceOK secondF23 = true := by
  decide +kernel

def secondF23Row : List Nat := [
  197, 247, 60, 16, 207, 148, 23, 21, 23, 210, 76, 244, 62, 163, 108, 178, 83, 20, 136, 238, 231, 171, 241,
  208, 146, 193, 196, 215, 95, 80, 231, 201, 167, 168, 80, 35, 125, 204, 155, 233, 148, 224, 160, 148, 28, 224,
  16, 199, 134, 208, 248, 183, 32, 200, 103, 262, 190, 217, 194, 159, 65, 132, 268, 148, 124, 9, 90, 273, 83,
  276, 180, 141, 29, 68, 204, 87, 162, 171, 90, 129, 187, 38, 221, 147, 64, 58, 156, 66, 227, 220, 85, 70,
  118, 253, 164, 32, 162, 147, 93, 268, 134, 180, 140, 41, 199, 76, 84, 34, 47, 192, 104, 171, 70, 101, 110,
  147, 0, 221, 146, 168, 258, 262, 206, 62, 262, 68, 64, 150, 172, 152, 186, 179, 78, 28, 266, 27, 164, 40,
  80, 30, 217, 261, 70, 129, 254, 256, 254, 67, 201, 33, 215, 114, 169, 99, 194, 257, 141, 39, 46, 106, 36,
  69, 131, 84, 81, 62, 182, 197, 46, 76, 110, 109, 197, 242, 152, 73, 122, 44, 129, 53, 117, 129, 249, 53,
  261, 78, 143, 69, 29, 94, 245, 77, 174, 15, 87, 60, 83, 118, 212, 145, 9, 129, 153, 268, 187, 4, 194,
  1, 97, 136, 248, 209, 73, 190, 115, 106, 187, 148, 90, 239, 56, 130, 213, 219, 121, 211, 50, 57, 192, 207,
  159, 24, 113, 245, 115, 130, 184, 9, 143, 97, 137, 236, 78, 201, 193, 243, 230, 85, 173, 106, 207, 176, 167,
  130, 0, 56, 131, 109, 19, 15, 71, 215, 15, 209, 213, 127, 105, 125, 91, 98, 199, 249, 11, 250, 113, 237]

theorem secondF23_logarithms : rowOK secondF23 secondF23Row = true := by
  decide +kernel

/-- Finite-field parameters at 649843 for the conductor factor 69. -/
def secondF69 : Source := ⟨649843, 2, 69, 619636, 568053, 94892⟩

theorem secondF69_parameters : sourceOK secondF69 = true := by
  decide +kernel

def secondF69Row : List Nat := [
  22, 170, 30, 139, 269, 17, 15, 105, 240, 241, 106, 114, 66, 257, 234, 82, 98, 114, 262, 46, 152, 249, 124,
  247, 238, 216, 170, 48, 271, 167, 180, 24, 83, 164, 25, 194, 160, 115, 227, 173, 219, 26, 244, 0, 102, 85,
  98, 68, 231, 22, 182, 106, 249, 190, 186, 62, 275, 113, 189, 226, 100, 165, 151, 37, 199, 254, 126, 98, 37,
  182, 241, 196, 151, 176, 105, 139, 226, 213, 227, 176, 30, 14, 248, 132, 246, 51, 6, 162, 32, 208, 238, 181,
  85, 258, 244, 107, 95, 179, 241, 119, 152, 55, 132, 185, 265, 2, 171, 58, 92, 215, 65, 9, 180, 36, 100,
  271, 115, 19, 91, 211, 28, 232, 17, 185, 140, 256, 68, 124, 132, 25, 67, 111, 130, 251, 61, 238, 75, 24,
  22, 170, 30, 139, 269, 17, 15, 105, 240, 241, 106, 114, 66, 257, 234, 82, 98, 114, 262, 46, 152, 249, 124,
  247, 238, 216, 170, 48, 271, 167, 180, 24, 83, 164, 25, 194, 160, 115, 227, 173, 219, 26, 244, 0, 102, 85,
  98, 68, 231, 22, 182, 106, 249, 190, 186, 62, 275, 113, 189, 226, 100, 165, 151, 37, 199, 254, 126, 98, 37,
  182, 241, 196, 151, 176, 105, 139, 226, 213, 227, 176, 30, 14, 248, 132, 246, 51, 6, 162, 32, 208, 238, 181,
  85, 258, 244, 107, 95, 179, 241, 119, 152, 55, 132, 185, 265, 2, 171, 58, 92, 215, 65, 9, 180, 36, 100,
  271, 115, 19, 91, 211, 28, 232, 17, 185, 140, 256, 68, 124, 132, 25, 67, 111, 130, 251, 61, 238, 75, 24]

theorem secondF69_logarithms : rowOK secondF69 secondF69Row = true := by
  decide +kernel

/- All nontrivial even characters with nonzero exponent have s even for
f=1,69 and s odd for f=3,23. The f=1 circular unit is a ratio. Its Fourier
multiplier 5^(-s)-1 is nonzero exactly when 5^s differs from 1. -/
theorem prime_conductor_ratio_multiplier :
    (weights false).all (fun s => power 5 s p != 1) = true := by
  decide +kernel

theorem first_f1_exceptions : missing false firstF1Row = [] := by
  decide +kernel

theorem first_f3_exceptions : missing true firstF3Row = [115, 169] := by
  decide +kernel

theorem first_f23_exceptions : missing true firstF23Row = [87] := by
  decide +kernel

theorem first_f69_exceptions : missing false firstF69Row = [126] := by
  decide +kernel

theorem second_f3_witnesses :
    ([115, 169] : List Nat).map (fourier secondF3Row) = [45, 34] := by
  decide +kernel

theorem second_f23_witness : fourier secondF23Row 87 = 228 := by
  decide +kernel

theorem second_f69_witness : fourier secondF69Row 126 = 5 := by
  decide +kernel

/-- The exponent-zero character has true conductor 69, rather than 69*277. -/
def conductor69ZeroOK (ell g z h d : Nat) : Bool :=
  let b := products ell 69 1 1 68 z z
  let n := (ell - 1) / p
  ((ell - 1) % 69 == 0 && z == power g ((ell - 1) / 69) ell) &&
    h == power g n ell && b.1 != 0 && b.2 != 0 &&
    power b.1 n ell == (power h d ell * power b.2 n ell) % ell

theorem trivial_exponent_true_conductor :
    conductor69ZeroOK 114679 6 21767 49063 41 = true ∧ 0 < (41 : Nat) := by
  decide +kernel

/-- The first prime detects all but four characters. The second detects each
of the four, and the additional true-conductor test detects exponent zero. -/
theorem all_551_character_checks :
    2*(weights false).length + 2*(weights true).length + 1 = 551 ∧
    missing false firstF1Row = [] ∧
    (missing true firstF3Row).all (fun s => fourier secondF3Row s != 0) = true ∧
    (missing true firstF23Row).all (fun s => fourier secondF23Row s != 0) = true ∧
    (missing false firstF69Row).all (fun s => fourier secondF69Row s != 0) = true ∧
    conductor69ZeroOK 114679 6 21767 49063 41 = true := by
  refine ⟨?_, first_f1_exceptions, ?_, ?_, ?_, trivial_exponent_true_conductor.1⟩
  · decide +kernel
  · rw [first_f3_exceptions] <;> decide +kernel
  · rw [first_f23_exceptions] <;> decide +kernel
  · rw [first_f69_exceptions] <;> decide +kernel

/-- The exceptional weights use the real unit (25+3*sqrt(69))/2.
These are its two residues modulo 277 squared and their first Fermat quotients. -/
theorem boundary_unit_arithmetic :
    25^2 - 3^2*69 = 4 ∧
    26839^2 % (277^2) = 69 ∧ 49890^2 % (277^2) = 69 ∧
    26839 % 277 ≠ 49890 % 277 ∧
    (25 + 3*26839) % (277^2) = (2*40271) % (277^2) ∧
    (25 + 3*49890) % (277^2) = (2*36483) % (277^2) ∧
    power 40271 276 (277^2) = 1 + 58*277 ∧
    power 36483 276 (277^2) = 1 + 219*277 := by
  decide +kernel

private theorem reduced_base_in_product (u b k m : Nat) :
    u * (b % m)^k % m = u * b^k % m := by
  calc
    _ = u * ((b % m)^k % m) % m := (Nat.mul_mod_mod _ _ _).symm
    _ = u * (b^k % m) % m := by rw [← Nat.pow_mod b k m]
    _ = _ := Nat.mul_mod_mod _ _ _

/-- Once the accumulator is reduced, halving the exponent and squaring the base
preserves the residue of the accumulator times the remaining power. The strict
fuel bound ensures that the zero-exponent branch is reached. -/
private theorem powerLoop_invariant (m fuel base n acc : Nat)
    (hf : n < fuel) (ha : acc % m = acc) :
    powerLoop m fuel base n acc = acc * base^n % m := by
  induction fuel generalizing base n acc with
  | zero => omega
  | succ fuel ih =>
    by_cases hz : n = 0
    · subst n
      simp [powerLoop, ha]
    · have hhalf : n / 2 < fuel := by omega
      have hsplit := Nat.div_add_mod n 2
      rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · have hp : base^n = (base * base)^(n / 2) := by
          calc
            _ = base^(2 * (n / 2)) := congrArg (fun j => base^j) (by omega)
            _ = _ := by rw [Nat.pow_mul, Nat.pow_two]
        simp only [powerLoop, hz, he, Nat.zero_ne_one, ↓reduceIte]
        rw [ih _ _ _ hhalf ha, reduced_base_in_product, hp]
      · have hp : base^n = base * (base * base)^(n / 2) := by
          calc
            _ = base^(2 * (n / 2) + 1) := congrArg (fun j => base^j) (by omega)
            _ = base^(2 * (n / 2)) * base := Nat.pow_succ _ _
            _ = _ := by rw [Nat.pow_mul, Nat.pow_two, Nat.mul_comm ((base*base)^(n/2)) base]
        simp only [powerLoop, hz, ho, ↓reduceIte]
        rw [ih _ _ _ hhalf (Nat.mod_mod _ _), reduced_base_in_product,
          Nat.mod_mul_mod, Nat.mul_assoc, hp]

/-- The executable binary routine computes ordinary exponentiation followed by
reduction for all natural inputs, including exponent zero and modulus zero. -/
theorem power_eq_pow_mod (a n m : Nat) : power a n m = a^n % m := by
  unfold power
  rw [powerLoop_invariant _ _ _ _ _ (by omega) (Nat.mod_mod _ _),
    reduced_base_in_product, Nat.mod_mul_mod, Nat.one_mul]

/-- At the true conductor 69, evaluate the positive and negative products in
the very same order as the zero-exponent witness. -/
theorem true69_signed_products :
    products 114679 69 1 1 68 21767 21767 = (48891, 65813) := by
  decide +kernel

/-- Label the square root so the positive product is the reduction of
(25 + 3 sqrt(69))/2. The second equality labels its conjugate. -/
theorem true69_quadratic_residues :
    70812^2 % 114679 = 69 ∧
    (25 + 3 * 70812) % 114679 = (2 * 48891) % 114679 ∧
    (25 + 3 * (114679 - 70812)) % 114679 = (2 * 65813) % 114679 ∧
    (48891 * 65813) % 114679 = 1 := by
  decide +kernel

/-- In the 277-order subgroup at 114679, the positive product has coordinate
159 and its conjugate has coordinate 118. Their difference is 41 modulo 277. -/
theorem true69_individual_logarithms :
    (114679 - 1) / 277 = 414 ∧
    power 48891 414 114679 = 74194 ∧ power 49063 159 114679 = 74194 ∧
    power 65813 414 114679 = 5365 ∧ power 49063 118 114679 = 5365 ∧
    (74194 : Nat) ≠ 1 ∧ (159 + 277 - 118) % 277 = 41 ∧
    2 * 159 % 277 = 41 := by
  decide +kernel

/-- The auxiliary residue meets each of the three power hypotheses of the
primitive-root calculation in the field of order 114679. -/
theorem true69_auxiliary_root_orders :
    21767^69 % 114679 = 1 ∧ 21767^23 % 114679 ≠ 1 ∧
    21767^3 % 114679 ≠ 1 := by
  decide +kernel

end ReimannWindow.CircularUnits

