import Std

/-!
# Integer certificates for the unit in the bottom cubic example

Polynomials below are lists of coefficients in ascending degree. The closed
checks cover the product with the conjugate, exact division by the monic
cubic, the Sylvester determinant, and evaluation in (ℤ/9)[s]/(s²−2).
They make no assertions about splitting fields, completions, or class groups.
-/

namespace ReimannWindow.BottomUnit

set_option maxRecDepth 8192
set_option maxHeartbeats 0

abbrev Coeffs := List Int

private def coef : Coeffs → Nat → Int
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: tail, n + 1 => coef tail n

private def trim (p : Coeffs) : Coeffs :=
  (p.reverse.dropWhile (fun a => a == 0)).reverse

private def add (p q : Coeffs) : Coeffs :=
  trim ((List.range (max p.length q.length)).map (fun k => coef p k + coef q k))

private def neg (p : Coeffs) : Coeffs := p.map (fun a => -a)
private def sub (p q : Coeffs) : Coeffs := add p (neg q)

private def mul (p q : Coeffs) : Coeffs :=
  trim ((List.range (p.length + q.length - 1)).map (fun k =>
    ((List.range (k + 1)).map (fun i => coef p i * coef q (k - i))).sum))

def cubic : Coeffs := [801, -164, 0, 1]
def unitU : Coeffs := [-6546564915489, 518244484752, 65084790424]
def unitV : Coeffs := [961424555660, -76109400788, -9558264431]
private def xPoly : Coeffs := [0, 1]
private def quadraticConstant : Coeffs := [-164, 0, 1]

/-- The pair (a,b) represents a(x)+b(x)y. Multiplication substitutes
y² = −xy−x²+164. -/
private def mulOverX (z w : Coeffs × Coeffs) : Coeffs × Coeffs :=
  let b := mul z.2 w.2
  (sub (mul z.1 w.1) (mul quadraticConstant b),
   sub (add (mul z.1 w.2) (mul z.2 w.1)) (mul xPoly b))

def normPolynomial : Coeffs :=
  add (sub (mul unitU unitU) (mul xPoly (mul unitU unitV)))
    (mul quadraticConstant (mul unitV unitV))

/-- The conjugate uses the other quadratic root −x−y. The y coefficient
vanishes already over ℤ[x]. -/
theorem relativeNormProduct :
    mulOverX (unitU, unitV) (sub unitU (mul xPoly unitV), neg unitV)
      = (normPolynomial, []) := by decide

theorem expandedRelativeNorm :
    normPolynomial =
      [-108733784708357166125729279, 23509476503528898084476524,
       1408422142835565902108844, -403203262726422587471471,
       -13426455914314174044780, 2077045194142136152000, 91360418932919753761] := by
  decide

def normQuotient : Coeffs :=
  [-135747546452380981306032, 1556652790684665572024,
   2077045194142136152000, 91360418932919753761]

def normRemainder : Coeffs := [-99597647, 27096052, -1831220]

theorem monicDivision :
    normPolynomial = add (mul cubic normQuotient) normRemainder ∧
    normRemainder.length < cubic.length ∧ cubic.reverse.head? = some 1 := by decide

/-- Expansion in the first row of an n-by-n integer matrix. -/
private def determinant : Nat → List Coeffs → Int
  | 0, _ => 1
  | n + 1, matrix =>
    let row := matrix.headD []
    ((List.range (n + 1)).map (fun k =>
      let minor := (matrix.drop 1).map (fun r => r.take k ++ r.drop (k + 1))
      let sign : Int := if k % 2 = 0 then 1 else -1
      sign * coef row k * determinant n minor)).sum

/-- Two shifts of the cubic, then three shifts of the quadratic, with
highest-degree coefficients first. -/
def sylvesterMatrix : List Coeffs :=
  let f := cubic.reverse
  let g := normRemainder.reverse
  [f ++ [0], 0 :: f, g ++ [0, 0], 0 :: (g ++ [0]), 0 :: 0 :: g]

theorem resultantOne : determinant 5 sylvesterMatrix = 1 := by decide

abbrev ResiduePair := Int × Int

private def qAdd (v w : ResiduePair) : ResiduePair :=
  ((v.1 + w.1) % 9, (v.2 + w.2) % 9)

private def qMul (v w : ResiduePair) : ResiduePair :=
  ((v.1 * w.1 + 2 * v.2 * w.2) % 9, (v.1 * w.2 + v.2 * w.1) % 9)

private def evaluate (p : Coeffs) (v : ResiduePair) : ResiduePair :=
  p.foldr (fun a acc => qAdd (a, 0) (qMul v acc)) (0, 0)

private def s : ResiduePair := (0, 1)
private def negS : ResiduePair := (0, 8)

theorem localCubicFactorization :
    cubic.map (fun c => c % 9) = (mul xPoly [-2, 0, 1]).map (fun c => c % 9) := by decide

theorem threeLocalRoots :
    qMul s s = (2, 0) ∧ evaluate cubic (0, 0) = (0, 0) ∧
    evaluate cubic s = (0, 0) ∧ evaluate cubic negS = (0, 0) := by decide

def etaAt (x y : ResiduePair) : ResiduePair :=
  qAdd (evaluate unitU x) (qMul (evaluate unitV x) y)

def localNorm (v : ResiduePair) : Int := (v.1 * v.1 - 2 * v.2 * v.2) % 9

theorem etaAtZeroS : etaAt (0, 0) s = (0, 8) := by decide
theorem etaAtSZero : etaAt s (0, 0) = (8, 0) := by decide
theorem etaAtSNegS : etaAt s negS = (0, 5) := by decide

theorem normAtZeroS : localNorm (etaAt (0, 0) s) = 7 := by decide
theorem normAtSZero : localNorm (etaAt s (0, 0)) = 1 := by decide
theorem normAtSNegS : localNorm (etaAt s negS) = 4 := by decide

structure LogVector where
  a : Nat
  b : Nat
  c : Nat

def logs : LogVector := ⟨2, 0, 1⟩
private def rotate (v : LogVector) : LogVector := ⟨v.c, v.a, v.b⟩

theorem cubicLogCoordinates :
    (4 : Int) ^ logs.a % 9 = localNorm (etaAt (0, 0) s) ∧
    (4 : Int) ^ logs.b % 9 = localNorm (etaAt s (0, 0)) ∧
    (4 : Int) ^ logs.c % 9 = localNorm (etaAt s negS) := by decide

private def firstMinor (v w : LogVector) : Int :=
  (v.a : Int) * (w.b : Int) - (v.b : Int) * (w.a : Int)

theorem rotationMinor : firstMinor logs (rotate logs) % 3 = 1 := by decide

end ReimannWindow.BottomUnit
