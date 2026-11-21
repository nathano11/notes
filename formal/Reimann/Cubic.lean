import Std

/-!
# Finite arithmetic for the cubic example

The closed theorems use Lean kernel reduction. The exhaustive reduced-ideal
enumerations are executable checks at the end of the file. The passage from
these certificates to ideal class groups and strict cohomology uses the
number-theoretic results identified in the accompanying proof.
-/

namespace Reimann.Cubic

/-- Coordinates on the basis 1, x, x² for x³ = 164x - 801. -/
structure CubicCoordinates where
  c0 : Int
  c1 : Int
  c2 : Int
  deriving DecidableEq, Repr

private def add (p q : CubicCoordinates) : CubicCoordinates :=
  ⟨p.c0 + q.c0, p.c1 + q.c1, p.c2 + q.c2⟩

private def sub (p q : CubicCoordinates) : CubicCoordinates :=
  ⟨p.c0 - q.c0, p.c1 - q.c1, p.c2 - q.c2⟩

/-- Multiply two degree-two representatives and reduce x³ and x⁴. -/
def mul (p q : CubicCoordinates) : CubicCoordinates :=
  let c3 := p.c1*q.c2 + p.c2*q.c1
  let c4 := p.c2*q.c2
  ⟨p.c0*q.c0 - 801*c3,
   p.c0*q.c1 + p.c1*q.c0 + 164*c3 - 801*c4,
   p.c0*q.c2 + p.c1*q.c1 + p.c2*q.c0 + 164*c4⟩

def xCoord : CubicCoordinates := ⟨0, 1, 0⟩
def xSq : CubicCoordinates := ⟨0, 0, 1⟩
def unitU : CubicCoordinates := ⟨-6546564915489, 518244484752, 65084790424⟩
def unitW : CubicCoordinates := ⟨961424555660, -76109400788, -9558264431⟩

/-- For y²+xy+x²-164=0, Norm(U+Wy) = U² - xUW + (x²-164)W². -/
def relativeNorm : CubicCoordinates :=
  add (sub (mul unitU unitU) (mul xCoord (mul unitU unitW)))
      (mul ⟨-164, 0, 1⟩ (mul unitW unitW))

theorem norm_remainder :
    relativeNorm = ⟨-99597647, 27096052, -1831220⟩ := by decide

/-- Determinant of multiplication by p in the monic cubic quotient. -/
def resultant (p : CubicCoordinates) : Int :=
  let q := mul p xCoord
  let r := mul p xSq
  p.c0 * (q.c1*r.c2 - q.c2*r.c1)
    - q.c0 * (p.c1*r.c2 - p.c2*r.c1)
    + r.c0 * (p.c1*q.c2 - p.c2*q.c1)

theorem absolute_norm_one : resultant relativeNorm = 1 := by decide

theorem cubic_discriminant :
    (4 : Int)*164^3 - 27*801^2 = 19*16871 := by decide

/-- Exhaust all trial divisors up to the square roots of the two discriminant factors. -/
theorem discriminant_factors_trial_division :
    4^2 ≤ 19 ∧ 19 < 5^2 ∧ 129^2 ≤ 16871 ∧ 16871 < 130^2 ∧
    (List.range 3).all (fun k => 19 % (k+2) != 0) = true ∧
    (List.range 128).all (fun k => 16871 % (k+2) != 0) = true := by decide

/-- A cubic has no linear factor modulo 5 if none of its residues is a root. -/
theorem no_root_mod_five :
    (List.range 5).all (fun n => ((n : Int)^3 - 164*(n : Int) + 801) % 5 != 0) = true := by
  decide

/-- Pairs represent a+bs with s²=2. Reductions modulo 9 are componentwise. -/
private def qAdd (p q : Int × Int) : Int × Int := (p.1+q.1, p.2+q.2)

private def qMul (p q : Int × Int) : Int × Int :=
  (p.1*q.1 + 2*p.2*q.2, p.1*q.2 + p.2*q.1)

private def qEval (p : CubicCoordinates) (t : Int × Int) : Int × Int :=
  qAdd (p.c0, 0) (qMul t (qAdd (p.c1, 0) (qMul t (p.c2, 0))))

def etaAt (x y : Int × Int) : Int × Int :=
  let z := qAdd (qEval unitU x) (qMul y (qEval unitW x))
  (z.1 % 9, z.2 % 9)

def localValues : List (Int × Int) :=
  [etaAt (0,0) (0,1), etaAt (0,1) (0,0), etaAt (0,1) (0,-1)]

theorem unit_residues : localValues = [(0,8),(8,0),(0,5)] := by decide

def localNorm (z : Int × Int) : Int := (z.1^2 - 2*z.2^2) % 9

theorem norm_residues : localValues.map localNorm = [7,1,4] := by decide

theorem norm_coordinates :
    ([2,0,1] : List Nat).map (fun n => (4 : Int)^n % 9) = localValues.map localNorm := by
  decide

/-- First two column minor of the rows (2,0,1) and (1,2,0). -/
theorem norm_coordinate_minor : ((2 : Int)*2 - 0*1) % 3 = 1 := by decide

/-- A linear combination of the rotated rows vanishes only for zero coefficients. -/
theorem local_rows_independent :
    ∀ a b : Fin 3,
      ((2*a.val + b.val) % 3 = 0 ∧ (2*b.val) % 3 = 0 ∧ a.val % 3 = 0) →
      a.val = 0 ∧ b.val = 0 := by decide

/-- A positive Pell solution for 641098; the witness is sufficient. -/
def pellU : Nat :=
  5483528512481796002932817388783300448702602025317638976164055091151016357200743701762140077205768601812289338444056006607390961749137637905744453646083383533943278301048998735798062531462269933550685914518807743

def pellV : Nat :=
  6848538396322087506059386495669389958255370805896335047636797958030601500379525998536364982767843382150527987810254606456228298099418805688612938691704757665131829945758948413325670624324749027177144451319576

theorem pell_certificate :
    pellU^2 = 641098*pellV^2 + 1 ∧ pellU % 9 = 8 ∧ pellV % 9 = 3 := by decide

theorem split_unit_residues :
    641098 % 9 = 1 ∧ (pellU + pellV) % 9 = 2 ∧ (pellU + 8*pellV) % 9 = 5 := by decide

/-- A reduced-ideal pair is recorded as (Q,P). All bounds use floor √Δ. -/
abbrev ReducedPair := Nat × Nat

def isReduced (d h : Nat) (v : ReducedPair) : Bool :=
  let (q,p) := v
  decide (0 < p ∧ p ≤ h ∧ 0 < q ∧ q % 2 = 0 ∧ h < q+p ∧ q ≤ h+p ∧
    (d-p*p) % (2*q) = 0)

def successor (d h : Nat) (v : ReducedPair) : ReducedPair :=
  let (q,p) := v
  let nextP := ((h+p) / q) * q - p
  ((d-nextP*nextP) / q, nextP)

/-- Check every point of a proposed orbit, including the first return and minimum. -/
def verifyOrbit (d h len : Nat) (start : ReducedPair) : Bool := Id.run do
  if len == 0 then return false
  let mut state := start
  for i in [0:len] do
    if !(isReduced d h state) then return false
    if i != 0 && state == start then return false
    if state.1 < start.1 ∨ (state.1 = start.1 ∧ state.2 < start.2) then return false
    state := successor d h state
  return state == start

/-- Count eligible even denominators in one row of the reduced interval. -/
def countEvenDenominators (numerator lo : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => countEvenDenominators numerator lo i +
      (if numerator % (4*(lo+i)) = 0 then 1 else 0)

def countReducedRows (d h : Nat) : Nat → Nat
  | 0 => 0
  | p+1 =>
      let currentP := p+1
      let numerator := d-currentP*currentP
      let lo := (h-currentP)/2 + 1
      let len := (h+currentP)/2 + 1 - lo
      countReducedRows d h p + (if numerator % 4 = 0 then
        countEvenDenominators numerator lo len else 0)

def reducedCount (d h : Nat) : Nat := countReducedRows d h h

theorem row_divisibility_necessity {n a : Nat} (h : n % (4*a) = 0) : n % 4 = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_right 4 a) (Nat.dvd_of_mod_eq_zero h))

theorem reduced_even_denominator (d h p a : Nat) (hp : 0 < p) (hp' : p ≤ h) :
    isReduced d h (2*a,p) = true ↔
      (h-p)/2 + 1 ≤ a ∧ a ≤ (h+p)/2 ∧ (d-p*p) % (4*a) = 0 := by
  simp only [isReduced, decide_eq_true_eq]
  have he : 2*(2*a) = 4*a := by omega
  rw [he]
  omega

structure CycleData where
  discriminant : Nat
  rootFloor : Nat
  orbits : List (Nat × ReducedPair)

def cycleData : List CycleData := [
  ⟨8, 2, [(1,(2,2))]⟩,
  ⟨57, 7, [(6,(2,7))]⟩,
  ⟨456, 21, [(6,(2,20)),(10,(6,18))]⟩,
  ⟨50613, 224, [(4,(2,223)),(6,(26,219)),(6,(26,223)),(8,(38,205)),(8,(38,213))]⟩,
  ⟨320549, 566, [(36,(2,565)),(36,(10,557)),(36,(10,563))]⟩,
  ⟨404904, 636, [(168,(2,636)),(148,(4,636))]⟩,
  ⟨2564392, 1601, [(424,(2,1600)),(400,(4,1600))]⟩
]

def verifyCycles (data : CycleData) : Bool :=
  let h := data.rootFloor
  let d := data.discriminant
  let orbits := data.orbits
  decide (h^2 < d ∧ d < (h+1)^2) &&
  decide ((orbits.map Prod.snd).Nodup) &&
  orbits.all (fun o => verifyOrbit d h o.1 o.2) &&
  reducedCount d h == (orbits.map Prod.fst).sum

/-- Evaluate the complete check for a single discriminant. -/
def certificateAt (d : Nat) : Bool :=
  cycleData.any (fun row => row.discriminant == d && verifyCycles row)

/- Independent build breakpoints, in increasing order of enumeration cost. -/
#guard certificateAt 8
#guard certificateAt 57
#guard certificateAt 456
#guard certificateAt 50613
#guard certificateAt 320549
#guard certificateAt 404904
#guard certificateAt 2564392

end Reimann.Cubic
