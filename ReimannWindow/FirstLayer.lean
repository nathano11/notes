import Std

/-!
# Integer certificates for the first dyadic layer

For each discriminant the checks count *every* reduced pair, then follow the
indicated cycles. Each cycle returns to its starting point for the first time
at its stated length, and its starting point is its lexicographic minimum.
Different certified minima therefore give disjoint cycles. Equality of the
point count with the sum of the lengths certifies exhaustion. The connection
between reduced-ideal cycles and ordinary ideal classes is arithmetic input
outside this file. The final theorem certifies a unit using the Pell equation.
-/

namespace ReimannWindow.FirstLayer

set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-- Coordinates are ordered as (denominator Q, numerator offset P). -/
abbrev ReducedPair := Nat × Nat

def isReduced (D h : Nat) (point : ReducedPair) : Bool :=
  let (q, p) := point
  decide (0 < p ∧ p ≤ h ∧ 0 < q ∧ q % 2 = 0 ∧
    h + 1 ≤ q + p ∧ q ≤ h + p ∧ (D - p * p) % (2 * q) = 0)

def successor (D h : Nat) (point : ReducedPair) : ReducedPair :=
  let (q, p) := point
  let newP := ((h + p) / q) * q - p
  ((D - newP * newP) / q, newP)

def lexLess (a b : ReducedPair) : Bool :=
  decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))

/-- The first point is checked separately. Every intermediate point must be
strictly larger than the seed, including in the last step before returning. -/
def followsCycle (D h : Nat) (seed : ReducedPair) :
    Nat → ReducedPair → Bool
  | 0, current => current == seed
  | n + 1, current =>
    isReduced D h current && lexLess seed current &&
      followsCycle D h seed n (successor D h current)

structure Cycle where
  q : Nat
  p : Nat
  length : Nat

def checkCycle (D h : Nat) (cycle : Cycle) : Bool :=
  let seed := (cycle.q, cycle.p)
  match cycle.length with
  | 0 => false
  | n + 1 => isReduced D h seed &&
    followsCycle D h seed n (successor D h seed)

/-- Count divisors of target in [low, low + count), visiting each once. -/
def countDivisors (target low : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | count + 1, acc =>
    let acc' := if target % (low + count) = 0 then acc + 1 else acc
    countDivisors target low count acc'

/-- At fixed P and Q = 2k the divisibility test is 4k ∣ D - P².
The inequality h + 1 - P ≤ Q ≤ h + P gives the closed range for k.
The outer loop covers P from h down to 1. -/
def countReducedRows (D h : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | p + 1, acc =>
    let offset := p + 1
    let remainder := D - offset * offset
    let low := (h + 2 - offset) / 2
    let high := (h + offset) / 2
    let rowCount := if remainder % 4 = 0 then
        countDivisors (remainder / 4) low (high + 1 - low) 0
      else 0
    rowCount + countReducedRows D h p acc

def distinctSeeds : List Cycle → Bool
  | [] => true
  | c :: cs => cs.all (fun z => z.q != c.q || z.p != c.p) && distinctSeeds cs

def checkTable (D h : Nat) (cycles : List Cycle) : Bool :=
  decide (h * h < D ∧ D < (h + 1) * (h + 1)) &&
    distinctSeeds cycles && cycles.all (checkCycle D h) &&
    (countReducedRows D h h 0 == (cycles.map Cycle.length).sum)

theorem cycles8 : checkTable 8 2 [⟨2, 2, 1⟩] = true := by decide
theorem cycles57 : checkTable 57 7 [⟨2, 7, 6⟩] = true := by decide
theorem cycles456 : checkTable 456 21 [⟨2, 20, 6⟩, ⟨6, 18, 10⟩] = true := by decide
theorem cycles50613 : checkTable 50613 224
    [⟨2, 223, 4⟩, ⟨26, 219, 6⟩, ⟨26, 223, 6⟩,
     ⟨38, 205, 8⟩, ⟨38, 213, 8⟩] = true := by decide
theorem cycles320549 : checkTable 320549 566
    [⟨2, 565, 36⟩, ⟨10, 557, 36⟩, ⟨10, 563, 36⟩] = true := by decide
theorem cycles404904 : checkTable 404904 636
    [⟨2, 636, 168⟩, ⟨4, 636, 148⟩] = true := by decide
theorem cycles2564392 : checkTable 2564392 1601
    [⟨2, 1600, 424⟩, ⟨4, 1600, 400⟩] = true := by decide

def pellX : Nat :=
  5483528512481796002932817388783300448702602025317638976164055091151016357200743701762140077205768601812289338444056006607390961749137637905744453646083383533943278301048998735798062531462269933550685914518807743

def pellY : Nat :=
  6848538396322087506059386495669389958255370805896335047636797958030601500379525998536364982767843382150527987810254606456228298099418805688612938691704757665131829945758948413325670624324749027177144451319576

/-- The Pell equation certifies norm +1. Sending √641098 to ±1 mod 9
gives the two residues. Addition by 8y represents subtraction modulo 9. -/
theorem pellCertificate :
    pellX * pellX = 641098 * pellY * pellY + 1 ∧
    641098 % 9 = 1 ∧ pellX % 9 = 8 ∧ pellY % 9 = 3 ∧
    (pellX + pellY) % 9 = 2 ∧ (pellX + 8 * pellY) % 9 = 5 := by decide

end ReimannWindow.FirstLayer
