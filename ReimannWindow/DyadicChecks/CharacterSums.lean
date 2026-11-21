import Std

namespace ReimannWindow.DyadicChecks

/- Finite arithmetic at weight one. The interpolation identity which turns
these numbers into values of a 2-adic characteristic polynomial is a
separate arithmetic input. All divisions in the final statements are
cleared over the integers. -/

def primeSign (b p : Nat) : Int :=
  let v := ((b % p) ^ ((p - 1) / 2)) % p
  if v = 0 then 0 else if v = 1 then 1 else -1

def sign69 (b : Nat) : Int := primeSign b 3 * primeSign b 23

def sign8 (b : Nat) : Int :=
  match b % 8 with
  | 1 | 7 => 1
  | 3 | 5 => -1
  | _ => 0

def sign552 (b : Nat) : Int := sign69 b * sign8 b

/-- Sum over b = 1,...,f, tracking the zeroth, first and second moments. -/
def moments (f : Nat) (χ : Nat → Int) : Int × Int × Int :=
  (List.range f).foldl (fun acc i =>
    let b := i + 1
    let z : Int := Int.ofNat b
    let c := χ b
    (acc.1 + c, acc.2.1 + c * z, acc.2.2 + c * z * z)) (0, 0, 0)

theorem eulerFactors : (1 - 2 * sign69 2, 1 - 2 * sign552 2) = (3, 1) := by
  decide
-- breakpoint eulerFactors

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem conductor69Moments : moments 69 sign69 = (0, 0, 3312) := by
  decide
-- breakpoint conductor69Moments

theorem conductor552Moments : moments 552 sign552 = (0, 0, 680064) := by
  decide
-- breakpoint conductor552Moments

theorem normalized69 :
    -(1 - 2 * sign69 2) * (moments 69 sign69).2.2 = (4 * 69 : Int) * (-36) := by
  have h := congrArg Prod.fst eulerFactors
  change 1 - 2 * sign69 2 = 3 at h
  rw [h, conductor69Moments] <;> decide
-- breakpoint normalized69

theorem normalized552 :
    -(1 - 2 * sign552 2) * (moments 552 sign552).2.2 = (4 * 552 : Int) * (-308) := by
  have h := congrArg Prod.snd eulerFactors
  change 1 - 2 * sign552 2 = 1 at h
  rw [h, conductor552Moments] <;> decide
-- breakpoint normalized552

theorem normalizedResidues : ((-36 : Int) % 8, (-308 : Int) % 8) = (4, 4) := by
  decide
-- breakpoint normalizedResidues

end ReimannWindow.DyadicChecks
