import Std

namespace Reimann.Foundation

/-- The signed prime weight in the previous formal checkpoint. -/
theorem character_filter (u v : Int) :
    1 + v - u - u * v = (1 + v) * (1 - u) := by
  grind

/-- All four unramified sign choices, in the order (+,+), (+,-), (-,+), (-,-)
    of (v,u). -/
theorem sign_table :
    ([(1,1),(1,-1),(-1,1),(-1,-1)] : List (Int × Int)).map
      (fun t => (1 + t.1) * (1 - t.2)) = [0,4,0,0] := by decide

/-- The weight and reflected weight add to a full tame period minus one. -/
theorem mirror_index_add (p r : Nat) (h : r + 1 ≤ p) :
    (p - 1 - r) + r + 1 = p := by omega

end Reimann.Foundation
