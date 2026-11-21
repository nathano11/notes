import Std

namespace ReimannWindow.Baseline

/-- The sign filter from the original formal checkpoint, over all integers. -/
theorem character_filter (u v : Int) :
    1 + v - u - u * v = (1 + v) * (1 - u) := by
  rw [Int.mul_sub, Int.mul_one, Int.add_mul, Int.one_mul, Int.mul_comm v u]
  omega

theorem filter_minus_plus : (1 + (1 : Int)) * (1 - (-1)) = 4 := by decide

theorem filter_minus_minus : (1 + (-1 : Int)) * (1 - (-1)) = 0 := by decide

theorem filter_plus_plus : (1 + (1 : Int)) * (1 - 1) = 0 := by decide

theorem filter_plus_minus : (1 + (-1 : Int)) * (1 - 1) = 0 := by decide

def cubic (x : Int) : Int := x ^ 3 - 164 * x + 801

theorem cubic_discriminant : -(4 : Int) * (-164)^3 - 27 * 801^2 =
    19 * 16871 := by decide

theorem cubic_mod_five : ([0, 1, 2, 3, 4] : List Int).map (fun x => cubic x % 5) =
    [1, 3, 1, 1, 4] := by decide

theorem norm_product : (7 * 1 * 4 : Nat) % 9 = 1 := by decide

theorem unit_cubes : ([1, 2, 4, 5, 7, 8] : List Nat).map (fun x => x^3 % 9) =
    [1, 8, 1, 8, 1, 8] := by decide

end ReimannWindow.Baseline
