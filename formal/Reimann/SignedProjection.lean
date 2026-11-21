import Std

/-! The distribution relation for the integer first character moments
used by the finite Stickelberger rows. -/
namespace Reimann.SignedProjection

/-- Sum over one block with indices from zero through `n-1`. -/
def total (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => total f n + f n

theorem total_append (f : Nat → Int) (m n : Nat) :
    total f (m+n) = total f m + total (fun k => f (m+k)) n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    change total f (m+n) + f (m+n) = total f m + (total (fun k => f (m+k)) n + f (m+n))
    rw [ih, Int.add_assoc]

theorem total_pairs (f : Nat → Int) (n : Nat) :
    total f (2*n) = total (fun k => f (2*k)) n + total (fun k => f (2*k+1)) n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega]
    change (total f (2*n) + f (2*n)) + f (2*n+1) = (total (fun k => f (2*k)) n + f (2*n)) + (total (fun k => f (2*k+1)) n + f (2*n+1))
    rw [ih]
    omega

theorem total_affine (f g : Nat → Int) (a b : Int) (n : Nat) :
    total (fun k => a*f k + b*g k) n = a * total f n + b * total g n := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp only [total, ih]; grind

/-- The coefficient numerator has the opposite sign of this first moment. -/
def moment (f : Nat → Int) (n : Nat) : Int := total (fun k => (k:Int)*f k) n

theorem moment_two_blocks (f : Nat → Int) (m : Nat)
    (period : ∀ k, f (m+k) = f k) (zeroSum : total f m = 0) :
    moment f (2*m) = 2 * moment f m := by
  unfold moment
  rw [show 2*m = m+m by omega, total_append]
  have shift : (fun k : Nat => ((m+k : Nat) : Int)*f (m+k)) =
      (fun k => (m:Int)*f k + 1*((k:Int)*f k)) := by
    funext k
    rw [period, Int.natCast_add]
    grind
  rw [shift, total_affine, zeroSum]
  omega

theorem moment_two_fibres (f : Nat → Int) (m : Nat)
    (zeroOdd : total (fun k => f (2*k+1)) m = 0) :
    moment f (2*m) = 2 * (moment (fun k => f (2*k)) m + moment (fun k => f (2*k+1)) m) := by
  unfold moment
  rw [total_pairs]
  have evenForm : (fun k : Nat => ((2*k : Nat) : Int)*f (2*k)) =
      (fun k : Nat => 2*((k:Int)*f (2*k)) + 0*f (2*k)) := by
    funext k
    simp [Int.mul_assoc]
  have oddForm : (fun k : Nat => ((2*k+1 : Nat) : Int)*f (2*k+1)) =
      (fun k : Nat => 2*((k:Int)*f (2*k+1)) + 1*f (2*k+1)) := by
    funext k
    simp [Int.add_mul, Int.mul_assoc]
  rw [evenForm, oddForm, total_affine, total_affine, zeroOdd]
  dsimp only
  omega

/-- Each negative first moment splits into the two child moments exactly. -/
theorem moment_refine (f : Nat → Int) (m : Nat)
    (period : ∀ k, f (m+k) = f k) (zeroSum : total f m = 0)
    (zeroOdd : total (fun k => f (2*k+1)) m = 0) :
    -moment f m = -moment (fun k => f (2*k)) m - moment (fun k => f (2*k+1)) m := by
  have h := (moment_two_blocks f m period zeroSum).symm.trans (moment_two_fibres f m zeroOdd)
  omega

/-- Pair a=t+Dk with M-a in the inverse-generator fibre of an even character.
After the mod-four sign twist their weighted contributions have opposite signs.
Division by 2M gives the normalized finite coefficient. -/
theorem paired_numerator (f : Nat → Int) (m : Nat) (t D M : Int)
    (zeroSum : total f m = 0) :
    total (fun k : Nat => ((M-(t+D*k))-(t+D*k))*f k) m = -2*D*moment f m := by
  have shape : (fun k : Nat => ((M-(t+D*k))-(t+D*k))*f k) =
      (fun k : Nat => (M-2*t)*f k + (-2*D)*((k:Int)*f k)) := by
    funext k
    grind
  rw [shape, total_affine, zeroSum]
  simp [moment]

/-- If the negative moment equals m times the integral row coefficient, the
paired raw numerator equals 2Dm times that coefficient before any division. -/
theorem paired_normalization (f : Nat → Int) (m : Nat) (t D coeff : Int)
    (zeroSum : total f m = 0) (momentEq : -moment f m = (m:Int)*coeff) :
    total (fun k : Nat => ((D*m-(t+D*k))-(t+D*k))*f k) m =
      2*(D*m)*coeff := by
  rw [paired_numerator f m t D (D*m) zeroSum]
  calc
    _ = 2*D*(-moment f m) := by grind
    _ = _ := by rw [momentEq]; grind

end Reimann.SignedProjection
