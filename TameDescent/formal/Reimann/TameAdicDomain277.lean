import Reimann.TameLimit277
import Reimann.TameTwist277
import Reimann.TameRootExhaustion277

namespace Reimann.TameAdicDomain277

open Reimann.TameLimit277

theorem nonzero_digit_coprime : ∀ j : Fin 277, j.val ≠ 0 →
    Int.gcd (j.val : Int) 277 = 1 := by decide +kernel

theorem unit_at_all_depths (x : Int) (hx : ¬ (277 : Int) ∣ x) (n : Nat) :
    ∃ i j : Int, x*i + (277 : Int)^n*j = 1 := by
  obtain ⟨r,c,hc⟩ := TameRootExhaustion277.digit_representative x
  have hn : r.val ≠ 0 := by
    intro hr
    apply hx
    exact ⟨c,by simpa [hr] using hc⟩
  obtain ⟨i,j,h⟩ := ScalarCoinvariants.int_gcd_bezout (r.val : Int) 277
  rw [nonzero_digit_coprime r hn] at h
  apply TameTwist277.lift_bezout 277 x i (j-c*i) n
  change (1 : Int) = _ at h
  grind

theorem cancel_nonzero_digit (x y : Int) (hx : ¬ (277 : Int) ∣ x) (n : Nat)
    (h : (277 : Int)^n ∣ x*y) : (277 : Int)^n ∣ y := by
  obtain ⟨i,j,hi⟩ := unit_at_all_depths x hx n
  obtain ⟨k,hk⟩ := h
  exact ⟨i*k+j*y, by grind⟩

theorem peel_factor (n : Nat) (x y : Int) (h : modulus (n+1) ∣ (277*x)*y) :
    modulus n ∣ x*y := by
  have he : modulus (n+1) = 277*modulus n := by
    unfold modulus
    rw [Int.pow_succ (277 : Int) (n+1),Int.mul_comm]
  rw [he,Int.mul_assoc] at h
  exact (Int.mul_dvd_mul_iff_left (by decide : (277 : Int) ≠ 0)).mp h

/-- Vanishing of a product at precision 277^(i+j+1) forces a factor
to vanish at one of the two prescribed lower precisions. -/
theorem product_precision (i j : Nat) (x y : Int)
    (h : modulus (i+j) ∣ x*y) : modulus i ∣ x ∨ modulus j ∣ y := by
  induction i generalizing x with
  | zero =>
    by_cases hx : (277 : Int) ∣ x
    · exact Or.inl (by simpa [modulus] using hx)
    · exact Or.inr (cancel_nonzero_digit x y hx (j+1) (by simpa [modulus] using h))
  | succ i ih =>
    by_cases hx : (277 : Int) ∣ x
    · obtain ⟨c,rfl⟩ := hx
      have h' : modulus (i+j) ∣ c*y :=
        peel_factor _ c y (by simpa only [Nat.succ_add] using h)
      rcases ih c h' with hl | hr
      · obtain ⟨z,hz⟩ := hl
        left
        refine ⟨z,?_⟩
        change 277*c = 277^(i+1+1)*z
        change c = 277^(i+1)*z at hz
        rw [hz, Int.pow_succ (277 : Int) (i+1)]
        grind
      · exact Or.inr hr
    · have hy := cancel_nonzero_digit x y hx (i+1+j+1) h
      exact Or.inr (Int.dvd_trans (modulus_dvd (by omega : j ≤ i+1+j)) hy)

theorem residue_zero_of_divides (x : Integer277) {i k : Nat} (hik : i ≤ k)
    (h : modulus i ∣ x.residue k) : x.residue i = 0 :=
  (reduce x hik).symm.trans (Int.emod_eq_zero_of_dvd h)

theorem product_residue_ne_zero (x y : Integer277) (i j : Nat)
    (hx : x.residue i ≠ 0) (hy : y.residue j ≠ 0) :
    (mul x y).residue (i+j) ≠ 0 := by
  intro he
  change (x.residue (i+j)*y.residue (i+j)) % modulus (i+j) = 0 at he
  rcases product_precision i j _ _ (Int.dvd_of_emod_eq_zero he) with h | h
  · exact hx (residue_zero_of_divides x (by omega : i ≤ i+j) h)
  · exact hy (residue_zero_of_divides y (by omega : j ≤ i+j) h)

theorem nonzero_coordinate (z : Integer277) (hz : z ≠ ofInt 0) :
    ∃ n, z.residue n ≠ 0 := by
  apply Classical.byContradiction
  intro h
  apply hz
  apply equal_of_residues
  intro n
  change z.residue n = 0 % modulus n
  rw [Int.zero_emod]
  exact Classical.byContradiction (fun hn => h ⟨n,hn⟩)

theorem product_nonzero (x y : Integer277) (hx : x ≠ ofInt 0) (hy : y ≠ ofInt 0) :
    mul x y ≠ ofInt 0 := by
  obtain ⟨i,hi⟩ := nonzero_coordinate x hx
  obtain ⟨j,hj⟩ := nonzero_coordinate y hy
  intro he
  have h := congrArg (fun z : Integer277 => z.residue (i+j)) he
  exact product_residue_ne_zero x y i j hi hj (h.trans (Int.zero_emod _))

theorem no_zero_divisors (x y : Integer277) (h : mul x y = ofInt 0) :
    x = ofInt 0 ∨ y = ofInt 0 := by
  by_cases hx : x = ofInt 0
  · exact Or.inl hx
  · exact Or.inr (Classical.byContradiction (fun hy => product_nonzero x y hx hy h))

end Reimann.TameAdicDomain277
