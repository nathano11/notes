import Reimann.CyclicBoundary
import Reimann.ScalarCoinvariants

namespace Reimann.TameTwist277

/-- The 275 nontrivial tame weights, tested directly on the actual integer
powers. This supplies a gcd certificate for each difference. -/
theorem nontrivial_weight_gcd : ∀ k : Fin 275, Int.gcd 277 ((5 : Int)^(k.val+1)-1) = 1 := by
  set_option maxRecDepth 4096 in decide +kernel

theorem weight_bezout_mod_prime (r : Nat) (hr : 1 ≤ r) (hr' : r ≤ 275) :
    ∃ i j : Int, ((5 : Int)^r-1)*i+277*j = 1 := by
  have he : r-1+1 = r := by omega
  have hg := nontrivial_weight_gcd ⟨r-1,by omega⟩
  change Int.gcd 277 ((5 : Int)^(r-1+1)-1) = 1 at hg
  rw [he] at hg
  obtain ⟨j,i,hi⟩ := ScalarCoinvariants.int_gcd_bezout 277 ((5 : Int)^r-1)
  rw [hg] at hi
  exact ⟨i,j,by omega⟩

/-- A Bézout witness modulo p lifts to every p-power using a finite
geometric expansion. Neither a primality hypothesis nor a limiting argument is needed. -/
theorem lift_bezout (p d i j : Int) (n : Nat) (h : d*i+p*j = 1) :
    ∃ a b : Int, d*a+p^n*b = 1 := by
  have hdi : d*i = 1+p*(-j) := by grind
  obtain ⟨a,b,hab⟩ := CyclicBoundary.unit_bezout_power p (-j) n
  exact ⟨i*a,b,by rw [← Int.mul_assoc, hdi]; exact hab⟩

/-- Any integer lift of the direct tame scalar has invertible difference from
one. This includes the Teichmüller lift and the ordinary integer power. -/
theorem direct_tame_unit (r n : Nat) (a : Int) (hr : 1 ≤ r) (hr' : r ≤ 275)
    (lift : (277 : Int) ∣ a-5^r) :
    ∃ i j : Int, (a-1)*i+277^n*j = 1 := by
  obtain ⟨c,hc⟩ := lift
  obtain ⟨i,j,h⟩ := weight_bezout_mod_prime r hr hr'
  apply lift_bezout 277 (a-1) i (j-c*i) n
  have ha : a = 5^r+277*c := by omega
  rw [ha]
  grind

/-- Every representative reducing to the inverse r-th power has invertible
difference from one modulo 277^n. -/
theorem inverse_tame_unit (r n : Nat) (a : Int) (hr : 1 ≤ r) (hr' : r ≤ 275)
    (inv : (277 : Int) ∣ 5^r*a-1) :
    ∃ i j : Int, (a-1)*i+277^n*j = 1 := by
  obtain ⟨c,hc⟩ := inv
  obtain ⟨i,j,h⟩ := weight_bezout_mod_prime r hr hr'
  apply lift_bezout 277 (a-1) (-(5^r)*i) (j+c*i) n
  calc
    (a-1)*(-(5^r)*i)+277*(j+c*i) = (5^r-1)*i+277*j+(277*c-(5^r*a-1))*i := by grind
    _ = 1 := by rw [hc, h]; grind

/-- Division by an invertible integer scalar on residues: x solves d*x=y
precisely when x is the residue of i*y. -/
theorem unit_division_iff (m d i j x y : Int) (h : d*i+m*j = 1) :
    (m ∣ d*x-y) ↔ m ∣ x-i*y := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨i*k+j*x,?_⟩
    calc
      x-i*y = (d*i+m*j)*x-i*y := by rw [h]; simp
      _ = i*(d*x-y)+m*(j*x) := by grind
      _ = m*(i*k+j*x) := by rw [hk]; grind
  · rintro ⟨k,hk⟩
    refine ⟨d*k-j*y,?_⟩
    calc
      d*x-y = d*x-(d*i+m*j)*y := by rw [h]; simp
      _ = d*(x-i*y)-m*(j*y) := by grind
      _ = m*(d*k-j*y) := by rw [hk]; grind

/-- A single inverse divides every coefficient for either sign of the weight. -/
theorem tame_division (r n : Nat) (a : Int) (hr : 1 ≤ r) (hr' : r ≤ 275)
    (lift : (277 : Int) ∣ a-5^r ∨ (277 : Int) ∣ 5^r*a-1) :
    ∃ i : Int, ∀ x y : Int, ((277 : Int)^n ∣ (a-1)*x-y) ↔ 277^n ∣ x-i*y := by
  have unit : ∃ i j : Int, (a-1)*i+277^n*j = 1 := by
    rcases lift with h | h
    · exact direct_tame_unit r n a hr hr' h
    · exact inverse_tame_unit r n a hr hr' h
  obtain ⟨i,j,hi⟩ := unit
  exact ⟨i,fun x y => unit_division_iff _ _ _ _ x y hi⟩

/-- At every depth and every nontrivial tame weight, the only fixed
coefficient modulo 277^n is the zero residue. -/
theorem tame_fixed_iff_zero (r n : Nat) (a x : Int) (hr : 1 ≤ r) (hr' : r ≤ 275)
    (lift : (277 : Int) ∣ a-5^r ∨ (277 : Int) ∣ 5^r*a-1) :
    (a*x % (277 : Int)^n = x % (277 : Int)^n) ↔ (x % (277 : Int)^n = 0) := by
  obtain ⟨i,hi⟩ := tame_division r n a hr hr' lift
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero,
    ← Int.dvd_iff_emod_eq_zero]
  have hdx : a*x-x = (a-1)*x := by grind
  rw [hdx]
  simpa using hi x 0

end Reimann.TameTwist277
