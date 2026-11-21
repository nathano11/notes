import Reimann.PairedSigns

/-! Compatible dyadic factorizations of the signed quadratic, for fixed integer coefficients. -/
namespace Reimann.SignedRoots

open Reimann.PairedSigns Reimann.SampleSpacing Reimann.Dyadic

/-- After substituting T = 2y and dividing the monic quadratic by four. -/
def halfPolynomial (b c y : Int) : Int := y^2 + b*y + c

theorem scaled_identity (b c y : Int) :
    (2*y)^2+(2*b)*(2*y)+4*c = 4*halfPolynomial b c y := by
  unfold halfPolynomial
  grind

theorem coefficient_halves (c0 c1 : Int) (h : WeightThree c0 c1) :
    c0 = 4*(c0/4) ∧ c1 = 2*(c1/2) ∧ (c0/4)%16 = 10 ∧ (c1/2)%16 = 9 := by
  have hc := weight_three_constant_coefficient c0 c1 h
  have hb := weight_three_linear_coefficient c0 c1 h
  omega

theorem half_shift (b c y m e : Int) :
    halfPolynomial b c (y+m*e) =
      halfPolynomial b c y + m*e*(2*y+b) + (m*e)^2 := by
  unfold halfPolynomial
  grind

/-- Correcting the parity of F(y)/m lifts a root from m to 2m. -/
theorem lift_digit (b c y m z : Int) (hy : halfPolynomial b c y = m*z)
    (hm : 2 ∣ m) (hb : b%2=1) :
    2*m ∣ halfPolynomial b c (y+m*(z%2)) := by
  obtain ⟨w,hw⟩ := hm
  let e := z%2
  have hz : z = 2*(z/2)+e := by dsimp [e]; omega
  have hb' : b = 2*(b/2)+1 := by omega
  refine ⟨z/2+e*(1+y+b/2)+w*e^2, ?_⟩
  rw [half_shift,hy]
  change m*z + m*e*(2*y+b)+(m*e)^2 = 2*m*(z/2+e*(1+y+b/2)+w*e^2)
  grind

/-- Start at precision four so the two root branches retain their labels modulo eight in T. -/
def precision (n : Nat) : Int := 4*2^n

theorem precision_succ (n : Nat) : precision (n+1) = 2*precision n := by
  unfold precision
  rw [Int.pow_succ]
  grind

/-- The coherent lift of the even root of the scaled polynomial. -/
def evenLift (b c : Int) : Nat → Int
  | 0 => 2
  | n+1 =>
    let y := evenLift b c n
    y + precision n * ((halfPolynomial b c y / precision n)%2)

theorem evenLift_compatible (b c : Int) (n : Nat) :
    precision n ∣ evenLift b c (n+1)-evenLift b c n := by
  refine ⟨(halfPolynomial b c (evenLift b c n)/precision n)%2, ?_⟩
  simp only [evenLift]
  omega

theorem evenLift_residue (b c : Int) (n : Nat) : evenLift b c n % 4 = 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨z,hz⟩ := evenLift_compatible b c n
    unfold precision at hz
    have hd : 4 ∣ evenLift b c (n+1)-evenLift b c n :=
      ⟨2^n*z,by rw [hz,Int.mul_assoc]⟩
    omega

theorem evenLift_root (b c : Int) (hb : b%16=9) (hc : c%16=10) (n : Nat) :
    precision n ∣ halfPolynomial b c (evenLift b c n) := by
  induction n with
  | zero =>
    change 4 ∣ (2:Int)^2+b*2+c
    omega
  | succ n ih =>
    let y := evenLift b c n
    let m := precision n
    have hdiv : m ∣ halfPolynomial b c y := ih
    have hy : halfPolynomial b c y = m*(halfPolynomial b c y/m) :=
      (Int.mul_ediv_cancel' hdiv).symm
    have hm : 2 ∣ m := ⟨2*2^n,by dsimp [m,precision]; grind⟩
    rw [precision_succ]
    exact lift_digit b c y m _ hy hm (by omega)

def rootFour (b c : Int) (n : Nat) : Int := 2*evenLift b c n

def rootTwo (b c : Int) (n : Nat) : Int := -2*(b+evenLift b c n)

theorem roots_compatible (b c : Int) (n : Nat) :
    2*precision n ∣ rootFour b c (n+1)-rootFour b c n ∧
    2*precision n ∣ rootTwo b c (n+1)-rootTwo b c n := by
  obtain ⟨z,h⟩ := evenLift_compatible b c n
  constructor
  · exact ⟨z,by unfold rootFour; grind⟩
  · exact ⟨-z,by unfold rootTwo; grind⟩

theorem roots_mod_eight (b c : Int) (hb : b%16=9) (n : Nat) :
    rootFour b c n % 8 = 4 ∧ rootTwo b c n % 8 = 2 := by
  have hr := evenLift_residue b c n
  unfold rootFour rootTwo
  omega

/-- The error in the product of the two lifted factors is the scaled Hensel residual. -/
theorem factor_remainder (b c s a : Int) (n : Nat) :
    numerator (4*c) (2*b) s a -
      ((s-a)-a*rootFour b c n)*((s-a)-a*rootTwo b c n) =
      4*a^2*halfPolynomial b c (evenLift b c n) := by
  unfold numerator rootFour rootTwo halfPolynomial
  grind

/-- A single compatible pair of linear factors works for every sign and denominator at every depth. -/
theorem signed_factorization (c0 c1 : Int) (h : WeightThree c0 c1) (s a : Int) (n : Nat) :
    4*precision n ∣ numerator c0 c1 s a -
      ((s-a)-a*rootFour (c1/2) (c0/4) n)*((s-a)-a*rootTwo (c1/2) (c0/4) n) := by
  obtain ⟨hc,hb,ch,bh⟩ := coefficient_halves c0 c1 h
  obtain ⟨z,hz⟩ := evenLift_root (c1/2) (c0/4) bh ch n
  have row := factor_remainder (c1/2) (c0/4) s a n
  rw [←hc,←hb] at row
  refine ⟨a^2*z, ?_⟩
  rw [row,hz]
  grind

/-- For every weight the opposite root contributes exactly one factor of two. -/
theorem opposite_factors (c0 c1 : Int) (h : WeightThree c0 c1) (r n : Nat) :
    let a := (5:Int)^r
    exactV ((1-a)-a*rootTwo (c1/2) (c0/4) n) 1 ∧
    exactV ((-1-a)-a*rootFour (c1/2) (c0/4) n) 1 := by
  dsimp only
  obtain ⟨_,_,_,hb⟩ := coefficient_halves c0 c1 h
  have ⟨h4,h2⟩ := roots_mod_eight (c1/2) (c0/4) hb n
  obtain ⟨u,hu⟩ := five_power_mod_four r
  let v := rootTwo (c1/2) (c0/4) n / 8
  let w := rootFour (c1/2) (c0/4) n / 8
  have ht : rootTwo (c1/2) (c0/4) n = 2+8*v := by dsimp [v]; omega
  have hf : rootFour (c1/2) (c0/4) n = 4+8*w := by dsimp [w]; omega
  constructor
  · refine ⟨-1-3*u-2*v-8*u*v, ?_⟩
    change (1-(5:Int)^r)-(5:Int)^r*_ = 2*(2*(-1-3*u-2*v-8*u*v)+1)
    rw [hu,ht]
    grind
  · refine ⟨-2-5*u-2*w-8*u*w, ?_⟩
    change (-1-(5:Int)^r)-(5:Int)^r*_ = 2*(2*(-2-5*u-2*w-8*u*w)+1)
    rw [hu,hf]
    grind

theorem exactV_of_congruent {x y : Int} {j : Nat} (hy : exactV y j)
    (hd : 2*twoPower j ∣ x-y) : exactV x j := by
  obtain ⟨z,hz⟩ := hy
  obtain ⟨k,hk⟩ := hd
  exact ⟨k+z, by grind⟩

theorem precision_supplies_digit (j : Nat) : 2*twoPower (j+1) ∣ 4*precision j := by
  rw [WeightClasses.twoPower_eq_pow,Int.pow_succ]
  refine ⟨4, ?_⟩
  unfold precision
  grind

/-- The valuation of either cleared specialization is one more than that of its near factor. -/
theorem valuation_from_near_factor (c0 c1 : Int) (h : WeightThree c0 c1) (r j : Nat) :
    let a := (5:Int)^r
    (exactV ((1-a)-a*rootFour (c1/2) (c0/4) j) j → exactV (positiveBranch c0 c1 r) (j+1)) ∧
    (exactV ((-1-a)-a*rootTwo (c1/2) (c0/4) j) j → exactV (negativeBranch c0 c1 r) (j+1)) := by
  dsimp only
  obtain ⟨⟨k,hk⟩,⟨z,hz⟩⟩ := opposite_factors c0 c1 h r j
  constructor
  · intro near
    apply exactV_of_congruent (hd := Int.dvd_trans (precision_supplies_digit j)
      (signed_factorization c0 c1 h 1 (5^r) j))
    rw [hk]
    exact exactV_mul_twice_odd _ j k near
  · intro near
    apply exactV_of_congruent (hd := Int.dvd_trans (precision_supplies_digit j)
      (signed_factorization c0 c1 h (-1) (5^r) j))
    rw [Int.mul_comm, hz]
    exact exactV_mul_twice_odd _ j z near

theorem exact_three_of_residue {x : Int} (hx : x%16=8) : exactV x 3 := by
  refine ⟨x/16, ?_⟩
  change x=8*(2*(x/16)+1)
  omega

theorem even_table :
    let low := fun s : Int => fun k : Nat => numerator 40 18 s ((5:Int)^k%32)%64%16
    low 1 0=8 ∧ low (-1) 0=8 ∧ low 1 2=8 ∧ low (-1) 2=8 ∧
    low 1 4=8 ∧ low (-1) 4=8 ∧ low 1 6=8 ∧ low (-1) 6=8 := by decide

/-- Even weights give valuation three on each polynomial branch. -/
theorem even_weight_pair (c0 c1 : Int) (h : WeightThree c0 c1) (r : Nat) (hr : r%2=0) :
    exactV (positiveBranch c0 c1 r) 3 ∧ exactV (negativeBranch c0 c1 r) 3 := by
  have hp := congrArg (fun x : Int => x%16) (signed_sample_mod_weight c0 c1 1 h (Or.inl rfl) r)
  have hm := congrArg (fun x : Int => x%16) (signed_sample_mod_weight c0 c1 (-1) h (Or.inr rfl) r)
  change numerator c0 c1 1 (5^r)%64%16 = numerator 40 18 1 ((5:Int)^(r%8)%32)%64%16 at hp
  change numerator c0 c1 (-1) (5^r)%64%16 = numerator 40 18 (-1) ((5:Int)^(r%8)%32)%64%16 at hm
  obtain ⟨p0,m0,p2,m2,p4,m4,p6,m6⟩ := even_table
  have low (x : Int) (hx : x%64%16=8) : exactV x 3 :=
    exact_three_of_residue ((Int.emod_emod_of_dvd x (by decide : (16:Int) ∣ 64)).symm.trans hx)
  have cases' : r%8=0 ∨ r%8=2 ∨ r%8=4 ∨ r%8=6 := by omega
  rcases cases' with h0 | h0 | h0 | h0
  all_goals rw [h0] at hp hm
  · exact ⟨low _ (hp.trans p0),low _ (hm.trans m0)⟩
  · exact ⟨low _ (hp.trans p2),low _ (hm.trans m2)⟩
  · exact ⟨low _ (hp.trans p4),low _ (hm.trans m4)⟩
  · exact ⟨low _ (hp.trans p6),low _ (hm.trans m6)⟩

end Reimann.SignedRoots
