import Reimann.TameSplitting277

namespace Reimann.TameLimit277

/-- Coordinate n has precision 277^(n+1). -/
def modulus (n : Nat) : Int := 277^(n+1)

theorem modulus_step (n : Nat) : modulus n ∣ modulus (n+1) :=
  ⟨277, Int.pow_succ 277 (n+1)⟩

/-- The inverse limit of the rings Z/277^(n+1) on canonical integer representatives. -/
structure Integer277 where
  residue : Nat → Int
  canonical : ∀ n, residue n % modulus n = residue n
  compatible : ∀ n, residue (n+1) % modulus n = residue n

theorem equal_of_residues {x y : Integer277} (h : ∀ n, x.residue n = y.residue n) :
    x = y := by
  cases x; cases y
  congr
  exact funext h

/-- An unnormalized system of congruent integer lifts represents a unique scalar. -/
def ofCompatible (s : Nat → Int) (h : ∀ n, modulus n ∣ s (n+1)-s n) : Integer277 where
  residue n := s n % modulus n
  canonical n := Int.emod_emod _ _
  compatible n := by
    rw [Int.emod_emod_of_dvd _ (modulus_step n)]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd (h n))

def ofInt (a : Int) : Integer277 :=
  ofCompatible (fun _ => a) (fun _ => by simp)

theorem step_difference (x : Integer277) (n : Nat) : modulus n ∣ x.residue (n+1)-x.residue n := by
  exact Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
    ((x.compatible n).trans (x.canonical n).symm))

def add (x y : Integer277) : Integer277 :=
  ofCompatible (fun n => x.residue n+y.residue n) (by
    intro n
    obtain ⟨a,ha⟩ := step_difference x n
    obtain ⟨b,hb⟩ := step_difference y n
    exact ⟨a+b, by grind⟩)

def neg (x : Integer277) : Integer277 :=
  ofCompatible (fun n => -x.residue n) (by
    intro n
    obtain ⟨a,ha⟩ := step_difference x n
    exact ⟨-a,by grind⟩)

def mul (x y : Integer277) : Integer277 :=
  ofCompatible (fun n => x.residue n*y.residue n) (by
    intro n
    obtain ⟨a,ha⟩ := step_difference x n
    obtain ⟨b,hb⟩ := step_difference y n
    exact ⟨a*y.residue (n+1)+x.residue n*b,by grind⟩)

open TameSplitting277

def liftedRoot (a x d : Int) (hx : 277 ∣ x^2-a) (hd : 277 ∣ 2*x*d-1) : Integer277 :=
  ofCompatible (fun n => (liftPair a x d n).1)
    (fun n => (liftPair_coherent 277 a x d hx hd n).1)

theorem lifted_square (a x d : Int) (hx : 277 ∣ x^2-a) (hd : 277 ∣ 2*x*d-1) :
    mul (liftedRoot a x d hx hd) (liftedRoot a x d hx hd) = ofInt a := by
  apply equal_of_residues
  intro n
  let z := (liftPair a x d n).1
  change (z % modulus n * (z % modulus n)) % modulus n = a % modulus n
  rw [← Int.mul_emod]
  have h := (liftPair_precision 277 a x d hx hd n).1
  rw [Int.pow_succ (liftPair a x d n).1 1,Int.pow_one] at h
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)

def rootThree : Integer277 := liftedRoot (-3) 44 85 simple_seeds.1 simple_seeds.2.1

def rootTwentyThree : Integer277 :=
  liftedRoot (-23) 114 130 simple_seeds.2.2.1 simple_seeds.2.2.2.1

theorem rootThree_square : mul rootThree rootThree = ofInt (-3) :=
  lifted_square _ _ _ _ _

theorem rootTwentyThree_square : mul rootTwentyThree rootTwentyThree = ofInt (-23) :=
  lifted_square _ _ _ _ _

theorem negative_squares (z : Integer277) : mul (neg z) (neg z) = mul z z := by
  apply equal_of_residues
  intro n
  change ((-z.residue n) % modulus n * ((-z.residue n) % modulus n)) % modulus n =
    (z.residue n*z.residue n) % modulus n
  rw [← Int.mul_emod, Int.neg_mul_neg]

theorem root_residues :
    rootThree.residue 0 = 44 ∧ (neg rootThree).residue 0 = 233 ∧
    rootTwentyThree.residue 0 = 114 ∧ (neg rootTwentyThree).residue 0 = 163 := by
  decide +kernel

theorem roots_distinct : rootThree ≠ neg rootThree ∧ rootTwentyThree ≠ neg rootTwentyThree := by
  constructor
  · intro h
    have hr := congrArg (fun z : Integer277 => z.residue 0) h
    have ⟨a,b,_⟩ := root_residues
    omega
  · intro h
    have hr := congrArg (fun z : Integer277 => z.residue 0) h
    have ⟨_,_,a,b⟩ := root_residues
    omega

theorem modulus_dvd {i j : Nat} (h : i ≤ j) : modulus i ∣ modulus j := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact Int.dvd_refl _
  | succ k ih => exact Int.dvd_trans ih (modulus_step (i+k))

/-- An arbitrary higher coordinate reduces to any lower precision. -/
theorem reduce (z : Integer277) {i j : Nat} (h : i ≤ j) : z.residue j % modulus i = z.residue i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact z.canonical i
  | succ k ih =>
    have hd := modulus_dvd (Nat.le_add_right i k)
    rw [← Nat.add_assoc, ← Int.emod_emod_of_dvd _ hd, z.compatible (i+k)]
    exact ih

theorem modulus_exceeds (n : Nat) : n < (modulus n).natAbs := by
  change n < 277^(n+1)
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ 277 (n+1)]
    omega

theorem ofInt_injective {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  let n := (a-b).natAbs
  have he := congrArg (fun z : Integer277 => z.residue n) h
  change a % modulus n = b % modulus n at he
  have hd := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he)
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (modulus_exceeds n)
  omega

theorem ofInt_add (a b : Int) : ofInt (a+b) = add (ofInt a) (ofInt b) :=
  equal_of_residues (fun n => Int.add_emod a b (modulus n))

theorem ofInt_mul (a b : Int) : ofInt (a*b) = mul (ofInt a) (ofInt b) :=
  equal_of_residues (fun n => Int.mul_emod a b (modulus n))

theorem ofInt_neg (a : Int) : ofInt (-a) = neg (ofInt a) := by
  apply equal_of_residues
  intro n
  change (-a) % modulus n = (-(a % modulus n)) % modulus n
  simp [Int.neg_emod, Int.dvd_iff_emod_eq_zero]

end Reimann.TameLimit277
