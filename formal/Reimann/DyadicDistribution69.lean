import Reimann.SignedProjection
import Reimann.DyadicZeroValues

/-!
At dyadic modulus D=2^n, the positive lift of a real quotient element has
representative t congruent to 1 modulo four. The 69-term progression is
a=t+Dk. Pairing a with 69D-a removes the sign character and the constant
Bernoulli term. Each resulting half-normalized coefficient is an integer,
and the two orientations above one fibre sum to its coefficient.
-/

namespace Reimann.DyadicDistribution69

open Reimann.SignedProjection Reimann.Dyadic

def psi (b : Nat) : Int := quadSymbol 3 b * quadSymbol 23 b

def fibre (n t k : Nat) : Int := psi (t+2^n*k)

/-- Division by 69 is exact, as proved below. -/
def coefficient (n t : Nat) : Int := -moment (fibre n t) 69 / 69

theorem psi_reduce (b : Nat) : psi (b%69) = psi b := by
  simp only [psi, quadSymbol, Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 69),
    Nat.mod_mod_of_dvd _ (by decide : 23 ∣ 69)]

theorem psi_congr {a b : Nat} (h : a%69 = b%69) : psi a = psi b := by
  rw [←psi_reduce a, ←psi_reduce b, h]

theorem psi_double (b : Nat) : psi (2*b) = -psi b := by
  have a := Reimann.DyadicZeroValues.prime_factor_multiplicative 3 (Or.inl rfl) 2 b
  have c := Reimann.DyadicZeroValues.prime_factor_multiplicative 23 (Or.inr rfl) 2 b
  rw [psi,a,c,show quadSymbol 3 2 = -1 by decide,show quadSymbol 23 2 = 1 by decide]
  simp [psi, Int.neg_mul]

theorem fibre_period (n t k : Nat) : fibre n t (69+k) = fibre n t k := by
  unfold fibre
  apply psi_congr
  rw [Nat.mul_add, ← Nat.add_assoc, Nat.mul_comm (2^n) 69]
  omega

/-- 35 is the inverse of 2 modulo 69, and doubling changes the character sign. -/
theorem fibre_descent (n t k : Nat) : fibre (n+1) t k = -fibre n (35*t) k := by
  unfold fibre
  rw [Nat.pow_succ]
  have e : t+2^n*2*k + 69*t = 2*(35*t+2^n*k) := by grind
  rw [←psi_double]
  apply psi_congr
  rw [←e]
  omega

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem base_masses : ∀ t : Fin 69, total (fun k => psi (t.val+k)) 69 = 0 := by decide

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem base_moment_divisibility :
    ∀ t : Fin 69, moment (fun k => psi (t.val+k)) 69 % 69 = 0 := by decide

theorem total_negated (f : Nat → Int) (m : Nat) :
    total (fun k => -f k) m = -total f m := by
  simpa using total_affine f f (-1) 0 m

theorem moment_negated (f : Nat → Int) (m : Nat) :
    moment (fun k => -f k) m = -moment f m := by
  simp only [moment, Int.mul_neg, total_negated]

/-- Every progression has mass zero and its first moment is a multiple of 69. -/
theorem all_fibre_moments (n t : Nat) :
    total (fibre n t) 69 = 0 ∧ moment (fibre n t) 69 % 69 = 0 := by
  induction n generalizing t with
  | zero =>
    let s : Fin 69 := ⟨t%69, Nat.mod_lt _ (by decide)⟩
    have h : fibre 0 t = (fun k => psi (s.val+k)) := by
      funext k
      apply psi_congr
      dsimp [s]
      omega
    rw [h]
    exact ⟨base_masses s,base_moment_divisibility s⟩
  | succ n ih =>
    obtain ⟨ht,hm⟩ := ih (35*t)
    rw [show fibre (n+1) t = (fun k => -fibre n (35*t) k) by
      funext k; exact fibre_descent n t k, total_negated, moment_negated]
    omega

/-- Clearing the odd denominator loses no integral information. -/
theorem coefficient_exact (n t : Nat) : -moment (fibre n t) 69 = 69*coefficient n t := by
  have h := (all_fibre_moments n t).2
  unfold coefficient
  omega

theorem fibre_even (n t k : Nat) : fibre n t (2*k) = fibre (n+1) t k := by
  simp [fibre, Nat.pow_succ, Nat.mul_assoc]

theorem fibre_odd (n t k : Nat) : fibre n t (2*k+1) = fibre (n+1) (t+2^n) k := by
  unfold fibre
  rw [Nat.pow_succ]
  congr 1
  grind

/-- Pushforward from modulus 2D to D sums precisely the two lifted coefficients. -/
theorem coefficient_refines (n t : Nat) :
    coefficient n t = coefficient (n+1) t + coefficient (n+1) (t+2^n) := by
  have h := moment_refine (fibre n t) 69 (fibre_period n t) (all_fibre_moments n t).1
    (by simpa only [fibre_odd] using (all_fibre_moments (n+1) (t+2^n)).1)
  simp only [fibre_even, fibre_odd] at h
  have h0 := coefficient_exact n t
  have h1 := coefficient_exact (n+1) t
  have h2 := coefficient_exact (n+1) (t+2^n)
  change -moment (fibre n t) 69 = -moment (fibre (n+1) t) 69 - moment (fibre (n+1) (t+2^n)) 69 at h
  rw [h0,h1] at h
  omega

/-- The numerator after pairing opposite representatives. The signed B₁
sum divided by two has denominator 2M with M=69D in this expression. -/
def pairedNumerator (n t : Nat) : Int :=
  let D : Int := (2^n : Nat)
  total (fun k : Nat => ((D*69-(t+D*k))-(t+D*k))*fibre n t k) 69

/-- Integer identity for the half-normalized signed Bernoulli coefficient. -/
theorem half_normalized_bernoulli (n t : Nat) :
    pairedNumerator n t = 2*((2^n : Nat) : Int)*69*coefficient n t := by
  have h := paired_normalization (fibre n t) 69 t (2^n : Nat) (coefficient n t)
    (all_fibre_moments n t).1 (coefficient_exact n t)
  change pairedNumerator n t = _ at h
  rw [h]
  grind

/-- The primitive even character is unchanged under reflection modulo 69D. -/
theorem psi_reflected (D a : Nat) (ha : a ≤ 69*D) : psi (69*D-a) = psi a := by
  have ht : ∀ s : Fin 69, psi (69-s.val) = psi s.val := by decide
  let s : Fin 69 := ⟨a%69, Nat.mod_lt _ (by decide)⟩
  calc
    psi (69*D-a) = psi (69-s.val) := by apply psi_congr; dsimp [s]; omega
    _ = psi s.val := ht s
    _ = psi a := psi_reduce _

/-- Integer numerator of -χ(a) B₁(a/M), with denominator 2M. -/
def signedBernoulliTerm (M a : Nat) : Int := ((M : Int)-2*(a : Int))*DyadicZeroValues.chi276 a

/-- On the positively oriented fibre, the mod-four sign reverses at M-a.
The two cleared B₁ terms contribute twice the paired numerator summand. -/
theorem signed_bernoulli_pair (D a : Nat) (hD : D%4=0) (ha : a ≤ 69*D) (hpos : a%4=1) :
    signedBernoulliTerm (69*D) a + signedBernoulliTerm (69*D) (69*D-a) =
      2*(((69*D : Nat) : Int)-2*(a : Int))*psi a := by
  have hneg : (69*D-a)%4=3 := by omega
  have hp : DyadicZeroValues.chi276 a = psi a := by simp [DyadicZeroValues.chi276, psi, hpos]
  have hm : DyadicZeroValues.chi276 (69*D-a) = -psi a := by
    simp only [DyadicZeroValues.chi276, hneg]
    exact congrArg Neg.neg (psi_reflected D a ha)
  simp only [signedBernoulliTerm, hp, hm, Int.ofNat_sub ha]
  grind

/-- Coefficients at the canonical representatives t=1+4j, whose inverses
index the degree-2^a real cyclotomic quotient. -/
def positiveRow (a : Nat) (j : Fin (2^a)) : Int := coefficient (a+2) (1+4*j.val)

theorem positive_row_pushforward (a : Nat) (j : Fin (2^a)) :
    positiveRow a j =
      positiveRow (a+1) ⟨j.val, by rw [Nat.pow_succ]; have h := j.isLt; omega⟩ +
      positiveRow (a+1) ⟨j.val+2^a, by rw [Nat.pow_succ]; have h := j.isLt; omega⟩ := by
  unfold positiveRow
  have he : 1+4*(j.val+2^a) = 1+4*j.val+2^(a+2) := by rw [Nat.pow_add]; grind
  rw [he]
  exact coefficient_refines (a+2) (1+4*j.val)

/-- The two literal Dirichlet-character terms in the k-th pair, with common denominator 2M. -/
def signedFibreTerm (n t k : Nat) : Int :=
  let M := 69*2^n
  let a := t+2^n*k
  signedBernoulliTerm M a + signedBernoulliTerm M (M-a)

theorem signed_fibre_term (n t k : Nat) (hD : 2^n%4=0) (ht : t < 2^n)
    (hp : t%4=1) (hk : k < 69) :
    signedFibreTerm n t k =
      2*((((2^n : Nat) : Int)*69-((t : Int)+(2^n : Nat)*k))-((t : Int)+(2^n : Nat)*k))*fibre n t k := by
  have hle := Nat.mul_le_mul_left (2^n) (show k+1 ≤ 69 by omega)
  rw [Nat.mul_succ, Nat.mul_comm (2^n) 69] at hle
  have ha : t+2^n*k ≤ 69*2^n := by omega
  have hor : (t+2^n*k)%4=1 := by
    rw [Nat.add_mod, Nat.mul_mod, hD, hp]
    simp
  have h := signed_bernoulli_pair (2^n) (t+2^n*k) hD ha hor
  unfold signedFibreTerm fibre
  rw [h]
  simp only [Int.natCast_mul, Int.natCast_add]
  grind

/-- The full 138-term signed Bernoulli numerator, before division by 4M
for the half-normalized coefficient. At all real cyclotomic layers D≥4,
take 0<t<D with t≡1 modulo four. -/
theorem literal_bernoulli_row (n t : Nat) (hD : 2^n%4=0) (ht : t < 2^n) (hp : t%4=1) :
    total (signedFibreTerm n t) 69 = 4*((2^n : Nat) : Int)*69*coefficient n t := by
  let D : Int := (2^n : Nat)
  let term := fun k : Nat => ((D*69-(t+D*k))-(t+D*k))*fibre n t k
  have h (j : Nat) (hj : j ≤ 69) : total (signedFibreTerm n t) j = 2*total term j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [total, total, ih (by omega), signed_fibre_term n t j hD ht hp (by omega)]
      dsimp [term,D]
      grind
  have eq := h 69 (by decide)
  change total (signedFibreTerm n t) 69 = 2*pairedNumerator n t at eq
  rw [eq, half_normalized_bernoulli]
  grind

end Reimann.DyadicDistribution69
