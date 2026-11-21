import Reimann.DyadicSeriesProjection
import Reimann.SignedTaylorScalar
import Reimann.SignedQuadraticLift

/-! From one-bit quadratic preparation to an exact factorization of a power
series over the inverse limit of the rings of binary residues. -/
namespace Reimann.SignedAnalyticPreparation

open DyadicLattice (Scalar)
open DyadicSeriesProjection (Series convolution quadraticSeries)

/-- Integer coefficient representative at binary precision n+1. -/
def rep (F : Series) (n k : Nat) : Int := ((F k).residue n).toNat

theorem rep_cast (F : Series) (n k : Nat) : BitVec.ofInt (n+1) (rep F n k) = (F k).residue n := by
  simp [rep, BitVec.ofNat_toNat]

theorem rep_step (F : Series) (n k : Nat) : (2:Int)^(n+1) ∣ rep F (n+1) k - rep F n k := by
  have hn := congrArg BitVec.toNat ((F k).reduce (Nat.le_succ n))
  rw [BitVec.toNat_setWidth] at hn
  have he : rep F (n+1) k % (2:Int)^(n+1) = rep F n k := by
    unfold rep
    exact_mod_cast hn
  refine ⟨rep F (n+1) k / (2:Int)^(n+1), ?_⟩
  have ha := Int.emod_add_mul_ediv (rep F (n+1) k) ((2:Int)^(n+1))
  rw [he] at ha
  omega

theorem ofInt_of_divides {x y : Int} {w : Nat} (h : (2:Int)^w ∣ x-y) :
    BitVec.ofInt w x = BitVec.ofInt w y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, Int.natCast_pow]
  exact congrArg Int.toNat (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h))

theorem all_steps (z : Nat → Int) (step : ∀ k, (2:Int)^(k+1) ∣ z (k+1)-z k)
    {i j : Nat} (hij : i ≤ j) : (2:Int)^(i+1) ∣ z j - z i := by
  induction j with
  | zero =>
    have he : i=0 := by omega
    rw [he, Int.sub_self]
    exact Int.dvd_zero _
  | succ j ih =>
    by_cases hi : i ≤ j
    · have hm : (2:Int)^(i+1) ∣ (2:Int)^(j+1) := by
        exact_mod_cast Nat.pow_dvd_pow 2 (Nat.succ_le_succ hi)
      have hs := Int.dvd_add (Int.dvd_trans hm (step j)) (ih hi)
      rwa [show z (j+1) - z j + (z j-z i) = z (j+1)-z i by omega] at hs
    · have he : i=j+1 := by omega
      rw [he, Int.sub_self]
      exact Int.dvd_zero _

/-- Reconstruct the unique coherent scalar having the prescribed compatible representatives. -/
def limit (z : Nat → Int) (step : ∀ k, (2:Int)^(k+1) ∣ z (k+1)-z k) : Scalar where
  residue n := BitVec.ofInt (n+1) (z n)
  reduce {i j} hij := by
    rw [SignedTaylorScalar.narrow_int (i+1) (j+1) (by omega)]
    exact ofInt_of_divides (all_steps z step hij)

/-- Cauchy multiplication at the binary width w. -/
def wordProduct {w : Nat} (f g : Nat → BitVec w) (n : Nat) : BitVec w :=
  ((List.range (n+1)).map (fun j => f j * g (n-j))).foldr (·+·) 0

theorem word_succ {w : Nat} (f g : Nat → BitVec w) (n : Nat) :
    wordProduct f g (n+1) = f 0*g (n+1) + wordProduct (fun k => f (k+1)) g n := by
  unfold wordProduct
  rw [List.range_succ_eq_map (n := n+1)]
  simp [List.map_map, Function.comp_def]

theorem word_zero {w : Nat} (f g : Nat → BitVec w) : wordProduct f g 0 = f 0*g 0 := by
  change _+0 = _
  simp

theorem zero_word {w : Nat} (u : Nat → BitVec w) (n : Nat) :
    wordProduct (fun _ => 0) u n = 0 := by
  induction n with
  | zero => simp [word_zero]
  | succ n ih => rw [word_succ]; simpa using ih

theorem sum_residue (i : Nat) (xs : List Scalar) :
    (xs.foldr DyadicLattice.add (DyadicLattice.natScalar 0)).residue i =
      (xs.map (fun a => a.residue i)).foldr (·+·) 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change a.residue i + (xs.foldr DyadicLattice.add (DyadicLattice.natScalar 0)).residue i = _
    rw [ih]
    rfl

theorem convolution_at_width (F U : Series) (i n : Nat) :
    (convolution F U n).residue i =
      wordProduct (fun k => (F k).residue i) (fun k => (U k).residue i) n := by
  simp only [convolution, wordProduct, sum_residue, List.map_map]
  rfl

def wordDelay {w : Nat} (f : Nat → BitVec w) : Nat → BitVec w
  | 0 => 0
  | k+1 => f k

/-- Every binary projection of the full convolution by the monic quadratic
is the same three-term formula as the integer one-bit lifting problem. -/
theorem quadratic_at_width (c0 c1 : Scalar) (U : Series) (i k : Nat) :
    let u := fun j => (U j).residue i
    (convolution (quadraticSeries c0 c1) U k).residue i =
      c0.residue i*u k + c1.residue i*wordDelay u k + wordDelay (wordDelay u) k := by
  rw [convolution_at_width]
  let q := fun j => (quadraticSeries c0 c1 j).residue i
  let u := fun j => (U j).residue i
  change wordProduct q u k = _
  have tail (n : Nat) : wordProduct (fun j => q (j+2)) u n = u n := by
    cases n with
    | zero => rw [word_zero]; change 1*u 0 = _; simp
    | succ n =>
      rw [word_succ]
      change 1*u (n+1) + wordProduct (fun _ => 0) u n = _
      rw [zero_word]; simp
  cases k with
  | zero => rw [word_zero]; simp [q, wordDelay, quadraticSeries, u]
  | succ k =>
    cases k with
    | zero => rw [word_succ, word_zero]; simp [q, wordDelay, quadraticSeries, u]
    | succ k =>
      rw [word_succ, word_succ]
      change c0.residue i*u (k+2) + (c1.residue i*u (k+1) + wordProduct (fun j => q (j+2)) u k) = _
      rw [tail]
      simp [wordDelay, u, BitVec.add_assoc]

/-- Choose the next representative of each input coefficient before the lift.
The previous representative agrees with it at all earlier digits. -/
def stage (F : Series) : Nat → SignedQuadraticLift.Stage
  | 0 => SignedQuadraticLift.initial (rep F 0)
  | n+1 => SignedQuadraticLift.lift (2^(n+1)) (rep F (n+1)) (stage F n)

theorem stage_steps (F : Series) (n : Nat) :
    (2:Int)^(n+1) ∣ (stage F (n+1)).c0-(stage F n).c0 ∧
    (2:Int)^(n+1) ∣ (stage F (n+1)).c1-(stage F n).c1 ∧
    ∀ k, (2:Int)^(n+1) ∣ (stage F (n+1)).cofactor k-(stage F n).cofactor k :=
  SignedQuadraticLift.lift_preserves

theorem stage_matches (F : Series) (h0 : rep F 0 0 % 2 = 0) (h1 : rep F 0 1 % 2 = 0)
    (h2 : rep F 0 2 % 2 = 1) (n : Nat) :
    SignedQuadraticLift.Matches (2^(n+1)) (rep F n) (stage F n) ∧
      SignedQuadraticLift.Distinguished (stage F n) := by
  induction n with
  | zero => exact ⟨SignedQuadraticLift.initial_matches h0 h1, SignedQuadraticLift.initial_distinguished h2⟩
  | succ n ih =>
    obtain ⟨matched, ds⟩ := ih
    let m := (2:Int)^(n+1)
    have hm : m%2=0 := by dsimp [m]; rw [Int.pow_succ]; omega
    have higher : SignedQuadraticLift.Matches m (rep F (n+1)) (stage F n) := by
      intro k
      have h := Int.dvd_add (rep_step F n k) (matched k)
      rwa [show rep F (n+1) k - rep F n k + (rep F n k - SignedQuadraticLift.product (stage F n) k) =
        rep F (n+1) k - SignedQuadraticLift.product (stage F n) k by omega] at h
    change SignedQuadraticLift.Matches (2^(n+1+1)) _ (SignedQuadraticLift.lift m _ _) ∧ _
    rw [show (2:Int)^(n+1+1) = 2*m by dsimp [m]; rw [Int.pow_succ]; grind]
    exact ⟨SignedQuadraticLift.lift_matches hm ds higher, SignedQuadraticLift.lift_distinguished hm ds⟩

def constant (F : Series) : Scalar :=
  limit (fun n => (stage F n).c0) (fun n => (stage_steps F n).1)

def linear (F : Series) : Scalar :=
  limit (fun n => (stage F n).c1) (fun n => (stage_steps F n).2.1)

def cofactor (F : Series) : Series := fun k =>
  limit (fun n => (stage F n).cofactor k) (fun n => (stage_steps F n).2.2 k)

theorem cast_delay (w : Nat) (f : Nat → Int) (k : Nat) :
    BitVec.ofInt w (SignedQuadraticLift.delay f k) = wordDelay (fun j => BitVec.ofInt w (f j)) k := by
  cases k <;> rfl

theorem residue_product (F : Series) (n k : Nat) :
    BitVec.ofInt (n+1) (SignedQuadraticLift.product (stage F n) k) =
      (convolution (quadraticSeries (constant F) (linear F)) (cofactor F) k).residue n := by
  rw [quadratic_at_width]
  simp only [SignedQuadraticLift.product, BitVec.ofInt_add, BitVec.ofInt_mul, cast_delay]
  rfl

/-- Once the mod-two series starts in degree two, the three-term product
agrees with F coefficient by coefficient at every binary precision. -/
theorem exact_factorization (F : Series) (h0 : rep F 0 0 % 2 = 0)
    (h1 : rep F 0 1 % 2 = 0) (h2 : rep F 0 2 % 2 = 1) :
    F = convolution (quadraticSeries (constant F) (linear F)) (cofactor F) := by
  funext k
  apply DyadicLattice.scalar_ext
  intro n
  calc
    _ = BitVec.ofInt (n+1) (rep F n k) := (rep_cast F n k).symm
    _ = BitVec.ofInt (n+1) (SignedQuadraticLift.product (stage F n) k) :=
      ofInt_of_divides ((stage_matches F h0 h1 h2 n).1 k)
    _ = _ := residue_product F n k

theorem factor_parities (F : Series) (h2 : rep F 0 2 % 2 = 1) :
    (constant F).residue 0 = 0 ∧ (linear F).residue 0 = 0 ∧ ((cofactor F) 0).residue 0 = 1 := by
  refine ⟨rfl, rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  change (rep F 0 2 % 2).toNat = 1
  rw [h2]
  rfl

/-- Explicit monic distinguished quadratic and cofactor with invertible
constant coefficient for any coherent series with initial degree two modulo 2. -/
theorem prepared (F : Series) (h0 : rep F 0 0 % 2 = 0) (h1 : rep F 0 1 % 2 = 0)
    (h2 : rep F 0 2 % 2 = 1) :
    (constant F).residue 0=0 ∧ (linear F).residue 0=0 ∧ ((cofactor F) 0).residue 0=1 ∧
      F = convolution (quadraticSeries (constant F) (linear F)) (cofactor F) := by
  obtain ⟨hc,hl,hu⟩ := factor_parities F h2
  exact ⟨hc,hl,hu,exact_factorization F h0 h1 h2⟩

end Reimann.SignedAnalyticPreparation
