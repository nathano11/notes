import Std

namespace Reimann.TameRationalField277

theorem rational_numerator (x : Rat) :
    x * (((x.den : Nat) : Int) : Rat) = (x.num : Rat) := by
  have h := Rat.num_divInt_den x
  rw [Rat.divInt_eq_div] at h
  have h0 : (((x.den : Nat) : Int) : Rat) ≠ 0 := by
    intro hz
    have hZ : (x.den : Int) = 0 := Rat.intCast_inj.mp (show (↑(x.den : Int) : Rat) = ↑(0 : Int) from hz)
    exact x.den_nz (by omega)
  calc
    _ = ((x.num : Rat)/(((x.den : Nat) : Int) : Rat)) * (((x.den : Nat) : Int) : Rat) :=
      congrArg (fun y : Rat => y * (((x.den : Nat) : Int) : Rat)) h.symm
    _ = _ := Rat.div_mul_cancel h0

theorem clear_square_denominator (x : Rat) (h : 3*x*x=23) :
    3*x.num*x.num = 23*(x.den:Int)*(x.den:Int) := by
  apply Rat.intCast_inj.mp
  simp only [Rat.intCast_mul]
  have hx := rational_numerator x
  have he := congrArg (fun y : Rat => y*(((x.den:Nat):Int):Rat)*(((x.den:Nat):Int):Rat)) h
  change (3:Rat)*(x.num:Rat)*(x.num:Rat) = 23*(((x.den:Nat):Int):Rat)*(((x.den:Nat):Int):Rat)
  grind

theorem three_dvd_of_square (z : Int) (h : 3 ∣ z*z) : 3 ∣ z := by
  have he := Int.emod_eq_zero_of_dvd h
  rw [Int.mul_emod] at he
  apply Int.dvd_of_emod_eq_zero
  have hp : z%3 = 0 ∨ z%3 = 1 ∨ z%3 = 2 := by omega
  rcases hp with h0 | h1 | h2
  · exact h0
  · rw [h1] at he; contradiction
  · rw [h2] at he; contradiction

theorem both_divisible_by_three (a b : Int) (h : 3*a*a=23*b*b) :
    (3 ∣ a) ∧ (3 ∣ b) := by
  have hb : 3 ∣ b*b := ⟨8*b*b-a*a, by grind⟩
  obtain ⟨k,hk⟩ := three_dvd_of_square b hb
  have ha : 3 ∣ a*a := ⟨23*k*k, by rw [hk] at h; grind⟩
  exact ⟨three_dvd_of_square a ha,⟨k,hk⟩⟩

theorem no_rat_square_ratio (x : Rat) : 3*x*x ≠ 23 := by
  intro h
  obtain ⟨ha,hb⟩ := both_divisible_by_three _ _ (clear_square_denominator x h)
  have ha' : 3 ∣ x.num.natAbs := Int.natAbs_dvd_natAbs.mpr ha
  have hb' : 3 ∣ x.den := Int.ofNat_dvd.mp hb
  have hz := Nat.dvd_gcd ha' hb'
  have hred : Nat.gcd x.num.natAbs x.den = 1 := x.reduced
  rw [hred] at hz
  exact (by decide : ¬ (3:Nat) ∣ 1) hz

theorem square_nonnegative (a : Rat) : 0 ≤ a*a := by
  by_cases h : 0 ≤ a
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -a := by grind
    have hh := Rat.mul_nonneg h' h'
    grind

/-- Coordinates a + b√−3 over the rationals. -/
abbrev Quad := Rat × Rat

def qm (x y : Quad) : Quad :=
  (x.1*y.1-3*x.2*y.2, x.1*y.2+x.2*y.1)

theorem no_square_neg23_in_quad (x : Quad) : qm x x ≠ (-23,0) := by
  rintro h
  rcases x with ⟨a,b⟩
  have h₀ := congrArg Prod.fst h
  have h₁ := congrArg Prod.snd h
  change a*a-3*b*b = -23 at h₀
  change a*b+b*a = 0 at h₁
  have hab : a*b=0 := by grind
  rcases Rat.mul_eq_zero.mp hab with ha | hb
  · apply no_rat_square_ratio b
    grind
  · have hnn := square_nonnegative a
    grind

theorem quad_norm_nonzero (x : Quad) (hx : x ≠ (0,0)) :
    x.1*x.1 + 3*x.2*x.2 ≠ 0 := by
  rcases x with ⟨a,b⟩
  change a*a+3*b*b ≠ 0
  intro hz
  have h₀ := square_nonnegative a
  have h₁ := square_nonnegative b
  have ha : a*a=0 := by grind
  have hb : b*b=0 := by grind
  have ha' := (Rat.mul_eq_zero.mp ha).elim id id
  have hb' := (Rat.mul_eq_zero.mp hb).elim id id
  exact hx (by simp [ha',hb'])

def qi (x : Quad) : Quad :=
  let d := (x.1*x.1+3*x.2*x.2)⁻¹
  (x.1*d,-x.2*d)

theorem quad_mul_inverse (x : Quad) (hx : x ≠ (0,0)) : qm x (qi x)=(1,0) := by
  have h := Rat.mul_inv_cancel _ (quad_norm_nonzero x hx)
  apply Prod.ext
  · change x.1 * (x.1*_) - 3*x.2*(-x.2*_) = 1
    grind
  · change x.1*(-x.2*_) + x.2*(x.1*_) = 0
    grind

theorem qm_assoc (x y z : Quad) : qm (qm x y) z = qm x (qm y z) := by
  apply Prod.ext <;> simp only [qm] <;> grind

theorem qm_comm (x y : Quad) : qm x y = qm y x := by
  apply Prod.ext <;> simp only [qm] <;> grind

theorem qm_one (x : Quad) : qm x (1,0)=x := by
  apply Prod.ext <;> simp only [qm] <;> grind

theorem qm_zero (x : Quad) : qm (0,0) x = (0,0) := by
  apply Prod.ext <;> simp only [qm] <;> grind

theorem qm_zero_right (x : Quad) : qm x (0,0) = (0,0) :=
  (qm_comm _ _).trans (qm_zero x)

theorem quad_square_zero (x : Quad) (h : qm x x = (0,0)) : x=(0,0) := by
  by_cases hx : x=(0,0)
  · exact hx
  · have hh : qm (qm x x) (qi x) = qm (0,0) (qi x) :=
      congrArg (fun a => qm a (qi x)) h
    rw [qm_assoc, quad_mul_inverse x hx, qm_one, qm_zero] at hh
    exact hh

def qa (x y : Quad) : Quad := (x.1+y.1, x.2+y.2)

def qs (c : Rat) (x : Quad) : Quad := (c*x.1,c*x.2)

/-- Coordinates A+B√−23 with A,B in Q(√−3). -/
abbrev Biquad := Quad × Quad

def bm (x y : Biquad) : Biquad :=
  (qa (qm x.1 y.1) (qs (-23) (qm x.2 y.2)), qa (qm x.1 y.2) (qm x.2 y.1))

def relativeNorm (x : Biquad) : Quad := qa (qm x.1 x.1) (qs 23 (qm x.2 x.2))

theorem norm_zero_identity (x : Biquad) (h : relativeNorm x=(0,0)) :
    qm x.1 x.1 = qm (-23,0) (qm x.2 x.2) := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext <;> simp only [relativeNorm,qa,qs,qm] at * <;> grind

theorem quad_square_product (a b : Quad) :
    qm (qm a b) (qm a b) = qm (qm a a) (qm b b) := by
  apply Prod.ext <;> simp only [qm] <;> grind

theorem norm_nonzero (x : Biquad) (hx : x≠((0,0),(0,0))) : relativeNorm x ≠ (0,0) := by
  intro h
  have he := norm_zero_identity x h
  by_cases hb : x.2=(0,0)
  · rw [hb, qm_zero, qm_zero_right] at he
    exact hx (Prod.ext (quad_square_zero x.1 he) hb)
  · apply no_square_neg23_in_quad (qm x.1 (qi x.2))
    rw [quad_square_product, he, qm_assoc, ← quad_square_product,
      quad_mul_inverse x.2 hb, qm_one, qm_one]

def bi (x : Biquad) : Biquad :=
  let w := qi (relativeNorm x)
  (qm x.1 w, qs (-1) (qm x.2 w))

theorem relative_inverse_identity (x : Biquad) (w : Quad) :
    bm x (qm x.1 w, qs (-1) (qm x.2 w)) = (qm (relativeNorm x) w,(0,0)) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,qm,relativeNorm,qa,qs] <;> grind

theorem biquad_mul_inverse (x : Biquad) (hx : x≠((0,0),(0,0))) :
    bm x (bi x)=((1,0),(0,0)) := by
  unfold bi
  rw [relative_inverse_identity, quad_mul_inverse _ (norm_nonzero x hx)]

def ba (x y : Biquad) : Biquad := (qa x.1 y.1, qa x.2 y.2)

def bn (x : Biquad) : Biquad := (qs (-1) x.1, qs (-1) x.2)

theorem add_group_laws (x y z : Biquad) :
    ba (ba x y) z = ba x (ba y z) ∧ ba x y=ba y x ∧
    ba x ((0,0),(0,0))=x ∧ ba x (bn x)=((0,0),(0,0)) := by
  repeat' apply And.intro
  all_goals apply Prod.ext <;> apply Prod.ext <;> simp only [ba,bn,qa,qs] <;> grind

theorem mul_assoc (x y z : Biquad) : bm (bm x y) z = bm x (bm y z) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,qm,qa,qs] <;> grind

theorem mul_comm (x y : Biquad) : bm x y = bm y x := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,qm,qa,qs] <;> grind

theorem mul_one (x : Biquad) : bm x ((1,0),(0,0))=x := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [bm,qm,qa,qs] <;> grind

theorem distributive (x y z : Biquad) : bm x (ba y z) = ba (bm x y) (bm x z) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [ba,bm,qm,qa,qs] <;> grind

def scalar (a : Rat) : Biquad := ((a,0),(0,0))

def gen3 : Biquad := ((0,1),(0,0))

def gen23 : Biquad := ((0,0),(1,0))

theorem scalar_embedding (a b : Rat) :
    (scalar a=scalar b ↔ a=b) ∧
    ba (scalar a) (scalar b)=scalar (a+b) ∧ bm (scalar a) (scalar b)=scalar (a*b) := by
  constructor
  · constructor
    · exact fun h => congrArg (fun x : Biquad => x.1.1) h
    · exact congrArg scalar
  · constructor <;> apply Prod.ext <;> apply Prod.ext <;> simp only [scalar,ba,bm,qm,qa,qs] <;> grind

theorem generator_squares :
    bm gen3 gen3=scalar (-3) ∧ bm gen23 gen23=scalar (-23) :=
  by constructor <;> apply Prod.ext <;> apply Prod.ext <;>
       simp only [scalar,gen3,gen23,bm,qm,qa,qs] <;> grind

/-- The independent coordinates give the full rational expansion, including ij. -/
theorem basis_expansion (a b c d : Rat) :
    ba (ba (scalar a) (bm (scalar b) gen3))
      (ba (bm (scalar c) gen23) (bm (scalar d) (bm gen3 gen23))) =
    ((a,b),(c,d)) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [scalar,gen3,gen23,ba,bm,qm,qa,qs] <;> grind

end Reimann.TameRationalField277
