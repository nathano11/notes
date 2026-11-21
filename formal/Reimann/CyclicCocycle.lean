import Reimann.CyclotomicNorm

namespace Reimann.CyclicCocycle

open Reimann.CyclotomicNorm

/-- The exponent in the actual finite cyclic group, represented in [0,L). -/
def exponent (L : Nat) (hL : 0 < L) (a : Nat) : Fin L :=
  ⟨a % L, Nat.mod_lt a hL⟩

/-- A normalized crossed homomorphism written in canonical residue representatives.
Both function inputs in the crossed law are reduced in the source cyclic group. -/
structure Crossed (M u : Int) (L : Nat) (hL : 0 < L) (f : Fin L → Int) : Prop where
  at_zero : f (exponent L hL 0) = 0
  add_rule (a b : Nat) : f (exponent L hL (a + b)) =
    (f (exponent L hL a) + u^a * f (exponent L hL b)) % M

theorem generator_formula {M u : Int} {L : Nat} {hL : 0 < L} {f : Fin L → Int}
    (hf : Crossed M u L hL f) (a : Nat) :
    f (exponent L hL a) = (geom u a * f (exponent L hL 1)) % M := by
  induction a with
  | zero => simp [geom, hf.at_zero]
  | succ a ih =>
    rw [hf.add_rule a 1, ih, geom, Int.add_mul]
    simp

theorem generator_norm {M u : Int} {L : Nat} {hL : 0 < L} {f : Fin L → Int}
    (hf : Crossed M u L hL f) : (geom u L * f (exponent L hL 1)) % M = 0 := by
  rw [← generator_formula hf L]
  simpa [exponent] using hf.at_zero

/-- The candidate with generator value z on the canonical finite representatives. -/
def fromGenerator (M u z : Int) {L : Nat} (i : Fin L) : Int := (geom u i.val * z) % M

theorem norm_multiple {M u z : Int} {L : Nat} (hz : (geom u L * z) % M = 0)
    (k : Nat) : (geom u (L*k) * z) % M = 0 := by
  rw [geom_blocks]
  have h : geom u L * geom (u^L) k * z = (geom u L * z) * geom (u^L) k := by grind
  rw [h, Int.mul_emod, hz]
  simp

theorem reduce_exponent {M u z : Int} {L : Nat} (hz : (geom u L * z) % M = 0)
    (a : Nat) : (geom u (a % L) * z) % M = (geom u a * z) % M := by
  have ha := Nat.mod_add_div a L
  conv => rhs; rw [← ha, geom_add, Int.add_mul, Int.mul_assoc]
  rw [Int.add_emod, Int.mul_emod (u^(a % L)), norm_multiple hz]
  simp

theorem fromGenerator_crossed {M u z : Int} {L : Nat} (hL : 0 < L)
    (hz : (geom u L * z) % M = 0) : Crossed M u L hL (fromGenerator M u z) := by
  constructor
  · simp [fromGenerator, exponent, geom]
  · intro a b
    change (geom u ((a+b)%L) * z) % M =
      ((geom u (a%L)*z)%M + u^a * ((geom u (b%L)*z)%M)) % M
    rw [reduce_exponent hz, reduce_exponent hz a, reduce_exponent hz b, geom_add,
      Int.add_mul, Int.mul_assoc]
    simp only [Int.emod_add_emod]
    rw [Int.add_emod, Int.add_emod (geom u a * z) (u^a * ((geom u b*z)%M)) M,
      Int.mul_emod (u^a) (geom u b*z) M, Int.mul_emod (u^a) ((geom u b*z)%M) M]
    simp

theorem fromGenerator_at_one {M u z : Int} {L : Nat} (hL : 0 < L)
    (hz : (geom u L * z) % M = 0) :
    fromGenerator M u z (exponent L hL 1) = z % M := by
  change (geom u (1 % L) * z) % M = z % M
  rw [reduce_exponent hz]
  simp [geom]

theorem reconstruct {M u : Int} {L : Nat} {hL : 0 < L} {f : Fin L → Int}
    (hf : Crossed M u L hL f) : f = fromGenerator M u (f (exponent L hL 1)) := by
  funext i
  have hi : exponent L hL i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [hi, fromGenerator] using generator_formula hf i.val

/-- The principal cocycle of w, evaluated on the finite source. -/
def principal (M u w : Int) {L : Nat} (i : Fin L) : Int := ((u^i.val-1)*w) % M

theorem principal_formula (M u w : Int) (L : Nat) :
    @principal M u w L = fromGenerator M u ((u-1)*w) := by
  funext i
  unfold principal fromGenerator
  have hi := geom_identity u i.val
  have h : (u^i.val - 1)*w = geom u i.val * ((u-1)*w) := by grind
  rw [h]

theorem principal_norm {M u : Int} {L : Nat} (hact : (u^L-1) % M = 0)
    (w : Int) : (geom u L * ((u-1)*w)) % M = 0 := by
  have hg := geom_identity u L
  have he : geom u L * ((u-1)*w) = (u^L-1)*w := by grind
  rw [he, Int.mul_emod, hact]
  simp

theorem principal_crossed {M u : Int} {L : Nat} (hL : 0 < L)
    (hact : (u^L-1) % M = 0) (w : Int) :
    Crossed M u L hL (principal M u w) := by
  rw [principal_formula]
  exact fromGenerator_crossed hL (principal_norm hact w)

theorem principal_at_one {M u : Int} {L : Nat} (hL : 0 < L)
    (hact : (u^L-1) % M = 0) (w : Int) :
    principal M u w (exponent L hL 1) = ((u-1)*w) % M := by
  rw [principal_formula]
  exact fromGenerator_at_one hL (principal_norm hact w)

theorem difference_at {M u : Int} {L : Nat} {hL : 0 < L} {f g : Fin L → Int}
    (hf : Crossed M u L hL f) (hg : Crossed M u L hL g) (i : Fin L) :
    (f i - g i) % M =
      (geom u i.val * (f (exponent L hL 1) - g (exponent L hL 1))) % M := by
  have hfi := congrFun (reconstruct hf) i
  have hgi := congrFun (reconstruct hg) i
  unfold fromGenerator at hfi hgi
  conv => lhs; rw [hfi, hgi]
  rw [Int.mul_sub, ← Int.sub_emod]

/-- Equality up to a given coboundary can be tested at the generator alone. -/
theorem differs_by_principal_iff {M u : Int} {L : Nat} {hL : 0 < L}
    {f g : Fin L → Int} (hf : Crossed M u L hL f) (hg : Crossed M u L hL g)
    (hact : (u^L-1) % M = 0) (w : Int) :
    (∀ i, (f i - g i) % M = principal M u w i) ↔
    (f (exponent L hL 1) - g (exponent L hL 1)) % M = ((u-1)*w) % M := by
  constructor
  · intro h
    simpa only [principal_at_one hL hact] using h (exponent L hL 1)
  · intro h i
    rw [difference_at hf hg, principal_formula]
    unfold fromGenerator
    rw [Int.mul_emod, h, ← Int.mul_emod]

theorem action_on_full_cycles {M u : Int} {L : Nat} (hact : (u^L - 1) % M = 0)
    (k : Nat) : (u^(L*k)) % M = 1 % M := by
  have hu : (u^L) % M = 1 % M := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hact
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Int.pow_add, Int.mul_emod, ih, hu, ← Int.mul_emod]
    simp

theorem action_reduce {M u : Int} {L : Nat} (hact : (u^L - 1) % M = 0)
    (a : Nat) : (u^a) % M = (u^(a%L)) % M := by
  conv => lhs; rw [← Nat.mod_add_div a L, Int.pow_add]
  rw [Int.mul_emod, action_on_full_cycles hact, ← Int.mul_emod, Int.mul_one]

/-- The crossed law quantified over exactly the elements of the finite source. -/
structure FiniteCrossed (M u : Int) (L : Nat) (hL : 0 < L) (f : Fin L → Int) : Prop where
  at_zero : f (exponent L hL 0) = 0
  add_rule (i j : Fin L) :
    f (exponent L hL (i.val+j.val)) = (f i + u^i.val * f j) % M

theorem finite_rule_of_crossed {M u : Int} {L : Nat} {hL : 0 < L} {f : Fin L → Int}
    (hf : Crossed M u L hL f) : FiniteCrossed M u L hL f := by
  refine ⟨hf.at_zero, ?_⟩
  intro i j
  have hi : exponent L hL i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hj : exponent L hL j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  simpa only [hi, hj] using hf.add_rule i.val j.val

theorem crossed_of_finite_rule {M u : Int} {L : Nat} {hL : 0 < L} {f : Fin L → Int}
    (hact : (u^L-1) % M = 0) (hf : FiniteCrossed M u L hL f) : Crossed M u L hL f := by
  refine ⟨hf.at_zero, ?_⟩
  intro a b
  have hab : exponent L hL ((a % L) + (b % L)) = exponent L hL (a+b) := by
    exact Fin.ext (Nat.add_mod a b L).symm
  have h := hf.add_rule (exponent L hL a) (exponent L hL b)
  change f (exponent L hL ((a % L)+(b % L))) =
    (f (exponent L hL a) + u^(a % L) * f (exponent L hL b)) % M at h
  rw [hab] at h
  rw [h]
  rw [Int.add_emod, Int.add_emod _ (u^a * _) M,
    Int.mul_emod (u^(a % L)) _ M, Int.mul_emod (u^a) _ M, action_reduce hact a]

/-- A prescribed canonical residue occurs on a unique finite cyclic cocycle precisely
when its cyclic norm is zero. This includes the cyclic group of order one. -/
theorem finite_generator_iff {M u z : Int} {L : Nat} (hL : 0 < L)
    (hact : (u^L-1) % M = 0) (hrep : z % M = z) :
    (geom u L * z) % M = 0 ↔
      ∃ f : Fin L → Int, FiniteCrossed M u L hL f ∧ f (exponent L hL 1) = z ∧
        ∀ g : Fin L → Int, FiniteCrossed M u L hL g → g (exponent L hL 1) = z → g = f := by
  constructor
  · intro hz
    refine ⟨fromGenerator M u z, finite_rule_of_crossed (fromGenerator_crossed hL hz),
      (fromGenerator_at_one hL hz).trans hrep, ?_⟩
    intro g hg hgen
    exact (reconstruct (crossed_of_finite_rule hact hg)).trans (by rw [hgen])
  · rintro ⟨f, hf, hgen, _⟩
    rw [← hgen]
    exact generator_norm (crossed_of_finite_rule hact hf)

/-- The odd-prime-power scalar really is an action of the finite source. -/
theorem cyclotomic_action_closes (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t : Int) (n : Nat) : ((1+(p : Int)*t)^(p^n : Nat)-1) % ((p : Int)^n) = 0 := by
  rw [← geom_identity (1+(p : Int)*t) (p^n), Int.mul_comm]
  exact norm_action_zero p q hp t _ n

/-- On the length-p^n group and coefficients modulo p^n, every canonical
residue extends uniquely to a crossed homomorphism for u = 1+pt. -/
theorem cyclotomic_cocycle_unique (p q : Nat) (hp : (p : Int) = 2*(q : Int)+1)
    (t z : Int) (n : Nat) (hL : 0 < p^n) (hrep : z % ((p : Int)^n) = z) :
    ∃ f : Fin (p^n) → Int, FiniteCrossed ((p : Int)^n) (1+(p : Int)*t) (p^n) hL f ∧
      f (exponent (p^n) hL 1) = z ∧
      ∀ g : Fin (p^n) → Int, FiniteCrossed ((p : Int)^n) (1+(p : Int)*t) (p^n) hL g →
        g (exponent (p^n) hL 1) = z → g = f := by
  exact (finite_generator_iff hL (cyclotomic_action_closes p q hp t n) hrep).mp
    (norm_action_zero p q hp t z n)

end Reimann.CyclicCocycle
