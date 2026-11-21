import Reimann.DyadicZeroValues
import Reimann.DyadicClass69

/-! The projection of the signed Stickelberger sum to Γ/Γ² at conductor
8·69. In C₂ each element equals its inverse. Modulo 8 the two projected
rows are associated if the actual tower polynomial and Φ differ by a unit
and the half-normalized Stickelberger row represents Φ. -/

namespace Reimann.DyadicStickelberger69

open Reimann.DyadicZeroValues Reimann.DyadicLattice Reimann.DyadicOrder

def inGeneratorCoset (a : Nat) : Bool := a%8==3 || a%8==5

/-- An odd residue is its own inverse modulo eight. The pairs ±1 and ±5
are the identity and generator cosets in the real cyclotomic quotient. -/
theorem inverse_coset (a : Nat) (ha : a%2 = 1) :
    (a*a)%8 = 1 ∧
    ((inGeneratorCoset a = false ↔ a%8=1 ∨ a%8=7) ∧
     (inGeneratorCoset a = true ↔ a%8=5 ∨ a%8=3)) := by
  have H : ∀ t : Fin 8, t.val%2=1 → (t.val*t.val)%8=1 ∧
      ((inGeneratorCoset t.val = false ↔ t.val=1 ∨ t.val=7) ∧
       (inGeneratorCoset t.val = true ↔ t.val=5 ∨ t.val=3)) := by decide
  have h := H ⟨a%8, Nat.mod_lt _ (by decide)⟩ (by
    change (a%8)%2 = 1
    rw [Nat.mod_mod_of_dvd _ (by decide : 2∣8),ha])
  simpa [inGeneratorCoset, ← Nat.mul_mod] using h

/-- The χ₆₉ω⁻¹-weighted constant and linear terms of B₁ in each coset. -/
def cosetMoments (generator : Bool) : Int × Int :=
  moments 552 (fun b => if inGeneratorCoset b = generator then chi276 b else 0)

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem identity_coset_moments : cosetMoments false = (0,-4416) := by decide

theorem generator_coset_moments : cosetMoments true = (0,0) := by decide

/-- Clearing 2·552 in −Σχ₆₉(a)ω⁻¹(a)(a/552−1/2)[σ_{⟨a⟩}⁻¹]. -/
def signedNumerator (generator : Bool) : Int :=
  let S := cosetMoments generator
  552*S.1-2*S.2

theorem signed_row_exact :
    signedNumerator false = (2*552:Int)*8 ∧ signedNumerator true = 0 := by
  simp [signedNumerator, identity_coset_moments, generator_coset_moments]

/-- Half of the signed row, reduced in (Z/8)[C₂] after integer division. -/
def halfRow : BitVec 3 × BitVec 3 :=
  (BitVec.ofInt 3 (signedNumerator false / (4*552)),
   BitVec.ofInt 3 (signedNumerator true / (4*552)))

theorem half_row_exact : halfRow = (4,0) := by
  obtain ⟨hp,hm⟩ := signed_row_exact
  unfold halfRow
  rw [hp,hm]
  decide

/-- Convolution on (Z/8)[C₂], in the ordered basis [1],[γ]. -/
def rowMul (x y : BitVec 3 × BitVec 3) : BitVec 3 × BitVec 3 :=
  (x.1*y.1+x.2*y.2, x.1*y.2+x.2*y.1)

/-- Projection of the actual coherent coefficients via T↦[γ]−[1]. -/
def polynomialRow (c0 c1 : Scalar) : BitVec 3 × BitVec 3 :=
  let t : BitVec 3 × BitVec 3 := (-1,1)
  let q := rowMul (t.1+c1.residue 2,t.2) t
  (q.1+c0.residue 2,q.2)

theorem polynomial_row_coordinates (c0 c1 : Scalar) :
    polynomialRow c0 c1 = (c0.residue 2-c1.residue 2+2,c1.residue 2-2) := by
  simp only [polynomialRow,rowMul]
  apply Prod.ext <;> grind

/-- Field-specific projection obligation. For the actual coherent coefficients
of the tower over Q(√−69), project the association of P and Φ into the
finite group ring and identify Φ's row with the half-normalized row above. -/
def StickelbergerProjection69 (c0 c1 : Scalar) : Prop :=
  ∃ u v : BitVec 3 × BitVec 3,
    rowMul u v = (1,0) ∧ polynomialRow c0 c1 = rowMul u halfRow

/-- A unit row remains invertible under both character evaluations γ↦±1. -/
theorem unit_at_two_signs {u v : BitVec 3 × BitVec 3} (h : rowMul u v = (1,0)) :
    (u.1+u.2)*(v.1+v.2) = 1 ∧ (u.1-u.2)*(v.1-v.2) = 1 := by
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
  constructor <;> grind

theorem four_times_unit (u v : BitVec 3) (h : u*v = 1) : 4*u = 4 := by
  exact (by decide : ∀ x y : BitVec 3, x*y=1 → 4*x=4) u v h

theorem signed_evaluations_of_projection {c0 c1 : Scalar}
    (h : StickelbergerProjection69 c0 c1) :
    c0.residue 2 = 4 ∧ 4-2*c1.residue 2+c0.residue 2 = 4 := by
  obtain ⟨u,v,hu,hp⟩ := h
  obtain ⟨aug,sgn⟩ := unit_at_two_signs hu
  have ha := four_times_unit _ _ aug
  have hs := four_times_unit _ _ sgn
  rw [half_row_exact, polynomial_row_coordinates] at hp
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj hp
  constructor <;> grind

/-- The finite projected association for the coherent coefficients suffices
for the entire positive-odd-weight strict lattice calculation at (3,23). -/
theorem samples_of_stickelberger_projection (c0 c1 : Scalar)
    (h : StickelbergerProjection69 c0 c1) : WeightOneSamples c0 c1 :=
  let e := signed_evaluations_of_projection h
  Reimann.DyadicClass69.samples_of_zero_and_minus_two c0 c1 e.1 e.2

theorem lattice_order_of_stickelberger_projection (c0 c1 : Scalar)
    (h : StickelbergerProjection69 c0 c1) (r a : Nat) :
    ∃ encode : Quot (latticeCoset c0 c1 r a) → Fin (2^(2*a+1)),
    ∃ decode : Fin (2^(2*a+1)) → Quot (latticeCoset c0 c1 r a),
      (∀ x, decode (encode x) = x) ∧ (∀ i, encode (decode i) = i) :=
  lattice_order_of_weight_one_samples (samples_of_stickelberger_projection c0 c1 h) r a

/-- Equality of principal ideals after projecting to (Z/8)[C₂], expressed
by divisibility in each direction. Both multipliers are unrestricted. -/
def ProjectedIdeal69 (c0 c1 : Scalar) : Prop :=
  ∃ u v : BitVec 3 × BitVec 3,
    polynomialRow c0 c1 = rowMul u halfRow ∧ halfRow = rowMul v (polynomialRow c0 c1)

/-- The only generator of the ideal (4) in Z/8 is 4. -/
theorem mutual_four (x u v : BitVec 3) (hu : x=u*4) (hv : 4=v*x) : x=4 := by
  exact (by decide : ∀ x u v : BitVec 3, x=u*4 → 4=v*x → x=4) x u v hu hv

theorem signed_evaluations_of_ideal {c0 c1 : Scalar} (h : ProjectedIdeal69 c0 c1) :
    c0.residue 2 = 4 ∧ 4-2*c1.residue 2+c0.residue 2 = 4 := by
  obtain ⟨u,v,hu,hv⟩ := h
  rw [polynomial_row_coordinates,half_row_exact] at hu
  rw [polynomial_row_coordinates,half_row_exact] at hv
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj hu
  obtain ⟨h₃,h₄⟩ := Prod.mk.inj hv
  constructor
  · apply mutual_four _ (u.1+u.2) (v.1+v.2) <;> grind
  · apply mutual_four _ (u.1-u.2) (v.1-v.2) <;> grind

theorem samples_of_projected_ideal (c0 c1 : Scalar) (h : ProjectedIdeal69 c0 c1) :
    WeightOneSamples c0 c1 :=
  let e := signed_evaluations_of_ideal h
  Reimann.DyadicClass69.samples_of_zero_and_minus_two c0 c1 e.1 e.2

/-- One projected ideal identity suffices for the exact order in every layer. -/
theorem lattice_order_of_projected_ideal (c0 c1 : Scalar) (h : ProjectedIdeal69 c0 c1)
    (r a : Nat) :
    ∃ encode : Quot (latticeCoset c0 c1 r a) → Fin (2^(2*a+1)),
    ∃ decode : Fin (2^(2*a+1)) → Quot (latticeCoset c0 c1 r a),
      (∀ x, decode (encode x) = x) ∧ (∀ i, encode (decode i) = i) :=
  lattice_order_of_weight_one_samples (samples_of_projected_ideal c0 c1 h) r a

end Reimann.DyadicStickelberger69
