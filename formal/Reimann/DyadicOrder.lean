import Reimann.DyadicMoments
import Reimann.DyadicLayers
import Reimann.DyadicBottom

/-! The cyclotomic scalar and the two moment hypotheses in the same
coherent 2-adic coordinates as the lattice. -/

namespace Reimann.DyadicOrder

open Reimann.DyadicLattice Reimann.DyadicMoments

theorem five_power_residue (r : Nat) :
    (natScalar (5^r)).residue 1 = 1 := by
  apply BitVec.eq_of_toNat_eq
  change 5^r % 4 = 1
  rw [Nat.pow_mod]
  simp

theorem five_power_odd (r : Nat) : (natScalar (5^r)).residue 0 = 1 := by
  rw [← (natScalar (5^r)).reduce (by decide : 0 ≤ 1), five_power_residue]
  rfl

/-- The unique compatible inverse of 5^r in the dyadic lattice coordinates. -/
noncomputable def inverseWeight (r : Nat) : Scalar :=
  Classical.choose (odd_scalar_inverse (natScalar (5^r)) (five_power_odd r))

theorem five_power_mul_inverse (r n : Nat) :
    (natScalar (5^r)).residue n * (inverseWeight r).residue n = 1 :=
  Classical.choose_spec (odd_scalar_inverse (natScalar (5^r)) (five_power_odd r)) n

theorem inverse_weight_mod_four (r : Nat) : (inverseWeight r).residue 1 = 1 := by
  have h := five_power_mul_inverse r 1
  rw [five_power_residue] at h
  bv_decide

theorem inverse_weight_one_mod_eight : (inverseWeight 1).residue 2 = 5 := by
  have h := five_power_mul_inverse 1 2
  change (5 : BitVec 3) * (inverseWeight 1).residue 2 = 1 at h
  exact (by decide : ∀ v : BitVec 3, 5*v = 1 → v = 5) _ h

/-- The two field-specific congruences still to construct. Here c0,c1 are
the actual Iwasawa coefficients when this predicate is used for Q(√(-69)).
The two odd unit residues may differ. -/
def WeightOneSamples (c0 c1 : Scalar) : Prop :=
  let a : Int := (c0.residue 2).toNat
  let b : Int := (c1.residue 2).toNat
  let s : Int := ((inverseWeight 1).residue 2).toNat
  ∃ u v : Int, u % 2 = 1 ∧ v % 2 = 1 ∧
    quadraticSample a b (s-1) % 8 = (u*realMoments.1) % 8 ∧
    quadraticSample a b (-s-1) % 8 = (v*realMoments.2) % 8

theorem moment_coefficient_bits {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) :
    c0.residue 2 = 4 ∧ c1.residue 1 = 2 := by
  unfold WeightOneSamples at H
  rw [inverse_weight_one_mod_eight] at H
  obtain ⟨u, v, hu, hv, hp, hm⟩ := H
  obtain ⟨h0,h1⟩ := coefficient_residues_of_mizusawa_samples
    (c0.residue 2).toNat (c1.residue 2).toNat 5 u v (by decide) hu hv hp hm
  constructor
  · exact (by decide : ∀ b : BitVec 3, (b.toNat : Int) % 8 = 4 → b = 4) _ h0
  · rw [← c1.reduce (by decide : 1 ≤ 2)]
    exact (by decide : ∀ b : BitVec 3, (b.toNat : Int) % 4 = 2 → b.setWidth 2 = 2) _ h1

/-- Cosets in X by the image of the actual companion difference, written
in the (2b,c) basis of X at a positive layer a=n+1. -/
def positiveCoset (c0 c1 : Scalar) (r n : Nat) (x y : Scalar × Scalar) : Prop :=
  let p := DyadicLayers.powerPair (DyadicLayers.companion c0 c1) (inverseWeight r) (n+1)
  ∃ v, let u := act (DyadicLayers.difference p.1 p.2) v
    DyadicQuotient.inAmbient x =
      (add (DyadicQuotient.inAmbient y).1 u.1, add (DyadicQuotient.inAmbient y).2 u.2)

theorem positive_coset_of_samples {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r n : Nat) :
    positiveCoset c0 c1 r n = DyadicQuotient.sameCoset (n+1) := by
  obtain ⟨hc0,hc1⟩ := moment_coefficient_bits H
  let p := DyadicLayers.powerPair (DyadicLayers.companion c0 c1) (inverseWeight r) (n+1)
  let D := DyadicLayers.difference p.1 p.2
  have image (y) : (∃ v, act D v = y) ↔
      ∃ v, scaleVector (natScalar (2^(n+2))) v = y :=
    DyadicLayers.positive_layer_image_of_residues c0 c1 _ hc0 hc1
      (inverse_weight_mod_four r) n y
  funext x y
  apply propext
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨z,hz⟩ := (image (act D v)).mp ⟨v,rfl⟩
    exact ⟨z, by dsimp only; rw [hz]; exact hv⟩
  · rintro ⟨z,hz⟩
    obtain ⟨v,hv⟩ := (image (scaleVector (natScalar (2^(n+2))) z)).mpr ⟨z,rfl⟩
    refine ⟨v, ?_⟩
    change DyadicQuotient.inAmbient x = (add _ (act D v).1, add _ (act D v).2)
    rw [hv]
    exact hz

/-- The layer-zero matrix and the positive-layer powers give relations on
the same pair of X-coordinates (coefficient of 2b, coefficient of c). -/
def latticeCoset (c0 c1 : Scalar) (r : Nat) : Nat → (Scalar × Scalar) → (Scalar × Scalar) → Prop
  | 0   => DyadicBottom.bottomClassRel c0 c1 (inverseWeight r)
  | n+1 => positiveCoset c0 c1 r n

/-- The moments imply the size of the lattice quotient for the explicit
scalar 5^(-r), at every layer. The arithmetic strict dual uses this quotient
at positive odd r. The lattice calculation itself permits every natural r. -/
theorem lattice_order_of_weight_one_samples {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r a : Nat) :
    ∃ encode : Quot (latticeCoset c0 c1 r a) → Fin (2^(2*a+1)),
    ∃ decode : Fin (2^(2*a+1)) → Quot (latticeCoset c0 c1 r a),
      (∀ x, decode (encode x) = x) ∧ (∀ i, encode (decode i) = i) := by
  cases a with
  | zero =>
    simp only [latticeCoset]
    obtain ⟨h0,h1⟩ := moment_coefficient_bits H
    obtain ⟨read, write, hr, hw, _, _⟩ :=
      DyadicBottom.coherent_bottom_quotient_of_residues c0 c1 _ h0 h1 (inverse_weight_mod_four r)
    refine ⟨fun x => (read x).toFin, fun i => write (BitVec.ofFin i), ?_, ?_⟩
    · intro x
      simpa only [BitVec.ofFin_toFin] using hw x
    · intro i
      simp [hr]
  | succ n =>
    simp only [latticeCoset]
    rw [positive_coset_of_samples H r n]
    exact DyadicQuotient.quotient_cardinality n

end Reimann.DyadicOrder
