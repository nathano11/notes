import Reimann.DyadicOrder

/-! Additive invariant factors of the positive-layer companion quotient.
The layer is `a = n+1`. The coordinates are the coefficients of `2b,c`
in the strict lattice, so reduction retains respectively `a` and `a+1` bits. -/

namespace Reimann.DyadicPositiveFactors

open Reimann.DyadicLattice Reimann.DyadicOrder Reimann.DyadicQuotient

abbrev Factors (n : Nat) := BitVec (n+1) × BitVec (n+2)

abbrev Q (c0 c1 : Scalar) (r n : Nat) := Quot (latticeCoset c0 c1 r (n+1))

theorem related_iff {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r n : Nat) (x y : Scalar × Scalar) :
    latticeCoset c0 c1 r (n+1) x y ↔ residuePair n x = residuePair n y := by
  change positiveCoset c0 c1 r n x y ↔ _
  rw [positive_coset_of_samples H r n]
  exact sameCoset_iff_residuePair n x y

/-- Reduction of each coordinate descends to the actual companion quotient. -/
def encode {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat) :
    Q c0 c1 r n → Factors n :=
  Quot.lift (residuePair n) (fun x y h => (related_iff H r n x y).mp h)

/-- Lift each residue using its least nonnegative integer representative. -/
def decode (c0 c1 : Scalar) (r n : Nat) (p : Factors n) : Q c0 c1 r n :=
  Quot.mk _ (natScalar p.1.toNat, natScalar p.2.toNat)

theorem encode_mk {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat)
    (x : Scalar × Scalar) : encode H r n (Quot.mk _ x) = residuePair n x := rfl

theorem encode_decode {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat)
    (p : Factors n) : encode H r n (decode c0 c1 r n p) = p :=
  residuePair_section n p

theorem decode_encode {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat)
    (x : Q c0 c1 r n) : decode c0 c1 r n (encode H r n x) = x := by
  induction x using Quot.ind with
  | mk v =>
    apply Quot.sound
    exact (related_iff H r n _ v).mpr (residuePair_section n (residuePair n v))

/-- Addition modulo each of the two advertised powers of two. -/
def factorAdd {n : Nat} (x y : Factors n) : Factors n := (x.1+y.1, x.2+y.2)

/-- Addition on classes, with the representative formula proved below. -/
def quotientAdd {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat)
    (x y : Q c0 c1 r n) : Q c0 c1 r n :=
  decode c0 c1 r n (factorAdd (encode H r n x) (encode H r n y))

theorem encode_add {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat)
    (x y : Q c0 c1 r n) : encode H r n (quotientAdd H r n x y) =
      factorAdd (encode H r n x) (encode H r n y) :=
  encode_decode H r n _

/-- Transported addition is precisely addition of arbitrary lattice representatives. -/
theorem quotientAdd_mk {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat)
    (x y : Scalar × Scalar) :
    quotientAdd H r n (Quot.mk _ x) (Quot.mk _ y) =
      Quot.mk _ (add x.1 y.1, add x.2 y.2) := by
  exact decode_encode H r n (Quot.mk _ (add x.1 y.1, add x.2 y.2))

theorem decode_add {c0 c1 : Scalar} (H : WeightOneSamples c0 c1) (r n : Nat)
    (x y : Factors n) : decode c0 c1 r n (factorAdd x y) =
      quotientAdd H r n (decode c0 c1 r n x) (decode c0 c1 r n y) := by
  simp only [quotientAdd, encode_decode]

/-- At every positive layer the two residue maps are mutually inverse and
the map to the cyclic factors is additive on the lattice quotient. -/
theorem positive_invariant_factors {c0 c1 : Scalar} (H : WeightOneSamples c0 c1)
    (r n : Nat) :
    Function.LeftInverse (decode c0 c1 r n) (encode H r n) ∧
    Function.RightInverse (decode c0 c1 r n) (encode H r n) ∧
    ∀ x y, encode H r n (quotientAdd H r n x y) =
      factorAdd (encode H r n x) (encode H r n y) :=
  ⟨decode_encode H r n, encode_decode H r n, encode_add H r n⟩

end Reimann.DyadicPositiveFactors
