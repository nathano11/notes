import Reimann.DyadicIntegralPlaces
import Reimann.DyadicFieldTrace69
import Reimann.Dyadic
import Reimann.TameBiquadratic277

/-! Reduction and completion in the integral basis (1,e,w,ew) at (3,23). -/

namespace Reimann.DyadicOrderCompletion69

open Lean.Grind
open Reimann.Dyadic (Matrix)
open Reimann.TameBiquadratic277 (Quad componentAdd)

def coords (x : Matrix) : Quad Int := ((x.a,x.b),(x.c,x.d))

def fromCoords (x : Quad Int) : Matrix := ⟨x.1.1,x.1.2,x.2.1,x.2.2⟩

def mapFour {R S : Type} (f : R → S) (x : Quad R) : Quad S :=
  ((f x.1.1,f x.1.2),(f x.2.1,f x.2.2))

def pairProduct {R : Type} [CommRing R] (x y : R × R) : R × R :=
  (x.1*y.1-x.2*y.2, x.1*y.2+x.2*y.1+x.2*y.2)

/-- The multiplication laws are e²=e−1 and w²=w−6. -/
def product {R : Type} [CommRing R] (x y : Quad R) : Quad R :=
  let ac := pairProduct x.1 y.1
  let bd := pairProduct x.2 y.2
  let ad := pairProduct x.1 y.2
  let bc := pairProduct x.2 y.1
  ((ac.1-6*bd.1,ac.2-6*bd.2),(ad.1+bc.1+bd.1,ad.2+bc.2+bd.2))

def integerSum (x y : Matrix) : Matrix := fromCoords (componentAdd (coords x) (coords y))

def integerProduct (x y : Matrix) : Matrix := fromCoords (product (coords x) (coords y))

def integerReduction (n : Nat) (x : Matrix) : Quad (BitVec (n+1)) :=
  mapFour (BitVec.ofInt (n+1)) (coords x)

theorem integer_reduction_add (n : Nat) (x y : Matrix) :
    integerReduction n (integerSum x y) = componentAdd (integerReduction n x) (integerReduction n y) := by
  simp [integerReduction,integerSum,coords,fromCoords,mapFour,componentAdd,BitVec.ofInt_add]

theorem integer_reduction_mul (n : Nat) (x y : Matrix) :
    integerReduction n (integerProduct x y) = product (integerReduction n x) (integerReduction n y) := by
  simp [integerReduction,integerProduct,coords,fromCoords,mapFour,product,pairProduct,
    Int.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.ofInt_add,BitVec.ofInt_neg,BitVec.ofInt_mul]

theorem integer_reduction_surjective (n : Nat) (y : Quad (BitVec (n+1))) :
    ∃ x, integerReduction n x = y := by
  refine ⟨fromCoords (mapFour (fun b : BitVec (n+1) => (b.toNat : Int)) y), ?_⟩
  simp [integerReduction,fromCoords,coords,mapFour,BitVec.ofNat_toNat]

theorem word_equal_iff_multiple (n : Nat) (a b : Int) :
    BitVec.ofInt (n+1) a = BitVec.ofInt (n+1) b ↔ ∃ z : Int, a = b + (2:Int)^(n+1)*z := by
  let m : Int := (2^(n+1) : Nat)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Nat.two_pow_pos (n+1)
  have hpow : m = (2:Int)^(n+1) := by simp [m]
  rw [← hpow, ← BitVec.toNat_inj, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  change (a%m).toNat = (b%m).toNat ↔ _
  have ha := Int.emod_nonneg a (by omega : m ≠ 0)
  have hb := Int.emod_nonneg b (by omega : m ≠ 0)
  constructor
  · intro h
    have he : a%m = b%m := by omega
    obtain ⟨z,hz⟩ := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he)
    exact ⟨z,by omega⟩
  · rintro ⟨z,hz⟩
    have he : m ∣ a-b := ⟨z,by omega⟩
    exact congrArg Int.toNat (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd he))

/-- The kernel at depth n+1 consists precisely of 2^(n+1) times the order. -/
theorem integer_reduction_eq_iff (n : Nat) (x y : Matrix) :
    integerReduction n x = integerReduction n y ↔
      ∃ t : Matrix, x = integerSum y (Dyadic.scale ((2:Int)^(n+1)) t) := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := (word_equal_iff_multiple n x.a y.a).mp (congrArg (fun v => v.1.1) h)
    obtain ⟨b,hb⟩ := (word_equal_iff_multiple n x.b y.b).mp (congrArg (fun v => v.1.2) h)
    obtain ⟨c,hc⟩ := (word_equal_iff_multiple n x.c y.c).mp (congrArg (fun v => v.2.1) h)
    obtain ⟨d,hd⟩ := (word_equal_iff_multiple n x.d y.d).mp (congrArg (fun v => v.2.2) h)
    refine ⟨⟨a,b,c,d⟩, ?_⟩
    cases x
    simp_all [integerSum,coords,fromCoords,componentAdd,Dyadic.scale]
  · rintro ⟨t,rfl⟩
    apply Prod.ext <;> apply Prod.ext
    · exact (word_equal_iff_multiple n _ _).mpr ⟨t.a,rfl⟩
    · exact (word_equal_iff_multiple n _ _).mpr ⟨t.b,rfl⟩
    · exact (word_equal_iff_multiple n _ _).mpr ⟨t.c,rfl⟩
    · exact (word_equal_iff_multiple n _ _).mpr ⟨t.d,rfl⟩

theorem truncate_signed {i j : Nat} (h : i ≤ j) (z : Int) :
    (BitVec.ofInt (j+1) z).setWidth (i+1) = BitVec.ofInt (i+1) z := by
  cases z with
  | ofNat a => exact BitVec.setWidth_ofNat_of_le (by omega) _
  | negSucc a =>
    change (BitVec.ofInt (j+1) (-((a+1 : Nat) : Int))).setWidth (i+1) =
      BitVec.ofInt (i+1) (-((a+1 : Nat) : Int))
    simp only [BitVec.ofInt_neg,BitVec.ofInt_natCast,BitVec.setWidth_neg_of_le (by omega : i+1 ≤ j+1),
      BitVec.setWidth_ofNat_of_le (by omega : i+1 ≤ j+1)]

/-- The inverse limit of the finite quotient algebras, with all transition maps. -/
structure Completion where
  level (n : Nat) : Quad (BitVec (n+1))
  compatible {i j : Nat} (h : i ≤ j) : mapFour (BitVec.setWidth (i+1)) (level j) = level i

def integerPoint (x : Matrix) : Completion where
  level n := integerReduction n x
  compatible h := by
    apply Prod.ext <;> apply Prod.ext <;> apply truncate_signed h

theorem completion_ext {x y : Completion} (h : ∀ n, x.level n = y.level n) : x = y := by
  cases x; cases y
  congr
  exact funext h

open Reimann.DyadicLattice (Scalar scalar_ext natScalar)
open Reimann.DyadicIntegralPlaces (Order)

def fromOrder (x : Order) : Completion where
  level n := mapFour (fun v : Scalar => v.residue n) x
  compatible h := by
    apply Prod.ext <;> apply Prod.ext <;> exact Scalar.reduce _ h

def toOrder (x : Completion) : Order :=
  ((⟨fun n => (x.level n).1.1, fun h => congrArg (fun z => z.1.1) (x.compatible h)⟩,
    ⟨fun n => (x.level n).1.2, fun h => congrArg (fun z => z.1.2) (x.compatible h)⟩),
   (⟨fun n => (x.level n).2.1, fun h => congrArg (fun z => z.2.1) (x.compatible h)⟩,
    ⟨fun n => (x.level n).2.2, fun h => congrArg (fun z => z.2.2) (x.compatible h)⟩))

theorem completion_inverse :
    (∀ x : Completion, fromOrder (toOrder x) = x) ∧
    (∀ x : Order, toOrder (fromOrder x) = x) :=
  ⟨fun _ => completion_ext (fun _ => rfl), fun _ => rfl⟩

theorem embed_integerSum (x y : Matrix) :
    DyadicFieldTrace69.embed (integerSum x y) =
      TameRationalField277.ba (DyadicFieldTrace69.embed x) (DyadicFieldTrace69.embed y) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [DyadicFieldTrace69.embed,DyadicBasisComparison.fromIntegral,
      TameRationalField277.ba,TameRationalField277.qa,integerSum,coords,fromCoords,componentAdd,
      Ring.intCast_add] <;> grind

theorem embed_integerProduct (x y : Matrix) :
    DyadicFieldTrace69.embed (integerProduct x y) =
      TameRationalField277.bm (DyadicFieldTrace69.embed x) (DyadicFieldTrace69.embed y) := by
  have hh := DyadicFieldTrace69.twice_half
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [DyadicFieldTrace69.embed,DyadicBasisComparison.fromIntegral,integerProduct,
      coords,fromCoords,product,pairProduct,TameRationalField277.bm,TameRationalField277.qa,
      TameRationalField277.qm,TameRationalField277.qs,Ring.intCast_sub,Ring.intCast_add,
      Ring.intCast_mul] <;> grind

def completedSum (x y : Completion) : Completion where
  level n := componentAdd (x.level n) (y.level n)
  compatible {i j} hij := by
    change mapFour _ (componentAdd _ _) = _
    calc
      _ = componentAdd (mapFour (BitVec.setWidth (i+1)) (x.level j))
          (mapFour (BitVec.setWidth (i+1)) (y.level j)) := by
        simp only [mapFour,componentAdd,BitVec.setWidth_add _ _ (show i+1 ≤ j+1 by omega)]
      _ = _ := by rw [x.compatible hij, y.compatible hij]

def completedProduct (x y : Completion) : Completion where
  level n := product (x.level n) (y.level n)
  compatible {i j} hij := by
    change mapFour _ (product _ _) = _
    calc
      _ = product (mapFour (BitVec.setWidth (i+1)) (x.level j))
          (mapFour (BitVec.setWidth (i+1)) (y.level j)) := by
        have h : i+1 ≤ j+1 := by omega
        have h6 : (6 : BitVec (j+1)).setWidth (i+1) = 6 := BitVec.setWidth_ofNat_of_le h 6
        simp only [mapFour,product,pairProduct,BitVec.sub_eq_add_neg,BitVec.setWidth_add _ _ h,
          BitVec.setWidth_mul _ _ h,BitVec.setWidth_neg_of_le h,h6]
      _ = _ := by rw [x.compatible hij, y.compatible hij]

theorem completion_add (x y : Order) :
    fromOrder (DyadicIntegralPlaces.sum x y) = completedSum (fromOrder x) (fromOrder y) := by
  exact completion_ext (fun _ => rfl)

theorem completion_mul (x y : Order) :
    fromOrder (DyadicPlaceAlgebra.product (natScalar 1) (natScalar 6) x y) =
      completedProduct (fromOrder x) (fromOrder y) := by
  apply completion_ext
  intro n
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [fromOrder,completedProduct,mapFour,product,pairProduct,DyadicPlaceAlgebra.product,
      DyadicPlaceAlgebra.plus,DyadicPlaceAlgebra.minus,DyadicInert.product,
      DyadicLattice.scaleVector,DyadicLattice.add,DyadicLattice.neg,DyadicLattice.mul,natScalar] <;> grind

/-- Every compatible class at any given depth has a lift from the global order. -/
theorem integer_dense (z : Completion) (n : Nat) : ∃ x, (integerPoint x).level n = z.level n :=
  integer_reduction_surjective n (z.level n)

/-- The inverse maps identify multiplication, addition and the zero and unit elements. -/
theorem completion_algebra_iso :
    (∀ z : Completion, fromOrder (toOrder z) = z) ∧
    (∀ x : Order, toOrder (fromOrder x) = x) ∧
    fromOrder DyadicIntegralPlaces.zero = integerPoint ⟨0,0,0,0⟩ ∧
    fromOrder DyadicIntegralPlaces.one = integerPoint ⟨1,0,0,0⟩ ∧
    (∀ x y, fromOrder (DyadicIntegralPlaces.sum x y) = completedSum (fromOrder x) (fromOrder y)) ∧
    (∀ x y, fromOrder (DyadicPlaceAlgebra.product (natScalar 1) (natScalar 6) x y) =
      completedProduct (fromOrder x) (fromOrder y)) :=
  ⟨completion_inverse.1,completion_inverse.2,completion_ext (fun _ => rfl),
   completion_ext (fun _ => rfl),completion_add,completion_mul⟩

end Reimann.DyadicOrderCompletion69
