import Std

namespace Reimann.BoundaryLifts

/-- Multiplying a fraction of denominator S*T by T lifts the class b/S
exactly when its numerator differs from b by a multiple of S. -/
theorem numerator_lift_iff {S T b k : Int} (hT : T ≠ 0) :
    (S*T ∣ T*k - T*b) ↔ ∃ j : Int, k = b + S*j := by
  constructor
  · rintro ⟨j, hj⟩
    have hm : T*(k-b) = T*(S*j) := by grind
    have he := Int.eq_of_mul_eq_mul_left hT hm
    exact ⟨j, by omega⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, by grind⟩

/-- The difference of the lifted fraction under u, written with denominator
T; the choice j contributes the usual principal value (u-1)*j. -/
theorem connecting_numerator {S T b k u c : Int} (hT : T ≠ 0)
    (hu : u-1 = S*c) (hlift : S*T ∣ T*k - T*b) :
    ∃ j : Int, k = b+S*j ∧ (u-1)*k = S*(c*b+(u-1)*j) := by
  obtain ⟨j, hj⟩ := (numerator_lift_iff hT).mp hlift
  exact ⟨j, hj, by rw [hu, hj]; grind⟩

/-- Equality of residues modulo m, after also allowing multiples of d. -/
def sameClass (m d x y : Int) : Prop :=
  ∃ a b : Int, y-x = m*a + d*b

/-- The map from invariant classes modulo T to generator values modulo
principal cocycles identifies their relations. The coefficient i is an
inverse to c modulo T. -/
theorem connecting_class_iff {S T c i j : Int} (hunit : i*c+T*j = 1)
    (b b' : Int) :
    sameClass T (S*c) (c*b) (c*b') ↔ sameClass S T b b' := by
  constructor
  · rintro ⟨a,k,h⟩
    have hd : c*(b'-b-S*k) = T*a := by grind
    have hz : b'-b-S*k = T*(i*a+j*(b'-b-S*k)) := by
      calc
        b'-b-S*k = (i*c+T*j)*(b'-b-S*k) := by rw [hunit]; simp
        _ = i*(c*(b'-b-S*k))+T*j*(b'-b-S*k) := by grind
        _ = T*(i*a+j*(b'-b-S*k)) := by rw [hd]; grind
    exact ⟨k, i*a+j*(b'-b-S*k), by omega⟩
  · rintro ⟨k,a,h⟩
    refine ⟨c*a,k, ?_⟩
    calc
      c*b'-c*b = c*(b'-b) := by grind
      _ = T*(c*a)+(S*c)*k := by rw [h]; grind

/-- Every generator value is the connecting value of an explicit preimage. -/
theorem connecting_class_surjective {S T c i j : Int} (hunit : i*c+T*j = 1)
    (z : Int) : sameClass T (S*c) (c*(i*z)) z := by
  refine ⟨j*z,0, ?_⟩
  calc
    z-c*(i*z) = (i*c+T*j)*z-c*(i*z) := by rw [hunit]; simp
    _ = _ := by grind

/-- For two powers of the same base the quotient relation is congruence
modulo the smaller power. This holds at depth zero as well. -/
theorem powers_sameClass (p : Int) (w n : Nat) (b b' : Int) :
    sameClass (p^w) (p^n) b b' ↔ p^(min w n) ∣ b'-b := by
  by_cases h : w ≤ n
  · rw [Nat.min_eq_left h]
    have e : p^n = p^w * p^(n-w) := by
      rw [← Int.pow_add]; exact congrArg (p^·) (by omega)
    constructor
    · rintro ⟨a,k,hk⟩
      exact ⟨a+p^(n-w)*k, by rw [hk,e]; grind⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,0, by simpa using ha⟩
  · rw [Nat.min_eq_right (by omega)]
    have e : p^w = p^n * p^(w-n) := by
      rw [← Int.pow_add]; exact congrArg (p^·) (by omega)
    constructor
    · rintro ⟨a,k,hk⟩
      exact ⟨p^(w-n)*a+k, by rw [hk,e]; grind⟩
    · rintro ⟨a,ha⟩
      exact ⟨0,a, by simpa using ha⟩

/-- At depth n and invariant denominator p^w, two boundary generator values
represent the same class exactly when the original numerators agree modulo
p^min(w,n). Every generator class occurs. -/
theorem exceptional_boundary_parameters (p c i j : Int) (w n : Nat)
    (hunit : i*c+p^n*j = 1) :
    (∀ b b' : Int, sameClass (p^n) (p^w*c) (c*b) (c*b') ↔
      p^(min w n) ∣ b'-b) ∧
    (∀ z : Int, sameClass (p^n) (p^w*c) (c*(i*z)) z) :=
  ⟨fun b b' => (connecting_class_iff hunit b b').trans
    (powers_sameClass p w n b b'), connecting_class_surjective hunit⟩

theorem inverse_class_respects {S T c i j : Int} (hunit : i*c+T*j = 1)
    (z z' : Int) (h : sameClass T (S*c) z z') : sameClass S T (i*z) (i*z') := by
  obtain ⟨a,k,hk⟩ := h
  have hi : i*c = 1-T*j := by omega
  refine ⟨k,i*a-j*S*k, ?_⟩
  calc
    i*z' - i*z = i*(z'-z) := by grind
    _ = i*T*a+S*(i*c)*k := by rw [hk]; grind
    _ = _ := by rw [hi]; grind

/-- The connecting map on actual quotient types. -/
def boundaryOnQuotient {S T c i j : Int} (hunit : i*c+T*j = 1) :
    Quot (sameClass S T) → Quot (sameClass T (S*c)) :=
  Quot.lift (fun b => Quot.mk _ (c*b))
    (fun b b' h => Quot.sound ((connecting_class_iff hunit b b').mpr h))

def liftFromQuotient {S T c i j : Int} (hunit : i*c+T*j = 1) :
    Quot (sameClass T (S*c)) → Quot (sameClass S T) :=
  Quot.lift (fun z => Quot.mk _ (i*z))
    (fun z z' h => Quot.sound (inverse_class_respects hunit z z' h))

theorem boundary_left_inverse {S T c i j : Int} (hunit : i*c+T*j = 1)
    (x : Quot (sameClass S T)) :
    liftFromQuotient hunit (boundaryOnQuotient hunit x) = x := by
  induction x using Quot.ind with
  | mk b =>
    apply Quot.sound
    refine ⟨0,j*b,?_⟩
    change b-i*(c*b) = S*0+T*(j*b)
    calc
      b-i*(c*b) = (i*c+T*j)*b-i*(c*b) := by rw [hunit]; simp
      _ = _ := by grind

theorem boundary_right_inverse {S T c i j : Int} (hunit : i*c+T*j = 1)
    (x : Quot (sameClass T (S*c))) :
    boundaryOnQuotient hunit (liftFromQuotient hunit x) = x := by
  induction x using Quot.ind with
  | mk z => exact Quot.sound (connecting_class_surjective hunit z)

def residue (m : Nat) (hm : 0 < m) (b : Int) : Fin m :=
  let hpos := Int.natCast_pos.mpr hm
  let r := b % (m : Int)
  ⟨r.toNat, (Int.toNat_lt (Int.emod_nonneg _ (by omega : (m : Int) ≠ 0))).mpr
    (Int.emod_lt_of_pos _ hpos)⟩

theorem residue_value (m : Nat) (hm : 0 < m) (b : Int) :
    ((residue m hm b).val : Int) = b % (m : Int) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

/-- Canonical representative of an invariant numerator class. -/
def sourceRepresentative (p w n : Nat) (hp : 0 < p) :
    Quot (sameClass ((p : Int)^w) ((p : Int)^n)) → Fin (p^(min w n)) :=
  Quot.lift (residue _ (Nat.pow_pos hp)) (by
    intro b b' h
    have hd := (powers_sameClass (p : Int) w n b b').mp h
    rw [← Int.natCast_pow] at hd
    have hr := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)
    apply Fin.ext
    change (b % ((p^(min w n) : Nat) : Int)).toNat =
      (b' % ((p^(min w n) : Nat) : Int)).toNat
    rw [hr])

theorem finite_representative_roundtrip (p w n : Nat) (hp : 0 < p)
    (a : Fin (p^(min w n))) :
    sourceRepresentative p w n hp (Quot.mk _ (a.val : Int)) = a := by
  apply Fin.ext
  change (((a.val : Int) % ((p^(min w n) : Nat) : Int)).toNat) = a.val
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr a.isLt)]
  rfl

theorem source_representative_roundtrip (p w n : Nat) (hp : 0 < p)
    (x : Quot (sameClass ((p : Int)^w) ((p : Int)^n))) :
    Quot.mk _ ((sourceRepresentative p w n hp x).val : Int) = x := by
  induction x using Quot.ind with
  | mk b =>
    apply Quot.sound
    apply (powers_sameClass _ w n _ _).mpr
    change (p : Int)^(min w n) ∣ b-((residue _ (Nat.pow_pos hp) b).val : Int)
    rw [← Int.natCast_pow, residue_value]
    exact ⟨b / ((p^(min w n) : Nat) : Int),
      by have h := Int.emod_add_mul_ediv b ((p^(min w n) : Nat) : Int); omega⟩

/-- The finite generator-value quotient has exactly p^min(w,n) classes.
The forward and inverse functions are induced by c and its inverse i. -/
theorem boundary_finite_classification (p w n : Nat) (hp : 0 < p) (c i j : Int)
    (hunit : i*c+(p : Int)^n*j = 1) :
    ∃ encode : Quot (sameClass ((p : Int)^n) ((p : Int)^w*c)) → Fin (p^(min w n)),
    ∃ decode : Fin (p^(min w n)) → Quot (sameClass ((p : Int)^n) ((p : Int)^w*c)),
      (∀ x, decode (encode x) = x) ∧ (∀ a, encode (decode a) = a) := by
  refine ⟨fun x => sourceRepresentative p w n hp (liftFromQuotient hunit x),
    fun a => boundaryOnQuotient hunit (Quot.mk _ (a.val : Int)), ?_, ?_⟩
  · intro x
    change boundaryOnQuotient hunit (Quot.mk _
      ((sourceRepresentative p w n hp (liftFromQuotient hunit x)).val : Int)) = x
    rw [source_representative_roundtrip, boundary_right_inverse]
  · intro a
    change sourceRepresentative p w n hp
      (liftFromQuotient hunit (boundaryOnQuotient hunit (Quot.mk _ (a.val : Int)))) = a
    rw [boundary_left_inverse, finite_representative_roundtrip]

end Reimann.BoundaryLifts
