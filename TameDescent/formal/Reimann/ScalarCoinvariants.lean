import Std

namespace Reimann.ScalarCoinvariants

/-- The two changes of an integer lift: a multiple of the coefficient modulus
and a coboundary for the generator acting by scalar multiplication by `u`. -/
def Related (m u x y : Int) : Prop :=
  ∃ a b : Int, x - y = m * a + (u - 1) * b

theorem remainder_as_difference (m n : Nat) :
    ((n % m : Nat) : Int) = (n : Int) - (m : Int) * ((n / m : Nat) : Int) := by
  have h : ((n % m : Nat) : Int) + (m : Int) * ((n / m : Nat) : Int) = (n : Int) := by
    exact_mod_cast Nat.mod_add_div n m
  omega

theorem nat_gcd_bezout (m n : Nat) :
    ∃ a b : Int, (Nat.gcd m n : Int) = (m : Int)*a + (n : Int)*b := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    cases m with
    | zero => exact ⟨0, 1, by simp⟩
    | succ m =>
      obtain ⟨a,b,h⟩ := ih (n % (m+1)) (Nat.mod_lt _ (Nat.succ_pos _)) (m+1)
      refine ⟨b - ((n / (m+1) : Nat) : Int)*a, a, ?_⟩
      rw [Nat.gcd_rec, h, remainder_as_difference]
      grind

theorem int_gcd_bezout (m d : Int) :
    ∃ a b : Int, (Int.gcd m d : Int) = m*a + d*b := by
  obtain ⟨a,b,h⟩ := nat_gcd_bezout m.natAbs d.natAbs
  refine ⟨m.sign*a, d.sign*b, ?_⟩
  rw [← Int.mul_assoc, ← Int.mul_assoc d, Int.mul_sign_self, Int.mul_sign_self]
  exact h

theorem gcd_dvd_difference {m u x y : Int} (h : Related m u x y) :
    (Int.gcd m (u-1) : Int) ∣ x-y := by
  obtain ⟨a,b,h⟩ := h
  rw [h]
  exact Int.dvd_add (Int.dvd_trans (Int.gcd_dvd_left _ _) (Int.dvd_mul_right _ _))
    (Int.dvd_trans (Int.gcd_dvd_right _ _) (Int.dvd_mul_right _ _))

theorem related_of_gcd_dvd_difference {m u x y : Int}
    (h : (Int.gcd m (u-1) : Int) ∣ x-y) : Related m u x y := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨a,b,hab⟩ := int_gcd_bezout m (u-1)
  refine ⟨a*k,b*k,?_⟩
  rw [hk, hab]
  grind

theorem related_iff_remainder (m u x y : Int) :
    Related m u x y ↔ x % (Int.gcd m (u-1) : Int) = y % (Int.gcd m (u-1) : Int) := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact ⟨fun h => Int.emod_eq_zero_of_dvd (gcd_dvd_difference h),
         fun h => related_of_gcd_dvd_difference (Int.dvd_of_emod_eq_zero h)⟩

def Coinvariants (m u : Int) := Quot (Related m u)

theorem modulus_pos {m : Int} (hm : m ≠ 0) (u : Int) :
    0 < (Int.gcd m (u-1) : Int) := by
  exact_mod_cast Int.gcd_pos_of_ne_zero_left (u-1) hm

def representative (m u : Int) (hm : m ≠ 0) (x : Int) : Fin (Int.gcd m (u-1)) :=
  ⟨(x % (Int.gcd m (u-1) : Int)).toNat, by
    have hp := modulus_pos hm u
    have h := Int.emod_lt_of_pos x hp
    omega⟩

theorem representative_val (m u : Int) (hm : m ≠ 0) (x : Int) :
    ((representative m u hm x).val : Int) = x % (Int.gcd m (u-1) : Int) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt (modulus_pos hm u)))

theorem representative_eq_iff (m u : Int) (hm : m ≠ 0) (x y : Int) :
    representative m u hm x = representative m u hm y ↔ Related m u x y := by
  rw [related_iff_remainder, ← representative_val m u hm x, ← representative_val m u hm y]
  rw [Fin.ext_iff]
  omega

def toResidue (m u : Int) (hm : m ≠ 0) :
    Coinvariants m u → Fin (Int.gcd m (u-1)) :=
  Quot.lift (representative m u hm)
    (fun x y h => (representative_eq_iff m u hm x y).mpr h)

def ofResidue (m u : Int) (x : Fin (Int.gcd m (u-1))) : Coinvariants m u :=
  Quot.mk (Related m u) (x.val : Int)

theorem toResidue_ofResidue (m u : Int) (hm : m ≠ 0) (x : Fin (Int.gcd m (u-1))) :
    toResidue m u hm (ofResidue m u x) = x := by
  apply Fin.ext
  change (((x.val : Int) % (Int.gcd m (u-1) : Int)).toNat) = x.val
  have h : (x.val : Int) < (Int.gcd m (u-1) : Int) := by exact_mod_cast x.isLt
  rw [Int.emod_eq_of_lt (by omega) h]
  rfl

theorem ofResidue_toResidue (m u : Int) (hm : m ≠ 0) (c : Coinvariants m u) :
    ofResidue m u (toResidue m u hm c) = c := by
  induction c using Quot.ind with
  | _ x =>
    apply Quot.sound
    apply (related_iff_remainder m u _ x).mpr
    change ((representative m u hm x).val : Int) % _ = _
    rw [representative_val, Int.emod_emod]

theorem representative_add (m u : Int) (hm : m ≠ 0) (x y : Int) :
    representative m u hm (x+y) = representative m u hm x + representative m u hm y := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [Fin.val_add, Int.natCast_emod, Int.natCast_add, representative_val,
      representative_val, representative_val, ← Int.add_emod]

def addClasses (m u : Int) (hm : m ≠ 0) (a b : Coinvariants m u) : Coinvariants m u :=
  ofResidue m u (toResidue m u hm a + toResidue m u hm b)

theorem addClasses_mk (m u : Int) (hm : m ≠ 0) (x y : Int) :
    addClasses m u hm (Quot.mk (Related m u) x) (Quot.mk (Related m u) y) =
      Quot.mk (Related m u) (x+y) := by
  change ofResidue m u (representative m u hm x + representative m u hm y) = _
  rw [← representative_add]
  exact ofResidue_toResidue m u hm (Quot.mk (Related m u) (x+y))

theorem toResidue_addClasses (m u : Int) (hm : m ≠ 0) (a b : Coinvariants m u) :
    toResidue m u hm (addClasses m u hm a b) = toResidue m u hm a + toResidue m u hm b :=
  toResidue_ofResidue m u hm _

theorem gcd_at_shallow_depth (p n k : Nat) (t : Int) (hn : n ≤ k) :
    Int.gcd ((p : Int)^n) ((p : Int)^k*t) = p^n := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hn
  have hd : (p : Int)^n ∣ (p : Int)^k*t := by
    refine ⟨(p : Int)^s*t, ?_⟩
    rw [hs, Int.pow_add, Int.mul_assoc]
  rw [Int.gcd_eq_natAbs_left hd, Int.natAbs_pow, Int.natAbs_natCast]

theorem gcd_at_deep_depth (p n k : Nat) (t : Int)
    (ht : Int.gcd (p : Int) t = 1) (hn : k ≤ n) :
    Int.gcd ((p : Int)^n) ((p : Int)^k*t) = p^k := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hn
  have hunit : Int.gcd ((p : Int)^s) t = 1 := Int.gcd_pow_left_of_gcd_eq_one ht
  rw [hs, Int.pow_add, Int.gcd_mul_left, hunit, Nat.mul_one, Int.natAbs_pow, Int.natAbs_natCast]

theorem scalar_order_at_depth (p n k : Nat) (u t : Int)
    (hu : u-1 = (p : Int)^k*t) (ht : Int.gcd (p : Int) t = 1) :
    Int.gcd ((p : Int)^n) (u-1) = p^(min n k) := by
  rw [hu]
  by_cases h : n ≤ k
  · rw [Nat.min_eq_left h, gcd_at_shallow_depth p n k t h]
  · have h' : k ≤ n := by omega
    rw [Nat.min_eq_right h', gcd_at_deep_depth p n k t ht h']

theorem related_at_depth (p n k : Nat) (u t x y : Int)
    (hu : u-1 = (p : Int)^k*t) (ht : Int.gcd (p : Int) t = 1) :
    Related ((p : Int)^n) u x y ↔ x % (p : Int)^(min n k) = y % (p : Int)^(min n k) := by
  rw [related_iff_remainder, scalar_order_at_depth p n k u t hu ht, Int.natCast_pow]

end Reimann.ScalarCoinvariants
