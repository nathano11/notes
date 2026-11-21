import Mathlib.Data.ZMod.Basic

namespace Reimann.TameCyclotomicUnits277

def modPrime (n : Nat) : ZMod (277^(n+1)) →+* ZMod 277 :=
  ZMod.castHom (show 277 ∣ 277^(n+1) from dvd_pow_self 277 (Nat.succ_ne_zero n)) _

theorem modPrime_val (n : Nat) (z : ZMod (277^(n+1))) :
    modPrime n z = (z.val : ZMod 277) := by
  calc
    _ = modPrime n (z.val : ZMod (277^(n+1))) := congrArg (modPrime n) (ZMod.natCast_zmod_val z).symm
    _ = _ := map_natCast _ _

theorem int_difference_nondivisible (n : Nat) (z : ZMod (277^(n+1)))
    (h : modPrime n z ≠ 1) : ¬(277 : ℤ) ∣ (z.val : ℤ)-1 := by
  intro hd
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd ((z.val:ℤ)-1) 277).mpr hd
  rw [Int.cast_sub,Int.cast_natCast,Int.cast_one,sub_eq_zero] at he
  exact h ((modPrime_val n z).trans he)

theorem unit_of_nonzero_modPrime (n : Nat) (d : ZMod (277^(n+1)))
    (h : modPrime n d ≠ 0) : IsUnit d := by
  have hnd : ¬277 ∣ d.val := fun hd =>
    h ((modPrime_val n d).trans ((ZMod.natCast_eq_zero_iff d.val 277).mpr hd))
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow (a := d.val)
    (by decide +kernel : Nat.Prime 277) (Nat.succ_pos n)).mpr hnd
  simpa only [ZMod.natCast_zmod_val] using hu

theorem unit_difference (n : Nat) (z : ZMod (277^(n+1))) (h : modPrime n z ≠ 1) :
    IsUnit (z-1) := by
  apply unit_of_nonzero_modPrime
  simpa only [map_sub,map_one,sub_ne_zero] using h

theorem five_period : (5 : ZMod 277)^276 = 1 := by decide +kernel

theorem five_first_period : ∀ j : Fin 275, (5 : ZMod 277)^(j.val+1) ≠ 1 := by decide +kernel

theorem five_pow_ne_one (r : Nat) (hr : ¬276 ∣ r) : (5 : ZMod 277)^r ≠ 1 := by
  have hn : r%276 ≠ 0 := fun h => hr (Nat.dvd_of_mod_eq_zero h)
  have hl := Nat.mod_lt r (by decide : 0 < 276)
  have h := five_first_period ⟨r%276-1,by omega⟩
  change (5 : ZMod 277)^(r%276-1+1) ≠ 1 at h
  rw [show r%276-1+1 = r%276 by omega] at h
  have he : (5:ZMod 277)^r = (5:ZMod 277)^(r%276) := calc
    _ = (5:ZMod 277)^(r%276 + 276*(r/276)) := congrArg (fun k : Nat => (5:ZMod 277)^k) (Nat.mod_add_div r 276).symm
    _ = _ := by rw [pow_add,pow_mul,five_period,one_pow,mul_one]
  rwa [he]

theorem inverse_five_ne_one (r : Nat) (hr : ¬276 ∣ r) (u : (ZMod 277)ˣ)
    (hu : (u : ZMod 277) = 5) : ((u^(-(r:ℤ)) : (ZMod 277)ˣ) : ZMod 277) ≠ 1 := by
  intro h
  have he : u^(-(r:ℤ)) = 1 := Units.ext h
  have hp : u^r = 1 := by simpa only [zpow_neg,zpow_natCast,inv_eq_one] using he
  have hv := congrArg (fun v : (ZMod 277)ˣ => (v : ZMod 277)) hp
  exact five_pow_ne_one r hr (by simpa only [Units.val_pow_eq_pow_val,hu,Units.val_one] using hv)

theorem inverse_scalar_of_five (u : (ZMod 277)ˣ) (hu : (u : ZMod 277) = 5) :
    ((u⁻¹ : (ZMod 277)ˣ) : ZMod 277) = 111 := by
  have hm : (u : ZMod 277) * 111 = 1 := by rw [hu]; decide +kernel
  calc
    _ = ((u⁻¹ : (ZMod 277)ˣ) : ZMod 277) * 1 := (mul_one _).symm
    _ = ((u⁻¹ : (ZMod 277)ˣ) : ZMod 277) * ((u : ZMod 277) * 111) := congrArg _ hm.symm
    _ = _ := by rw [← mul_assoc, u.inv_mul, one_mul]

theorem inverse_scalar_power (r : Nat) (u : (ZMod 277)ˣ) (hu : (u : ZMod 277) = 5) :
    ((u ^ (-(r : ℤ)) : (ZMod 277)ˣ) : ZMod 277) = 111 ^ r := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, inverse_scalar_of_five u hu]

end Reimann.TameCyclotomicUnits277
