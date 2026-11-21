import Mathlib.GroupTheory.Torsion
import Reimann2893.SignedNativeScalar2893
import Reimann2893.SignedNormLimit2893

/-! Coefficient multiplication by a p-adic integer on norm-coherent families
of two-primary abelian groups. Individual classes may have different orders. -/
namespace Reimann.SignedClassScalars2893

universe u v
variable {G : Type u} {H : Type v} [CommGroup G] [CommGroup H]

abbrev KilledByTwoPowers (G : Type*) [CommGroup G] := ∀ x : G, ∃ k : Nat, x^(2^k)=1

theorem power_cast {p i j : Nat} (x : G) (hx : x^p=1)
    (h : (i : ZMod p) = (j : ZMod p)) : x^i=x^j := by
  apply pow_eq_pow_iff_modEq.mpr
  exact ((ZMod.natCast_eq_natCast_iff i j p).mp h).of_dvd (orderOf_dvd_of_pow_eq_one hx)

theorem at_larger_precision (x : G) (a : ℤ_[2]) (k l : Nat) (hk : x^(2^k)=1) (hkl : k≤l) :
    x^(a.appr k) = x^(a.appr l) := by
  apply power_cast x hk
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  change a.appr k % 2^k = a.appr l % 2^k
  rw [SignedNativeScalar2893.appr_mod a k l hkl,Nat.mod_eq_of_lt (a.appr_lt k)]

noncomputable def power (h : KilledByTwoPowers G) (a : ℤ_[2]) (x : G) : G :=
  x^(a.appr (h x).choose)

theorem power_at (h : KilledByTwoPowers G) (a : ℤ_[2]) (x : G) (k : Nat) (hk : x^(2^k)=1) :
    power h a x = x^(a.appr k) :=
  (at_larger_precision x a (h x).choose (max (h x).choose k) (h x).choose_spec (Nat.le_max_left ..)).trans
    (at_larger_precision x a k (max (h x).choose k) hk (Nat.le_max_right ..)).symm

theorem power_from_reduction (h : KilledByTwoPowers G) (a : ℤ_[2]) (x : G) (k r : Nat)
    (hk : x^(2^k)=1) (ha : PadicInt.toZModPow k a=(r : ZMod (2^k))) :
    power h a x=x^r := by
  rw [power_at h a x k hk]
  exact power_cast x hk ha

theorem killing_mono {x : G} {k l : Nat} (h : x^(2^k)=1) (hle : k≤l) : x^(2^l)=1 := by
  obtain ⟨d,hd⟩ := Nat.pow_dvd_pow 2 hle
  rw [hd,pow_mul,h,one_pow]

theorem power_nat (h : KilledByTwoPowers G) (r : Nat) (x : G) : power h (r : ℤ_[2]) x = x^r :=
  power_from_reduction h _ x (h x).choose r (h x).choose_spec (map_natCast _ _)

theorem power_group_one (h : KilledByTwoPowers G) (a : ℤ_[2]) : power h a 1 = 1 := by
  simp only [power,one_pow]

theorem power_scalar_add (h : KilledByTwoPowers G) (a b : ℤ_[2]) (x : G) :
    power h (a+b) x = power h a x * power h b x := by
  obtain ⟨k,hk⟩ := h x
  rw [power_at h a x k hk,power_at h b x k hk,←pow_add]
  apply power_from_reduction h _ x k _ hk
  rw [map_add,Nat.cast_add]
  rfl

theorem power_scalar_mul (h : KilledByTwoPowers G) (a b : ℤ_[2]) (x : G) :
    power h (a*b) x = power h a (power h b x) := by
  obtain ⟨k,hk⟩ := h x
  rw [power_at h b x k hk]
  have hy : (x^(b.appr k))^(2^k)=1 := by rw [pow_right_comm,hk,one_pow]
  rw [power_at h a _ k hy,←pow_mul]
  apply power_from_reduction h _ x k _ hk
  rw [map_mul,Nat.cast_mul,mul_comm (PadicInt.toZModPow k a)]
  rfl

theorem power_group_mul (h : KilledByTwoPowers G) (a : ℤ_[2]) (x y : G) :
    power h a (x*y) = power h a x * power h a y := by
  obtain ⟨k,hx⟩ := h x
  obtain ⟨l,hy⟩ := h y
  have h1 := killing_mono hx (Nat.le_max_left k l)
  have h2 := killing_mono hy (Nat.le_max_right k l)
  have hxy : (x*y)^(2^(max k l))=1 := by rw [mul_pow,h1,h2,one_mul]
  rw [power_at h a _ _ hxy,power_at h a _ _ h1,power_at h a _ _ h2,mul_pow]

theorem map_power (h : KilledByTwoPowers G) (h' : KilledByTwoPowers H) (f : G →* H)
    (a : ℤ_[2]) (x : G) : f (power h a x) = power h' a (f x) := by
  obtain ⟨k,hk⟩ := h x
  have hf : (f x)^(2^k)=1 := by rw [←map_pow,hk,map_one]
  rw [power_at h a x k hk,power_at h' a (f x) k hf,map_pow]

noncomputable abbrev torsionModule (h : KilledByTwoPowers G) : Module ℤ_[2] (Additive G) where
  smul a x := Additive.ofMul (power h a x.toMul)
  one_smul x := by
    change power h (1 : ℤ_[2]) x.toMul = x.toMul
    simpa only [Nat.cast_one,pow_one] using power_nat h 1 x.toMul
  mul_smul a b x := power_scalar_mul h a b x.toMul
  smul_zero a := power_group_one h a
  smul_add a x y := power_group_mul h a x.toMul y.toMul
  add_smul a b x := power_scalar_add h a b x.toMul
  zero_smul x := by
    change power h (0 : ℤ_[2]) x.toMul = 1
    simpa only [Nat.cast_zero,pow_zero] using power_nat h 0 x.toMul

abbrev Primary (G : Type*) [CommGroup G] := ↥(CommGroup.primaryComponent G 2)

theorem primary_killed (G : Type*) [CommGroup G] : KilledByTwoPowers (Primary G) := by
  intro x
  obtain ⟨k,hk⟩ := CommGroup.mem_primaryComponent.mp x.property
  exact ⟨k,Subtype.ext hk⟩

noncomputable instance primaryModule (G : Type*) [CommGroup G] : Module ℤ_[2] (Additive (Primary G)) :=
  torsionModule (primary_killed G)

section Tower

variable (A : Nat → Type u) [∀ n, CommGroup (A n)]
variable (N : ∀ n, Primary (A (n+1)) →* Primary (A n))

abbrev ClassLimit := SignedNormLimit2893.coherent (G := fun n => Primary (A n)) N

/-- Every transition preserves the scalar action; thus it restricts to the inverse limit. -/
noncomputable def limitPower (a : ℤ_[2]) (x : ClassLimit A N) :
    ClassLimit A N :=
  ⟨fun n => power (primary_killed (A n)) a (x.val n), fun n => by
    rw [map_power _ (primary_killed (A n)) (N n),x.property n]⟩

noncomputable instance limitModule : Module ℤ_[2] (Additive (ClassLimit A N)) where
  smul a x := Additive.ofMul (limitPower A N a x.toMul)
  one_smul x := by
    change limitPower A N (1 : ℤ_[2]) x.toMul = x.toMul
    apply Subtype.ext
    funext n
    change power (primary_killed (A n)) (1 : ℤ_[2]) (x.toMul.val n) = x.toMul.val n
    simpa only [Nat.cast_one,pow_one] using power_nat (primary_killed (A n)) 1 (x.toMul.val n)
  mul_smul a b x := Subtype.ext <| funext fun n => power_scalar_mul (primary_killed (A n)) a b (x.toMul.val n)
  smul_zero a := Subtype.ext <| funext fun n => power_group_one (primary_killed (A n)) a
  smul_add a x y := Subtype.ext <| funext fun n => power_group_mul (primary_killed (A n)) a (x.toMul.val n) (y.toMul.val n)
  add_smul a b x := Subtype.ext <| funext fun n => power_scalar_add (primary_killed (A n)) a b (x.toMul.val n)
  zero_smul x := by
    change limitPower A N (0 : ℤ_[2]) x.toMul = 1
    apply Subtype.ext
    funext n
    change power (primary_killed (A n)) (0 : ℤ_[2]) (x.toMul.val n) = 1
    simpa only [Nat.cast_zero,pow_zero] using power_nat (primary_killed (A n)) 0 (x.toMul.val n)

theorem scalar_at_level (a : ℤ_[2]) (x : Additive (ClassLimit A N)) (n : Nat) (k : Nat)
    (hk : (x.toMul.val n)^(2^k)=1) :
    (a • x).toMul.val n = (x.toMul.val n)^(a.appr k) :=
  power_at (primary_killed (A n)) a _ k hk

noncomputable def limitForwardLinear
    (σ : ∀ n, Primary (A n) ≃* Primary (A n)) (comm : ∀ n x, N n (σ (n+1) x) = σ n (N n x)) :
    Additive (ClassLimit A N) ≃ₗ[ℤ_[2]] Additive (ClassLimit A N) where
  toFun x := Additive.ofMul (SignedNormLimit2893.forward (G := fun n => Primary (A n)) N σ comm x.toMul)
  invFun x := Additive.ofMul ((SignedNormLimit2893.forward (G := fun n => Primary (A n)) N σ comm).symm x.toMul)
  left_inv x := (SignedNormLimit2893.forward (G := fun n => Primary (A n)) N σ comm).left_inv x.toMul
  right_inv x := (SignedNormLimit2893.forward (G := fun n => Primary (A n)) N σ comm).right_inv x.toMul
  map_add' x y := (SignedNormLimit2893.forward (G := fun n => Primary (A n)) N σ comm).map_mul x.toMul y.toMul
  map_smul' a x := Subtype.ext <| funext fun n =>
    map_power (primary_killed (A n)) (primary_killed (A n)) (σ n).toMonoidHom a (x.toMul.val n)

end Tower
end Reimann.SignedClassScalars2893
