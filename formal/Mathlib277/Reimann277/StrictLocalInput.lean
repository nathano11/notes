import Reimann277.CyclotomicLocal
import Reimann.TameAdicDomain277
import Reimann.TameGaloisInterface

namespace Reimann.TameStrictLocal277

open TameCyclotomicLocal277 TameRestriction

def law (G : Type) [Group G] : Transfer.GroupLaw G where
  zero := 1
  add := (· * ·)
  neg := (·⁻¹)
  assoc := mul_assoc
  zero_add := one_mul
  add_zero := mul_one
  add_neg := mul_inv_cancel
  neg_add := inv_mul_cancel

def asHom {G H : Type} [Group G] [Group H] (f : G →* H) : Transfer.Hom (law G) (law H) where
  app := f
  preserves_zero := f.map_one
  preserves_add := f.map_mul
  preserves_neg := f.map_inv

abbrev modulus (n : ℕ) : ℤ := ((277 ^ (n+1) : ℕ) : ℤ)

noncomputable def scalar (r n : ℕ) (g : Global) : ℤ :=
  ((finiteTwist r n g : ZMod (277^(n+1))).val : ℤ)

theorem scalar_cast (r n : ℕ) (g : Global) :
    (scalar r n g : ZMod (277^(n+1))) = (finiteTwist r n g : ZMod (277^(n+1))) := by
  rw [scalar,Int.cast_natCast,ZMod.natCast_zmod_val]

theorem kernel_scalar {r n : ℕ} {g : Global} (hg : g ∈ globalKernel r n) :
    modulus n ∣ scalar r n g - 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (277^(n+1))).mp
  have h : finiteTwist r n g = 1 := hg
  simp only [Int.cast_sub, Int.cast_one, scalar_cast, h, Units.val_one, sub_self]

theorem scalar_product (r n : ℕ) (a b : Global) :
    modulus n ∣ scalar r n (a*b) - scalar r n a * scalar r n b := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (277^(n+1))).mp
  simp only [Int.cast_sub,Int.cast_mul,scalar_cast,map_mul,Units.val_mul,sub_self]

theorem commutator_in (r n : ℕ) (a b : Global) : commutator (law Global) a b ∈ globalKernel r n := by
  apply (mem_globalKernel_iff r n _).mpr
  change finiteTwist r n (a*b*a⁻¹*b⁻¹) = 1
  simp [mul_comm,mul_left_comm]

theorem bezout_inverse {n : ℕ} {d : ℤ} (h : ¬(277 : ℤ) ∣ d) :
    ∃ i : ℤ, modulus n ∣ i*d - 1 := by
  obtain ⟨i,j,hij⟩ := TameAdicDomain277.unit_at_all_depths d h (n+1)
  refine ⟨i,-j,?_⟩
  simp only [modulus,Nat.cast_pow,Nat.cast_ofNat]
  grind

/-- Only a local tame element with nontrivial scalar modulo 277 is required.
All homomorphisms, kernels and positive-depth scalars are the arithmetic ones. -/
structure Witness (r n : ℕ) where
  generator : Local
  nontrivial : ∀ s : Bool × Bool, ¬ (277 : ℤ) ∣ scalar r n (restriction s generator) - 1

noncomputable def data {r n : ℕ} (w : Witness r n) :
    TameData (law Global) (restriction (false,false) w.generator) (modulus n) where
  kernel g := g ∈ globalKernel r n
  mul_in := (globalKernel r n).mul_mem
  inv_in := (globalKernel r n).inv_mem
  conj_in g {h} hh := (globalKernelNormal r n).conj_mem h hh g
  comm_in := commutator_in r n _
  scalar := scalar r n
  trivial_on_kernel := kernel_scalar
  scalar_mul := scalar_product r n
  inverse := Classical.choose (bezout_inverse (n := n) (w.nontrivial (false,false)))
  inverse_spec := Classical.choose_spec (bezout_inverse (n := n) (w.nontrivial (false,false)))

noncomputable def localImage (s : Bool × Bool) (a : Global) : Local →* Global :=
  (MulAut.conj a).toMonoidHom.comp (restriction s).toMonoidHom

theorem scalar_conjugate (r n : ℕ) (a g : Global) :
    scalar r n (a*g*a⁻¹) = scalar r n g := by
  unfold scalar
  simp [mul_comm,mul_left_comm]

noncomputable def places {r n : ℕ} (w : Witness r n) : TameStrictInterface.Places (data w) where
  index := (Bool × Bool) × Global
  carrier _ := Local
  law _ := law Local
  embed i := asHom (localImage i.1 i.2)
  tame _ := w.generator
  inverse i := Classical.choose (bezout_inverse (n := n) (w.nontrivial i.1))
  isUnit i := by
    change modulus n ∣ _ * (scalar r n (i.2 * restriction i.1 w.generator * i.2⁻¹) - 1) - 1
    rw [scalar_conjugate]
    exact Classical.choose_spec (bezout_inverse (n := n) (w.nontrivial i.1))
  comm_in i g := by
    apply (mem_globalKernel_iff r n _).mpr
    change finiteTwist r n (localImage i.1 i.2 ((w.generator*g)*(g*w.generator)⁻¹)) = 1
    simp [map_mul,map_inv,mul_comm,mul_left_comm,mul_assoc]

theorem localKernel_iff {r n : ℕ} (w : Witness r n) (x : globalKernel r n) :
    TameStrictInterface.LocalKernel (places w) x ↔ x ∈ atPlaces r n := by
  constructor
  · rintro ⟨⟨s,a⟩,g,hg⟩
    change a * restriction s g * a⁻¹ = x.val at hg
    have hc : finiteTwist r n x.val = 1 := x.property
    rw [← hg] at hc
    have hk : g ∈ localKernel r n s := by
      change finiteTwist r n (restriction s g) = 1
      simpa [mul_comm,mul_left_comm,mul_assoc] using hc
    exact ⟨s,a,⟨g,hk⟩,Subtype.ext hg.symm⟩
  · rintro ⟨s,a,y,rfl⟩
    exact ⟨⟨s,a⟩,y.val,rfl⟩

theorem strict_iff_split {r n : ℕ} (w : Witness r n) {c : Global → ℤ}
    (hc : Crossed (data w) c) :
    TameStrictInterface.Strict (places w) c ↔ ∀ x : globalKernel r n, x ∈ atPlaces r n → modulus n ∣ c x.val := by
  rw [TameStrictInterface.strict_iff_local_kernel _ hc]
  exact forall_congr' (fun x => by rw [← localKernel_iff w x])

end Reimann.TameStrictLocal277
