import Std

namespace Reimann.TameCoefficients
open Lean.Grind

variable {G M : Type} [IntModule M] {mul : G → G → G}

/-- An action by additive maps. Only composition and subtraction are used. -/
structure Action (G M : Type) [IntModule M] (mul : G → G → G) where
  act : G → M → M
  act_mul : ∀ g h x, act (mul g h) x = act g (act h x)
  act_sub : ∀ g x y, act g (x-y) = act g x - act g y

def Cocycle (A : Action G M mul) (c : G → M) : Prop :=
  ∀ g h, c (mul g h) = c g + A.act g (c h)

def delta (A : Action G M mul) (b : M) (g : G) : M := A.act g b-b

theorem delta_cocycle (A : Action G M mul) (b : M) : Cocycle A (delta A b) := by
  intro g h
  simp only [delta, A.act_mul, A.act_sub]
  grind

theorem subtract_cocycles {A : Action G M mul} {c d : G → M}
    (hc : Cocycle A c) (hd : Cocycle A d) : Cocycle A (fun g => c g - d g) := by
  intro g h
  simp only [hc g h, hd g h, A.act_sub]
  grind

structure CoefficientMap (A : Action G M mul) where
  map : M → M
  map_sub : ∀ x y, map (x-y) = map x-map y
  equivariant : ∀ g x, map (A.act g x) = A.act g (map x)

def Kernel {A : Action G M mul} (P : CoefficientMap A) := {x : M // P.map x = 0}

theorem map_delta {A : Action G M mul} (P : CoefficientMap A) (b : M) (g : G) :
    P.map (delta A b g) = delta A (P.map b) g := by
  rw [delta, P.map_sub, P.equivariant, delta]

theorem corrected_in_kernel {A : Action G M mul} (P : CoefficientMap A)
    {c : G → M} {b v : M} (h : ∀ g, P.map (c g) = delta A b g)
    (hv : P.map v = b) (g : G) : P.map (c g - delta A v g) = 0 := by
  rw [P.map_sub, map_delta, hv, h, AddCommGroup.sub_self]

theorem lift_torsion_cocycle {A : Action G M mul} (P : CoefficientMap A)
    (hsurj : Function.Surjective P.map) {c : G → M} (hc : Cocycle A c)
    (htorsion : ∃ b, ∀ g, P.map (c g) = delta A b g) :
    ∃ (f : G → Kernel P) (v : M),
      Cocycle A (fun g => (f g).val) ∧ ∀ g, (f g).val = c g - delta A v g := by
  obtain ⟨b,hb⟩ := htorsion
  obtain ⟨v,hv⟩ := hsurj b
  refine ⟨fun g => ⟨c g-delta A v g, corrected_in_kernel P hb hv g⟩, v, ?_, fun _ => rfl⟩
  exact subtract_cocycles hc (delta_cocycle A v)

theorem torsion_of_kernel_lift {A : Action G M mul} (P : CoefficientMap A)
    {c : G → M} (f : G → Kernel P) (v : M)
    (h : ∀ g, (f g).val = c g - delta A v g) :
    ∀ g, P.map (c g) = delta A (P.map v) g := by
  intro g
  have he := (f g).property
  rw [h, P.map_sub, map_delta] at he
  exact AddCommGroup.sub_eq_zero_iff.mp he

theorem torsion_iff_kernel_lift {A : Action G M mul} (P : CoefficientMap A)
    (hsurj : Function.Surjective P.map) {c : G → M} (hc : Cocycle A c) :
    (∃ b, ∀ g, P.map (c g) = delta A b g) ↔
    ∃ (f : G → Kernel P) (v : M), Cocycle A (fun g => (f g).val) ∧
      ∀ g, (f g).val = c g - delta A v g := by
  constructor
  · exact lift_torsion_cocycle P hsurj hc
  · rintro ⟨f,v,_,h⟩
    exact ⟨P.map v, torsion_of_kernel_lift P f v h⟩

theorem primitive_image_fixed {A : Action G M mul} (P : CoefficientMap A)
    {H : Type} (loc : H → G) (f : H → Kernel P) {v : M}
    (hv : ∀ h, (f h).val = delta A v (loc h)) :
    ∀ h, A.act (loc h) (P.map v) = P.map v := by
  intro h
  have he := (f h).property
  rw [hv, map_delta, delta] at he
  exact AddCommGroup.sub_eq_zero_iff.mp he

theorem local_principal_iff {A : Action G M mul} (P : CoefficientMap A)
    {H : Type} (loc : H → G) (f : H → Kernel P)
    (hfixed : ∀ x : M, (∀ h, A.act (loc h) x = x) → x = 0) :
    (∃ v : M, ∀ h, (f h).val = delta A v (loc h)) ↔
    (∃ v : Kernel P, ∀ h, (f h).val = delta A v.val (loc h)) := by
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨⟨v, hfixed _ (primitive_image_fixed P loc f hv)⟩, hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨v.val,hv⟩

theorem fixed_zero_of_tame_injectivity (A : Action G M mul) {H : Type}
    (loc : H → G) (t : H) (hinj : Function.Injective (fun x => delta A x (loc t))) :
    ∀ x : M, (∀ h, A.act (loc h) x = x) → x = 0 := by
  intro x hx
  apply hinj
  have hz : A.act (loc t) (0 : M) = 0 := by
    have h := A.act_sub (loc t) x x
    simpa only [AddCommGroup.sub_self] using h
  simp only [delta, hx t, hz, AddCommGroup.sub_self]

theorem action_zero (A : Action G M mul) (g : G) : A.act g 0 = 0 := by
  simpa only [AddCommGroup.sub_self] using A.act_sub g (0 : M) 0

theorem action_add (A : Action G M mul) (g : G) (x y : M) :
    A.act g (x+y) = A.act g x + A.act g y := by
  have h := A.act_sub g (x+y) y
  rw [AddCommGroup.add_sub_cancel] at h
  grind

theorem action_nat_multiple (A : Action G M mul) (g : G) (k : Nat) (x : M) :
    (k : Int) • A.act g x = A.act g ((k : Int) • x) := by
  induction k with
  | zero => simp only [Int.natCast_zero, IntModule.zero_zsmul, action_zero]
  | succ k ih =>
    rw [Int.natCast_succ, IntModule.add_zsmul, IntModule.add_zsmul, IntModule.one_zsmul,
        IntModule.one_zsmul, action_add, ih]

def primePowerMap (A : Action G M mul) (p n : Nat) : CoefficientMap A where
  map := fun x => ((p^n : Nat) : Int) • x
  map_sub := IntModule.zsmul_sub _
  equivariant := fun g x => action_nat_multiple A g (p^n) x

theorem delta_sub (A : Action G M mul) (x y : M) (g : G) :
    delta A (x-y) g = delta A x g - delta A y g := by
  simp only [delta, A.act_sub]
  grind

theorem local_strictness_of_lift {A : Action G M mul} (P : CoefficientMap A)
    {H : Type} (loc : H → G) (hfixed : ∀ x : M, (∀ h, A.act (loc h) x = x) → x = 0)
    (f : G → Kernel P) (c : G → M) (v : M) (hlift : ∀ g, (f g).val = c g - delta A v g)
    (hlocal : ∃ b, ∀ h, c (loc h) = delta A b (loc h)) :
    ∃ w : Kernel P, ∀ h, (f (loc h)).val = delta A w.val (loc h) := by
  obtain ⟨b,hb⟩ := hlocal
  apply (local_principal_iff P loc (fun h => f (loc h)) hfixed).mp
  refine ⟨b-v, fun h => ?_⟩
  rw [hlift, hb, delta_sub]

theorem primePower_surj (A : Action G M mul) (p : Nat)
    (hp : Function.Surjective (fun x : M => (p : Int) • x)) (n : Nat) :
    Function.Surjective (primePowerMap A p n).map := by
  induction n with
  | zero =>
    intro y
    exact ⟨y, by simp [primePowerMap, IntModule.one_zsmul]⟩
  | succ n ih =>
    intro y
    obtain ⟨v,hv⟩ := ih y
    obtain ⟨w,hw⟩ := hp v
    change (p : Int) • w = v at hw
    refine ⟨w, ?_⟩
    change ((p^(n+1) : Nat) : Int) • w = y
    rw [Nat.pow_succ, Int.natCast_mul, IntModule.mul_zsmul, hw]
    exact hv

def kernelDifference {A : Action G M mul} (P : CoefficientMap A) (x y : Kernel P) : Kernel P :=
  ⟨x.val-y.val, by rw [P.map_sub, x.property, y.property, AddCommGroup.sub_self]⟩

theorem finite_classes_equal_iff {A : Action G M mul} (P : CoefficientMap A)
    (f k : G → Kernel P) (hfixed : ∀ x : M, (∀ g, A.act g x = x) → x = 0) :
    (∃ b : Kernel P, ∀ g, (f g).val - (k g).val = delta A b.val g) ↔
    (∃ b : M, ∀ g, (f g).val - (k g).val = delta A b g) :=
  (local_principal_iff P (fun g => g) (fun g => kernelDifference P (f g) (k g)) hfixed).symm

end Reimann.TameCoefficients
