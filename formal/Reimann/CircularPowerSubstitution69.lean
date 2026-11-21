import Reimann.CircularSubstitution69
import Reimann.CircularKernel69

/-! The automorphisms x ↦ x^a for invertible conductor residues. -/
namespace Reimann.CircularPowerSubstitution69

open Lean.Grind CircularPolynomialField69 CircularFieldReduction69 CircularKernel69
  CircularSubstitution69

variable {R : Type} [Field R]

theorem inverse_exponent_exists : ∀ a : Fin 69, Nat.Coprime a.val 69 →
    ∃ b : Fin 69, (a.val*b.val)%69 = 1 := by decide +kernel

theorem power_commutes (x : R) (a b : Nat) : (x^a)^b = (x^b)^a := by
  rw [power_of_power,power_of_power,Nat.mul_comm]

theorem recover_generator (x : R) (hx : Primitive69 x) (a b : Fin 69)
    (hab : (a.val*b.val)%69 = 1) : (x^a.val)^b.val = x := by
  rw [power_of_power,power_period x hx.order69,hab,Semiring.pow_one]

theorem primitive_unit_power (x : R) (hx : Primitive69 x) (a : Fin 69)
    (ha : Nat.Coprime a.val 69) : Primitive69 (x^a.val) := by
  obtain ⟨b,hab⟩ := inverse_exponent_exists a ha
  have recover := recover_generator x hx a b hab
  have lower (k : Nat) (hk : x^k ≠ 1) : (x^a.val)^k ≠ 1 := by
    intro h
    apply hk
    calc
      x^k = ((x^a.val)^b.val)^k := congrArg (fun t : R => t^k) recover.symm
      _ = ((x^a.val)^k)^b.val := power_commutes .. 
      _ = 1 := by rw [h,Semiring.one_pow]
  exact ⟨by rw [power_commutes, hx.order69, Semiring.one_pow],lower 23 hx.not23,lower 3 hx.not3⟩

variable [IsCharP R 0]

theorem generated_trans {x u v : R} (hu : Generated x u) (hv : Generated u v) : Generated x v := by
  obtain ⟨p,m,_,ep⟩ := hv
  let term := evalTerm x ⟨u,hu⟩ p m
  have eqn : term.val = v := (evalTerm_val x ⟨u,hu⟩ p m).trans ep
  exact eqn ▸ term.property

theorem generated_power_iff (x : R) (hx : Primitive69 x) (a : Fin 69)
    (ha : Nat.Coprime a.val 69) (v : R) : Generated (x^a.val) v ↔ Generated x v := by
  obtain ⟨b,hab⟩ := inverse_exponent_exists a ha
  have hx' := (power (x^a.val) (generator (x^a.val)) b.val).property
  change Generated (x^a.val) ((x^a.val)^b.val) at hx'
  rw [recover_generator x hx a b hab] at hx'
  exact ⟨generated_trans (power x (generator x) a.val).property,generated_trans hx'⟩

def transport (x z : R) (h : ∀ t, Generated x t → Generated z t) (u : Carrier x) : Carrier z :=
  ⟨u.val, h u.val u.property⟩

def transportIso (x z : R) (hx : Primitive69 x) (hz : Primitive69 z)
    (hm : ∀ t, Generated x t ↔ Generated z t) : FieldIso x z hx hz where
  forward := transport x z (fun t => (hm t).mp)
  backward := transport z x (fun t => (hm t).mpr)
  leftInv := fun _ => Subtype.ext rfl
  rightInv := fun _ => Subtype.ext rfl
  map_constant := fun _ => Subtype.ext rfl
  map_plus := fun _ _ => Subtype.ext rfl
  map_times := fun _ _ => Subtype.ext rfl
  map_inverse := fun _ => Subtype.ext rfl

def compose {A B C : Type} [Field A] [Field B] [Field C] [IsCharP A 0]
    [IsCharP B 0] [IsCharP C 0] {x : A} {y : B} {z : C} {hx : Primitive69 x}
    {hy : Primitive69 y} {hz : Primitive69 z} (e : FieldIso x y hx hy) (f : FieldIso y z hy hz) :
    FieldIso x z hx hz where
  forward u := f.forward (e.forward u)
  backward w := e.backward (f.backward w)
  leftInv u := by rw [f.leftInv,e.leftInv]
  rightInv w := by rw [e.rightInv,f.rightInv]
  map_constant a := by rw [e.map_constant,f.map_constant]
  map_plus u v := by rw [e.map_plus,f.map_plus]
  map_times u v := by rw [e.map_times,f.map_times]
  map_inverse u := by rw [e.map_inverse,f.map_inverse]

noncomputable def power_automorphism (x : R) (hx : Primitive69 x) (a : Fin 69)
    (ha : Nat.Coprime a.val 69) : FieldIso x x hx hx :=
  let hp := primitive_unit_power x hx a ha
  compose (substitutionIso x (x^a.val) hx hp)
    (transportIso (x^a.val) x hp hx (generated_power_iff x hx a ha))

theorem power_automorphism_generator (x : R) (hx : Primitive69 x) (a : Fin 69)
    (ha : Nat.Coprime a.val 69) :
    (power_automorphism x hx a ha).forward (generator x) = power x (generator x) a.val := by
  apply Subtype.ext
  change (substitute x (x^a.val) (generator x)).val = (generator (x^a.val)).val
  exact congrArg Subtype.val (substitute_root x (x^a.val) hx (primitive_unit_power x hx a ha))

theorem power_automorphism_eval (x : R) (hx : Primitive69 x) (a : Fin 69)
    (ha : Nat.Coprime a.val 69) (u : Carrier x) (p : Nat → Rat) (m : Nat)
    (ep : CircularRelationEval69.evalAt x p m = u.val) :
    ((power_automorphism x hx a ha).forward u).val = CircularRelationEval69.evalAt (x^a.val) p m := by
  rw [map_eval (power_automorphism x hx a ha) u p m ep,power_automorphism_generator]
  rfl

def identityIso (x : R) (hx : Primitive69 x) : FieldIso x x hx hx where
  forward := id
  backward := id
  leftInv _ := rfl
  rightInv _ := rfl
  map_constant _ := rfl
  map_plus _ _ := rfl
  map_times _ _ := rfl
  map_inverse _ := rfl

theorem unit_product (a b : Fin 69) (ha : Nat.Coprime a.val 69) (hb : Nat.Coprime b.val 69) :
    Nat.Coprime (a*b).val 69 := by
  change ((a.val*b.val)%69).gcd 69 = 1
  rw [← Nat.gcd_rec,Nat.gcd_comm]
  exact ha.mul_left hb

theorem power_automorphism_one (x : R) (hx : Primitive69 x) :
    power_automorphism x hx 1 (by decide) = identityIso x hx := by
  apply iso_ext_generator
  rw [power_automorphism_generator]
  exact Subtype.ext (Semiring.pow_one x)

theorem power_automorphism_product (x : R) (hx : Primitive69 x) (a b : Fin 69)
    (ha : Nat.Coprime a.val 69) (hb : Nat.Coprime b.val 69) :
    power_automorphism x hx (a*b) (unit_product a b ha hb) =
      compose (power_automorphism x hx b hb) (power_automorphism x hx a ha) := by
  apply iso_ext_generator
  change _ = (power_automorphism x hx a ha).forward ((power_automorphism x hx b hb).forward _)
  rw [power_automorphism_generator,power_automorphism_generator,map_power,power_automorphism_generator]
  apply Subtype.ext
  change x^((a.val*b.val)%69) = (x^a.val)^b.val
  rw [power_of_power, ← power_period x hx.order69 (a.val*b.val)]

theorem power_one_apply (x : R) (hx : Primitive69 x) (u : Carrier x) :
    (power_automorphism x hx 1 (by decide)).forward u = u := by
  rw [power_automorphism_one]; rfl

theorem power_product_apply (x : R) (hx : Primitive69 x) (a b : Fin 69)
    (ha : Nat.Coprime a.val 69) (hb : Nat.Coprime b.val 69) (u : Carrier x) :
    (power_automorphism x hx (a*b) (unit_product a b ha hb)).forward u =
      (power_automorphism x hx a ha).forward ((power_automorphism x hx b hb).forward u) := by
  rw [power_automorphism_product x hx a b ha hb]; rfl

end Reimann.CircularPowerSubstitution69
