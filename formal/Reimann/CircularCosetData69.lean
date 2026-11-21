import Reimann.CircularKernel69

/-! Subgroups of the positive character kernel at conductor 69. -/
namespace Reimann.CircularCosetData69

open CircularPolynomial69

def needsSign (a : Fin 69) : Bool := a^11 == 68

def needsLong (a : Fin 69) : Bool := a != 1 && a != 68

def members (u v : Bool) : List (Fin 69) :=
  (List.finRange 69).filter (fun a => decide (eta a.val = 1) &&
    (!needsSign a || u) && (!needsLong a || v))

theorem members_nodup : ∀ u v, (members u v).Nodup := by decide +kernel

theorem model_orders : (members false false).length = 1 ∧ (members true false).length = 2 ∧
    (members false true).length = 11 ∧ (members true true).length = 22 := by decide +kernel

theorem members_iff : ∀ (u v : Bool) (a : Fin 69), a ∈ members u v ↔
    eta a.val = 1 ∧ (needsSign a = true → u = true) ∧ (needsLong a = true → v = true) := by
  decide +kernel

theorem sign_extraction : ∀ a : Fin 69, needsSign a = true → a^11 = 68 := by decide +kernel

theorem long_extraction : ∀ a : Fin 69, eta a.val = 1 → needsLong a = true →
    ∃ j : Fin 22, a^j.val = 25 := by decide +kernel

theorem component_product : ∀ a : Fin 69, eta a.val = 1 → ∃ j : Fin 22,
    (if needsSign a then 68 else 1) * (if needsLong a then 25 else 1)^j.val = a := by
  decide +kernel

theorem subgroup_power (S : Fin 69 → Prop) (h1 : S 1)
    (hm : ∀ a b : Fin 69, S a → S b → S (a*b)) (a : Fin 69) (ha : S a) (n : Nat) : S (a^n) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [Lean.Grind.Semiring.pow_succ]
    exact hm _ _ ih ha

theorem subgroup_components (S : Fin 69 → Prop) (h1 : S 1)
    (hm : ∀ a b : Fin 69, S a → S b → S (a*b)) (hp : ∀ a, S a → eta a.val = 1)
    (a : Fin 69) :
    S a ↔ eta a.val = 1 ∧ (needsSign a = true → S 68) ∧ (needsLong a = true → S 25) := by
  constructor
  · intro ha
    refine ⟨hp a ha,fun hs => sign_extraction a hs ▸ subgroup_power S h1 hm a ha 11,?_⟩
    intro hl
    obtain ⟨j,hj⟩ := long_extraction a (hp a ha) hl
    exact hj ▸ subgroup_power S h1 hm a ha j.val
  · intro ⟨pos,small,big⟩
    obtain ⟨j,hj⟩ := component_product a pos
    have hs : S (if needsSign a then 68 else 1) := by
      split
      · exact small ‹_›
      · exact h1
    have hl : S (if needsLong a then 25 else 1) := by
      split
      · exact big ‹_›
      · exact h1
    exact hj ▸ hm _ _ hs (subgroup_power S h1 hm _ hl j.val)

theorem subgroup_model (S : Fin 69 → Prop) (h1 : S 1)
    (hm : ∀ a b : Fin 69, S a → S b → S (a*b)) (hp : ∀ a, S a → eta a.val = 1) :
    ∃ u v : Bool, ∀ a : Fin 69, S a ↔ a ∈ members u v := by
  classical
  refine ⟨decide (S 68),decide (S 25),?_⟩
  intro a
  rw [members_iff,subgroup_components S h1 hm hp a]
  simp

end Reimann.CircularCosetData69
