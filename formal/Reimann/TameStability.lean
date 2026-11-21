import Reimann.OddDescent

namespace Reimann.TameStability

/-- For multiplication by p the neutral element is a fixed point. -/
theorem iterate_fixed_zero {A : Type} (step : A → A) (z : A)
    (hz : step z = z) (n : Nat) : OddDescent.iterate step n z = z := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg step ih).trans hz

theorem iterate_on_image {A : Type} (step : A → A) (n : Nat) (x : A) :
    OddDescent.iterate step n (step x) = OddDescent.iterate step (n+1) x := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg step ih

/-- A single equality of two consecutive kernels captures every iterated
    kernel. Only the descending implication is required. -/
theorem plateau_captures_kernel {A : Type} (step : A → A) (z : A)
    (hz : step z = z) (e : Nat)
    (plateau : ∀ x, OddDescent.iterate step (e+1) x = z → OddDescent.iterate step e x = z)
    (n : Nat) (x : A) (hn : OddDescent.iterate step n x = z) :
    OddDescent.iterate step e x = z := by
  induction n generalizing x with
  | zero =>
    change x = z at hn
    rw [hn]
    exact iterate_fixed_zero step z hz e
  | succ n ih =>
    apply plateau x
    rw [← iterate_on_image]
    exact ih (step x) ((iterate_on_image step n x).trans hn)

/-- Instantiating step with multiplication by p works for arbitrary locally
    p-power-torsion groups; no single exponent is assumed in advance. -/
theorem all_torsion_stabilizes {A : Type} (step : A → A) (z : A)
    (hz : step z = z) (e : Nat)
    (plateau : ∀ x, OddDescent.iterate step (e+1) x = z → OddDescent.iterate step e x = z)
    (torsion : ∀ x, ∃ n, OddDescent.iterate step n x = z) :
    ∀ x, OddDescent.iterate step e x = z := by
  intro x
  obtain ⟨n,hn⟩ := torsion x
  exact plateau_captures_kernel step z hz e plateau n x hn

theorem zero_layer {A : Type} (step : A → A) (z : A) (hz : step z = z)
    (kernel : ∀ x, step x = z → x = z)
    (torsion : ∀ x, ∃ n, OddDescent.iterate step n x = z) :
    ∀ x, x = z := all_torsion_stabilizes step z hz 0 kernel torsion

theorem one_layer {A : Type} (step : A → A) (z : A) (hz : step z = z)
    (kernel : ∀ x, step (step x) = z → step x = z)
    (torsion : ∀ x, ∃ n, OddDescent.iterate step n x = z) :
    ∀ x, step x = z := all_torsion_stabilizes step z hz 1 kernel torsion

/-- A character parametrization of the stabilized kernel parametrizes the
    entire torsion group. The returned data include both inverse identities. -/
def full_character_readout {A C : Type} (step : A → A) (z : A) (e : Nat)
    (hall : ∀ x, OddDescent.iterate step e x = z)
    (characters : OddDescent.InverseMaps {x : A // OddDescent.iterate step e x = z} C) :
    OddDescent.InverseMaps A C where
  forward x := characters.forward ⟨x,hall x⟩
  backward c := (characters.backward c).val
  backward_forward x := congrArg Subtype.val (characters.backward_forward ⟨x,hall x⟩)
  forward_backward c := characters.forward_backward c

end Reimann.TameStability
