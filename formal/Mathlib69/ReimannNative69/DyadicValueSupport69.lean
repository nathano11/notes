import ReimannNative69.DyadicIntegerPrime69
import ReimannNative69.DyadicValueUnion69

/-! The integer support of the union valuation is determined by its finite
prime contractions on the rings of algebraic integers. -/
namespace Reimann.DyadicValueSupport69

open DyadicIntegerPrime69 DyadicValueUnion69 DyadicLocalRestriction69
variable {L : Type} [Field L]

theorem integer_in_stage (D : Stages L) (x : integerRing L) :
    ∃ (n : ℕ) (y : integerRing (D.stage n)), integersMap (D.stage n).subtype y = x := by
  obtain ⟨n,hn⟩ := D.covers x.val
  let z : D.stage n := ⟨x.val,hn⟩
  exact ⟨n,⟨z,(integers_reflect (D.stage n).subtype Subtype.val_injective z).mp x.property⟩,rfl⟩

theorem union_integer_support (D : Stages L) (P : Ideal (integerRing L))
    (finiteSupport : ∀ n (y : integerRing (D.stage n)),
      y ∈ P.comap (integersMap (D.stage n).subtype) ↔ Supports (D.value n) y.val)
    (x : integerRing L) : x ∈ P ↔ Supports (normalized_union D) x.val := by
  obtain ⟨n,y,rfl⟩ := integer_in_stage D x
  refine (finiteSupport n y).trans ?_
  change (y.val=0 ∨ 0<(D.value n).val y.val) ↔ y.val.val = 0 ∨ 0<unionValue D y.val.val
  rw [on_stage]
  exact or_congr Subtype.ext_iff Iff.rfl

end Reimann.DyadicValueSupport69

