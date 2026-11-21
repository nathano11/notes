import Reimann.CircularHorner69
import Reimann.CircularIrreducible69
import Reimann.CircularLeastRelation69
import Reimann.CircularNormalForm69

/-! The ordinary 44 powers of a primitive 69th root have unique rational
coordinates for every value of a rational polynomial. -/

namespace Reimann.CircularIndependence69

open Lean.Grind CircularGauss69 CircularMonomial69 CircularLeastRelation69
  CircularRelationEval69 CircularNormalForm69

def phiQ (i : Nat) : Rat := ((coeff CircularPolynomial69.phi i : Int) : Rat)

theorem phiQ_bounded : Bounded phiQ 45 := by
  intro i hi; unfold phiQ; rw [CircularHorner69.phi_bounded i hi]; rfl

theorem phiQ_monic : phiQ 44 = 1 := by
  unfold phiQ; rw [CircularHorner69.phi_monic]; rfl

theorem primitive_vanishes {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) : Vanishes x phiQ := by
  refine ⟨45,phiQ_bounded,?_⟩
  exact (CircularHorner69.phi_eval_sum x).trans
    (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3)

theorem no_short_monic {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (d : Nat) (hd : d < 44) : ¬ MonicRelation (Vanishes x) d := by
  apply no_shorter_than_irreducible phiQ 44 phiQ_bounded phiQ_monic
    (Vanishes x) (primitive_vanishes x h69 h23 h3) _ _ _ _ d hd
  · rintro ⟨p,hb,hc,hv⟩
    exact no_monic_constant x p hb hc hv
  · exact fun f D s a hf hD => vanishes_sub_shift x f D s a hf hD
  · exact fun p m hp hv hn => monic_of_vanishing x p m hp hn hv
  · exact CircularIrreducible69.no_rational_split

theorem primitive_monomials_independent {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (p : Nat → Rat) (hp : Bounded p 44) (he : evalAt x p 44 = 0) : ∀ i, p i = 0 := by
  intro i; apply Classical.byContradiction; intro h
  obtain ⟨d,hd,hm⟩ := monic_of_vanishing x p 44 hp ⟨i,h⟩ ⟨44,hp,he⟩
  exact no_short_monic x h69 h23 h3 d hd hm

/-- Every rational-polynomial value at x has exactly one coefficient vector
supported in degrees 0 through 43. -/
theorem unique_rational_coordinates {R : Type} [Field R] [IsCharP R 0] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (p : Nat → Rat) (m : Nat) (hp : Bounded p m) :
    ∃ r, Bounded r 44 ∧ evalAt x r 44 = evalAt x p m ∧
      ∀ s, Bounded s 44 → evalAt x s 44 = evalAt x p m → s = r := by
  obtain ⟨r,hr,er⟩ := normal_form_at_root x phiQ 44 phiQ_bounded phiQ_monic
    (primitive_vanishes x h69 h23 h3) p m hp
  refine ⟨r,hr,er,?_⟩
  intro s hs es
  exact unique_at_degree x 44 (primitive_monomials_independent x h69 h23 h3)
    s r hs hr (es.trans er.symm)

end Reimann.CircularIndependence69
