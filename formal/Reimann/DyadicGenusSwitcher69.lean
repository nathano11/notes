import Reimann.DyadicAbelianTower69

/-! The genus characters of Mizusawa's two generators at the dyadic primes.
Here x²=−3 and y²=−23, so i*x and i*y generate the two real quadratic fields. -/
namespace Reimann.DyadicGenusSwitcher69

open Lean.Grind Reimann.DyadicLocalRestriction69 Reimann.DyadicBottomValue69
open Reimann.DyadicGenusField69 Reimann.DyadicCyclotomicSpan69
open Reimann.DyadicDecomposition69 Reimann.TameRationalField277

variable {F : Type} [Field F]

theorem fixed_subfield (g : Automorphism F) : Subfield (fun x => g.app x=x) where
  zero := g.zero
  one := g.one
  add := by intro x y hx hy; rw [g.add,hx,hy]
  neg := by intro x hx; rw [DyadicAbelianTower69.map_neg,hx]
  mul := by intro x y hx hy; rw [g.mul,hx,hy]
  inv := by intro x hx; rw [DyadicAbelianTower69.map_inverse,hx]

theorem fixed_on_genus (g : Automorphism F) (i x y : F) (ζ : Nat → F)
    (hk : g.app (i*x*y)=i*x*y) (h3 : g.app (i*x)=i*x) (h23 : g.app (i*y)=i*y)
    (hreal : ∀ n, g.app (realTrace (ζ n))=realTrace (ζ n)) (z : F)
    (hz : genusFieldByLayers (fun _ => False) i x y ζ z) : g.app z=z :=
  hz (fun t => g.app t=t) (fixed_subfield g) (fun _ h => h.elim) ⟨hk,h3,h23,hreal⟩

theorem fixed_factor (g : Automorphism F) (x y : F) (hy : y≠0)
    (yfix : g.app y=y) (xyfix : g.app (x*y)=x*y) : g.app x=x := by
  rw [g.mul,yfix] at xyfix
  have h := congrArg (fun t => t*y⁻¹) xyfix
  simpa only [Semiring.mul_assoc,Field.mul_inv_cancel hy,Semiring.mul_one] using h

theorem fixed_complement (g : Automorphism F) (i x y : F) (hy : i*y≠0)
    (hk : g.app (i*x*y)=i*x*y) (h23 : g.app (i*y)=i*y) : g.app x=x := by
  apply fixed_factor g x (i*y) hy h23
  rwa [show x*(i*y)=i*x*y by grind only]

/-- Fixing k∞ and i*y and acting nontrivially somewhere on the genus field
forces the signs on both radicals. The sign alternative is supplied by
the quadratic equation of y. -/
theorem nontrivial_coset_signs (g : Automorphism F) (i x y : F) (ζ : Nat → F)
    (ni : i≠0) (ny : y≠0) (sign : g.app y=y ∨ g.app y= -y)
    (hk : g.app (i*x*y)=i*x*y) (h23 : g.app (i*y)=i*y)
    (hreal : ∀ n, g.app (realTrace (ζ n))=realTrace (ζ n))
    (moves : ∃ z, genusFieldByLayers (fun _ => False) i x y ζ z ∧ g.app z≠z) :
    g.app x=x ∧ g.app y= -y ∧ g.app i= -i := by
  have nx := fixed_complement g i x y (fun h => (Field.of_mul_eq_zero h).elim ni ny) hk h23
  have ey : g.app y= -y := sign.resolve_left (by
    intro fix
    have ei := fixed_factor g i y ny fix h23
    obtain ⟨z,hz,ne⟩ := moves
    apply ne
    exact fixed_on_genus g i x y ζ hk (by rw [g.mul,ei,nx]) h23 hreal z hz)
  have h := g.mul i y
  rw [h23,ey] at h
  have eq : g.app i*y=(-i)*y := by grind only
  have ei := congrArg (fun z => z*y⁻¹) eq
  exact ⟨nx,ey,by simpa only [Semiring.mul_assoc,Field.mul_inv_cancel ny,Semiring.mul_one] using ei⟩

theorem genus_symmetric (i x y : F) (ζ : Nat → F) (z : F) :
    genusFieldByLayers (fun _ => False) i x y ζ z ↔ genusFieldByLayers (fun _ => False) i y x ζ z := by
  have sw : i*x*y=i*y*x := by grind only
  unfold genusFieldByLayers
  rw [sw]
  constructor <;> rintro h C c hb ⟨hk,h1,h2,hr⟩ <;> exact h C c hb ⟨hk,h2,h1,hr⟩

theorem radical_sign (f : Embedding F) (g : Automorphism F) (x : Biquad) (q : Rat)
    (hx : bm x x=scalar q) : g.app (f.app x)=f.app x ∨ g.app (f.app x)= -(f.app x) := by
  obtain ⟨s,hs⟩ := DyadicPrimeExchange69.radical_image_sign f g.app g.mul
    (DyadicPrimeExchange69.fixed_rationals f g.app g.zero g.one g.add g.mul) x q hx
  cases s <;> simp_all

theorem radicals_nonzero (f : Embedding F) (i : F) (hi : i*i= -1) :
    i≠0 ∧ f.app gen3≠0 ∧ f.app gen23≠0 := by
  refine ⟨?_,fun h => (by decide +kernel : gen3 ≠ scalar 0) (f.faithful _ h),
    fun h => (by decide +kernel : gen23 ≠ scalar 0) (f.faithful _ h)⟩
  intro e
  rw [e,Semiring.zero_mul] at hi
  have h : (0:F)=1 := by grind only
  exact Field.zero_ne_one h

/-- B from N′ fixes k∞(√23), and BH generates the nontrivial quotient N′/H. -/
theorem mizusawa_B_signs (f : Embedding F) (g : Automorphism F) (i : F) (hi : i*i= -1) (ζ : Nat → F)
    (hk : g.app (i*f.app gen3*f.app gen23)=i*f.app gen3*f.app gen23)
    (h23 : g.app (i*f.app gen23)=i*f.app gen23)
    (hreal : ∀ n, g.app (realTrace (ζ n))=realTrace (ζ n))
    (moves : ∃ z, genusFieldByLayers (fun _ => False) i (f.app gen3) (f.app gen23) ζ z ∧ g.app z≠z) :
    g.app (f.app gen3)=f.app gen3 ∧ g.app (f.app gen23)= -(f.app gen23) ∧ g.app i= -i :=
  nontrivial_coset_signs g i _ _ ζ (radicals_nonzero f i hi).1 (radicals_nonzero f i hi).2.2
    (radical_sign f g gen23 (-23) generator_squares.2) hk h23 hreal moves

/-- A from N fixes k∞(√3), and AH generates the nontrivial quotient N/H. -/
theorem mizusawa_A_signs (f : Embedding F) (g : Automorphism F) (i : F) (hi : i*i= -1) (ζ : Nat → F)
    (hk : g.app (i*f.app gen3*f.app gen23)=i*f.app gen3*f.app gen23)
    (h3 : g.app (i*f.app gen3)=i*f.app gen3)
    (hreal : ∀ n, g.app (realTrace (ζ n))=realTrace (ζ n))
    (moves : ∃ z, genusFieldByLayers (fun _ => False) i (f.app gen3) (f.app gen23) ζ z ∧ g.app z≠z) :
    g.app (f.app gen23)=f.app gen23 ∧ g.app (f.app gen3)= -(f.app gen3) ∧ g.app i= -i := by
  have hk' : g.app (i*f.app gen23*f.app gen3)=i*f.app gen23*f.app gen3 := by
    rwa [show i*f.app gen23*f.app gen3=i*f.app gen3*f.app gen23 by grind only]
  obtain ⟨z,hz,ne⟩ := moves
  exact nontrivial_coset_signs g i _ _ ζ (radicals_nonzero f i hi).1 (radicals_nonzero f i hi).2.1
    (radical_sign f g gen3 (-3) generator_squares.1) hk' h3 hreal
    ⟨z,(genus_symmetric _ _ _ _ _).mp hz,ne⟩

/-- At either labeled dyadic prime and at arbitrary real levels, B switches
the two centers as a consequence of its defining genus coset. -/
theorem mizusawa_switcher (f : Embedding F) (B : Automorphism F) (i : F) (hi : i*i= -1) (ζ : Nat → F)
    (hk : B.app (i*f.app gen3*f.app gen23)=i*f.app gen3*f.app gen23)
    (h23 : B.app (i*f.app gen23)=i*f.app gen23)
    (hreal : ∀ n, B.app (realTrace (ζ n))=realTrace (ζ n))
    (moves : ∃ z, genusFieldByLayers (fun _ => False) i (f.app gen3) (f.app gen23) ζ z ∧ B.app z≠z)
    (V : DyadicValue F) (v : Bool) (hV : Centered f V v) :
    Centered f (pull V B) (!v) ∧ ¬ Centered f (pull V B) v :=
  DyadicPrimeExchange69.artin_place_exchange f B.app V (pull V B) B.zero B.one B.add B.mul
    (mizusawa_B_signs f B i hi ζ hk h23 hreal moves).2.1 v hV (fun _ => rfl)

end Reimann.DyadicGenusSwitcher69
