import Reimann.CircularNormAction69

/-! The quadratic period embeds in the real part of the compositum generated
by square roots of −3 and −23 and the 277th roots of unity. -/

namespace Reimann.CircularRealUnit69

open Lean.Grind Lean.Grind.Field.NormNum CircularPolynomialField69
open CircularRational69 CircularRationalPeriod69 CircularRelationEval69

theorem product_square {R : Type} [Field R] (u v : R) (hu : u^2 = -3) (hv : v^2 = -23) :
    (u*v)^2 = 69 := by rw [CommSemiring.mul_pow, hu, hv]; grind only

theorem discriminant_square {R : Type} [Field R] (t : R) (ht : t^2 = t+17) : (2*t-1)^2=69 := by
  grind only

theorem signed_root {R : Type} [Field R] (t u v : R) (ht : t^2=t+17)
    (hu : u^2 = -3) (hv : v^2 = -23) : 2*t-1 = u*v ∨ 2*t-1 = -(u*v) := by
  have h1 := discriminant_square t ht
  have h2 := product_square u v hu hv
  have hz : ((2*t-1)-u*v)*((2*t-1)+u*v) = 0 := by grind only
  rcases Field.of_mul_eq_zero hz with h | h
  · left; grind only
  · right; grind only

theorem half_identity {R : Type} [Field R] [IsCharP R 0] : (ofRat (1/2) : R)*2=1 := by
  have hh := ofRat_mul (α := R) (1/2) 2
  have hq : (1/2 : Rat)*2=1 := by decide +kernel
  have htwo := cast_int (R := R) 2
  change (ofRat 2 : R) = _ at htwo
  rw [hq, ofRat_one, htwo] at hh
  grind only

theorem half_formula {R : Type} [Field R] [IsCharP R 0] (t u v : R) (ht : t^2=t+17)
    (hu : u^2 = -3) (hv : v^2 = -23) :
    t = ofRat (1/2)*(1+u*v) ∨ t = ofRat (1/2)*(1-u*v) := by
  have hh := half_identity (R := R)
  rcases signed_root t u v ht hu hv with h | h
  · left; grind only
  · right; grind only

theorem value_in_product_subfield {R : Type} [Field R] [IsCharP R 0]
    (t u v : R) (ht : t^2=t+17) (hu : u^2 = -3) (hv : v^2 = -23)
    (S : R → Prop) (hs : SubfieldContaining (u*v) S) (a : Element) : S (evaluate t a) := by
  have ho : S 1 := by simpa only [ofRat_one] using hs.rational 1
  have hhalf := hs.rational (1/2)
  have hroot : S t := by
    rcases half_formula t u v ht hu hv with h | h
    · rw [h]; exact hs.mul _ _ hhalf (hs.add _ _ ho hs.root)
    · rw [h]; exact hs.mul _ _ hhalf (hs.sub _ _ ho hs.root)
  exact hs.add _ _ (hs.rational a.a) (hs.mul _ _ (hs.rational a.b) hroot)

theorem value_in_subfield {R : Type} [Field R] [IsCharP R 0] (t u v : R)
    (ht : t^2=t+17) (hu : u^2 = -3) (hv : v^2 = -23)
    (S : R → Prop) (hs : SubfieldContaining u S) (hsv : S v) (a : Element) : S (evaluate t a) :=
  value_in_product_subfield t u v ht hu hv S { hs with root := hs.mul _ _ hs.root hsv } a

/-- A rational field automorphism whose square is the identity. -/
structure Conjugation (R : Type) [Field R] where
  app : R → R
  involutive : ∀ z, app (app z) = z
  rat : ∀ q : Rat, app (ofRat q) = ofRat q
  add : ∀ z w, app (z+w) = app z + app w
  sub : ∀ z w, app (z-w) = app z - app w
  mul : ∀ z w, app (z*w) = app z * app w
  inv : ∀ z, app z⁻¹ = (app z)⁻¹

theorem fixed_subfield {R : Type} [Field R] (c : Conjugation R) (z : R) (hz : c.app z = z) :
    SubfieldContaining z (fun w => c.app w = w) where
  rational := c.rat
  root := hz
  add := fun a b ha hb => by rw [c.add, ha, hb]
  sub := fun a b ha hb => by rw [c.sub, ha, hb]
  mul := fun a b ha hb => by rw [c.mul, ha, hb]
  inv := fun a _ ha => by rw [c.inv, ha]

theorem product_fixed {R : Type} [Field R] (c : Conjugation R) (u v : R)
    (hcu : c.app u = -u) (hcv : c.app v = -v) : c.app (u*v) = u*v := by
  rw [c.mul, hcu, hcv]; grind only

theorem value_fixed {R : Type} [Field R] [IsCharP R 0] (t u v : R)
    (ht : t^2=t+17) (hu : u^2 = -3) (hv : v^2 = -23)
    (c : Conjugation R) (hcu : c.app u = -u) (hcv : c.app v = -v) (a : Element) :
    c.app (evaluate t a) = evaluate t a :=
  value_in_product_subfield t u v ht hu hv _ (fixed_subfield c _ (product_fixed c u v hcu hcv)) a

/-- The smallest rational subfield containing u, v, and all ambient 277th roots of unity. -/
def Compositum {R : Type} [Field R] (u v y : R) : Prop :=
  ∀ S : R → Prop, SubfieldContaining u S → S v → (∀ z : R, z^277 = 1 → S z) → S y

theorem compositum_subfield {R : Type} [Field R] (u v : R) :
    SubfieldContaining u (Compositum u v) where
  rational := fun q _ hs _ _ => hs.rational q
  root := fun _ hs _ _ => hs.root
  add := fun a b ha hb S hs hv hz => hs.add a b (ha S hs hv hz) (hb S hs hv hz)
  sub := fun a b ha hb S hs hv hz => hs.sub a b (ha S hs hv hz) (hb S hs hv hz)
  mul := fun a b ha hb S hs hv hz => hs.mul a b (ha S hs hv hz) (hb S hs hv hz)
  inv := fun a hn ha S hs hv hz => hs.inv a hn (ha S hs hv hz)

theorem compositum_generators {R : Type} [Field R] (u v : R) :
    Compositum u v v ∧ ∀ z : R, z^277 = 1 → Compositum u v z :=
  ⟨fun _ _ hv _ => hv, fun z h _ _ _ hz => hz z h⟩

theorem map_one {R : Type} [Field R] (c : Conjugation R) : c.app 1 = 1 := by
  simpa only [ofRat_one] using c.rat 1

theorem map_power {R : Type} [Field R] (c : Conjugation R) (z : R) (n : Nat) :
    c.app (z^n) = (c.app z)^n := by
  induction n with
  | zero => rw [Semiring.pow_zero, Semiring.pow_zero, map_one]
  | succ n ih => rw [Semiring.pow_succ, c.mul, ih, Semiring.pow_succ]

theorem compositum_stable {R : Type} [Field R] (c : Conjugation R) (u v : R)
    (hcu : c.app u = -u) (hcv : c.app v = -v) {y : R} (hy : Compositum u v y) :
    Compositum u v (c.app y) := by
  let S := Compositum u v
  have hs := compositum_subfield u v
  have hzero : S 0 := by simpa only [ofRat_zero] using hs.rational 0
  have neg_mem (z : R) (hz : S z) : S (-z) := by
    have he : (0:R)-z = -z := by grind only
    rw [← he]; exact hs.sub _ _ hzero hz
  have hpre : SubfieldContaining u (fun z => S (c.app z)) := {
    rational := fun q => by rw [c.rat]; exact hs.rational q
    root := by rw [hcu]; exact neg_mem _ hs.root
    add := fun a b ha hb => by rw [c.add]; exact hs.add _ _ ha hb
    sub := fun a b ha hb => by rw [c.sub]; exact hs.sub _ _ ha hb
    mul := fun a b ha hb => by rw [c.mul]; exact hs.mul _ _ ha hb
    inv := fun a hn ha => by
      rw [c.inv]
      apply hs.inv _ _ ha
      intro he
      have hzero' := c.rat 0
      rw [ofRat_zero] at hzero'
      exact hn ((c.involutive a).symm.trans ((congrArg c.app he).trans hzero')) }
  apply hy _ hpre
  · rw [hcv]; exact neg_mem _ (compositum_generators u v).1
  · intro z hz
    apply (compositum_generators u v).2
    rw [← map_power, hz, map_one]

def RealPart {R : Type} [Field R] (c : Conjugation R) (u v y : R) : Prop :=
  Compositum u v y ∧ c.app y = y

theorem real_subfield {R : Type} [Field R] (c : Conjugation R) (u v : R) :
    SubfieldContaining (1 : R) (RealPart c u v) := by
  have s := compositum_subfield u v
  have f := fixed_subfield c 1 (map_one c)
  exact {
    rational := fun q => ⟨s.rational q, f.rational q⟩
    root := ⟨by simpa only [ofRat_one] using s.rational 1, f.root⟩
    add := fun a b ha hb => ⟨s.add a b ha.1 hb.1, f.add _ _ ha.2 hb.2⟩
    sub := fun a b ha hb => ⟨s.sub a b ha.1 hb.1, f.sub _ _ ha.2 hb.2⟩
    mul := fun a b ha hb => ⟨s.mul a b ha.1 hb.1, f.mul _ _ ha.2 hb.2⟩
    inv := fun a hn ha => ⟨s.inv a hn ha.1, f.inv _ hn ha.2⟩ }

theorem period_image_in_real_compositum {R : Type} [Field R] [IsCharP R 0]
    (x u v : R) (h69 : x^69=1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (hu : u^2 = -3) (hv : v^2 = -23) (c : Conjugation R)
    (hcu : c.app u = -u) (hcv : c.app v = -v) (a : Element) :
    RealPart c u v (evaluate (CircularFactor69.periodTheta x) a) := by
  have ht := CircularFactor69.period_theta_quadratic x (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3)
  exact ⟨value_in_subfield _ u v ht hu hv _ (compositum_subfield u v) (compositum_generators u v).1 a,
    value_fixed _ u v ht hu hv c hcu hcv a⟩

theorem period_embedding {R : Type} [Field R] [IsCharP R 0] (x u v : R)
    (h69 : x^69=1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hu : u^2=-3) (hv : v^2=-23)
    (c : Conjugation R) (hcu : c.app u = -u) (hcv : c.app v = -v) :
    (∀ a : Element, RealPart c u v (evaluate (CircularFactor69.periodTheta x) a)) ∧
    (∀ a b : Element, evaluate (CircularFactor69.periodTheta x) a =
      evaluate (CircularFactor69.periodTheta x) b → a = b) :=
  ⟨period_image_in_real_compositum x u v h69 h23 h3 hu hv c hcu hcv,
    fun _ _ => primitive_period_injective x h69 h23 h3⟩

theorem signed_real_units {R : Type} [Field R] [IsCharP R 0] (x u v : R)
    (h69 : x^69=1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hu : u^2=-3) (hv : v^2=-23)
    (c : Conjugation R) (hcu : c.app u = -u) (hcv : c.app v = -v) :
    let e := CircularPolynomial69.signedProduct x 1
    let f := 25-e
    RealPart c u v e ∧ RealPart c u v f ∧ e*f=1 ∧
      e^2-25*e+1=0 ∧ f^2-25*f+1=0 := by
  dsimp only
  have phi := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  let t := CircularFactor69.periodTheta x
  have ht : t^2=t+17 := CircularFactor69.period_theta_quadratic x phi
  have epi := period_image_in_real_compositum x u v h69 h23 h3 hu hv c hcu hcv (ofIntegral CircularQuadratic69.epsilon)
  rw [primitive_epsilon_image x h69 h23 h3] at epi
  have hs := real_subfield c u v
  have h25 : RealPart c u v 25 := by
    have hh := hs.rational 25
    have hc := cast_int (R := R) 25
    change (ofRat 25 : R) = _ at hc
    have hnum : (ofRat 25 : R) = 25 := by rw [hc]; grind only
    rwa [hnum] at hh
  refine ⟨epi, hs.sub _ _ h25 epi, ?_⟩
  have p := CircularNormAction69.quadratic_units_product t ht
  obtain ⟨a,b⟩ := CircularNormAction69.quadratic_units_monic t ht
  have h : CircularPolynomial69.signedProduct x 1 = 11+3*t := CircularFactor69.positive_signed_value x phi
  rw [h]
  exact ⟨by grind only, a, by grind only⟩

/-- Generator actions of complex conjugation on the common realization. -/
structure Compatible {R : Type} [Field R] (c : Conjugation R) (u v : R) : Prop where
  first : c.app u = -u
  second : c.app v = -v
  roots : ∀ z : R, z^277=1 → c.app z = z⁻¹

theorem compatible_conjugations_agree {R : Type} [Field R] (u v : R)
    (c d : Conjugation R) (hc : Compatible c u v) (hd : Compatible d u v)
    (y : R) (hy : Compositum u v y) : c.app y = d.app y := by
  apply hy (fun z => c.app z = d.app z)
  · exact {
      rational := fun q => (c.rat q).trans (d.rat q).symm
      root := hc.first.trans hd.first.symm
      add := fun a b ha hb => by rw [c.add, d.add, ha, hb]
      sub := fun a b ha hb => by rw [c.sub, d.sub, ha, hb]
      mul := fun a b ha hb => by rw [c.mul, d.mul, ha, hb]
      inv := fun a _ ha => by rw [c.inv, d.inv, ha] }
  · exact hc.second.trans hd.second.symm
  · exact fun z hz => (hc.roots z hz).trans (hd.roots z hz).symm

theorem compatible_real_parts_agree {R : Type} [Field R] (u v : R)
    (c d : Conjugation R) (hc : Compatible c u v) (hd : Compatible d u v) (y : R) :
    RealPart c u v y ↔ RealPart d u v y := by
  constructor
  · rintro ⟨hy, fixed⟩
    exact ⟨hy, (compatible_conjugations_agree u v c d hc hd y hy).symm.trans fixed⟩
  · rintro ⟨hy, fixed⟩
    exact ⟨hy, (compatible_conjugations_agree u v c d hc hd y hy).trans fixed⟩

theorem compatible_real_embedding {R : Type} [Field R] [IsCharP R 0] (x u v : R)
    (h69 : x^69=1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) (hu : u^2 = -3) (hv : v^2 = -23)
    (c : Conjugation R) (hc : Compatible c u v) :
    (∀ a : Element, RealPart c u v (evaluate (CircularFactor69.periodTheta x) a)) ∧
    (∀ a b : Element, evaluate (CircularFactor69.periodTheta x) a =
      evaluate (CircularFactor69.periodTheta x) b → a = b) :=
  period_embedding x u v h69 h23 h3 hu hv c hc.first hc.second

end Reimann.CircularRealUnit69
