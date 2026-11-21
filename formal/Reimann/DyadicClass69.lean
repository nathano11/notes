import Reimann.DyadicOrder

/-!
Complete enumeration of reduced primitive positive binary quadratic forms
for the fundamental discriminants -276 and -552. The field-theoretic step
identifies classes of primitive forms with ideal classes. Reducedness here
uses proper equivalence and the conventional positive sign on boundary rows.
-/

namespace Reimann.DyadicClass69

open Reimann.DyadicLattice Reimann.DyadicMoments Reimann.DyadicOrder

structure Form where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq

/-- The parameter m is the absolute value of the negative discriminant. -/
abbrev Reduced (m : Int) (f : Form) : Prop :=
  0 < f.a ∧ -f.a < f.b ∧ f.b ≤ f.a ∧ f.a ≤ f.c ∧
    (f.a = f.c → 0 ≤ f.b) ∧ 4*f.a*f.c - f.b*f.b = m

abbrev Primitive (f : Form) : Prop := Nat.gcd (Nat.gcd f.a.natAbs f.b.natAbs) f.c.natAbs = 1

/-- From |b| ≤ a ≤ c one obtains 3a² ≤ 4ac-b². -/
theorem leading_bound {m : Int} {f : Form} (h : Reduced m f) :
    3*f.a*f.a ≤ m := by
  obtain ⟨ha,hlo,hhi,hc,_,hd⟩ := h
  have hbb := Int.mul_nonneg (show 0 ≤ f.a-f.b by omega) (show 0 ≤ f.a+f.b by omega)
  have haa := Int.mul_nonneg (show 0 ≤ f.a by omega) (show 0 ≤ f.c-f.a by omega)
  grind

theorem coefficient_bounds {m : Int} {f : Form} (hm : m ≤ 552) (h : Reduced m f) :
    0 < f.a ∧ f.a ≤ 13 ∧ -13 ≤ f.b ∧ f.b ≤ 13 := by
  have hbound := leading_bound h
  obtain ⟨ha,hlo,hhi,hc,_,hd⟩ := h
  have hmax : f.a ≤ 13 := by
    by_cases hbig : f.a ≤ 13
    · exact hbig
    · have hx := Int.mul_nonneg (show 0 ≤ f.a-14 by omega) (show 0 ≤ f.a+14 by omega)
      grind
  omega

theorem last_coefficient {m : Int} {f : Form} (h : Reduced m f) :
    (m+f.b*f.b)/(4*f.a) = f.c := by
  obtain ⟨ha,_,_,_,_,hd⟩ := h
  have he : m+f.b*f.b = 4*f.a*f.c := by omega
  rw [he, Int.mul_ediv_cancel_left _ (by omega)]

def candidate (m : Int) (i j : Nat) : Form :=
  let a : Int := i
  let b : Int := (j : Int) - 13
  ⟨a, b, (m+b*b)/(4*a)⟩

def reducedForms (m : Int) : List Form :=
  ((List.range 14).flatMap (fun i => (List.range 27).map (candidate m i))).filter
    (fun f => decide (Reduced m f ∧ Primitive f))

/-- Every reduced primitive form of discriminant -m appears in the search. -/
theorem membership_iff (m : Int) (hm : m ≤ 552) (f : Form) :
    f ∈ reducedForms m ↔ Reduced m f ∧ Primitive f := by
  simp only [reducedForms, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨ha,ha13,hb0,hb13⟩ := coefficient_bounds hm h.1
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨f.a.toNat, by omega, (f.b+13).toNat, by omega, ?_⟩
    have ea : (f.a.toNat : Int) = f.a := by omega
    have eb : (((f.b+13).toNat : Int)-13) = f.b := by omega
    simp only [candidate, ea, eb, last_coefficient h.1]

set_option maxRecDepth 8000 in
theorem reduced_forms_276 : reducedForms 276 =
    [⟨1,0,69⟩, ⟨2,2,35⟩, ⟨3,0,23⟩, ⟨5,-2,14⟩, ⟨5,2,14⟩, ⟨6,6,13⟩,
     ⟨7,-2,10⟩, ⟨7,2,10⟩] := by decide

set_option maxRecDepth 8000 in
theorem reduced_forms_552 : reducedForms 552 =
    [⟨1,0,138⟩, ⟨2,0,69⟩, ⟨3,0,46⟩, ⟨6,0,23⟩, ⟨7,-6,21⟩, ⟨7,6,21⟩,
     ⟨11,-8,14⟩, ⟨11,8,14⟩] := by decide

/-- Each exhaustive list has exactly eight distinct rows. -/
theorem two_form_counts :
    (reducedForms 276).length = 8 ∧ (reducedForms 276).Nodup ∧
    (reducedForms 552).length = 8 ∧ (reducedForms 552).Nodup := by
  rw [reduced_forms_276, reduced_forms_552]
  decide

/-- The finite weight-one predicate is exactly realized once the two bits
of arithmetic information on the characteristic polynomial are known. -/
theorem sample_bits_of_coefficients (c0 c1 : Scalar)
    (h0 : c0.residue 2 = 4) (h1 : c1.residue 1 = 2) : WeightOneSamples c0 c1 := by
  unfold WeightOneSamples
  rw [inverse_weight_one_mod_eight, normalized_real_moments_3_23, h0]
  refine ⟨1, 1, by decide, by decide, ?_⟩
  have hred := (c1.reduce (by decide : 1 ≤ 2)).trans h1
  exact (by decide : ∀ b : BitVec 3, b.setWidth 2 = 2 →
    (quadraticSample 4 b.toNat 4 % 8 = 4 ∧ quadraticSample 4 b.toNat (-6) % 8 = 4))
    (c1.residue 2) hred

/-- The specializations at 0 and -2 are alternative sources of the two coefficient bits.
The value 4 modulo eight expresses exact valuation two. -/
theorem samples_of_zero_and_minus_two (c0 c1 : Scalar)
    (hp : c0.residue 2 = 4)
    (hm : (4 - 2*c1.residue 2 + c0.residue 2 : BitVec 3) = 4) :
    WeightOneSamples c0 c1 := by
  rw [hp] at hm
  apply sample_bits_of_coefficients _ _ hp
  rw [← c1.reduce (by decide : 1 ≤ 2)]
  exact (by decide : ∀ z : BitVec 3, 4-2*z+4=4 → z.setWidth 2 = 2) _ hm

/-- After arithmetic control identifies the bottom index with twice 2^e and
the first-layer index with twice 2^e·2^f, Kuroda's half-product of the two
quadratic class numbers supplies the second count. -/
theorem exponents_of_two_layer_counts (e f : Nat)
    (h0 : 2*2^e = (reducedForms 276).length)
    (h1 : 2*2^e*2^f = (reducedForms 276).length*(reducedForms 552).length/2) :
    e = 2 ∧ f = 2 := by
  have ⟨h276, _, h552, _⟩ := two_form_counts
  rw [h276] at h0
  rw [h276, h552, h0] at h1
  constructor
  · apply (Nat.pow_right_inj (by decide : 1 < 2)).mp
    change 2^e = 4
    omega
  · apply (Nat.pow_right_inj (by decide : 1 < 2)).mp
    change 2^f = 4
    omega

/-- The two field-control equalities fix the finite moment predicate when e
and f are the valuations of P(0) and P(-2). The last two hypotheses only
record their standard odd-unit factorizations reduced modulo eight. -/
theorem samples_of_two_layer_counts (c0 c1 : Scalar) (e f : Nat) (u v : BitVec 3)
    (h0 : 2*2^e = (reducedForms 276).length)
    (h1 : 2*2^e*2^f = (reducedForms 276).length*(reducedForms 552).length/2)
    (hp : c0.residue 2 = BitVec.ofNat 3 (2^e)*(1+2*u))
    (hm : 4-2*c1.residue 2+c0.residue 2 = BitVec.ofNat 3 (2^f)*(1+2*v)) :
    WeightOneSamples c0 c1 := by
  obtain ⟨rfl,rfl⟩ := exponents_of_two_layer_counts e f h0 h1
  have hunit : ∀ z : BitVec 3, BitVec.ofNat 3 (2^2)*(1+2*z) = 4 := by decide
  exact samples_of_zero_and_minus_two _ _ (hp.trans (hunit _)) (hm.trans (hunit _))

/-- The pair 3,23 is in the quadratic-residue branch of the finite example on
p.134 of Mizusawa: 7 is a square-root witness for 3 modulo 23. -/
theorem mizusawa_example_69 :
    3 % 8 = 3 ∧ 23 % 16 = 7 ∧ 3*23 < 5000 ∧ 7^2 % 23 = 3 := by decide

end Reimann.DyadicClass69
