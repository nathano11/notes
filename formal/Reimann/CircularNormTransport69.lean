import Reimann.CircularNorm69
import Reimann.CircularKernel69

/-! Base change of the signed quadratic determinant and the orbit product
at conductor 69. The target determinant expands all cofactors. -/
namespace Reimann.CircularNormTransport69

open Lean.Grind CircularQuadratic69 CircularFactor69 CircularNorm69
attribute [local instance] Ring.intCast

/-- Ordinary first-row Laplace expansion. The formula is valid on all square
row tables. Both missing entries and missing rows are padded by zero. -/
def laplace {R : Type} [CommRing R] : Nat → List (List R) → R
  | 0, _ => 1
  | n+1, rows => (List.range (n+1)).foldl (fun acc j =>
      let a := (rows.headD [])[j]?.getD 0
      let minor := rows.tail.map (fun row => row.eraseIdx j)
      let term := a * laplace n minor
      acc + (if j % 2 = 0 then term else -term)) 0

theorem embed_neg {R : Type} [CommRing R] (t : R) (a : Element) :
    embed t (-a.1, -a.2) = -embed t a := by
  simp only [embed, Ring.intCast_neg]
  grind only

theorem map_entry {R : Type} [CommRing R] (t : R) (row : List Element) (j : Nat) :
    ((row.map (embed t))[j]?).getD 0 = embed t ((row[j]?).getD (0, 0)) := by
  rw [List.getElem?_map]
  cases row[j]? <;> simp [embed_zero]

theorem map_first_row {R : Type} [CommRing R] (t : R) (rows : List (List Element)) :
    (rows.map (List.map (embed t))).headD [] = (rows.headD []).map (embed t) := by
  cases rows <;> rfl

theorem map_minor {R : Type} [CommRing R] (t : R) (rows : List (List Element)) (j : Nat) :
    (rows.map (List.map (embed t))).tail.map (fun row => row.eraseIdx j) =
    (rows.tail.map (fun row => row.eraseIdx j)).map (List.map (embed t)) := by
  have row_identity (r : List Element) (i : Nat) :
      (r.map (embed t)).eraseIdx i = (r.eraseIdx i).map (embed t) := by
    induction r generalizing i with
    | nil => rfl
    | cons a r ih =>
      cases i with
      | zero => rfl
      | succ k => exact congrArg (List.cons (embed t a)) (ih k)
  cases rows with
  | nil => rfl
  | cons row rest =>
    simp only [List.map_cons, List.tail_cons, List.map_map, Function.comp_def]
    exact List.map_congr_left (fun r _ => row_identity r j)

theorem fold_map {A B : Type} (f : A → B) (s : A → Nat → A) (u : B → Nat → B)
    (compatible : ∀ a j, f (s a j) = u (f a) j) (indices : List Nat) (initial : A) :
    f (indices.foldl s initial) = indices.foldl u (f initial) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons j js ih => rw [List.foldl_cons, List.foldl_cons, ih, compatible]

theorem embed_cofactor_step {R : Type} [CommRing R] (t : R) (ht : t^2=t+17)
    (acc a d : Element) (j : Nat) :
    embed t (if a = (0,0) then acc else
      pairAdd acc (if j % 2 = 0 then product a d else (-(product a d).1, -(product a d).2))) =
    embed t acc + (if j % 2 = 0 then embed t a * embed t d else -(embed t a * embed t d)) := by
  by_cases h : a = (0,0)
  · subst a
    simp only [ite_true, embed_zero, Semiring.zero_mul]
    split <;> grind only
  · simp only [h, ↓reduceIte, embed_add]
    split <;> simp only [embed_neg, embed_product t ht]

/-- Specialization commutes with the determinant in every size, including
when a nonzero source entry specializes to zero. -/
theorem embed_determinant {R : Type} [CommRing R] (t : R) (ht : t^2=t+17) (n : Nat)
    (rows : List (List Element)) :
    embed t (determinant n rows) = laplace n (rows.map (List.map (embed t))) := by
  induction n generalizing rows with
  | zero =>
    simp only [determinant, laplace, embed, Ring.intCast_one, Ring.intCast_zero]
    grind only
  | succ n ih =>
    rw [determinant, laplace]
    rw [← embed_zero t]
    apply fold_map
    intro acc j
    simp only [map_first_row, embed_zero, map_entry, map_minor]
    rw [← ih]
    exact embed_cofactor_step t ht acc _ _ j

theorem positive_determinant_at_root {R : Type} [CommRing R] (t : R) (ht : t^2 = t+17) :
    laplace 22 ((multiplicationMatrix positiveCoeffs.dropLast).map (List.map (embed t))) =
      11 + 3*t := by
  calc
    _ = laplace positiveCoeffs.dropLast.length _ := by rw [monic_decompositions.2.2.1]
    _ = embed t (companionNorm positiveCoeffs.dropLast) := (embed_determinant t ht _ _).symm
    _ = _ := by
      rw [positive_companion_norm]
      change Int.cast 11 + Int.cast 3 * t = _
      grind only

theorem negative_determinant_at_root {R : Type} [CommRing R] (t : R) (ht : t^2 = t+17) :
    laplace 22 ((multiplicationMatrix negativeCoeffs.dropLast).map (List.map (embed t))) =
      14 - 3*t := by
  calc
    _ = laplace negativeCoeffs.dropLast.length _ := by rw [monic_decompositions.2.2.2]
    _ = embed t (companionNorm negativeCoeffs.dropLast) := (embed_determinant t ht _ _).symm
    _ = _ := by
      rw [negative_companion_norm]
      change Int.cast 14 + Int.cast (-3) * t = _
      grind only

theorem signed_product_eq_specialized_determinant {R : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1) :
    CircularPolynomial69.signedProduct x 1 =
      laplace 22 ((multiplicationMatrix positiveCoeffs.dropLast).map
        (List.map (embed (periodTheta x)))) := by
  rw [signed_product_eq_embedded_companion_determinant x h69 h23 h3]
  have hx := CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3
  have ht := period_theta_quadratic x hx
  simpa only [companionNorm, monic_decompositions.2.2.1] using
    (embed_determinant (periodTheta x) ht positiveCoeffs.dropLast.length
      (multiplicationMatrix positiveCoeffs.dropLast))

/-- A conjugate of the circular factor depends only on the exponent of the
image of the generator. -/
theorem conjugate_factor {R : Type} [CommRing R] (x : R) (σ : R → R) (a : Nat)
    (hsub : σ (1-x) = 1-σ x) (hgen : σ x = x^a) :
    σ (1-x) = 1-x^a := by rw [hsub, hgen]

/-- An enumeration of the conjugates may use any ordering of the signed
exponents. For automorphisms the subtraction hypothesis follows by functoriality. -/
theorem orbit_product_of_power_action {R A : Type} [CommRing R] (x : R) (sign : Nat)
    (autos : List A) (exponent : A → Nat) (act : A → R → R)
    (hsub : ∀ σ, act σ (1-x) = 1-act σ x) (hgen : ∀ σ, act σ x = x^(exponent σ))
    (horbit : (autos.map exponent).Perm (CircularPolynomial69.exponents sign)) :
    autos.foldr (fun σ acc => act σ (1-x) * acc) 1 =
      CircularPolynomial69.signedProduct x sign := by
  have hf := fun σ => conjugate_factor x (act σ) (exponent σ) (hsub σ) (hgen σ)
  have h := CircularKernel69.product_permutation x horbit
  simpa only [CircularPolynomial69.eval_factors, CircularPolynomial69.signedProduct,
    List.foldr_map, Function.comp_def, hf] using h

theorem positive_orbit_product {R A : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (autos : List A) (exponent : A → Nat) (act : A → R → R)
    (hsub : ∀ σ, act σ (1-x) = 1-act σ x) (hgen : ∀ σ, act σ x = x^(exponent σ))
    (horbit : (autos.map exponent).Perm (CircularPolynomial69.exponents 1)) :
    autos.foldr (fun σ acc => act σ (1-x) * acc) 1 = 11 + 3 * periodTheta x := by
  rw [orbit_product_of_power_action x 1 autos exponent act hsub hgen horbit,
    signed_product_eq_specialized_determinant x h69 h23 h3]
  exact positive_determinant_at_root _ (period_theta_quadratic x
    (CircularPrimitive69.phi_vanishes_of_order69 x h69 h23 h3))

/-- Descend an orbit-product norm formula to the base field through an
injective embedding. The inputs identify the actual norm, the full relative
automorphism orbit, and the chosen period in the base. -/
theorem descent_of_relative_orbit_product {R A B : Type} [Field R] (x : R)
    (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (autos : List A) (exponent : A → Nat) (act : A → R → R)
    (hsub : ∀ σ, act σ (1-x) = 1-act σ x) (hgen : ∀ σ, act σ x = x^(exponent σ))
    (horbit : (autos.map exponent).Perm (CircularPolynomial69.exponents 1))
    (ι : B → R) (hinj : ∀ a b, ι a = ι b → a = b) (relativeNorm unitValue : B)
    (hnorm : ι relativeNorm = autos.foldr (fun σ acc => act σ (1-x) * acc) 1)
    (hunit : ι unitValue = 11 + 3 * periodTheta x) :
    relativeNorm = unitValue := by
  apply hinj
  rw [hnorm, hunit]
  exact positive_orbit_product x h69 h23 h3 autos exponent act hsub hgen horbit

end Reimann.CircularNormTransport69
