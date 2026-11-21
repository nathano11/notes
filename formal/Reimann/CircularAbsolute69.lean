import Reimann.CircularConvolution69
import Reimann.CircularPrimeDivisor69

/-! Integral coefficient factorization of the conductor-69 polynomial. -/
namespace Reimann.CircularAbsolute69

open Lean.Grind CircularGauss69 CircularEisenstein69
set_option maxHeartbeats 600000

theorem coeff_nil {R : Type} [OfNat R 0] (n : Nat) : coeff ([] : List R) n = 0 := by
  simp [coeff]

theorem coeff_cons_zero {R : Type} [OfNat R 0] (a : R) (p : List R) :
    coeff (a::p) 0 = a := rfl

theorem coeff_cons_succ {R : Type} [OfNat R 0] (a : R) (p : List R) (n : Nat) :
    coeff (a::p) (n+1) = coeff p n := rfl

theorem coeff_padd {R : Type} [CommRing R] (p q : List R) (n : Nat) :
    coeff (padd p q) n = coeff p n + coeff q n := by
  induction p generalizing q n with
  | nil => simp [padd, coeff_nil, AddCommMonoid.zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, coeff_nil, AddCommMonoid.add_zero]
    | cons b q =>
      cases n with
      | zero => rfl
      | succ n => exact ih q n

theorem coeff_scale {R : Type} [CommRing R] (a : R) (q : List R) (n : Nat) :
    coeff (q.map (fun b => a*b)) n = a * coeff q n := by
  induction q generalizing n with
  | nil => simp [coeff_nil] <;> grind only
  | cons b q ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n

theorem sumBelow_first {R : Type} [CommRing R] (f : Nat → R) (n : Nat) :
    sumBelow f (n+1) = f 0 + sumBelow (fun k => f (k+1)) n := by
  induction n with
  | zero => simp only [sumBelow]; grind only
  | succ n ih =>
    change sumBelow f (n+1) + f (n+1) = f 0 + (sumBelow _ n + f (n+1))
    rw [ih]
    grind only

theorem sumBelow_ext {R : Type} [CommRing R] (f g : Nat → R) (n : Nat)
    (h : ∀ i, i<n → f i = g i) : sumBelow f n = sumBelow g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumBelow, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumBelow_zero {R : Type} [CommRing R] (n : Nat) :
    sumBelow (fun _ => (0:R)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumBelow, ih, AddCommMonoid.add_zero]

theorem convolution_nil {R : Type} [CommRing R] (q : List R) (n : Nat) :
    convolution (coeff []) (coeff q) n = 0 := by
  unfold convolution
  rw [← sumBelow_zero (R := R) (n+1)]
  apply sumBelow_ext
  intro i hi
  simp [coeff_nil]
  grind only

theorem convolution_cons_zero {R : Type} [CommRing R] (a : R) (p q : List R) :
    convolution (coeff (a::p)) (coeff q) 0 = a * coeff q 0 := by
  simp [convolution, sumBelow, coeff_cons_zero, AddCommMonoid.zero_add]

theorem convolution_cons_succ {R : Type} [CommRing R] (a : R) (p q : List R) (n : Nat) :
    convolution (coeff (a::p)) (coeff q) (n+1) =
      a * coeff q (n+1) + convolution (coeff p) (coeff q) n := by
  unfold convolution
  rw [sumBelow_first]
  simp only [coeff_cons_zero, Nat.sub_zero, coeff_cons_succ, Nat.succ_sub_succ_eq_sub]

theorem coeff_pmul {R : Type} [CommRing R] (p q : List R) (n : Nat) :
    coeff (pmul p q) n = convolution (coeff p) (coeff q) n := by
  induction p generalizing n with
  | nil => simp [pmul, coeff_nil, convolution_nil]
  | cons a p ih =>
    cases n with
    | zero =>
      simp [pmul, coeff_padd, coeff_scale, convolution_cons_zero, coeff_cons_zero,
        AddCommMonoid.add_zero]
    | succ n =>
      simp only [pmul, coeff_padd, coeff_scale, coeff_cons_succ, convolution_cons_succ, ih]

theorem sumBelow_reverse {R : Type} [CommRing R] (f : Nat → R) (n : Nat) :
    sumBelow (fun i => f (n-i)) (n+1) = sumBelow f (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_first]
    simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub, ih]
    change f (n+1) + sumBelow f (n+1) = sumBelow f (n+1) + f (n+1)
    grind only

theorem convolution_comm {R : Type} [CommRing R] (a b : Nat → R) (n : Nat) :
    convolution a b n = convolution b a n := by
  unfold convolution
  rw [← sumBelow_reverse (fun i => b i * a (n-i)) n]
  apply sumBelow_ext
  intro i hi
  have index : n - (n-i) = i := by omega
  rw [index]
  grind only

theorem length_padd {R : Type} [Add R] (p q : List R) :
    (padd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q => simp only [padd, List.length_cons, ih]; omega

theorem length_pmul_cons {R : Type} [CommRing R] (a : R) (p q : List R) (hq : 0 < q.length) :
    (pmul (a::p) q).length = p.length + q.length := by
  induction p generalizing a with
  | nil => simp only [pmul, length_padd, List.length_map, List.length_cons, List.length_nil]; omega
  | cons b p ih =>
    change (padd (q.map _) (0 :: pmul (b::p) q)).length = _
    simp only [length_padd, List.length_map, List.length_cons, ih]
    omega

theorem length_pmul {R : Type} [CommRing R] (p q : List R)
    (hp : 0 < p.length) (hq : 0 < q.length) :
    (pmul p q).length + 1 = p.length + q.length := by
  cases p with
  | nil => simp at hp
  | cons a p => rw [length_pmul_cons a p q hq]; simp; omega

theorem eq_of_coeff_length {R : Type} [OfNat R 0] (p q : List R) (hlen : p.length = q.length)
    (hc : ∀ n, coeff p n = coeff q n) : p = q := by
  induction p generalizing q with
  | nil => simpa using hlen.symm
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      have hab : a = b := hc 0
      have ht := ih q (by simpa using hlen) (fun n => hc (n+1))
      rw [hab, ht]

theorem polynomial_product_of_convolution (p q : List Int) (u v : Nat)
    (hp : p.length = u+1) (hq : q.length = v+1) (hdeg : u+v=44)
    (hconv : ∀ n, convolution (coeff p) (coeff q) n = coeff CircularPolynomial69.phi n) :
    pmul p q = CircularPolynomial69.phi := by
  apply eq_of_coeff_length
  · have h := length_pmul p q (by omega) (by omega)
    have spec : CircularPolynomial69.phi.length = 45 := by decide
    omega
  · intro n
    exact (coeff_pmul p q n).trans (hconv n)

theorem pmul_comm_nonempty {R : Type} [CommRing R] (p q : List R)
    (hp : 0 < p.length) (hq : 0 < q.length) : pmul p q = pmul q p := by
  apply eq_of_coeff_length
  · have h := length_pmul p q hp hq
    have h' := length_pmul q p hq hp
    omega
  · intro n
    simpa only [coeff_pmul] using convolution_comm (coeff p) (coeff q) n

theorem monic_split {R : Type} [OfNat R 1] (p : List R) (hp : p.getLast? = some 1) :
    ∃ s, p = s ++ [1] := by
  induction p with
  | nil => simp at hp
  | cons a p ih =>
    cases p with
    | nil =>
      have h : a = 1 := by simpa using hp
      exact ⟨[], by simp [h]⟩
    | cons b p =>
      have ht : (b::p).getLast? = some 1 := hp
      obtain ⟨s,h⟩ := ih ht
      exact ⟨a::s, by simp [← h]⟩

theorem factor_vanishes (p q : List Int) (v : Nat) (hv : v<44)
    (hq : q.getLast? = some 1) (hdeg : q.length = v+1)
    (h : pmul p q = CircularPolynomial69.phi) : omegaEval (p.map reduce23) = (0,0) := by
  obtain ⟨s,hs⟩ := monic_split q hq
  have hprod := congrArg (List.map reduce23) h
  rw [reduce23_pmul, phi_reduce, hs, List.map_append] at hprod
  apply CircularPrimeDivisor69.positive_factor_vanishes (p.map reduce23) (s.map reduce23)
  · rw [hs, List.length_append] at hdeg
    simp only [List.length_map, List.length_cons, List.length_nil] at *
    omega
  · exact hprod

/-- No two monic positive-degree integer polynomials have product Φ₆₉. -/
theorem no_monic_integer_factorization (p q : List Int) (u v : Nat)
    (hu : 0<u) (hv : 0<v) (hdeg : u+v=44)
    (hp : p.length = u+1) (hq : q.length = v+1)
    (mp : p.getLast? = some 1) (mq : q.getLast? = some 1)
    (hconv : ∀ n, convolution (coeff p) (coeff q) n = coeff CircularPolynomial69.phi n) :
    False := by
  have product := polynomial_product_of_convolution p q u v hp hq hdeg hconv
  have comm := pmul_comm_nonempty p q (by omega) (by omega)
  have left := factor_vanishes p q v (by omega) mq hq product
  have right := factor_vanishes q p u (by omega) mp hp (comm.symm.trans product)
  exact phi_factor_obstruction p q product left right

/-- In every monic integer factorization of Φ₆₉, one factor is constant. -/
theorem integer_factor_is_constant (p q : List Int)
    (mp : p.getLast? = some 1) (mq : q.getLast? = some 1)
    (h : pmul p q = CircularPolynomial69.phi) : p.length = 1 ∨ q.length = 1 := by
  obtain ⟨pp,ep⟩ := monic_split p mp
  obtain ⟨qq,eq⟩ := monic_split q mq
  have hp : p.length = pp.length + 1 := by simp [ep]
  have hq : q.length = qq.length + 1 := by simp [eq]
  have hsum := length_pmul p q (by omega) (by omega)
  rw [h] at hsum
  have hphi : CircularPolynomial69.phi.length = 45 := by decide
  by_cases hpone : p.length = 1
  · exact Or.inl hpone
  by_cases hqone : q.length = 1
  · exact Or.inr hqone
  exfalso
  apply no_monic_integer_factorization p q pp.length qq.length (by omega) (by omega)
    (by omega) hp hq mp mq
  intro n
  rw [← coeff_pmul, h]

#print axioms integer_factor_is_constant

end Reimann.CircularAbsolute69
