import Reimann.CircularConvolution69

/-! Clearing rational monic factors using the first surviving coefficient
of a product modulo a prime divisor of a minimal common denominator. -/
namespace Reimann.CircularGauss69

theorem least_witness {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ k < n, ¬ P k := by
  classical
  obtain ⟨n,hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases earlier : ∃ k < n, P k
    · obtain ⟨k,hk,hp⟩ := earlier
      exact ih k hk hp
    · exact ⟨n,hn, fun k hk hp => earlier ⟨k,hk,hp⟩⟩

def PrimeDivisor (p : Nat) : Prop :=
  1 < p ∧ ∀ k, k ∣ p → k = 1 ∨ k = p

theorem prime_divisor_exists (n : Nat) (hn : 1 < n) :
    ∃ p, PrimeDivisor p ∧ p ∣ n := by
  obtain ⟨p,⟨hp,hpn⟩,least⟩ := least_witness (P := fun k => 1 < k ∧ k ∣ n)
    ⟨n,hn,Nat.dvd_refl n⟩
  refine ⟨p,⟨hp,?_⟩,hpn⟩
  intro k hk
  have kle := Nat.le_of_dvd (by omega : 0 < p) hk
  have kn : k ∣ n := Nat.dvd_trans hk hpn
  by_cases e : k = p
  · exact Or.inr e
  · have nc := least k (by omega) 
    have nz : k ≠ 0 := by intro h; subst k; simp at hk; omega
    have small : ¬ 1 < k := fun h => nc ⟨h,kn⟩
    exact Or.inl (by omega)

theorem prime_dvd_mul_int {p : Nat} (hp : PrimeDivisor p) {a b : Int}
    (h : (p : Int) ∣ a*b) : (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  have hn : p ∣ a.natAbs * b.natAbs := by
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr h
  rcases hp.2 (Nat.gcd p a.natAbs) (Nat.gcd_dvd_left _ _) with e | e
  · exact Or.inr (Int.natAbs_dvd_natAbs.mp ((show Nat.Coprime p a.natAbs from e).dvd_of_dvd_mul_left hn))
  · exact Or.inl (Int.natAbs_dvd_natAbs.mp (e ▸ Nat.gcd_dvd_right p a.natAbs))

theorem sum_dvd (p : Int) (f : Nat → Int) (n : Nat) (h : ∀ k < n, p ∣ f k) :
    p ∣ sumBelow f n := by
  induction n with
  | zero => exact Int.dvd_zero p
  | succ n ih => exact Int.dvd_add (ih (fun k hk => h k (by omega))) (h n (by omega))

theorem sum_except_dvd (p : Int) (f : Nat → Int) (n i : Nat) (hi : i < n)
    (h : ∀ k < n, k ≠ i → p ∣ f k) : p ∣ (sumBelow f n - f i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases e : i = n
    · subst i
      simpa [sumBelow] using sum_dvd p f n (fun k hk => h k (by omega) (by omega))
    · have hlow := ih (by omega) (fun k hk => h k (by omega))
      have hh := Int.dvd_add hlow (h n (by omega) (Ne.symm e))
      have eqn : sumBelow f (n+1) - f i = (sumBelow f n - f i) + f n := by simp only [sumBelow]; omega
      exact eqn ▸ hh

theorem convolution_survives_prime {p : Nat} (hp : PrimeDivisor p) (a b : Nat → Int)
    (ha : ∃ i, ¬ (p : Int) ∣ a i) (hb : ∃ j, ¬ (p : Int) ∣ b j) :
    ∃ n, ¬ (p : Int) ∣ convolution a b n := by
  classical
  obtain ⟨i,hi,hbefore⟩ := least_witness ha
  obtain ⟨j,hj,hbelow⟩ := least_witness hb
  let f := fun k => a k * b (i+j-k)
  have others : ∀ k < i+j+1, k ≠ i → (p : Int) ∣ f k := by
    intro k hk hki
    by_cases lt : k < i
    · exact Int.dvd_mul_of_dvd_left (Classical.not_not.mp (hbefore k lt))
    · exact Int.dvd_mul_of_dvd_right (Classical.not_not.mp (hbelow _ (by omega)))
  have rest := sum_except_dvd (p : Int) f (i+j+1) i (by omega) others
  refine ⟨i+j, fun h => ?_⟩
  have one := Int.dvd_sub h rest
  change (p : Int) ∣ sumBelow f (i+j+1) - (sumBelow f (i+j+1) - f i) at one
  have prod : (p : Int) ∣ a i * b j := by
    simpa [f, Int.sub_sub_self] using one
  exact (prime_dvd_mul_int hp prod).elim hi hj

theorem clear_single_denominator (q : Rat) : (q.den : Rat) * q = (q.num : Rat) := by
  have eqn := Rat.num_divInt_den q
  rw [Rat.divInt_eq_div, Rat.intCast_natCast] at eqn
  have nz : (q.den : Rat) ≠ 0 := by
    intro h
    exact q.den_nz (Rat.natCast_inj.mp (show (q.den : Rat) = ((0 : Nat) : Rat) from h))
  calc
    (q.den : Rat) * q = q * q.den := Rat.mul_comm ..
    _ = ((q.num : Rat) / q.den) * q.den := congrArg (fun t : Rat => t * q.den) eqn.symm
    _ = q.num := Rat.div_mul_cancel nz

theorem clear_list_denominators (a : List Rat) :
    ∃ d : Nat, 0 < d ∧ ∀ q ∈ a, ∃ z : Int, (d : Rat)*q = (z : Rat) := by
  induction a with
  | nil => exact ⟨1,by decide,by simp⟩
  | cons q a ih =>
    obtain ⟨d,hd,clear⟩ := ih
    refine ⟨d*q.den,Nat.mul_pos hd (Nat.pos_of_ne_zero q.den_nz),?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with e | h
    · subst t
      refine ⟨(d : Int)*q.num,?_⟩
      rw [Rat.natCast_mul, Rat.intCast_mul, Rat.intCast_natCast, Rat.mul_assoc, clear_single_denominator]
    · obtain ⟨z,hz⟩ := clear t h
      refine ⟨(q.den : Int)*z,?_⟩
      rw [Nat.mul_comm, Rat.natCast_mul, Rat.intCast_mul, Rat.intCast_natCast, Rat.mul_assoc, hz]

def Clears (a : List Rat) (d : Nat) : Prop :=
  ∀ i, ∃ z : Int, (d : Rat) * coeff a i = (z : Rat)

theorem minimal_denominator (a : List Rat) :
    ∃ d : Nat, (0 < d ∧ Clears a d) ∧ ∀ k < d, ¬ (0 < k ∧ Clears a k) := by
  apply least_witness
  obtain ⟨d,hd,hall⟩ := clear_list_denominators a
  refine ⟨d,hd,?_⟩
  intro i
  cases e : a[i]? with
  | none => exact ⟨0,by simp [coeff, e]⟩
  | some q =>
    have hm := List.mem_iff_getElem?.mpr ⟨i,e⟩
    simpa [coeff,e] using hall q hm

theorem coeff_of_mem {A : Type} [OfNat A 0] {c : A} {a : List A} (h : c ∈ a) :
    ∃ i, coeff a i = c := by
  obtain ⟨i,e⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i,by simp [coeff,e]⟩

theorem cancel_rational_natural {p : Nat} (hp : 0 < p) {x y : Rat}
    (h : (p : Rat)*x = (p : Rat)*y) : x = y := by
  have nz : (p : Rat) ≠ 0 := fun e => (Nat.ne_of_gt hp) (Rat.natCast_eq_zero_iff.mp e)
  have eqn := congrArg (fun t : Rat => (p : Rat)⁻¹*t) h
  simpa only [← Rat.mul_assoc, Rat.inv_mul_cancel _ nz, Rat.one_mul] using eqn

theorem smaller_clear_of_prime_divisor (a : List Rat) {d p : Nat} (hd : 0 < d)
    (hp : 1 < p) (pd : p ∣ d) (v : Nat → Int)
    (hv : ∀ i, (d : Rat)*coeff a i = (v i : Rat)) (hall : ∀ i, (p : Int) ∣ v i) :
    ∃ k < d, 0 < k ∧ Clears a k := by
  obtain ⟨k,eqn⟩ := pd
  have hk : 0 < k := by
    cases k with
    | zero => simp_all
    | succ k => omega
  have lt : k < d := by
    rw [eqn]
    simpa using Nat.mul_lt_mul_of_pos_right hp hk
  refine ⟨k,lt,hk,?_⟩
  intro i
  obtain ⟨z,hz⟩ := hall i
  refine ⟨z,cancel_rational_natural (by omega : 0 < p) ?_⟩
  have eqi := hv i
  rwa [eqn,Rat.natCast_mul,Rat.mul_assoc,hz,Rat.intCast_mul,Rat.intCast_natCast] at eqi

theorem primitive_minimal_lift (a : List Rat) (ha : (1 : Rat) ∈ a)
    {d : Nat} (hd : 0 < d) (minimal : ∀ k < d, ¬ (0 < k ∧ Clears a k))
    (v : Nat → Int) (hv : ∀ i, (d : Rat)*coeff a i = (v i : Rat)) :
    ∀ p, PrimeDivisor p → ∃ i, ¬ (p : Int) ∣ v i := by
  classical
  obtain ⟨i,hi⟩ := coeff_of_mem ha
  have leading : (d : Int) = v i := Rat.intCast_inj.mp (by simpa only [hi,Rat.mul_one,Rat.intCast_natCast] using hv i)
  intro p hp
  apply Classical.byContradiction
  intro no
  have hall : ∀ j, (p : Int) ∣ v j := fun j => Classical.byContradiction (fun nd => no ⟨j,nd⟩)
  have pd : p ∣ d := Int.ofNat_dvd.mp (leading ▸ hall i)
  obtain ⟨k,lt,clear⟩ := smaller_clear_of_prime_divisor a hd hp.1 pd v hv hall
  exact minimal k lt clear

theorem exists_primitive_lift (a : List Rat) (ha : (1 : Rat) ∈ a) :
    ∃ (d : Nat) (v : Nat → Int), 0 < d ∧
      (∀ i, (d : Rat)*coeff a i = (v i : Rat)) ∧
      ∀ p, PrimeDivisor p → ∃ i, ¬ (p : Int) ∣ v i := by
  classical
  obtain ⟨d,⟨hd,hclear⟩,hmin⟩ := minimal_denominator a
  let v := fun i => Classical.choose (hclear i)
  have hv : ∀ i, (d : Rat)*coeff a i = (v i : Rat) := fun i => Classical.choose_spec (hclear i)
  exact ⟨d,v,hd,hv,primitive_minimal_lift a ha hd hmin v hv⟩

theorem scaled_sum (c : Rat) (z : Nat → Int) (q : Nat → Rat)
    (h : ∀ i, c*q i = (z i : Rat)) (n : Nat) :
    c * sumBelow q n = ((sumBelow z n : Int) : Rat) := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => simp only [sumBelow,Rat.mul_add,Rat.intCast_add,ih,h]

theorem scaled_convolution {a b : Nat → Rat} {u v : Nat → Int} {d e : Nat}
    (ha : ∀ i, (d : Rat)*a i = (u i : Rat))
    (hb : ∀ j, (e : Rat)*b j = (v j : Rat)) (n : Nat) :
    ((d*e : Nat) : Rat)*convolution a b n = ((convolution u v n : Int) : Rat) := by
  apply scaled_sum
  intro i
  rw [Rat.natCast_mul,Rat.intCast_mul,← ha,← hb]
  grind

theorem cleared_product_multiple {a b : Nat → Rat} {u v : Nat → Int} {d e : Nat}
    (ha : ∀ i, (d : Rat)*a i = (u i : Rat))
    (hb : ∀ j, (e : Rat)*b j = (v j : Rat))
    (integral : ∀ n, ∃ z : Int, convolution a b n = (z : Rat)) (n : Nat) :
    ((d*e : Nat) : Int) ∣ convolution u v n := by
  obtain ⟨z,hz⟩ := integral n
  refine ⟨z,Rat.intCast_inj.mp ?_⟩
  rw [Rat.intCast_mul,Rat.intCast_natCast,← hz,scaled_convolution ha hb]

theorem denominator_product_one {a b : Nat → Rat} {u v : Nat → Int} {d e : Nat}
    (hd : 0 < d) (he : 0 < e) (ha : ∀ i, (d : Rat)*a i = (u i : Rat))
    (hb : ∀ j, (e : Rat)*b j = (v j : Rat))
    (pu : ∀ p, PrimeDivisor p → ∃ i, ¬ (p : Int) ∣ u i)
    (pv : ∀ p, PrimeDivisor p → ∃ i, ¬ (p : Int) ∣ v i)
    (integral : ∀ n, ∃ z : Int, convolution a b n = (z : Rat)) : d*e = 1 := by
  have positive := Nat.mul_pos hd he
  by_cases one : d*e = 1
  · exact one
  · obtain ⟨p,hp,pde⟩ := prime_divisor_exists (d*e) (by omega)
    obtain ⟨n,miss⟩ := convolution_survives_prime hp u v (pu p hp) (pv p hp)
    exact False.elim (miss (Int.dvd_trans (Int.ofNat_dvd.mpr pde) (cleared_product_multiple ha hb integral n)))

theorem list_integral_of_denominator_one {a : List Rat} {u : Nat → Int} {d : Nat}
    (hd : d = 1) (hu : ∀ i, (d : Rat)*coeff a i = (u i : Rat)) :
    ∀ c ∈ a, ∃ z : Int, c = (z : Rat) := by
  intro c hc
  obtain ⟨i,hi⟩ := coeff_of_mem hc
  exact ⟨u i,by simpa [hd,hi] using hu i⟩

theorem monic_factors_integral (a b : List Rat) (ha : (1 : Rat) ∈ a) (hb : (1 : Rat) ∈ b)
    (h : ∀ n, ∃ z : Int, convolution (coeff a) (coeff b) n = (z : Rat)) :
    (∀ c ∈ a, ∃ z : Int, c = (z : Rat)) ∧ (∀ c ∈ b, ∃ z : Int, c = (z : Rat)) := by
  obtain ⟨d,u,hd,hu,pu⟩ := exists_primitive_lift a ha
  obtain ⟨e,v,he,hv,pv⟩ := exists_primitive_lift b hb
  have eqn := denominator_product_one hd he hu hv pu pv h
  exact ⟨list_integral_of_denominator_one (Nat.eq_one_of_mul_eq_one_right eqn) hu,
    list_integral_of_denominator_one (Nat.eq_one_of_mul_eq_one_left eqn) hv⟩

theorem integral_list_cast (a : List Rat) (h : ∀ c ∈ a, ∃ z : Int, c = (z : Rat)) :
    ∃ u : List Int, u.map (fun z : Int => (z : Rat)) = a := by
  induction a with
  | nil => exact ⟨[],rfl⟩
  | cons c a ih =>
    obtain ⟨z,hz⟩ := h c (by simp)
    obtain ⟨u,hu⟩ := ih (fun t ht => h t (List.mem_cons_of_mem c ht))
    exact ⟨z :: u,by simp [hu,hz]⟩

theorem coeff_cast (a : List Int) (n : Nat) :
    coeff (a.map (fun z : Int => (z : Rat))) n = ((coeff a n : Int) : Rat) := by
  cases e : a[n]? <;> simp [coeff,List.getElem?_map,e]

theorem convolution_cast (a b : List Int) (n : Nat) :
    convolution (coeff (a.map (fun z : Int => (z : Rat)))) (coeff (b.map (fun z : Int => (z : Rat)))) n =
    ((convolution (coeff a) (coeff b) n : Int) : Rat) := by
  have h := scaled_convolution (d := 1) (e := 1) (u := coeff a) (v := coeff b)
    (a := coeff (a.map (fun z : Int => (z : Rat)))) (b := coeff (b.map (fun z : Int => (z : Rat))))
    (fun i => by simp [coeff_cast]) (fun j => by simp [coeff_cast]) n
  simpa using h

theorem monic_factorization_descends (f : List Int) (a b : List Rat) (ha : (1 : Rat) ∈ a)
    (hb : (1 : Rat) ∈ b) (h : ∀ n, convolution (coeff a) (coeff b) n = ((coeff f n : Int) : Rat)) :
    ∃ A B : List Int, A.map (fun z : Int => (z : Rat)) = a ∧ B.map (fun z : Int => (z : Rat)) = b ∧
      ∀ n, convolution (coeff A) (coeff B) n = coeff f n := by
  obtain ⟨ia,ib⟩ := monic_factors_integral a b ha hb (fun n => ⟨coeff f n,h n⟩)
  obtain ⟨A,rfl⟩ := integral_list_cast a ia
  obtain ⟨B,rfl⟩ := integral_list_cast b ib
  exact ⟨A,B,rfl,rfl,fun n => Rat.intCast_inj.mp (by simpa only [convolution_cast] using h n)⟩

end Reimann.CircularGauss69
