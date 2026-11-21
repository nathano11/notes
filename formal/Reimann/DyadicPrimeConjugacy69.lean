import Reimann.DyadicUnramifiedBase69
import Reimann.Transfer

/-! Finite Galois prime conjugacy from maximal-ideal separation and the
orbit norm at a common lower prime. -/
namespace Reimann.DyadicPrimeConjugacy69

open Lean.Grind
open DyadicUnramifiedBase69 (RingMap)

variable {R : Type} [CommRing R]

/-- The last law is invertibility of every nonzero residue class. -/
structure ResidueMaximal (P : R → Prop) : Prop where
  zero : P 0
  proper : ¬ P 1
  plus : ∀ x y, P x → P y → P (x+y)
  absorb : ∀ x y, P x → P (x*y)
  inverse : ∀ x, ¬ P x → ∃ y, P (1-x*y)

theorem kernel_of_residue_field {k : Type} [Field k] (r : RingMap R k)
    (onto : ∀ y, ∃ x, r.app x = y) : ResidueMaximal (fun x => r.app x=0) := by
  refine ⟨r.zero,?_,?_,?_,?_⟩
  · rw [r.one]
    exact fun h => Field.zero_ne_one h.symm
  · intro x y hx hy
    rw [r.add,hx,hy,Semiring.add_zero]
  · intro x y hx
    rw [r.mul,hx,Semiring.zero_mul]
  · intro x hx
    obtain ⟨y,hy⟩ := onto (r.app x)⁻¹
    refine ⟨y,?_⟩
    rw [AddCommGroup.sub_eq_add_neg,r.add,r.one,r.neg,r.mul,hy,Field.mul_inv_cancel hx]
    grind only

theorem pullback_maximal {P : R → Prop} (p : ResidueMaximal P) (f : RingMap R R)
    (onto : ∀ y, ∃ x, f.app x=y) : ResidueMaximal (fun x => P (f.app x)) := by
  refine ⟨by rw [f.zero]; exact p.zero, by rw [f.one]; exact p.proper, ?_, ?_, ?_⟩
  · intro x y hx hy
    rw [f.add]
    exact p.plus _ _ hx hy
  · intro x y hx
    rw [f.mul]
    exact p.absorb _ _ hx
  · intro x hx
    obtain ⟨v,hv⟩ := p.inverse _ hx
    obtain ⟨y,rfl⟩ := onto v
    refine ⟨y,?_⟩
    rwa [AddCommGroup.sub_eq_add_neg,f.add,f.one,f.neg,f.mul,←AddCommGroup.sub_eq_add_neg]

theorem prime_product {P : R → Prop} (p : ResidueMaximal P) (x y : R) (h : P (x*y)) :
    P x ∨ P y := by
  by_cases hx : P x
  · exact Or.inl hx
  · obtain ⟨u,hu⟩ := p.inverse x hx
    have hh := p.plus _ _ (p.absorb _ y hu) (p.absorb _ u h)
    rw [show (1-x*u)*y+(x*y)*u=y by grind only] at hh
    exact Or.inr hh

theorem inclusion_equal {P Q : R → Prop} (p : ResidueMaximal P) (q : ResidueMaximal Q)
    (inc : ∀ x, Q x → P x) (x : R) : Q x ↔ P x := by
  refine ⟨inc x,?_⟩
  intro hx
  by_cases hq : Q x
  · exact hq
  · obtain ⟨y,hy⟩ := q.inverse x hq
    have he := p.plus _ _ (inc _ hy) (p.absorb _ y hx)
    rw [show 1-x*y+x*y=1 by grind only] at he
    exact False.elim (p.proper he)

theorem separating_element {P Q : R → Prop} (p : ResidueMaximal P) (q : ResidueMaximal Q)
    (unequal : ¬ ∀ x, Q x ↔ P x) : ∃ a, Q a ∧ P (1-a) := by
  classical
  have exists_out : ∃ a, Q a ∧ ¬ P a := by
    apply Classical.byContradiction
    intro h
    apply unequal
    apply inclusion_equal p q
    intro x hx
    exact Classical.byContradiction (fun he => h ⟨x,hx,he⟩)
  obtain ⟨x,hx,hout⟩ := exists_out
  obtain ⟨y,hy⟩ := p.inverse x hout
  exact ⟨x*y,q.absorb x y hx,hy⟩

/-- Finite prime avoidance with a stronger conclusion: the chosen element
is one modulo each of the listed ideals. Duplicate ideals are allowed. -/
theorem simultaneous_separation {H : Type} {Q : R → Prop} (q : ResidueMaximal Q)
    (P : H → R → Prop) (family : ∀ g, ResidueMaximal (P g)) (gs : List H)
    (distinct : ∀ g ∈ gs, ¬ ∀ x, Q x ↔ P g x) :
    ∃ a, Q a ∧ ∀ g ∈ gs, P g (1-a) := by
  induction gs with
  | nil => exact ⟨0,q.zero,by simp⟩
  | cons g gs ih =>
    obtain ⟨x,hx,he⟩ := separating_element (family g) q (distinct g (by simp))
    obtain ⟨y,hy,hf⟩ := ih (fun t ht => distinct t (List.mem_cons_of_mem _ ht))
    refine ⟨x + y*(1-x), q.plus _ _ hx (q.absorb _ _ hy), ?_⟩
    intro t ht
    rw [show 1-(x+y*(1-x))=(1-x)*(1-y) by grind only]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (family _).absorb _ _ he
    · rw [CommSemiring.mul_comm]
      exact (family _).absorb _ _ (hf _ ht)

theorem avoids_orbit {H : Type} {Q : R → Prop} (q : ResidueMaximal Q)
    (P : H → R → Prop) (family : ∀ g, ResidueMaximal (P g)) (gs : List H)
    (distinct : ∀ g ∈ gs, ¬ ∀ x, Q x ↔ P g x) :
    ∃ a, Q a ∧ ∀ g ∈ gs, ¬ P g a := by
  obtain ⟨a,ha,h⟩ := simultaneous_separation q P family gs distinct
  refine ⟨a,ha,?_⟩
  intro g hg hga
  have z := (family g).plus _ _ hga (h g hg)
  rw [show a+(1-a) = 1 by grind only] at z
  exact (family g).proper z

def orbitNorm {H : Type} (act : H → RingMap R R) (gs : List H) (x : R) :=
  (gs.map (fun g => (act g).app x)).prod

theorem norm_mem_iff {H : Type} {P : R → Prop} (p : ResidueMaximal P)
    (act : H → RingMap R R) (gs : List H) (x : R) :
    P (orbitNorm act gs x) ↔ ∃ g ∈ gs, P ((act g).app x) := by
  induction gs with
  | nil =>
    change P 1 ↔ _
    simp [p.proper]
  | cons g gs ih =>
    change P ((act g).app x * orbitNorm act gs x) ↔ _
    constructor
    · intro h
      rcases prime_product p _ _ h with h | h
      · exact ⟨g,by simp,h⟩
      · obtain ⟨t,ht,hm⟩ := ih.mp h
        exact ⟨t,List.mem_cons_of_mem g ht,hm⟩
    · rintro ⟨t,ht,hm⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact p.absorb _ _ hm
      · rw [CommSemiring.mul_comm]
        exact p.absorb _ _ (ih.mpr ⟨t,ht,hm⟩)

/-- Orbit-norm conjugacy of any two primes over the same lower prime.
Only the listed automorphisms and norm values are used. -/
theorem finite_prime_conjugacy {A H : Type} (includeBase : A → R)
    {P Q : R → Prop} (p : ResidueMaximal P) (q : ResidueMaximal Q)
    (act : H → RingMap R R) (onto : ∀ g y, ∃ x, (act g).app x=y)
    (gs : List H) (one : H) (hone : one ∈ gs) (identity : ∀ x, (act one).app x=x)
    (normInBase : ∀ x, ∃ a, includeBase a = orbitNorm act gs x)
    (sameBelow : ∀ a, P (includeBase a) ↔ Q (includeBase a)) :
    ∃ g ∈ gs, ∀ x, Q x ↔ P ((act g).app x) := by
  classical
  apply Classical.byContradiction
  intro no
  have distinct (g : H) (hg : g ∈ gs) : ¬ ∀ x, Q x ↔ P ((act g).app x) :=
    fun h => no ⟨g,hg,h⟩
  obtain ⟨x,hx,hout⟩ := avoids_orbit q (fun g y => P ((act g).app y))
    (fun g => pullback_maximal p (act g) (onto g)) gs distinct
  have hq := (norm_mem_iff q act gs x).mpr ⟨one,hone,by rwa [identity]⟩
  obtain ⟨a,ha⟩ := normInBase x
  have hb := sameBelow a
  rw [ha] at hb
  obtain ⟨g,hg,hp⟩ := (norm_mem_iff p act gs x).mp (hb.mpr hq)
  exact hout g hg hp

theorem translate_enumeration {H : Type} (G : Transfer.GroupLaw H) (gs : List H)
    (nodup : gs.Nodup) (covers : ∀ g, g ∈ gs) (k : H) : (gs.map (G.add k)).Perm gs := by
  classical
  have inj (a b : H) (h : G.add k a = G.add k b) : a=b := by
    have e := congrArg (G.add (G.neg k)) h
    simpa only [←G.assoc,G.neg_add,G.zero_add] using e
  have nodup' : (gs.map (G.add k)).Nodup :=
    List.Pairwise.map _ (fun a b h e => h (inj a b e)) nodup
  apply (List.perm_ext_iff_of_nodup nodup' nodup).mpr
  intro a
  refine ⟨fun _ => covers a,fun _ => List.mem_map.mpr ⟨G.add (G.neg k) a,covers _,?_⟩⟩
  rw [←G.assoc,G.add_neg,G.zero_add]

theorem map_product (f : RingMap R R) (xs : List R) : f.app xs.prod = (xs.map f.app).prod := by
  induction xs with
  | nil => exact f.one
  | cons a xs ih => rw [List.prod_cons,f.mul,ih,List.map_cons,List.prod_cons]

theorem permuted_product {xs ys : List R} (h : xs.Perm ys) : xs.prod=ys.prod := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [List.prod_cons,ih]
  | swap a b xs => simp only [List.prod_cons]; grind only
  | trans _ _ ha hb => exact ha.trans hb

theorem norm_fixed {H : Type} (G : Transfer.GroupLaw H) (gs : List H)
    (nodup : gs.Nodup) (covers : ∀ g, g ∈ gs) (act : H → RingMap R R)
    (compose : ∀ g h x, (act (G.add g h)).app x = (act g).app ((act h).app x))
    (k : H) (x : R) : (act k).app (orbitNorm act gs x) = orbitNorm act gs x := by
  have h := permuted_product ((translate_enumeration G gs nodup covers k).map (fun g => (act g).app x))
  unfold orbitNorm
  rw [map_product,List.map_map]
  simpa only [List.map_map,Function.comp_apply,compose,Function.comp_def] using h

/-- For a finite group action, the group laws supply inverses and the norm
is fixed by permutation of its factors. Fixed integral elements descending
to the base therefore suffices. -/
theorem finite_galois_prime_conjugacy {A H : Type} (includeBase : A → R)
    (G : Transfer.GroupLaw H) (gs : List H) (nodup : gs.Nodup) (covers : ∀ g, g ∈ gs)
    (act : H → RingMap R R) (identity : ∀ x, (act G.zero).app x=x)
    (compose : ∀ g h x, (act (G.add g h)).app x = (act g).app ((act h).app x))
    (fixedBase : ∀ t, (∀ g, (act g).app t=t) → ∃ a, includeBase a=t)
    {P Q : R → Prop} (p : ResidueMaximal P) (q : ResidueMaximal Q)
    (sameBelow : ∀ a, P (includeBase a) ↔ Q (includeBase a)) :
    ∃ g ∈ gs, ∀ x, Q x ↔ P ((act g).app x) := by
  apply finite_prime_conjugacy includeBase p q act _ gs G.zero (covers _) identity _ sameBelow
  · intro g y
    exact ⟨(act (G.neg g)).app y,by rw [←compose,G.add_neg,identity]⟩
  · intro x
    exact fixedBase _ (fun g => norm_fixed G gs nodup covers act compose g x)

end Reimann.DyadicPrimeConjugacy69
