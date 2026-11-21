import Reimann.CircularCosetData69

/-! Products over cosets of an arbitrary subgroup of the positive exponents modulo 69. -/
namespace Reimann.CircularCosets69

open Lean.Grind CircularPolynomial69
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def labels (S : Fin 69 → Prop) [DecidablePred S] : List (Fin 69) :=
  (List.finRange 69).filter (fun s => decide (S s))

theorem labels_mem (S : Fin 69 → Prop) [DecidablePred S] (a : Fin 69) :
    a ∈ labels S ↔ S a := by simp [labels]

theorem labels_ext (S T : Fin 69 → Prop) [DecidablePred S] [DecidablePred T]
    (h : ∀ a, S a ↔ T a) : labels S = labels T := by
  unfold labels
  apply List.filter_congr
  intro a _
  simp only [h a]

def cosetLabels (ss : List (Fin 69)) (a : Fin 69) : List Nat :=
  ss.map (fun s => (s.val*a.val)%69)

def representatives (u v : Bool) : List (Fin 69) :=
  if u then
    if v then [1] else (List.range 11).map (fun j => (25 : Fin 69)^j)
  else
    if v then [1,68] else labels (fun a => eta a.val = 1)

theorem five_order : (5 : Fin 69)^22 = 1 ∧
    ∀ j : Fin 22, (5 : Fin 69)^j.val = 1 → j.val = 0 := by decide +kernel

theorem five_generates_positive :
    ((List.range 22).map (fun j => ((5 : Fin 69)^j).val)).Perm (exponents 1) := by decide +kernel

theorem representatives_positive : ∀ u v : Bool, ∀ a : Fin 69,
    a ∈ representatives u v → eta a.val = 1 := by decide +kernel

def factorProduct {R : Type} [CommRing R] (x : R) (as : List Nat) : R :=
  as.foldr (fun a z => (1-x^a)*z) 1

def orbitProduct {R : Type} [CommRing R] (x : R) (S : Fin 69 → Prop) [DecidablePred S]
    (a : Fin 69) : R := factorProduct x (cosetLabels (labels S) a)

theorem factorProduct_append {R : Type} [CommRing R] (x : R) (as bs : List Nat) :
    factorProduct x (as++bs) = factorProduct x as * factorProduct x bs := by
  induction as with
  | nil => simp [factorProduct, Semiring.one_mul]
  | cons a as ih =>
    change (1-x^a)*factorProduct x (as++bs) = ((1-x^a)*factorProduct x as)*factorProduct x bs
    rw [ih, Semiring.mul_assoc]

theorem factorProduct_perm {R : Type} [CommRing R] (x : R) {as bs : List Nat} (p : as.Perm bs) :
    factorProduct x as = factorProduct x bs := by
  have h := CircularKernel69.product_permutation x p
  simpa only [factorProduct, eval_factors] using h

theorem factorProduct_flatMap {R : Type} [CommRing R] (x : R) (S : Fin 69 → Prop)
    [DecidablePred S] (reps : List (Fin 69)) :
    factorProduct x (reps.flatMap (cosetLabels (labels S))) =
      reps.foldr (fun a z => orbitProduct x S a * z) 1 := by
  induction reps with
  | nil => rfl
  | cons a reps ih =>
    rw [List.flatMap_cons, factorProduct_append, ih]
    rfl

theorem orbit_products_mem {R : Type} [CommRing R] (x : R) (S : Fin 69 → Prop)
    [DecidablePred S] (P : R → Prop) (one : P 1) (mul : ∀ u v, P u → P v → P (u*v))
    (orbits : ∀ a : Fin 69, eta a.val = 1 → P (orbitProduct x S a))
    (reps : List (Fin 69)) (pos : ∀ a ∈ reps, eta a.val = 1) :
    P (reps.foldr (fun a z => orbitProduct x S a * z) 1) := by
  induction reps with
  | nil => exact one
  | cons a reps ih =>
    exact mul _ _ (orbits a (pos a List.mem_cons_self))
      (ih (fun b hb => pos b (List.mem_cons_of_mem _ hb)))

theorem orbit_as_power_product {R : Type} [CommRing R] (x : R) (h69 : x^69=1)
    (S : Fin 69 → Prop) [DecidablePred S] (a : Fin 69) :
    orbitProduct x S a = (labels S).foldr (fun s z => (1-(x^a.val)^s.val)*z) 1 := by
  unfold orbitProduct cosetLabels factorProduct
  generalize labels S = ss
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.foldr_cons, ih,
      CircularKernel69.translated_factor x h69 a.val s.val, Nat.mul_comm a.val s.val]

theorem model_partition : ∀ u v : Bool,
    ((representatives u v).flatMap
      (cosetLabels (labels (fun a => a ∈ CircularCosetData69.members u v)))).Perm (exponents 1) := by
  decide +kernel

theorem positive_labels_nodup : (exponents 1).Nodup := by decide +kernel

theorem subgroup_partition (S : Fin 69 → Prop) [DecidablePred S] (h1 : S 1)
    (hm : ∀ a b, S a → S b → S (a*b)) (hp : ∀ a, S a → eta a.val = 1) :
    ∃ reps : List (Fin 69), (∀ a ∈ reps, eta a.val = 1) ∧
      (reps.flatMap (cosetLabels (labels S))).Perm (exponents 1) := by
  obtain ⟨u,v,h⟩ := CircularCosetData69.subgroup_model S h1 hm hp
  refine ⟨representatives u v, representatives_positive u v, ?_⟩
  rw [labels_ext S _ h]
  exact model_partition u v

/-- Every positive exponent occurs in exactly one of the listed cosets. -/
theorem partition_has_no_repetitions (S : Fin 69 → Prop) [DecidablePred S]
    (reps : List (Fin 69)) (h : (reps.flatMap (cosetLabels (labels S))).Perm (exponents 1)) :
    (reps.flatMap (cosetLabels (labels S))).Nodup := by
  exact h.nodup_iff.mpr positive_labels_nodup

theorem signed_product_over_cosets {R : Type} [CommRing R] (x : R)
    (S : Fin 69 → Prop) [DecidablePred S] (h1 : S 1)
    (hm : ∀ a b, S a → S b → S (a*b)) (hp : ∀ a, S a → eta a.val = 1) :
    ∃ reps : List (Fin 69), (∀ a ∈ reps, eta a.val = 1) ∧
      (reps.flatMap (cosetLabels (labels S))).Perm (exponents 1) ∧
      signedProduct x 1 = reps.foldr (fun a z => orbitProduct x S a * z) 1 := by
  obtain ⟨reps,pos,h⟩ := subgroup_partition S h1 hm hp
  refine ⟨reps,pos,h,?_⟩
  exact (factorProduct_perm x h).symm.trans (factorProduct_flatMap x S reps)

theorem signed_product_mem {R : Type} [CommRing R] (x : R)
    (S : Fin 69 → Prop) [DecidablePred S] (h1 : S 1)
    (hm : ∀ a b, S a → S b → S (a*b)) (hp : ∀ a, S a → eta a.val = 1)
    (P : R → Prop) (one : P 1) (mul : ∀ u v, P u → P v → P (u*v))
    (orbits : ∀ a : Fin 69, eta a.val = 1 → P (orbitProduct x S a)) :
    P (signedProduct x 1) := by
  obtain ⟨reps,pos,_,h⟩ := signed_product_over_cosets x S h1 hm hp
  rw [h]
  exact orbit_products_mem x S P one mul orbits reps pos

#print axioms signed_product_mem

end Reimann.CircularCosets69
