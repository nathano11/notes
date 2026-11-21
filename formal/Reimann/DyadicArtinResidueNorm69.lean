import Reimann.DyadicArtinFrobenius69

/-! The local residue-degree law for norms in unramified Artin towers. -/
namespace Reimann.DyadicArtinResidueNorm69

open Lean.Grind Reimann.Transfer Reimann.DyadicLift Reimann.DyadicArtinFrobenius69

variable {R Γ : Type} [CommRing R] {G : GroupLaw Γ}

theorem sum_mem {P : R → Prop} (hp : IsPrimeIdeal P) {x y : R} (hx : P x) (hy : P y) : P (x+y) := by
  have h := hp.sub_mem x (0-y) hx (hp.sub_mem _ _ hp.zero_mem hy)
  exact (show x-(0-y)=x+y by grind only) ▸ h

theorem pow_respects_prime {P : R → Prop} (hp : IsPrimeIdeal P) {x y : R} (h : P (x-y)) (n : Nat) :
    P (x^n-y^n) := by
  induction n with
  | zero => simpa only [Semiring.pow_zero,AddCommGroup.sub_self] using hp.zero_mem
  | succ n ih =>
    have a := hp.absorb (x^n-y^n) x ih
    have b := hp.absorb (x-y) (y^n) h
    have eq : x^(n+1)-y^(n+1)=(x^n-y^n)*x+(x-y)*y^n := by
      rw [Semiring.pow_succ,Semiring.pow_succ]; grind only
    rw [eq]
    exact sum_mem hp a b

theorem iterate_power (x : R) (n k : Nat) : (x^n)^k=x^(n*k) := by
  induction k with
  | zero => simp only [Semiring.pow_zero,Nat.mul_zero]
  | succ k ih => rw [Semiring.pow_succ,ih,Nat.mul_succ,Semiring.pow_add]

theorem frobenius_power (A : RingAction G R) {P : R → Prop} (hp : IsPrimeIdeal P) (q f : Nat)
    {s : Γ} (hs : IsFrobenius A P q s) :
    IsFrobenius A P (q^f) (multiple G f s) := by
  induction f with
  | zero =>
    refine ⟨fun x => by change P (A.act G.zero x) ↔ P x; rw [A.identity],fun x => ?_⟩
    change P (A.act G.zero x-x^(q^0))
    rw [A.identity,Nat.pow_zero,Semiring.pow_one]
    simpa only [AddCommGroup.sub_self] using hp.zero_mem
  | succ f ih =>
    refine ⟨stabilizes_product A P _ s ih.1 hs.1,?_⟩
    intro x
    let y := A.act s x
    have a := ih.2 y
    have b := pow_respects_prime hp (hs.2 x) (q^f)
    change P (y^(q^f)-(x^q)^(q^f)) at b
    have sum := sum_mem hp a b
    have e : (A.act (multiple G f s) y-y^(q^f))+(y^(q^f)-(x^q)^(q^f)) =
        A.act (multiple G f s) y-(x^q)^(q^f) := by grind only
    rw [e,iterate_power,Nat.mul_comm q (q^f),← Nat.pow_succ] at sum
    change P (A.act (G.add (multiple G f s) s) x-x^(q^(f+1)))
    rw [A.compose]
    exact sum

theorem restrict_frobenius {S Δ : Type} [CommRing S] {H : GroupLaw Δ}
    (A : RingAction G R) (B : RingAction H S) (res : Hom H G) (j : R → S)
    (sub : ∀ x y, j (x-y)=j x-j y) (pow : ∀ x (k : Nat), j (x^k)=(j x)^k)
    (equivariant : ∀ g x, B.act g (j x)=j (A.act (res.app g) x))
    {P : R → Prop} {Q : S → Prop} (contract : ∀ x, Q (j x) ↔ P x)
    (n : Nat) {g : Δ} (hg : IsFrobenius B Q n g) : IsFrobenius A P n (res.app g) := by
  constructor
  · intro x
    rw [← contract,← equivariant,hg.1,contract]
  · intro x
    apply (contract _).mp
    rw [sub,← equivariant,pow]
    exact hg.2 (j x)

/-- For residue degree f above a base prime of norm q, the restriction of
arithmetic Frobenius is the f-th power of the lower arithmetic Frobenius.
Inertia triviality is imposed only in the lower relative Galois group. -/
theorem frobenius_norm_at_prime {S Δ : Type} [CommRing S] {H : GroupLaw Δ}
    (A : RingAction G R) (B : RingAction H S) (res : Hom H G) (j : R → S)
    (sub : ∀ x y, j (x-y)=j x-j y) (pow : ∀ x (k : Nat), j (x^k)=(j x)^k)
    (equivariant : ∀ g x, B.act g (j x)=j (A.act (res.app g) x))
    {P : R → Prop} {Q : S → Prop} (hp : IsPrimeIdeal P) (contract : ∀ x, Q (j x) ↔ P x)
    (q f : Nat) {s : Γ} {g : Δ} (hs : IsFrobenius A P q s) (hg : IsFrobenius B Q (q^f) g)
    (unramified : ∀ u, InInertia A P u → u=G.zero) :
    res.app g=multiple G f s := by
  let full : Subgroup G := ⟨fun _ => True,trivial,fun _ _ => trivial,fun _ => trivial⟩
  exact frobenius_unique A full P (q^f) hp.sub_mem (fun u hu => unramified u.val hu)
    ⟨res.app g,trivial⟩ ⟨multiple G f s,trivial⟩
    (restrict_frobenius A B res j sub pow equivariant contract _ hg) (frobenius_power A hp q f hs)

end Reimann.DyadicArtinResidueNorm69
