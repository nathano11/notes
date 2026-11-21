import Init

/-!
# Images of dyadic differences of commuting operators

Write `G_a = G^(2^a)` and `S_a = S^(2^a)`, where powers denote composition.
The main theorem proves that the image of `G_a - S_a` is the image of
`a + 1` doublings for `a ≥ 1`. It assumes that the layer-one difference
is four times a surjective map and that each later sum `G_a + S_a` is twice
a surjective map. In the arithmetic application these maps are automorphisms
of a lattice over the 2-adic integers.

Addition and subtraction are supplied as operations. The two elementary
identities used of them are explicit so the file can be checked with Lean
core alone. No topology, computation of a determinant, or assertion about
Galois cohomology is required by this operator theorem.
-/

namespace DyadicLayerGrowth

universe u

variable {X : Type u}

/-- Applying an operator twice moves up one dyadic layer. -/
def squareIterate (f : X → X) : Nat → X → X
  | 0 => f
  | n + 1 => fun x => squareIterate f n (squareIterate f n x)

/-- The ordinary composition power, starting with the identity. -/
def iterate (f : X → X) : Nat → X → X
  | 0 => fun x => x
  | n + 1 => fun x => f (iterate f n x)

def Surj (f : X → X) : Prop := ∀ y, ∃ x, f x = y

def Preserves (add : X → X → X) (f : X → X) : Prop :=
  ∀ x y, f (add x y) = add (f x) (f y)

def difference (sub : X → X → X) (g s : X → X) (a : Nat) (x : X) : X :=
  sub (squareIterate g a x) (squareIterate s a x)

def companion (add : X → X → X) (g s : X → X) (a : Nat) (x : X) : X :=
  add (squareIterate g a x) (squareIterate s a x)

theorem squareIterate_preserves (add : X → X → X) (f : X → X)
    (hf : Preserves add f) (a : Nat) : Preserves add (squareIterate f a) := by
  induction a with
  | zero => exact hf
  | succ a ih =>
    intro x y
    change squareIterate f a (squareIterate f a (add x y)) = _
    rw [ih x y, ih (squareIterate f a x) (squareIterate f a y)] <;> rfl
-- breakpoint squareIterate_preserves

theorem squareIterate_commutes (g s : X → X)
    (h : ∀ x, g (s x) = s (g x)) (a : Nat) :
    ∀ x, squareIterate g a (squareIterate s a x) =
      squareIterate s a (squareIterate g a x) := by
  induction a with
  | zero => exact h
  | succ a ih =>
    intro x
    let f := squareIterate g a
    let t := squareIterate s a
    have comm (y : X) : f (t y) = t (f y) := ih y
    change f (f (t (t x))) = t (t (f (f x)))
    rw [comm (t x), comm x, comm (t (f x)), comm (f x)]
-- breakpoint squareIterate_commutes

/-- Factor the actual dyadic difference at every layer. -/
theorem difference_succ (add sub : X → X → X) (g s : X → X)
    (hg : Preserves add g) (hs : Preserves add s)
    (hcomm : ∀ x, g (s x) = s (g x))
    (hcancel : ∀ x y z, sub (add x y) (add y z) = sub x z)
    (a : Nat) (x : X) :
    difference sub g s (a + 1) x =
      difference sub g s a (companion add g s a x) := by
  let f := squareIterate g a
  let t := squareIterate s a
  have hf : Preserves add f := squareIterate_preserves add g hg a
  have ht : Preserves add t := squareIterate_preserves add s hs a
  have hc : f (t x) = t (f x) := squareIterate_commutes g s hcomm a x
  change sub (f (f x)) (t (t x)) =
    sub (f (add (f x) (t x))) (t (add (f x) (t x)))
  rw [hf (f x) (t x), ht (f x) (t x), hc, hcancel]
-- breakpoint difference_succ

/-- The operator difference carries a doubled input to a doubled output. -/
theorem difference_double (add sub : X → X → X) (g s : X → X)
    (hg : Preserves add g) (hs : Preserves add s)
    (hdouble : ∀ x y, sub (add x x) (add y y) = add (sub x y) (sub x y))
    (a : Nat) (x : X) :
    difference sub g s a (add x x) =
      add (difference sub g s a x) (difference sub g s a x) := by
  unfold difference
  rw [squareIterate_preserves add g hg a x x,
      squareIterate_preserves add s hs a x x, hdouble]
-- breakpoint difference_double

/-- The initial and complementary factorizations propagate as factorizations
through surjections. This lemma also works for operators given recursively. -/
theorem factors_by_iterated_doubling
    (double : X → X) (d c : Nat → X → X)
    (base : ∃ v : X → X, Surj v ∧ ∀ x, d 1 x = double (double (v x)))
    (factor : ∀ i x, d (i + 2) x = d (i + 1) (c (i + 1) x))
    (linear : ∀ i x, d i (double x) = double (d i x))
    (comp : ∀ i, ∃ v : X → X, Surj v ∧ ∀ x, c (i + 1) x = double (v x))
    (i : Nat) :
    ∃ u : X → X, Surj u ∧ ∀ x, d (i + 1) x = iterate double (i + 2) (u x) := by
  induction i with
  | zero => exact base
  | succ i ih =>
    obtain ⟨u, hu, hd⟩ := ih
    obtain ⟨v, hv, hc⟩ := comp i
    refine ⟨fun x => u (v x), ?_, ?_⟩
    · intro y
      obtain ⟨z, hz⟩ := hu y
      obtain ⟨x, hx⟩ := hv z
      exact ⟨x, (congrArg u hx).trans hz⟩
    · intro x
      calc
        d (i + 2) x = d (i + 1) (c (i + 1) x) := factor i x
        _ = d (i + 1) (double (v x)) := congrArg (d (i + 1)) (hc x)
        _ = double (d (i + 1) (v x)) := linear (i + 1) (v x)
        _ = double (iterate double (i + 2) (u (v x))) := congrArg double (hd (v x))
        _ = iterate double (i + 3) (u (v x)) := rfl
-- breakpoint factors_by_iterated_doubling

/-- Layer `i+1` has image exactly `2^(i+2) X`, expressed by equality of
its membership predicates. The theorem needs no rank or freeness assumption. -/
theorem dyadic_difference_image
    (add sub : X → X → X) (g s : X → X)
    (hg : Preserves add g) (hs : Preserves add s)
    (hcomm : ∀ x, g (s x) = s (g x))
    (hcancel : ∀ x y z, sub (add x y) (add y z) = sub x z)
    (hdouble : ∀ x y, sub (add x x) (add y y) = add (sub x y) (sub x y))
    (base : ∃ v : X → X, Surj v ∧
      ∀ x, difference sub g s 1 x = iterate (fun z => add z z) 2 (v x))
    (comp : ∀ i, ∃ v : X → X, Surj v ∧
      ∀ x, companion add g s (i + 1) x = add (v x) (v x))
    (i : Nat) (y : X) :
    (∃ x, difference sub g s (i + 1) x = y) ↔
      ∃ x, iterate (fun z => add z z) (i + 2) x = y := by
  obtain ⟨u, hu, hd⟩ := factors_by_iterated_doubling (fun z => add z z)
    (difference sub g s) (companion add g s) base
    (fun j x => difference_succ add sub g s hg hs hcomm hcancel (j + 1) x)
    (difference_double add sub g s hg hs hdouble) comp i
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨u x, (hd x).symm.trans hx⟩
  · intro h
    obtain ⟨z, hz⟩ := h
    obtain ⟨x, hx⟩ := hu z
    exact ⟨x, (hd x).trans ((congrArg _ hx).trans hz)⟩
-- breakpoint dyadic_difference_image

end DyadicLayerGrowth
