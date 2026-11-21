import Reimann.TameEmbeddings277
import Reimann.TameLimitRoots277
import Reimann.TameOrderFaithful277

namespace Reimann.TameSignedEmbeddings277

open Reimann.TameRationalField277 Reimann.TameEmbeddings277
open Reimann.TameLimit277 Reimann.TameLimitRoots277 Reimann.TameArithmetic277
open Reimann.TameBiquadratic277 Reimann.TameOrderFaithful277

/-- Exchange the positive-root flag in algebra maps with the negative-root
flag used to label the four prime ideals. -/
def embeddingSigns (branch : Bool × Bool) : Bool × Bool :=
  (!branch.1, !branch.2)

theorem embeddingSigns_twice (s : Bool × Bool) : embeddingSigns (embeddingSigns s) = s := by
  rcases s with ⟨x,y⟩
  cases x <;> cases y <;> rfl

theorem orderImage_add (x y : Bool) (v w : OrderCoordinates) :
    orderImage x y (componentAdd v w) = add (orderImage x y v) (orderImage x y w) := by
  apply equal_of_residues
  intro n
  change branchEval x y n (componentAdd v w) % modulus n =
    (branchEval x y n v % modulus n + branchEval x y n w % modulus n) % modulus n
  rw [TameLocalOrders277.evaluation_sum,Int.add_emod]

theorem orderImage_generators (x y : Bool) :
    orderImage x y ((0,1),(0,0)) = chooseRoot x rootThree ∧
    orderImage x y ((0,0),(1,0)) = chooseRoot y rootTwentyThree := by
  constructor
  · apply equal_of_residues
    intro n
    rw [orderImage_residue,rootThree,signed_lift_residue]
    cases x <;> simp [branchEval,evalAt,rootAt,TameRootExhaustion277.signed]
  · apply equal_of_residues
    intro n
    rw [orderImage_residue,rootTwentyThree,signed_lift_residue]
    cases y <;> simp [branchEval,evalAt,rootAt,TameRootExhaustion277.signed]

def linearOrder (a b : Int) : OrderCoordinates :=
  componentAdd (integerCoordinates a)
    (product (-3) (-23) (integerCoordinates b) ((0,1),(0,0)))

theorem order_expansion (a b c d : Int) :
    ((a,b),(c,d)) = componentAdd (linearOrder a b)
      (product (-3) (-23) (linearOrder c d) ((0,0),(1,0))) := by
  simp [linearOrder, componentAdd, integerCoordinates, product]

theorem orderImage_linear (x y : Bool) (a b : Int) :
    orderImage x y (linearOrder a b) =
      add (ofInt a) (mul (ofInt b) (chooseRoot x rootThree)) := by
  rw [linearOrder, orderImage_add, orderImage_product, orderImage_integer,
    orderImage_integer, (orderImage_generators x y).1]

theorem orderImage_expansion (x y : Bool) (a b c d : Int) :
    orderImage x y ((a,b),(c,d)) =
      add (add (ofInt a) (mul (ofInt b) (chooseRoot x rootThree)))
        (mul (add (ofInt c) (mul (ofInt d) (chooseRoot x rootThree)))
          (chooseRoot y rootTwentyThree)) := by
  rw [order_expansion,orderImage_add,orderImage_product,orderImage_linear,
    orderImage_linear,(orderImage_generators x y).2]

/-- A map out of the completed integral model compatible with the rational
coefficient inclusion. -/
structure IntegralMap {F : Type} [Lean.Grind.CommRing F] (q : RatMap F) where
  app : Integer277 → F
  onInt : ∀ a : Int, app (ofInt a) = q.app (a : Rat)
  onAdd : ∀ x y, app (add x y) = app x + app y
  onMul : ∀ x y, app (mul x y) = app x * app y
  onNeg : ∀ x, app (neg x) = -app x

variable {F : Type} [Lean.Grind.CommRing F] {q : RatMap F}

theorem chooseRoot_image (h : IntegralMap q) (b : Bool) (x : Integer277) :
    h.app (chooseRoot b x) = sign (!b) (h.app x) := by
  cases b with
  | false => rfl
  | true => exact h.onNeg x

theorem root_images_square (h : IntegralMap q) :
    h.app rootThree * h.app rootThree = q.app (-3) ∧
    h.app rootTwentyThree * h.app rootTwentyThree = q.app (-23) := by
  constructor
  · rw [← h.onMul,rootThree_square,h.onInt]
    rfl
  · rw [← h.onMul,rootTwentyThree_square,h.onInt]
    rfl

def branchEmbedding (h : IntegralMap q) (s : Bool × Bool) : OverRat q :=
  signedMap (root_images_square h).1 (root_images_square h).2 (embeddingSigns s)

theorem branch_generators (h : IntegralMap q) (s : Bool × Bool) :
    (branchEmbedding h s).app gen3 = h.app (chooseRoot s.1 rootThree) ∧
    (branchEmbedding h s).app gen23 = h.app (chooseRoot s.2 rootTwentyThree) := by
  rw [chooseRoot_image,chooseRoot_image]
  exact signed_images (root_images_square h).1 (root_images_square h).2 (embeddingSigns s)

theorem embedding_on_order (h : IntegralMap q) (s : Bool × Bool) (v : OrderCoordinates) :
    (branchEmbedding h s).app (rationalize v) = h.app (orderImage s.1 s.2 v) := by
  obtain ⟨⟨a,b⟩,⟨c,d⟩⟩ := v
  rw [orderImage_expansion]
  simp only [h.onAdd,h.onMul,h.onInt,chooseRoot_image]
  rfl

theorem four_labelled_embeddings {K : Type} [Lean.Grind.Field K] {c : RatMap K}
    (h : IntegralMap c) :
    (∀ s t, branchEmbedding h s = branchEmbedding h t ↔ s = t) ∧
    (∀ g : OverRat c, ∃ s, branchEmbedding h s = g) ∧
    (∀ (g : OverRat c) (x y : Biquad), g.app x = g.app y → x = y) := by
  obtain ⟨hinj,hsur,hfaithful⟩ := four_embeddings c (h.app rootThree)
    (h.app rootTwentyThree) (root_images_square h).1 (root_images_square h).2
  refine ⟨fun s t => ⟨fun he => ?_,fun he => congrArg (branchEmbedding h) he⟩,?_,hfaithful⟩
  · have eq := (hinj (embeddingSigns s) (embeddingSigns t)).mp he
    simpa only [embeddingSigns_twice] using congrArg embeddingSigns eq
  · intro g
    obtain ⟨s,hs⟩ := hsur g
    exact ⟨embeddingSigns s,by simpa only [branchEmbedding,embeddingSigns_twice] using hs⟩

/-- A unital coefficient-preserving homomorphism between two target fields. -/
structure ScalarExtension {A B : Type} [Lean.Grind.CommRing A] [Lean.Grind.CommRing B]
    (a : RatMap A) (b : RatMap B) where
  app : A → B
  coefficients : ∀ r : Rat, app (a.app r) = b.app r
  onAdd : ∀ x y, app (x+y) = app x + app y
  onMul : ∀ x y, app (x*y) = app x * app y
  onNeg : ∀ x, app (-x) = -app x

def extendIntegralMap {A B : Type} [Lean.Grind.CommRing A] [Lean.Grind.CommRing B]
    {a : RatMap A} {b : RatMap B} (i : ScalarExtension a b) (h : IntegralMap a) :
    IntegralMap b where
  app x := i.app (h.app x)
  onInt z := (congrArg i.app (h.onInt z)).trans (i.coefficients _)
  onAdd x y := (congrArg i.app (h.onAdd x y)).trans (i.onAdd _ _)
  onMul x y := (congrArg i.app (h.onMul x y)).trans (i.onMul _ _)
  onNeg x := (congrArg i.app (h.onNeg x)).trans (i.onNeg _)

def extendEmbedding {A B : Type} [Lean.Grind.CommRing A] [Lean.Grind.CommRing B]
    {a : RatMap A} {b : RatMap B} (i : ScalarExtension a b) (g : OverRat a) :
    OverRat b where
  app x := i.app (g.app x)
  onScalar r := (congrArg i.app (g.onScalar r)).trans (i.coefficients r)
  onAdd x y := (congrArg i.app (g.onAdd x y)).trans (i.onAdd _ _)
  onMul x y := (congrArg i.app (g.onMul x y)).trans (i.onMul _ _)

theorem extend_branch {A B : Type} [Lean.Grind.CommRing A] [Lean.Grind.CommRing B]
    {a : RatMap A} {b : RatMap B} (i : ScalarExtension a b) (h : IntegralMap a)
    (s : Bool × Bool) :
    extendEmbedding i (branchEmbedding h s) = branchEmbedding (extendIntegralMap i h) s := by
  apply algebra_map_ext
  · exact (congrArg i.app (branch_generators h s).1).trans
      (branch_generators (extendIntegralMap i h) s).1.symm
  · exact (congrArg i.app (branch_generators h s).2).trans
      (branch_generators (extendIntegralMap i h) s).2.symm

/-- If both lifted roots already lie in the smaller field, every embedding in
the larger field factors uniquely through one of its four labelled embeddings. -/
theorem factor_over_subfield {A B : Type} [Lean.Grind.Field A] [Lean.Grind.Field B]
    {a : RatMap A} {b : RatMap B} (i : ScalarExtension a b) (h : IntegralMap a)
    (g : OverRat b) :
    ∃ s : Bool × Bool, extendEmbedding i (branchEmbedding h s) = g ∧
      ∀ t, extendEmbedding i (branchEmbedding h t) = g → t = s := by
  obtain ⟨hinj,hsur,_⟩ := four_labelled_embeddings (extendIntegralMap i h)
  obtain ⟨s,hs⟩ := hsur g
  exact ⟨s,(extend_branch i h s).trans hs,fun t ht =>
    (hinj t s).mp ((extend_branch i h t).symm.trans (ht.trans hs.symm))⟩

end Reimann.TameSignedEmbeddings277
