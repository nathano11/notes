import Reimann.TameRationalField277

namespace Reimann.TameEmbeddings277

open Reimann.TameRationalField277

/-- A specified rational coefficient inclusion in the target ring. -/
structure RatMap (F : Type) [Lean.Grind.CommRing F] where
  app : Rat → F
  zero : app 0 = 0
  one : app 1 = 1
  add : ∀ a b, app (a+b) = app a + app b
  mul : ∀ a b, app (a*b) = app a * app b
  sub : ∀ a b, app (a-b) = app a - app b

variable {F : Type} [Lean.Grind.CommRing F]

theorem map_neg (ι : RatMap F) (a : Rat) : ι.app (-a) = -(ι.app a) := by
  have h := ι.sub 0 a
  have hz : (0:Rat)-a = -a := by grind
  rw [hz,ι.zero] at h
  grind

def evalQuad (ι : RatMap F) (u : F) (x : Quad) : F :=
  ι.app x.1 + ι.app x.2*u

theorem evalQuad_add (ι : RatMap F) (u : F) (x y : Quad) :
    evalQuad ι u (qa x y)=evalQuad ι u x+evalQuad ι u y := by
  simp only [evalQuad,qa,ι.add]
  grind

theorem evalQuad_scale (ι : RatMap F) (u : F) (c : Rat) (x : Quad) :
    evalQuad ι u (qs c x)=ι.app c*evalQuad ι u x := by
  simp only [evalQuad,qs,ι.mul]
  grind

theorem evalQuad_mul (ι : RatMap F) (u : F) (hu : u*u=ι.app (-3)) (x y : Quad) :
    evalQuad ι u (qm x y)=evalQuad ι u x*evalQuad ι u y := by
  rw [map_neg] at hu
  simp only [evalQuad,qm,ι.sub,ι.add,ι.mul]
  grind

def evaluate (ι : RatMap F) (u v : F) (x : Biquad) : F :=
  evalQuad ι u x.1 + evalQuad ι u x.2*v

theorem evaluate_add (ι : RatMap F) (u v : F) (x y : Biquad) :
    evaluate ι u v (ba x y)=evaluate ι u v x+evaluate ι u v y := by
  simp only [evaluate,ba,evalQuad_add]
  grind

theorem evaluate_mul (ι : RatMap F) (u v : F)
    (hu : u*u=ι.app (-3)) (hv : v*v=ι.app (-23)) (x y : Biquad) :
    evaluate ι u v (bm x y)=evaluate ι u v x*evaluate ι u v y := by
  simp only [evaluate,bm,evalQuad_add,evalQuad_scale,evalQuad_mul ι u hu]
  grind

theorem evaluate_scalar (ι : RatMap F) (u v : F) (a : Rat) :
    evaluate ι u v (scalar a)=ι.app a := by
  simp only [evaluate,evalQuad,scalar,ι.zero]
  grind

theorem evaluate_generators (ι : RatMap F) (u v : F) :
    evaluate ι u v gen3=u ∧ evaluate ι u v gen23=v := by
  simp only [evaluate,evalQuad,gen3,gen23,ι.zero,ι.one]
  constructor <;> grind

/-- Unital algebra maps over the specified rational coefficients. -/
structure OverRat (ι : RatMap F) where
  app : Biquad → F
  onScalar : ∀ a, app (scalar a) = ι.app a
  onAdd : ∀ x y, app (ba x y)=app x+app y
  onMul : ∀ x y, app (bm x y)=app x*app y

def ofRoots (ι : RatMap F) (u v : F) (hu : u*u = ι.app (-3)) (hv : v*v = ι.app (-23)) :
    OverRat ι :=
  ⟨evaluate ι u v, evaluate_scalar ι u v, evaluate_add ι u v, evaluate_mul ι u v hu hv⟩

theorem images_are_roots {ι : RatMap F} (h : OverRat ι) :
    h.app gen3*h.app gen3 = ι.app (-3) ∧ h.app gen23*h.app gen23 = ι.app (-23) := by
  constructor
  · rw [← h.onMul, generator_squares.1, h.onScalar]
  · rw [← h.onMul, generator_squares.2, h.onScalar]

theorem determined_by_generators {ι : RatMap F} (h : OverRat ι) (z : Biquad) :
    h.app z = evaluate ι (h.app gen3) (h.app gen23) z := by
  rcases z with ⟨⟨a,b⟩,⟨c,d⟩⟩
  calc
    h.app ((a,b),(c,d)) = _ := congrArg h.app (basis_expansion a b c d).symm
    _ = _ := by simp only [h.onAdd,h.onMul,h.onScalar,evaluate,evalQuad]; grind

theorem algebra_map_ext {ι : RatMap F} (h k : OverRat ι)
    (h3 : h.app gen3=k.app gen3) (h23 : h.app gen23=k.app gen23) : h=k := by
  have eq : h.app=k.app := funext fun z => (determined_by_generators h z).trans
    (by rw [h3,h23,← determined_by_generators k z])
  cases h
  cases k
  cases eq
  rfl

theorem unique_map_of_roots (ι : RatMap F) (u v : F) (hu : u*u = ι.app (-3))
    (hv : v*v = ι.app (-23)) :
    ∃ h : OverRat ι, h.app gen3=u ∧ h.app gen23=v ∧
      ∀ k : OverRat ι, k.app gen3=u → k.app gen23=v → k=h := by
  let h := ofRoots ι u v hu hv
  have he : h.app gen3=u ∧ h.app gen23=v := evaluate_generators ι u v
  exact ⟨h,he.1,he.2,fun k h₃ h₂₃ => algebra_map_ext k h (h₃.trans he.1.symm) (h₂₃.trans he.2.symm)⟩

theorem zero_kernel {ι : RatMap F} (h : OverRat ι) (hnon : (1:F) ≠ 0)
    (x : Biquad) (hx : h.app x = 0) : x = scalar 0 := by
  by_cases he : x=scalar 0
  · exact he
  · have hi := h.onMul x (bi x)
    rw [biquad_mul_inverse x he, hx] at hi
    have h₁ : h.app ((1,0),(0,0)) = 1 := (h.onScalar 1).trans ι.one
    rw [h₁] at hi
    grind

theorem map_negate {ι : RatMap F} (h : OverRat ι) (x : Biquad) :
    h.app (bn x) = -h.app x := by
  have he := h.onAdd x (bn x)
  rw [(add_group_laws x x x).2.2.2] at he
  have h₀ : h.app ((0,0),(0,0))=0 := (h.onScalar 0).trans ι.zero
  rw [h₀] at he
  grind

theorem embedding_injective {ι : RatMap F} (h : OverRat ι) (hnon : (1:F) ≠ 0)
    {x y : Biquad} (he : h.app x=h.app y) : x=y := by
  have hz : h.app (ba x (bn y)) = 0 := by rw [h.onAdd, map_negate, he]; grind
  have hh := zero_kernel h hnon _ hz
  have hxy : ba (ba x (bn y)) y = x := by
    apply Prod.ext <;> apply Prod.ext <;> simp only [ba,bn,qa,qs] <;> grind
  rw [hh,(add_group_laws (scalar 0) y y).2.1] at hxy
  have hy : ba y (scalar 0)=y := (add_group_laws y y y).2.2.1
  rw [hy] at hxy
  exact hxy.symm

def sign (b : Bool) (u : F) : F := if b then u else -u

theorem sign_square (b : Bool) (u : F) : sign b u * sign b u = u*u := by
  cases b <;> simp only [sign] <;> grind

theorem sign_unique (u : F) (hu : u ≠ -u) (a b : Bool)
    (h : sign a u=sign b u) : a=b := by
  cases a <;> cases b <;> simp only [sign] at * <;> grind

def signedMap {ι : RatMap F} {u v : F} (hu : u*u=ι.app (-3)) (hv : v*v=ι.app (-23))
    (b : Bool × Bool) : OverRat ι :=
  ofRoots ι (sign b.1 u) (sign b.2 v) ((sign_square b.1 u).trans hu) ((sign_square b.2 v).trans hv)

theorem signed_images {ι : RatMap F} {u v : F} (hu : u*u=ι.app (-3)) (hv : v*v=ι.app (-23))
    (b : Bool × Bool) :
    (signedMap hu hv b).app gen3=sign b.1 u ∧ (signedMap hu hv b).app gen23=sign b.2 v :=
  evaluate_generators ι _ _

theorem signed_injective {ι : RatMap F} {u v : F} (hu : u*u=ι.app (-3)) (hv : v*v=ι.app (-23))
    (hud : u≠-u) (hvd : v≠-v) {a b : Bool × Bool} (h : signedMap hu hv a=signedMap hu hv b) : a=b := by
  apply Prod.ext
  · apply sign_unique u hud
    rw [← (signed_images hu hv a).1, ← (signed_images hu hv b).1, h]
  · apply sign_unique v hvd
    rw [← (signed_images hu hv a).2, ← (signed_images hu hv b).2, h]

theorem exists_sign_of_square {K : Type} [Lean.Grind.Field K] (x u : K) (h : x*x=u*u) :
    ∃ b : Bool, x=sign b u := by
  have hz : (x-u)*(x+u)=0 := by grind
  rcases Lean.Grind.Field.of_mul_eq_zero hz with he | he
  · exact ⟨true, by simp only [sign]; grind⟩
  · exact ⟨false, by simp only [sign]; grind⟩

theorem signed_surjective {K : Type} [Lean.Grind.Field K] {ι : RatMap K} {u v : K}
    (hu : u*u=ι.app (-3)) (hv : v*v=ι.app (-23)) (h : OverRat ι) :
    ∃ b : Bool × Bool, signedMap hu hv b = h := by
  obtain ⟨r,hr⟩ := exists_sign_of_square (h.app gen3) u ((images_are_roots h).1.trans hu.symm)
  obtain ⟨s,hs⟩ := exists_sign_of_square (h.app gen23) v ((images_are_roots h).2.trans hv.symm)
  exact ⟨(r,s),algebra_map_ext _ h ((signed_images hu hv (r,s)).1.trans hr.symm)
    ((signed_images hu hv (r,s)).2.trans hs.symm)⟩

theorem source_signs_distinct : gen3 ≠ bn gen3 ∧ gen23 ≠ bn gen23 := by
  constructor
  · intro h
    have he := congrArg (fun x : Biquad => x.1.2) h
    change (1:Rat)=(-1)*1 at he
    grind
  · intro h
    have he := congrArg (fun x : Biquad => x.2.1) h
    change (1:Rat)=(-1)*1 at he
    grind

theorem root_signs_distinct {ι : RatMap F} {u v : F} (hu : u*u=ι.app (-3)) (hv : v*v=ι.app (-23))
    (hnon : (1:F) ≠ 0) : u≠-u ∧ v≠-v := by
  let h := ofRoots ι u v hu hv
  have he : h.app gen3=u ∧ h.app gen23=v := evaluate_generators ι u v
  constructor
  · intro e
    exact source_signs_distinct.1 (embedding_injective h hnon
      (show h.app gen3=h.app (bn gen3) by rw [map_negate,he.1]; exact e))
  · intro e
    exact source_signs_distinct.2 (embedding_injective h hnon
      (show h.app gen23=h.app (bn gen23) by rw [map_negate,he.2]; exact e))

/-- Both roots in a target field suffice. The four signed evaluations are
all of its rational algebra maps from the biquadratic field, each injective. -/
theorem four_embeddings {K : Type} [Lean.Grind.Field K] (ι : RatMap K) (u v : K)
    (hu : u*u=ι.app (-3)) (hv : v*v=ι.app (-23)) :
    (∀ a b : Bool × Bool, signedMap hu hv a=signedMap hu hv b ↔ a=b) ∧
    (∀ h : OverRat ι, ∃ b : Bool × Bool, signedMap hu hv b=h) ∧
    (∀ (h : OverRat ι) (x y : Biquad), h.app x=h.app y → x=y) := by
  have hn : (1:K) ≠ 0 := fun e => Lean.Grind.Field.zero_ne_one e.symm
  obtain ⟨hud,hvd⟩ := root_signs_distinct hu hv hn
  exact ⟨fun a b => ⟨signed_injective hu hv hud hvd, fun e => congrArg (signedMap hu hv) e⟩,
    signed_surjective hu hv, fun h _ _ => embedding_injective h hn⟩

end Reimann.TameEmbeddings277
