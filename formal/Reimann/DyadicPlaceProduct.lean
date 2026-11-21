import Reimann.DyadicLift

/-! Construct the first dyadic product decomposition from a quotient homomorphism.
A homomorphism on the global group may be induced by conjugation in a larger
ambient group. Its image of the first subgroup describes the second place. -/

namespace Reimann.DyadicPlaceProduct

open Lean.Grind Reimann.Transfer Reimann.TameRestriction Reimann.TameCoefficients Reimann.DyadicLift

variable {G Q M : Type} {P : GroupLaw G} {H : GroupLaw Q}

def kernel (π : Hom P H) : Subgroup P where
  mem x := π.app x = H.zero
  identity := π.preserves_zero
  product := by
    intro g h hg hh
    rw [π.preserves_add, hg, hh, H.zero_add]
  inverse := by
    intro g hg
    have h := H.neg_add H.zero
    rw [H.add_zero] at h
    rw [π.preserves_neg, hg, h]

theorem kernel_normal (π : Hom P H) (g k : G) (hk : (kernel π).mem k) :
    (kernel π).mem (conjugate P g k) := by
  change π.app k = H.zero at hk
  change π.app (P.add (P.add g k) (P.neg g)) = H.zero
  rw [π.preserves_add, π.preserves_add, π.preserves_neg, hk, H.add_zero, H.add_neg]

/-- Only equality of the local and global images is required; the quotient
target may contain more than the image of the global group. -/
def CoversImage (π : Hom P H) (D : Subgroup P) : Prop :=
  ∀ g, ∃ d : Subtype D.mem, π.app d.val = π.app g

theorem same_image_difference (π : Hom P H) (g d : G) (h : π.app d = π.app g) :
    (kernel π).mem (P.add g (P.neg d)) := by
  change π.app (P.add g (P.neg d)) = H.zero
  rw [π.preserves_add, π.preserves_neg, h, H.add_neg]

theorem difference_times (g d : G) : P.add (P.add g (P.neg d)) d = g := by
  rw [P.assoc, P.neg_add, P.add_zero]

theorem factor_iff_covers_image (π : Hom P H) (D : Subgroup P) :
    (∀ g, ∃ (k : Subtype (kernel π).mem) (d : Subtype D.mem), P.add k.val d.val = g) ↔
      CoversImage π D := by
  constructor
  · intro hf g
    obtain ⟨k,d,hkd⟩ := hf g
    refine ⟨d, ?_⟩
    have hk : π.app k.val = H.zero := k.property
    rw [← hkd, π.preserves_add, hk, H.zero_add]
  · intro h g
    obtain ⟨d,hd⟩ := h g
    exact ⟨⟨P.add g (P.neg d.val), same_image_difference π g d.val hd⟩, d, difference_times g d.val⟩

def localProduct (π : Hom P H) (D : Subgroup P) (hD : CoversImage π D) : LocalProduct P where
  kernel := kernel π
  first := D
  normal := fun g {k} h => kernel_normal π g k h
  factor := (factor_iff_covers_image π D).mpr hD

def mapSubgroup (j : Hom P P) (D : Subgroup P) : Subgroup P where
  mem x := ∃ d : Subtype D.mem, j.app d.val = x
  identity := ⟨⟨P.zero,D.identity⟩, j.preserves_zero⟩
  product := by
    rintro x y ⟨d,rfl⟩ ⟨e,rfl⟩
    exact ⟨⟨P.add d.val e.val,D.product d.property e.property⟩, j.preserves_add _ _⟩
  inverse := by
    rintro x ⟨d,rfl⟩
    exact ⟨⟨P.neg d.val,D.inverse d.property⟩, j.preserves_neg _⟩

/-- If j is conjugation by B in an overgroup, this is [B,d] in P. -/
def discrepancy (j : Hom P P) (d : G) : G := P.add (j.app d) (P.neg d)

theorem discrepancy_in_kernel (π : Hom P H) (j : Hom P P) (d : G)
    (h : π.app (j.app d) = π.app d) : (kernel π).mem (discrepancy j d) :=
  same_image_difference π _ _ h.symm

theorem discrepancy_factor (j : Hom P P) (d : G) :
    P.add (discrepancy j d) d = j.app d := difference_times _ _

variable [IntModule M] {A : Action G M P.add} {π : Hom P H} {D : Subgroup P}
variable {hD : CoversImage π D}

theorem extend_on_conjugate (f : Character (localProduct π D hD) A) (hf : KillsIntersection f)
    (j : Hom P P) (d : Subtype D.mem) (h : π.app (j.app d.val) = π.app d.val) :
    extend f (j.app d.val) = f.value ⟨discrepancy j d.val, discrepancy_in_kernel π j d.val h⟩ := by
  rw [← discrepancy_factor j d.val]
  exact extend_product f hf ⟨_,discrepancy_in_kernel π j d.val h⟩ d

theorem discrepancy_action (j : Hom P P) (d : Subtype D.mem)
    (h : π.app (j.app d.val) = π.app d.val)
    (hact : ∀ k : Subtype (kernel π).mem, ∀ x, A.act k.val x = x) (x : M) :
    A.act (j.app d.val) x = A.act d.val x := by
  rw [← discrepancy_factor j d.val, A.act_mul]
  exact hact ⟨_,discrepancy_in_kernel π j d.val h⟩ _

/-- The second place's local principal condition is pulled back to D.
It uses the explicit difference j(d)d⁻¹, independently of any quotient section. -/
theorem principal_conjugate_iff (f : Character (localProduct π D hD) A) (hf : KillsIntersection f)
    (j : Hom P P) (hπ : ∀ d : Subtype D.mem, π.app (j.app d.val) = π.app d.val)
    (hact : ∀ k : Subtype (kernel π).mem, ∀ x, A.act k.val x = x) :
    PrincipalOn A (mapSubgroup j D) (extend f) ↔
      ∃ b : M, ∀ d : Subtype D.mem,
        f.value ⟨discrepancy j d.val, discrepancy_in_kernel π j d.val (hπ d)⟩ = delta A b d.val := by
  have hd (b : M) (d : Subtype D.mem) : delta A b (j.app d.val) = delta A b d.val :=
    congrArg (fun z => z - b) (discrepancy_action j d (hπ d) hact b)
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b, fun d => ?_⟩
    exact (extend_on_conjugate f hf j d (hπ d)).symm.trans
      ((hb ⟨_,d,rfl⟩).trans (hd b d))
  · rintro ⟨b,hb⟩
    refine ⟨b, fun s => ?_⟩
    obtain ⟨d,hs⟩ := s.property
    rw [← hs, extend_on_conjugate f hf j d (hπ d), hd, hb]

/-- Both first-place normalization and the second-place test, for the kernel
of π. Here j may come from conjugation by an element outside P. -/
theorem strict_iff_conjugate_discrepancy (f : Character (localProduct π D hD) A)
    (j : Hom P P) (hπ : ∀ d : Subtype D.mem, π.app (j.app d.val) = π.app d.val)
    (hact : ∀ k : Subtype (kernel π).mem, ∀ x, A.act k.val x = x) :
    (∃ c : G → M, Cocycle A c ∧ (∀ k : Subtype (kernel π).mem, c k.val = f.value k) ∧
      PrincipalOn A D c ∧ PrincipalOn A (mapSubgroup j D) c) ↔
    KillsIntersection f ∧ ∃ b : M, ∀ d : Subtype D.mem,
      f.value ⟨discrepancy j d.val, discrepancy_in_kernel π j d.val (hπ d)⟩ = delta A b d.val := by
  refine (strict_lift_iff f (mapSubgroup j D) hact).trans ?_
  constructor
  · rintro ⟨hf,hs⟩
    exact ⟨hf, (principal_conjugate_iff f hf j hπ hact).mp
      ((second_principal_iff f hf (mapSubgroup j D)).mpr hs)⟩
  · rintro ⟨hf,hs⟩
    exact ⟨hf, (second_principal_iff f hf (mapSubgroup j D)).mp
      ((principal_conjugate_iff f hf j hπ hact).mpr hs)⟩

variable {Ω : Type} {ambient : GroupLaw Ω}

/-- Restrict the ambient group law to the subgroup representing P. -/
def subgroupLaw (S : Subgroup ambient) : GroupLaw (Subtype S.mem) where
  zero := ⟨ambient.zero,S.identity⟩
  add x y := ⟨ambient.add x.val y.val,S.product x.property y.property⟩
  neg x := ⟨ambient.neg x.val,S.inverse x.property⟩
  assoc x y z := Subtype.ext (ambient.assoc x.val y.val z.val)
  zero_add x := Subtype.ext (ambient.zero_add x.val)
  add_zero x := Subtype.ext (ambient.add_zero x.val)
  add_neg x := Subtype.ext (ambient.add_neg x.val)
  neg_add x := Subtype.ext (ambient.neg_add x.val)

theorem conjugate_product (B x y : Ω) : conjugate ambient B (ambient.add x y) =
    ambient.add (conjugate ambient B x) (conjugate ambient B y) := by
  simp only [conjugate, ambient.assoc, cancel_inside]

theorem conjugate_identity (B : Ω) : conjugate ambient B ambient.zero = ambient.zero := by
  rw [conjugate, ambient.add_zero, ambient.add_neg]

theorem conjugate_inverse (B x : Ω) :
    conjugate ambient B (ambient.neg x) = ambient.neg (conjugate ambient B x) := by
  apply right_cancel ambient _ _ (conjugate ambient B x)
  rw [← conjugate_product, ambient.neg_add, conjugate_identity, ambient.neg_add]

/-- A normalizing element may be outside S. Forward preservation suffices
for the induced homomorphism and all of the local discrepancy tests. -/
def ambientConjugation (S : Subgroup ambient) (B : Ω)
    (hB : ∀ x : Subtype S.mem, S.mem (conjugate ambient B x.val)) :
    Hom (subgroupLaw S) (subgroupLaw S) where
  app x := ⟨conjugate ambient B x.val,hB x⟩
  preserves_zero := Subtype.ext (conjugate_identity B)
  preserves_add x y := Subtype.ext (conjugate_product B x.val y.val)
  preserves_neg x := Subtype.ext (conjugate_inverse B x.val)

theorem ambient_discrepancy (S : Subgroup ambient) (B : Ω)
    (hB : ∀ x : Subtype S.mem, S.mem (conjugate ambient B x.val)) (d : Subtype S.mem) :
    (discrepancy (ambientConjugation S B hB) d).val = commutator ambient B d.val := rfl

end Reimann.DyadicPlaceProduct
