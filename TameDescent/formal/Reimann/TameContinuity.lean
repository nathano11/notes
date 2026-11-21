import Reimann.TameRestriction

namespace Reimann.TameContinuity

open Reimann.Transfer Reimann.TameRestriction

/-- A topology specified by its opens. The local axiom gives arbitrary
unions (including the empty union) from open neighborhoods of their points. -/
structure Topology (A : Type u) where
  isOpen : (A → Prop) → Prop
  univ_open : isOpen (fun _ => True)
  inter_open : ∀ {U V}, isOpen U → isOpen V → isOpen (fun a => U a ∧ V a)
  local_open : ∀ {S : A → Prop}, (∀ a, S a → ∃ U, isOpen U ∧ U a ∧ (∀ b, U b → S b)) → isOpen S

def Continuous (τ : Topology A) (η : Topology B) (f : A → B) : Prop :=
  ∀ U, η.isOpen U → τ.isOpen (fun x => U (f x))

theorem id_continuous (τ : Topology A) : Continuous τ τ id := fun _ h => h

theorem const_continuous (τ : Topology A) (η : Topology B) (b : B) :
    Continuous τ η (fun _ => b) := by
  intro U _
  apply τ.local_open
  intro a ha
  exact ⟨fun _ => True, τ.univ_open, trivial, fun _ _ => ha⟩

theorem comp_continuous {τ : Topology A} {η : Topology B} {κ : Topology C}
    {f : A → B} {g : B → C} (hf : Continuous τ η f) (hg : Continuous η κ g) :
    Continuous τ κ (fun a => g (f a)) := fun U hU => hf _ (hg U hU)

/-- Multiplication is continuous for the product topology, expressed by open
rectangles about a pair, and inversion is continuous. -/
structure GroupTopology (P : GroupLaw G) (τ : Topology G) : Prop where
  neg_continuous : Continuous τ τ P.neg
  add_neighborhoods : ∀ g h U, τ.isOpen U → U (P.add g h) → ∃ V W,
    τ.isOpen V ∧ τ.isOpen W ∧ V g ∧ W h ∧ ∀ x y, V x → W y → U (P.add x y)

theorem pointwise_add_continuous {P : GroupLaw G} {τ : Topology G}
    (top : GroupTopology P τ) {η : Topology A} {f g : A → G}
    (hf : Continuous η τ f) (hg : Continuous η τ g) :
    Continuous η τ (fun a => P.add (f a) (g a)) := by
  intro U hU
  apply η.local_open
  intro a ha
  obtain ⟨V,W,hV,hW,hfa,hga,hprod⟩ := top.add_neighborhoods (f a) (g a) U hU ha
  exact ⟨fun b => V (f b) ∧ W (g b), η.inter_open (hf V hV) (hg W hW), ⟨hfa,hga⟩,
    fun b h => hprod (f b) (g b) h.1 h.2⟩

theorem commutator_continuous {P : GroupLaw G} {τ : Topology G}
    (top : GroupTopology P τ) (t : G) : Continuous τ τ (commutator P t) := by
  exact pointwise_add_continuous top (pointwise_add_continuous top
    (pointwise_add_continuous top (const_continuous τ τ t) (id_continuous τ))
    (const_continuous τ τ (P.neg t))) top.neg_continuous

def RelativeOpen (τ : Topology G) (K : G → Prop) (V : Subtype K → Prop) : Prop :=
  ∃ U, τ.isOpen U ∧ ∀ x : Subtype K, V x ↔ U x.val

theorem preimage_relative_open {τ : Topology A} {η : Topology G} {K : G → Prop}
    {f : A → G} (hf : Continuous τ η f) (hK : ∀ a, K (f a))
    {V : Subtype K → Prop} (hV : RelativeOpen η K V) :
    τ.isOpen (fun a => V ⟨f a,hK a⟩) := by
  obtain ⟨U,hU,h⟩ := hV
  have he : (fun a => V ⟨f a,hK a⟩) = (fun a => U (f a)) :=
    funext (fun a => propext (h ⟨f a,hK a⟩))
  rw [he]
  exact hf U hU

def discrete (A : Type u) : Topology A where
  isOpen _ := True
  univ_open := trivial
  inter_open _ _ := trivial
  local_open _ := trivial

/-- Ordinary continuity of the upstairs character to the discrete residues,
with the subspace topology on the kernel. -/
def ContinuousKernelCharacter {P : GroupLaw G} {t : G} {m : Int} {T : TameData P t m}
    (τ : Topology G) (f : KernelCharacter T) : Prop :=
  ∀ V : Int → Prop, RelativeOpen τ T.kernel (fun x => V (f.value x % m))

theorem commutator_value_continuous {P : GroupLaw G} {τ : Topology G}
    (top : GroupTopology P τ) {t : G} {m : Int} {T : TameData P t m}
    (f : KernelCharacter T) (hf : ContinuousKernelCharacter τ f) :
    Continuous τ (discrete Int) (fun g => f.value ⟨commutator P t g, T.comm_in g⟩ % m) := by
  intro V _
  exact preimage_relative_open (commutator_continuous top t) T.comm_in (hf V)

theorem scalar_residue (d x m : Int) : (d*(x%m))%m = (d*x)%m := by
  rw [Int.mul_emod d (x%m) m, Int.emod_emod, ← Int.mul_emod]

/-- The actual normalized commutator extension is continuous as a residue-valued
cocycle. The kernel only carries its subspace topology and need not be open. -/
theorem normalized_extension_continuous {P : GroupLaw G} {τ : Topology G}
    (top : GroupTopology P τ) {t : G} {m : Int} {T : TameData P t m}
    (f : KernelCharacter T) (hf : ContinuousKernelCharacter τ f) :
    Continuous τ (discrete Int) (fun g => extend f g % m) := by
  intro V _
  have h := commutator_value_continuous top f hf (fun a => V ((T.inverse*a)%m)) trivial
  simpa only [extend, scalar_residue] using h

theorem restriction_continuous {P : GroupLaw G} {τ : Topology G}
    {t : G} {m : Int} {T : TameData P t m} {c : G → Int}
    (hc : Crossed T c) (hcont : Continuous τ (discrete Int) (fun g => c g % m)) :
    ContinuousKernelCharacter τ (restrictCharacter hc) := by
  intro V
  exact ⟨fun g => V (c g % m), hcont V trivial, fun _ => Iff.rfl⟩

theorem continuous_crossed_lift {P : GroupLaw G} {τ : Topology G} (top : GroupTopology P τ)
    {t : G} {m : Int} {T : TameData P t m} (f : KernelCharacter T)
    (hf : ContinuousKernelCharacter τ f) :
    Crossed T (extend f) ∧ Continuous τ (discrete Int) (fun g => extend f g % m) ∧
      ∀ g (hg : T.kernel g), m ∣ extend f g - f.value ⟨g,hg⟩ :=
  ⟨extend_crossed f, normalized_extension_continuous top f hf, fun _ hg => extend_restrict f hg⟩

theorem discrete_binary_continuous {τ : Topology A} {f : A → B} {g : A → C}
    (hf : Continuous τ (discrete B) f) (hg : Continuous τ (discrete C) g) (k : B → C → D) :
    Continuous τ (discrete D) (fun a => k (f a) (g a)) := by
  intro V _
  apply τ.local_open
  intro a ha
  refine ⟨fun b => f b = f a ∧ g b = g a,
    τ.inter_open (hf (fun x => x = f a) trivial) (hg (fun x => x = g a) trivial),
    ⟨rfl,rfl⟩, ?_⟩
  intro b h
  change V (k (f b) (g b))
  rw [h.1,h.2]
  exact ha

theorem correction_residue (m b x y : Int) :
    (x%m + (y%m-1)*b)%m = (x+(y-1)*b)%m := by
  have hy : (y%m-1)%m = (y-1)%m := by
    rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
  rw [Int.add_emod, Int.add_emod x ((y-1)*b) m, Int.emod_emod,
    Int.mul_emod (y%m-1) b m, Int.mul_emod (y-1) b m, hy]

theorem reconstruction_as_residues {P : GroupLaw G} {t : G} {m : Int} {T : TameData P t m}
    {c : G → Int} (hc : Crossed T c) (g : G) :
    c g % m = (extend (restrictCharacter hc) g % m +
      (T.scalar g % m - 1)*(T.inverse*c t)) % m := by
  rw [correction_residue]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.emod_eq_zero_of_dvd (reconstruct_mod_principal hc g))

/-- For a continuous scalar action, the restriction detects continuity of every
crossed cocycle, including its principal correction at the chosen tame element. -/
theorem crossed_continuous_iff_restriction {P : GroupLaw G} {τ : Topology G}
    (top : GroupTopology P τ) {t : G} {m : Int} {T : TameData P t m} {c : G → Int}
    (hscalar : Continuous τ (discrete Int) (fun g => T.scalar g % m)) (hc : Crossed T c) :
    Continuous τ (discrete Int) (fun g => c g % m) ↔
      ContinuousKernelCharacter τ (restrictCharacter hc) := by
  constructor
  · exact restriction_continuous hc
  · intro hr
    have he := normalized_extension_continuous top (restrictCharacter hc) hr
    have hcombine := discrete_binary_continuous he hscalar
      (fun x y => (x+(y-1)*(T.inverse*c t))%m)
    have hfun := funext (reconstruction_as_residues hc)
    rw [hfun]
    exact hcombine

end Reimann.TameContinuity
