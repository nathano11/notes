import Reimann.Transfer

namespace Reimann.TameRestriction

/-- The commutator [t,g] in an arbitrary (possibly noncommutative) group. -/
def commutator (P : Transfer.GroupLaw G) (t g : G) : G :=
  P.add (P.add (P.add t g) (P.neg t)) (P.neg g)

def conjugate (P : Transfer.GroupLaw G) (g x : G) : G :=
  P.add (P.add g x) (P.neg g)

theorem cancel_inside (P : Transfer.GroupLaw G) (g x : G) :
    P.add (P.neg g) (P.add g x) = x := by
  rw [← P.assoc, P.neg_add, P.zero_add]

theorem right_cancel (P : Transfer.GroupLaw G) (x y a : G)
    (h : P.add x a = P.add y a) : x = y := by
  have he := congrArg (fun z => P.add z (P.neg a)) h
  simpa only [P.assoc, P.add_neg, P.add_zero] using he

theorem commutator_swap (P : Transfer.GroupLaw G) (t g : G) :
    P.add (commutator P t g) (P.add g t) = P.add t g := by
  simp only [commutator, P.assoc, cancel_inside, P.neg_add, P.add_zero]

/-- This identity holds before taking a character or passing to a quotient. -/
theorem commutator_product (P : Transfer.GroupLaw G) (t g h : G) :
    commutator P t (P.add g h) =
      P.add (commutator P t g) (conjugate P g (commutator P t h)) := by
  apply right_cancel P _ _ (P.add (P.add g h) t)
  rw [commutator_swap]
  simp only [conjugate, P.assoc, cancel_inside, commutator, P.neg_add, P.add_zero]

/-- Kernel of the quotient, scalar action on coefficients, and an inverse
to the tame difference. Centrality in the quotient is exactly comm_in. -/
structure TameData (P : Transfer.GroupLaw G) (t : G) (m : Int) where
  kernel : G → Prop
  mul_in : ∀ {g h}, kernel g → kernel h → kernel (P.add g h)
  inv_in : ∀ {g}, kernel g → kernel (P.neg g)
  conj_in : ∀ g {h}, kernel h → kernel (conjugate P g h)
  comm_in : ∀ g, kernel (commutator P t g)
  scalar : G → Int
  trivial_on_kernel : ∀ {g}, kernel g → m ∣ scalar g-1
  scalar_mul : ∀ g h, m ∣ scalar (P.add g h) - scalar g*scalar h
  inverse : Int
  inverse_spec : m ∣ inverse*(scalar t-1)-1

/-- Characters are evaluated only on kernel elements. Integer outputs represent
coefficients modulo m; equivariance uses the given scalar (the inverse twist
in the arithmetic application). -/
structure KernelCharacter {P : Transfer.GroupLaw G} {t : G} {m : Int}
    (T : TameData P t m) where
  value : {g // T.kernel g} → Int
  additive : ∀ {x y} (hx : T.kernel x) (hy : T.kernel y),
    m ∣ value ⟨P.add x y, T.mul_in hx hy⟩ - (value ⟨x,hx⟩ + value ⟨y,hy⟩)
  equivariant : ∀ g {x} (hx : T.kernel x),
    m ∣ value ⟨conjugate P g x, T.conj_in g hx⟩ - T.scalar g * value ⟨x,hx⟩

/-- The normalized extension is obtained from the actual commutator [t,g].
The formula works for a nonsplit group extension. -/
def extend {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} (f : KernelCharacter T) (g : G) : Int :=
  T.inverse * f.value ⟨commutator P t g, T.comm_in g⟩

theorem commutator_character_product {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} (f : KernelCharacter T) (g h : G) :
    m ∣ f.value ⟨commutator P t (P.add g h), T.comm_in _⟩ -
      (f.value ⟨commutator P t g, T.comm_in _⟩ +
        T.scalar g * f.value ⟨commutator P t h, T.comm_in _⟩) := by
  have he : (⟨commutator P t (P.add g h), T.comm_in _⟩ : Subtype T.kernel) =
      ⟨_, T.mul_in (T.comm_in g) (T.conj_in g (T.comm_in h))⟩ :=
    Subtype.ext (commutator_product P t g h)
  rw [he]
  obtain ⟨a,ha⟩ := f.additive (T.comm_in g) (T.conj_in g (T.comm_in h))
  obtain ⟨b,hb⟩ := f.equivariant g (T.comm_in h)
  exact ⟨a+b, by grind⟩

theorem extend_crossed {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} (f : KernelCharacter T) (g h : G) :
    m ∣ extend f (P.add g h) - (extend f g + T.scalar g * extend f h) := by
  obtain ⟨b,hb⟩ := commutator_character_product f g h
  refine ⟨T.inverse*b, ?_⟩
  unfold extend
  grind

theorem commutator_times (P : Transfer.GroupLaw G) (t g : G) :
    P.add (commutator P t g) g = conjugate P t g := by
  unfold commutator conjugate
  rw [P.assoc, P.neg_add, P.add_zero]

theorem commutator_on_kernel {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} (f : KernelCharacter T) {g : G} (hg : T.kernel g) :
    m ∣ f.value ⟨commutator P t g,T.comm_in _⟩ -
      (T.scalar t-1)*f.value ⟨g,hg⟩ := by
  have he : (⟨P.add (commutator P t g) g, T.mul_in (T.comm_in _) hg⟩ : Subtype T.kernel) =
      ⟨conjugate P t g,T.conj_in t hg⟩ := Subtype.ext (commutator_times P t g)
  obtain ⟨a,ha⟩ := f.additive (T.comm_in g) hg
  rw [he] at ha
  obtain ⟨b,hb⟩ := f.equivariant t hg
  exact ⟨b-a, by grind⟩

theorem extend_restrict {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} (f : KernelCharacter T) {g : G} (hg : T.kernel g) :
    m ∣ extend f g - f.value ⟨g,hg⟩ := by
  obtain ⟨a,ha⟩ := commutator_on_kernel f hg
  obtain ⟨b,hb⟩ := T.inverse_spec
  refine ⟨T.inverse*a+b*f.value ⟨g,hg⟩, ?_⟩
  unfold extend
  grind

def Crossed {P : Transfer.GroupLaw G} {t : G} {m : Int}
    (T : TameData P t m) (c : G → Int) : Prop :=
  ∀ g h, m ∣ c (P.add g h) - (c g + T.scalar g*c h)

theorem crossed_kernel_left {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} {c : G → Int} (hc : Crossed T c)
    {x : G} (hx : T.kernel x) (y : G) :
    m ∣ c (P.add x y) - (c x+c y) := by
  obtain ⟨a,ha⟩ := hc x y
  obtain ⟨b,hb⟩ := T.trivial_on_kernel hx
  exact ⟨a+b*c y, by grind⟩

theorem crossed_commutator {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} {c : G → Int} (hc : Crossed T c) (g : G) :
    m ∣ c (commutator P t g) - ((T.scalar t-1)*c g - (T.scalar g-1)*c t) := by
  obtain ⟨a,ha⟩ := crossed_kernel_left hc (T.comm_in g) (P.add g t)
  rw [commutator_swap] at ha
  obtain ⟨b,hb⟩ := hc t g
  obtain ⟨d,hd⟩ := hc g t
  exact ⟨b-d-a, by grind⟩

theorem conjugate_times (P : Transfer.GroupLaw G) (g x : G) :
    P.add (conjugate P g x) g = P.add g x := by
  unfold conjugate
  rw [P.assoc, P.neg_add, P.add_zero]

def restrictCharacter {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} {c : G → Int} (hc : Crossed T c) : KernelCharacter T where
  value x := c x.val
  additive hx _ := crossed_kernel_left hc hx _
  equivariant := by
    intro g x hx
    obtain ⟨a,ha⟩ := crossed_kernel_left hc (T.conj_in g hx) g
    rw [conjugate_times] at ha
    obtain ⟨b,hb⟩ := hc g x
    exact ⟨b-a, by grind⟩

/-- Restriction followed by normalized extension differs from the original
cocycle by the principal cocycle attached to inverse * c(t). -/
theorem reconstruct_mod_principal {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} {c : G → Int} (hc : Crossed T c) (g : G) :
    m ∣ c g - (extend (restrictCharacter hc) g +
      (T.scalar g-1)*(T.inverse*c t)) := by
  obtain ⟨a,ha⟩ := crossed_commutator hc g
  obtain ⟨b,hb⟩ := T.inverse_spec
  change m ∣ c g - (T.inverse*c (commutator P t g)+(T.scalar g-1)*(T.inverse*c t))
  exact ⟨-T.inverse*a-b*c g, by grind⟩

/-- Two cocycles restrict to the same character exactly when their difference
is principal. A single primitive works for every g simultaneously. -/
theorem fibres_iff {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} {c d : G → Int} (hc : Crossed T c) (hd : Crossed T d) :
    (∀ g, T.kernel g → m ∣ c g-d g) ↔
      ∃ b : Int, ∀ g, m ∣ c g-d g-(T.scalar g-1)*b := by
  constructor
  · intro h
    refine ⟨T.inverse*(c t-d t), fun g => ?_⟩
    obtain ⟨a,ha⟩ := reconstruct_mod_principal hc g
    obtain ⟨b,hb⟩ := reconstruct_mod_principal hd g
    obtain ⟨z,hz⟩ := h _ (T.comm_in g)
    change c g-(T.inverse*c (commutator P t g)+(T.scalar g-1)*(T.inverse*c t)) = _ at ha
    change d g-(T.inverse*d (commutator P t g)+(T.scalar g-1)*(T.inverse*d t)) = _ at hb
    exact ⟨a-b+T.inverse*z, by grind⟩
  · rintro ⟨b,h⟩ g hg
    obtain ⟨a,ha⟩ := h g
    obtain ⟨z,hz⟩ := T.trivial_on_kernel hg
    exact ⟨a+z*b, by grind⟩

/-- The extension is additive on any representatives congruent to the sum.
Consequently the inverse on cohomology respects addition. -/
theorem extend_additive {P : Transfer.GroupLaw G} {t : G} {m : Int}
    {T : TameData P t m} (f h s : KernelCharacter T)
    (hs : ∀ x, m ∣ s.value x - (f.value x + h.value x)) (g : G) :
    m ∣ extend s g - (extend f g + extend h g) := by
  obtain ⟨a,ha⟩ := hs ⟨_, T.comm_in g⟩
  exact ⟨T.inverse*a, by unfold extend; grind⟩

end Reimann.TameRestriction
