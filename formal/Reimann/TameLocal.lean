import Std

namespace Reimann.TameLocal

/-- A scalar one-cocycle given by integer lifts of coefficients modulo `m`. -/
def Cocycle {G : Type} (m : Int) (mul : G → G → G) (a c : G → Int) : Prop :=
  ∀ g h, m ∣ c (mul g h) - (c g + a g*c h)

def Principal {G : Type} (m : Int) (a c : G → Int) : Prop :=
  ∃ b : Int, ∀ g, m ∣ c g - (a g-1)*b

def VanishesOnKernel {G : Type} (m : Int) (a c : G → Int) : Prop :=
  ∀ k, m ∣ a k-1 → m ∣ c k

theorem principal_vanishes_on_kernel {G : Type} {m : Int} {a c : G → Int}
    (h : Principal m a c) : VanishesOnKernel m a c := by
  obtain ⟨b,hb⟩ := h
  intro k hk
  obtain ⟨v,hv⟩ := hk
  obtain ⟨w,hw⟩ := hb k
  exact ⟨w+v*b, by grind⟩

theorem swap_yields_cross_relation {G : Type} {m : Int} {mul : G → G → G}
    {a c : G → Int} (hc : Cocycle m mul a c) (t g : G)
    (hswap : m ∣ c (mul t g) - c (mul g t)) :
    m ∣ (a t-1)*c g - (a g-1)*c t := by
  obtain ⟨i,hi⟩ := hc t g
  obtain ⟨j,hj⟩ := hc g t
  obtain ⟨w,hw⟩ := hswap
  exact ⟨w-i+j, by grind⟩

theorem primitive_from_cross_relation {m atame ag ctame cg i : Int}
    (hi : m ∣ i*(atame-1)-1) (hcross : m ∣ (atame-1)*cg - (ag-1)*ctame) :
    m ∣ cg - (ag-1)*(i*ctame) := by
  obtain ⟨v,hv⟩ := hi
  obtain ⟨w,hw⟩ := hcross
  refine ⟨i*w-v*cg, ?_⟩
  have h := congrArg (fun z : Int => i*z) hw
  have j := congrArg (fun z : Int => z*cg) hv
  grind

theorem principal_of_swaps {G : Type} {m i : Int} {mul : G → G → G}
    {a c : G → Int} (hc : Cocycle m mul a c) (t : G)
    (hi : m ∣ i*(a t-1)-1) (hswap : ∀ g, m ∣ c (mul t g) - c (mul g t)) :
    ∀ g, m ∣ c g - (a g-1)*(i*c t) := by
  intro g
  exact primitive_from_cross_relation hi (swap_yields_cross_relation hc t g (hswap g))

def ScalarAction {G : Type} (m : Int) (mul : G → G → G) (a : G → Int) : Prop :=
  ∀ g h, m ∣ a (mul g h) - a g*a h

theorem action_swap {G : Type} {m : Int} {mul : G → G → G} {a : G → Int}
    (ha : ScalarAction m mul a) (t g : G) : m ∣ a (mul t g) - a (mul g t) := by
  obtain ⟨v,hv⟩ := ha t g
  obtain ⟨w,hw⟩ := ha g t
  exact ⟨v-w, by grind⟩

theorem scalar_inverse_of_left_inverse {G : Type} {m : Int} {mul : G → G → G}
    {a : G → Int} (ha : ScalarAction m mul a) {e y j : G}
    (he : m ∣ a e-1) (hj : mul j y = e) : m ∣ a j*a y - 1 := by
  obtain ⟨v,hv⟩ := ha j y
  rw [hj] at hv
  obtain ⟨w,hw⟩ := he
  exact ⟨w-v, by grind⟩

theorem cancel_unit_factor {m d y j : Int}
    (hy : m ∣ j*y-1) (hd : m ∣ d*y) : m ∣ d := by
  obtain ⟨v,hv⟩ := hy
  obtain ⟨w,hw⟩ := hd
  refine ⟨j*w-v*d, ?_⟩
  have h := congrArg (fun z : Int => j*z) hw
  have k := congrArg (fun z : Int => d*z) hv
  grind

theorem quotient_in_kernel {G : Type} {m j : Int} {mul : G → G → G} {a : G → Int}
    (ha : ScalarAction m mul a) {k x y : G} (hk : mul k y = x)
    (hxy : m ∣ a x-a y) (hy : m ∣ j*a y-1) : m ∣ a k-1 := by
  apply cancel_unit_factor hy
  obtain ⟨v,hv⟩ := ha k y
  rw [hk] at hv
  obtain ⟨w,hw⟩ := hxy
  exact ⟨w-v, by grind⟩

theorem equal_across_kernel {G : Type} {m : Int} {mul : G → G → G} {a c : G → Int}
    (hc : Cocycle m mul a c) (hker : VanishesOnKernel m a c)
    {k x y : G} (hk : mul k y = x) (hak : m ∣ a k-1) : m ∣ c x-c y := by
  obtain ⟨v,hv⟩ := hc k y
  rw [hk] at hv
  obtain ⟨w,hw⟩ := hker k hak
  obtain ⟨s,hs⟩ := hak
  exact ⟨v+w+s*c y, by grind⟩

theorem cocycle_constant_on_scalar_fibers {G : Type} {m : Int} {mul : G → G → G}
    {a c : G → Int} (ha : ScalarAction m mul a) (hc : Cocycle m mul a c)
    (hker : VanishesOnKernel m a c) {e : G} (he : m ∣ a e-1)
    (rightDiv : ∀ x y, ∃ k, mul k y = x) {x y : G} (hxy : m ∣ a x-a y) :
    m ∣ c x-c y := by
  obtain ⟨k,hk⟩ := rightDiv x y
  obtain ⟨j,hj⟩ := rightDiv e y
  have hy := scalar_inverse_of_left_inverse ha he hj
  exact equal_across_kernel hc hker hk (quotient_in_kernel ha hk hxy hy)

theorem primitive_from_kernel {G : Type} {m i : Int} {mul : G → G → G}
    {a c : G → Int} (ha : ScalarAction m mul a) (hc : Cocycle m mul a c)
    {e : G} (he : m ∣ a e-1) (rightDiv : ∀ x y, ∃ k, mul k y = x)
    (t : G) (hi : m ∣ i*(a t-1)-1) (hker : VanishesOnKernel m a c) :
    ∀ g, m ∣ c g - (a g-1)*(i*c t) := by
  apply principal_of_swaps hc t hi
  intro g
  exact cocycle_constant_on_scalar_fibers ha hc hker he rightDiv (action_swap ha t g)

theorem principal_iff_vanishes_on_kernel {G : Type} {m i : Int} {mul : G → G → G}
    {a c : G → Int} (ha : ScalarAction m mul a) (hc : Cocycle m mul a c)
    {e : G} (he : m ∣ a e-1) (rightDiv : ∀ x y, ∃ k, mul k y = x)
    (t : G) (hi : m ∣ i*(a t-1)-1) :
    Principal m a c ↔ VanishesOnKernel m a c :=
  ⟨principal_vanishes_on_kernel,
   fun h => ⟨i*c t, primitive_from_kernel ha hc he rightDiv t hi h⟩⟩

def swapCommutator {G : Type} (mul : G → G → G) (inv : G → G) (t g : G) : G :=
  mul (mul t g) (inv (mul g t))

theorem swapCommutator_factor {G : Type} (mul : G → G → G) (inv : G → G) (e : G)
    (assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (rightId : ∀ x, mul x e = x) (leftInv : ∀ x, mul (inv x) x = e) (t g : G) :
    mul (swapCommutator mul inv t g) (mul g t) = mul t g := by
  rw [swapCommutator, assoc, leftInv, rightId]

theorem swapCommutator_in_kernel {G : Type} {m : Int} {mul : G → G → G} {inv : G → G}
    {e : G} {a : G → Int} (ha : ScalarAction m mul a) (he : m ∣ a e-1)
    (assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (rightId : ∀ x, mul x e = x) (leftInv : ∀ x, mul (inv x) x = e) (t g : G) :
    m ∣ a (swapCommutator mul inv t g)-1 := by
  have hfactor := swapCommutator_factor mul inv e assoc rightId leftInv t g
  have hinverse := scalar_inverse_of_left_inverse ha he (leftInv (mul g t))
  exact quotient_in_kernel ha hfactor (action_swap ha t g) hinverse

theorem cocycle_swap_of_commutator_zero {G : Type} {m : Int} {mul : G → G → G}
    {inv : G → G} {a c : G → Int} (hc : Cocycle m mul a c) (t g : G)
    (hfactor : mul (swapCommutator mul inv t g) (mul g t) = mul t g)
    (hak : m ∣ a (swapCommutator mul inv t g)-1)
    (hck : m ∣ c (swapCommutator mul inv t g)) : m ∣ c (mul t g)-c (mul g t) := by
  obtain ⟨v,hv⟩ := hc (swapCommutator mul inv t g) (mul g t)
  rw [hfactor] at hv
  obtain ⟨w,hw⟩ := hck
  obtain ⟨s,hs⟩ := hak
  exact ⟨v+w+s*c (mul g t), by grind⟩

/-- It suffices to test commutators with a single scalar-unit element. -/
theorem principal_iff_vanishes_on_swapCommutators {G : Type} {m i : Int}
    {mul : G → G → G} {inv : G → G} {e : G} {a c : G → Int}
    (ha : ScalarAction m mul a) (hc : Cocycle m mul a c) (he : m ∣ a e-1)
    (assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
    (rightId : ∀ x, mul x e = x) (leftInv : ∀ x, mul (inv x) x = e)
    (t : G) (hi : m ∣ i*(a t-1)-1) :
    Principal m a c ↔ ∀ g, m ∣ c (swapCommutator mul inv t g) := by
  have hak := swapCommutator_in_kernel ha he assoc rightId leftInv t
  constructor
  · intro hp g
    exact principal_vanishes_on_kernel hp _ (hak g)
  · intro h
    refine ⟨i*c t, principal_of_swaps hc t hi ?_⟩
    intro g
    exact cocycle_swap_of_commutator_zero hc t g
      (swapCommutator_factor mul inv e assoc rightId leftInv t g) (hak g) (h g)

end Reimann.TameLocal
