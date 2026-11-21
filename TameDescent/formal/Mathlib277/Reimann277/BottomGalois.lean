import Mathlib.Algebra.Algebra.Equiv
import Reimann277.Biquadratic
import Reimann.TameDecomposition277

namespace Reimann.TameBottomGalois277

open TameRationalField277 TameBiquadraticField277 TameArithmetic277 TameDecomposition277

abbrev Galois := Biquadratic ≃ₐ[ℚ] Biquadratic

/-- Read a genuine rational algebra automorphism in the checked four coordinates. -/
def toEndMap (g : Galois) : EndMap where
  app x := (g ⟨x⟩).coord
  onRat r := by
    have h := g.commutes r
    rw [coefficientHom_apply] at h
    exact congrArg Biquadratic.coord h
  onAdd x y := congrArg Biquadratic.coord (map_add g (⟨x⟩ : Biquadratic) ⟨y⟩)
  onMul x y := congrArg Biquadratic.coord (map_mul g (⟨x⟩ : Biquadratic) ⟨y⟩)

theorem toEndMap_injective : Function.Injective toEndMap := by
  intro g h eq
  apply AlgEquiv.ext
  intro x
  apply coord_injective
  exact congrArg (fun u : EndMap => u.app x.coord) eq

/-- The two radical signs give an involution of the actual rational algebra. -/
def signedAut (s : Signs) : Galois where
  toFun x := ⟨conjugate s x.coord⟩
  invFun x := ⟨conjugate s x.coord⟩
  left_inv x := coord_injective (sign_involution s x.coord)
  right_inv x := coord_injective (sign_involution s x.coord)
  map_add' x y := coord_injective (preserves_add s x.coord y.coord)
  map_mul' x y := coord_injective (preserves_mul s x.coord y.coord)
  commutes' r := by
    rw [coefficientHom_apply]
    exact coord_injective (preserves_scalars s r)

theorem toEndMap_signed (s : Signs) : toEndMap (signedAut s) = automorphism s := rfl

theorem signedAut_injective : Function.Injective signedAut := by
  intro s t h
  exact distinct_automorphisms s t (congrArg toEndMap h)

theorem signedAut_surjective : Function.Surjective signedAut := by
  intro g
  obtain ⟨s, h⟩ := every_automorphism (toEndMap g)
  exact ⟨s, toEndMap_injective ((toEndMap_signed s).trans h.symm)⟩

noncomputable def four_automorphisms : Signs ≃ Galois :=
  Equiv.ofBijective signedAut ⟨signedAut_injective, signedAut_surjective⟩

theorem compose_signs (s t : Signs) : (signedAut s).trans (signedAut t) = signedAut (change t s) := by
  apply AlgEquiv.ext
  intro x
  exact coord_injective (sign_action t s x.coord)

theorem identity_sign : signedAut (false,false) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  rfl

def integralPoint (v : OrderCoordinates) : Biquadratic := ⟨TameOrderFaithful277.rationalize v⟩

theorem act_on_order (s : Signs) (v : OrderCoordinates) :
    signedAut s (integralPoint v) = integralPoint (conjugate s v) :=
  coord_injective (integral_restriction s v).symm

/-- The action on the actual four ordinary prime ideals of the explicit order R. -/
def MapsPrime (g : Galois) (p q : Signs) : Prop :=
  ∀ v w, g (integralPoint v) = integralPoint w →
    (TamePrimePowers277.primePlace p.1 p.2 v ↔ TamePrimePowers277.primePlace q.1 q.2 w)

theorem mapsPrime_coordinates (g : Galois) (p q : Signs) :
    MapsPrime g p q ↔ CarriesPrime (toEndMap g) p q := by
  constructor
  · intro h v w hw
    exact h v w (coord_injective hw)
  · intro h v w hw
    exact h v w (congrArg Biquadratic.coord hw)

theorem simply_transitive (p q : Signs) :
    ∃! g : Galois, MapsPrime g p q := by
  obtain ⟨h,huniq⟩ := TameDecomposition277.simply_transitive p q
  refine ⟨signedAut (change p q), (mapsPrime_coordinates _ _ _).mpr h, ?_⟩
  intro g hg
  exact toEndMap_injective (huniq (toEndMap g) ((mapsPrime_coordinates _ _ _).mp hg))

theorem stabilizer_eq_identity (g : Galois) (p : Signs) :
    MapsPrime g p p ↔ g = AlgEquiv.refl := by
  rw [mapsPrime_coordinates, decomposition_trivial, ← identity_sign]
  exact ⟨fun h => toEndMap_injective h, congrArg toEndMap⟩

/-- The Frobenius criterion includes the action on every residue of the order. -/
def IsFrobenius (g : Galois) (p : Signs) : Prop :=
  MapsPrime g p p ∧ ∀ v w, g (integralPoint v) = integralPoint w →
    TameOrderPrimes277.red w (TameLocalOrders277.branchIndex p.1 p.2) =
      (TameOrderPrimes277.red v (TameLocalOrders277.branchIndex p.1 p.2)) ^ 277

theorem frobenius_coordinates (g : Galois) (p : Signs) :
    IsFrobenius g p ↔ IsArithmeticFrobenius (toEndMap g) p := by
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨(mapsPrime_coordinates _ _ _).mp h₁, fun v w h => h₂ v w (coord_injective h)⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨(mapsPrime_coordinates _ _ _).mpr h₁, fun v w h => h₂ v w (congrArg Biquadratic.coord h)⟩

theorem frobenius_eq_identity (g : Galois) (p : Signs) :
    IsFrobenius g p ↔ g = AlgEquiv.refl := by
  rw [frobenius_coordinates, arithmetic_frobenius_identity, ← identity_sign]
  exact ⟨fun h => toEndMap_injective h, congrArg toEndMap⟩

theorem exists_unique_frobenius (p : Signs) : ∃! g : Galois, IsFrobenius g p :=
  ⟨AlgEquiv.refl, (frobenius_eq_identity _ p).mpr rfl,
    fun g hg => (frobenius_eq_identity g p).mp hg⟩

/-- Choose the unique element of the bottom Galois group satisfying the arithmetic
Frobenius residue condition for this ordinary prime. -/
noncomputable def bottomArtin (p : Signs) : Galois := (exists_unique_frobenius p).exists.choose

theorem bottom_artin_identity (p : Signs) : bottomArtin p = AlgEquiv.refl :=
  (frobenius_eq_identity _ p).mp (exists_unique_frobenius p).exists.choose_spec

end Reimann.TameBottomGalois277
