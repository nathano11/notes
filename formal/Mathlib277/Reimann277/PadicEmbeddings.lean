import Reimann277.Biquadratic
import Reimann277.PadicInteger
import Reimann.TameSignedEmbeddings277

namespace Reimann.TamePadicEmbeddings277

open TameRationalField277 TameEmbeddings277 TameLimit277
open TameBiquadraticField277 TameSignedEmbeddings277

local instance fact277 : Fact (Nat.Prime 277) := ⟨TamePadicInteger277.prime277⟩

/-- Realize the project integer model in the standard p-adic field through
the usual inclusion of its ring of integers. -/
noncomputable def includeInteger (x : Integer277) : ℚ_[277] :=
  (TamePadicInteger277.realize x : ℤ_[277])

theorem includeInteger_ofInt (a : Int) :
    includeInteger (ofInt a) = (coefficients ℚ_[277]).app (a : Rat) := by
  rw [includeInteger,TamePadicInteger277.realize_ofInt,PadicInt.coe_intCast]
  exact (map_intCast (algebraMap ℚ ℚ_[277]) a).symm

theorem includeInteger_add (x y : Integer277) :
    includeInteger (add x y) = includeInteger x + includeInteger y := by
  simp only [includeInteger,TamePadicInteger277.realize_add,PadicInt.coe_add]

theorem includeInteger_mul (x y : Integer277) :
    includeInteger (mul x y) = includeInteger x * includeInteger y := by
  simp only [includeInteger,TamePadicInteger277.realize_mul,PadicInt.coe_mul]

theorem includeInteger_neg (x : Integer277) : includeInteger (neg x) = -includeInteger x := by
  simp only [includeInteger,TamePadicInteger277.realize_neg,PadicInt.coe_neg]

noncomputable def integralMap : IntegralMap (coefficients ℚ_[277]) :=
  ⟨includeInteger,includeInteger_ofInt,includeInteger_add,includeInteger_mul,includeInteger_neg⟩

/-- Label `false` chooses 44 or 114 modulo 277 and `true` its negative.
These are the same labels as the four primes of the integral order. -/
noncomputable def embedding (s : Bool × Bool) : Biquadratic →ₐ[ℚ] ℚ_[277] :=
  toAlgHom (branchEmbedding integralMap s)

theorem embedding_on_generators (s : Bool × Bool) :
    embedding s ⟨gen3⟩ = includeInteger (TameLimitRoots277.chooseRoot s.1 rootThree) ∧
    embedding s ⟨gen23⟩ = includeInteger (TameLimitRoots277.chooseRoot s.2 rootTwentyThree) :=
  branch_generators integralMap s

theorem embedding_on_integral_order (s : Bool × Bool) (x : TameArithmetic277.OrderCoordinates) :
    embedding s ⟨TameOrderFaithful277.rationalize x⟩ =
      includeInteger (TameOrderFaithful277.orderImage s.1 s.2 x) :=
  embedding_on_order integralMap s x

theorem embedding_injective (s : Bool × Bool) : Function.Injective (embedding s) :=
  (embedding s).injective

theorem distinct_branches {s t : Bool × Bool} (eq : embedding s = embedding t) : s = t := by
  have h := congrArg toCoordinateMap eq
  simp only [embedding,toCoordinateMap_toAlgHom] at h
  exact ((four_labelled_embeddings integralMap).1 s t).mp h

theorem all_embeddings (g : Biquadratic →ₐ[ℚ] ℚ_[277]) :
    ∃ s : Bool × Bool, embedding s = g := by
  obtain ⟨s, hs⟩ := (four_labelled_embeddings integralMap).2.1 (toCoordinateMap g)
  exact ⟨s, (congrArg toAlgHom hs).trans (toAlgHom_toCoordinateMap g)⟩

/-- The four explicit maps exhaust the genuine rational algebra homomorphisms
to the standard 277-adic field. -/
theorem four_padic_embeddings (g : Biquadratic →ₐ[ℚ] ℚ_[277]) :
    ∃! s : Bool × Bool, embedding s = g := by
  obtain ⟨s,hs⟩ := all_embeddings g
  exact ⟨s,hs,fun t ht => distinct_branches (ht.trans hs.symm)⟩

theorem embedding_dense (g : Biquadratic →ₐ[ℚ] ℚ_[277]) : DenseRange g := by
  have h : g ∘ (algebraMap ℚ Biquadratic) = ((↑) : ℚ → ℚ_[277]) :=
    funext (fun q => g.commutes q)
  apply DenseRange.of_comp (g := algebraMap ℚ Biquadratic)
  rw [h]
  exact Padic.denseRange_ratCast 277

/-- Ordinary powers of the signed order prime are precisely the balls cut
out by the standard 277-adic absolute value on the embedded order. -/
theorem norm_le_iff_prime_power (s : Bool × Bool) (n : Nat)
    (v : TameArithmetic277.OrderCoordinates) :
    ‖embedding s ⟨TameOrderFaithful277.rationalize v⟩‖ ≤
      ((277 : Nat) : ℝ) ^ (-(↑(n+1) : ℤ)) ↔
      TamePrimePowers277.primePower s.1 s.2 (n+1) v := by
  rw [embedding_on_integral_order,TamePrimePowers277.prime_power_iff]
  let z := TameOrderFaithful277.orderImage s.1 s.2 v
  change ‖TamePadicInteger277.realize z‖ ≤ _ ↔ _
  have hz : TamePadicInteger277.realize (ofInt 0) = 0 := by
    simpa using TamePadicInteger277.realize_ofInt 0
  have h := TamePadicInteger277.norm_sub_le_iff_residue z (ofInt 0) n
  rw [hz,sub_zero] at h
  rw [h]
  change TameArithmetic277.branchEval s.1 s.2 n v % modulus n = 0 % modulus n ↔ _
  rw [Int.zero_emod]
  exact Int.dvd_iff_emod_eq_zero.symm

theorem norm_lt_one_iff_prime (s : Bool × Bool) (v : TameArithmetic277.OrderCoordinates) :
    ‖embedding s ⟨TameOrderFaithful277.rationalize v⟩‖ < 1 ↔
      TamePrimePowers277.primePlace s.1 s.2 v := by
  rw [embedding_on_integral_order]
  let z := TameOrderFaithful277.orderImage s.1 s.2 v
  change ‖TamePadicInteger277.realize z‖ < 1 ↔ _
  have hz : TamePadicInteger277.realize (ofInt 0) = 0 := by
    simpa using TamePadicInteger277.realize_ofInt 0
  have h := TamePadicInteger277.norm_sub_lt_one_iff_first_residue z (ofInt 0)
  rw [hz,sub_zero] at h
  rw [h]
  change TameArithmetic277.branchEval s.1 s.2 0 v % 277 = 0 ↔ _
  exact Int.dvd_iff_emod_eq_zero.symm

variable {L : Type} [Field L] [Algebra ℚ L]

/-- The evident extension of the coefficient target along a rational algebra map. -/
noncomputable def scalarExtension (i : ℚ_[277] →ₐ[ℚ] L) :
    ScalarExtension (coefficients ℚ_[277]) (coefficients L) where
  app := i
  coefficients := i.commutes
  onAdd := i.map_add
  onMul := i.map_mul
  onNeg := map_neg i

/-- Every rational embedding into a field containing the standard 277-adic
numbers factors through exactly one of the four maps to that base field. -/
theorem factor_through_padic (i : ℚ_[277] →ₐ[ℚ] L)
    (g : Biquadratic →ₐ[ℚ] L) :
    ∃! s : Bool × Bool, i.comp (embedding s) = g := by
  obtain ⟨s,hs,_⟩ := factor_over_subfield (scalarExtension i) integralMap (toCoordinateMap g)
  have he : i.comp (embedding s) = g := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun e => OverRat.app e x.coord) hs
  refine ⟨s,he,?_⟩
  intro t ht
  apply distinct_branches
  apply AlgHom.ext
  intro x
  exact i.injective (DFunLike.congr_fun (ht.trans he.symm) x)

/-- A completion generated densely by the biquadratic field cannot extend a
closed copy of ℚ_[277] properly. The topological hypotheses hold in particular
for an isometric inclusion into a metric completion. -/
theorem surjective_of_closed_dense [TopologicalSpace L] (i : ℚ_[277] →ₐ[ℚ] L)
    (g : Biquadratic →ₐ[ℚ] L) (hi : IsClosed (Set.range i)) (hg : DenseRange g) :
    Function.Surjective i := by
  obtain ⟨s,hs,_⟩ := factor_through_padic i g
  have sub : Set.range g ⊆ Set.range i := by
    rintro y ⟨x,rfl⟩
    exact ⟨embedding s x,DFunLike.congr_fun hs x⟩
  have dense : DenseRange i := hg.mono sub
  exact Set.range_eq_univ.mp (hi.closure_eq.symm.trans dense.closure_eq)

end Reimann.TamePadicEmbeddings277
