`ExampleSatisfiesConditionsAtFive` (including `on_core_sharp` and `on_core`) compiled cleanly (`EXIT=0`) on Lean 4.36.0 in the disposable copy; waiting for the integrated `OnCoreSharpJrec7` (`DyadicJrec7` + `on_core_sharp`) build to finish.

I have applied the 13 remaining Lean 4.36.0 compatibility fixes to the upstream Nov 20 modules in the disposable copy (`rh-disposable-e1-436`) and kicked off `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for the build task to complete.

Fixed the remaining 5 upstream Lean 4.36.0 compatibility errors (`LHwlineLemmas`, `Wlocal`, `WorkedExample`, `SSYTPeel`, `PeelLead`) and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed the last upstream compatibility error in `HWLine.lean` and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed the 4 compatibility errors in `LDbasisLemmas`, `LDlatLemmas`, `LDrowLemmas`, and `TensorBasis` and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed the 4 compatibility errors in `LDrowLemmas`, `TensorBasis`, `NablaLKBasis`, and `ProdInitialMinorsMemDetSpan` and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed the 4 compatibility errors in `TensorBasis`, `NablaLLe`, `HighestWeightShiftEqDetMul`, and `RealLocalDeltaNabla` and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed `TensorBasis.lean:54` (`Finsupp.mapDomain_apply_of_injective`) and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Patched all remaining 13 unbuilt upstream modules for Lean 4.36.0 compatibility in a single pass and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed the remaining two compatibility diffs (`DividedPowerZeroZeroVector`, `UnitNormBounds`, `LEhwLemmas`) and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Updated `DividedPowerZeroZeroVector.lean` and `UnitNormBounds.lean` for `multiplicity` vs `padicValNat` and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed `UnitNormBounds.lean` (`Nat.padicValNat_def` / `Nat.multiplicity_mul`) and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed `DepthNonnegative.lean:546` (`MultilinearMap.map_update_smul` with `RingHom.id`) and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed `WeightBounds.lean:633` (`Real.posLog_le_posLog` now takes `-1 ≤ x` in 4.36.0) and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

All upstream Nov 20 modules now compile cleanly on Lean 4.36.0. I fixed the 3 minor tactic lines in `DyadicJrec7.lean` and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Fixed line 492 in `DyadicJrec7.lean` and re-launched `lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7`. Waiting for completion.

Completed the integrated E1 checkpoint in a **disposable copy** of the November 20 release on **Lean 4.36.0** (`C:\Users\natha\AppData\Local\Temp\rh-disposable-e1-436`). The live repo `c:\code\Reimann` was left untouched (read-only).

### **1. Build Verification (Lean 4.36.0)**

- **Compiler:** `Lean (version 4.36.0, x86_64-w64-windows-gnu, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release)`
- **Target command:**  &#x20;
  ```
  powershell
  ```
  lake build Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive \`

  &#x20;          Formalism.PieriBlockIdeals.PieriColumnMinors.DyadicJrec7 \`

  &#x20;          Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.OnCoreSharpJrec7
- **Result:** `Build completed successfully (19019 jobs).` (`BUILD_EXIT=0`, zero `sorry`).

---

### **2. Declarations**

#### **A. Sharper per-row aggregate before the `CE · E1u` rewrite**

In ExampleSatisfiesConditionsAtFive.lean:

- `OnObj.sharpRowBound`:  &#x20;
  ```
  lean
  ```
  def sharpRowBound (Jcap : Bs.J → ℝ) (j : Bs.J) : ℝ :=

  &#x20; Jcap j + 8 \* O.C \* O.B0 \* Real.log O.k

  &#x20;   \+ (4 \* O.C ^ 2 + 17 \* O.C + 12) \* (O.f \* O.m \* O.b)

  &#x20;   \+ O.Cb \* O.B0

  where `O.B0 = O.f * O.m * O.b * O.L` and `O.Cb = O.Cb1 + O.Cb2 + 4`.
- `LeafJSumCap`: per-row prime-sum hypothesis `∀ j, (∀ l, 0 ≤ O.Jp j l) ∧ ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, O.Jp j p * Real.log p ≤ Jcap j`.
- `on_core_sharp`:     &#x20;
  - Keeps `O.Jp`, `hJE : LeafJExp N O`, and `O.errOn` unchanged.
  - Uses the actual `place_sum` (`RamBasic.lean`), `local_conditions_global_form : OnExport2` (`LocalConditionsGlobalForm.lean`), `lead_exact` (exposed from AbsorbLocalConditionsOfExact.lean), `budget_numeric`, and `bad_sum_of_bad` (dropping the unused `LeafX` parameter).
  - Charges `Jcap j` **once** per row `j` and exports `ONwith S { N with E1 := O.sharpRowBound Jcap } O.errOn` **before** any `N.E1 j = CE * O.E1u` rewrite (`ErrorConstantMatchesDefinition`).
  - Drops `CE`, `hCE : c.CE ≤ CE`, `tE1 : ErrorConstantMatchesDefinition N O CE`, and `hX : LeafX O`.
- `on_core` is refactored to call `on_core_sharp` with `Jcap := fun _ => O.EJ`, verifying backward compatibility (`8 + 17 = 25` and `12 + 32 = 44` recover `4 C² + 25 C + Cb + 44` verbatim).

#### **B. Elementary dyadic supplier for the actual `Wts.Jrec7`**

In DyadicJrec7.lean:

- `dyadicBracket`:  &#x20;
  ```
  lean
  ```
  def dyadicBracket (L Λ lk : ℝ) : ℝ :=

  &#x20; 8 \* L \* Real.log L + 14 \* L + 8 \* Λ ^ 2 + 41 \* Λ + 309 / 4 + 2 \* (1 + lk) \* (L + 7 / 10)

  with `Λ = Real.log (8 * P.k * P.t)` and `lk = Real.log P.k` (replacing the coarse `30 * L²` via elementary Chebyshev `chebyshevThetaElementary_holds`, dyadic binning in `smallPrimeSumDyadic_holds` and `largePrimeSumDyadic_holds`, and harmonic telescoping in `sum_gateTerm_mul_log_le_sharp`).
- `recursion_sum_exceptional_dyadic` (**pre-collapse**):     &#x20;
  - Bounds `∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log l ≤ totalBound P W.T2.card (P.m * P.b * dyadicBracket P.L Λ lk)`.
  - Keeps all three `totalBound` tail terms explicit—nothing is forced into `2 m b`.
- `sum_jrec7_log_le_of_cut_dyadic` (**under `Rows` + `Big`**):     &#x20;
  - Bounds `∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log l ≤ W.T2.card * (P.m * P.b * dyadicBracket P.L Λ lk) + 2 * P.m * P.b`.
  - Collapses **only** the three `totalBound` tail terms already proved `≤ 2 m b` by the source's `LargeParameterEstimates.sum_of_small_terms_bound`, while keeping `T2.card * m * b * dyadicBracket(...)` uncollapsed.

#### **C. Integrated `on_core_sharp` + actual `Wts.Jrec7` bridge**

In OnCoreSharpJrec7.lean:

- `jrec7DyadicCap` / `leafJSumCap_of_jrec7` / `on_core_sharp_of_jrec7`: wires `hJp : ∀ j l, O.Jp j l = ((Wj j).Jrec7 (Pj j) l : ℝ)` directly into `on_core_sharp` with pre-collapse `jrec7DyadicCap (Pj j) (Wj j).T2.card`.
- `jrec7DyadicCapRows` / `leafJSumCap_of_jrec7_of_rows` / `on_core_sharp_of_jrec7_of_rows`: same integration under per-row `Rows` + `Big`.

---

### **3. Remaining Hypotheses & Scope Notes**

1. **In `on_core_sharp`:** Keeps the existing `OnObj` leaf hypotheses (`RankRows`, `LeafMackey`..`LeafBad`, `LeafJExp`) unchanged, replaces `LeafJSum O` with `LeafJSumCap O Jcap`, and eliminates `CE`, `hCE`, `ErrorConstantMatchesDefinition`, and `LeafX`.
2. **In `on_core_sharp_of_jrec7`:** Takes the exact per-row `Jrec7` supplier inputs matching `ExpansionOfNumericsModel.hasExpBound_at`:     &#x20;
   - `hCut : Formalism.CohomologicalDescent.E.ExCut` (already proved in the Nov 20 release as `GlobalTheory.LeviCut.exCut` in `WeylLatticeExactExponentBlockCut.lean`; kept explicit here just as in `SumExponentLogLeOfCut`, `ExcSet`, and `ExpansionOfNumericsModel`),
   - per-row `(Pj j).Hyp`, `(Pj j).Large`, `(Wj j).Ok (Pj j)`, `Fintype.card (ι j) = (Pj j).f`, `(Wj j).Sp.card ≤ 5`, and `hJp : ∀ j l, O.Jp j l = ((Wj j).Jrec7 (Pj j) l : ℝ)`.
   - Note that the fixed per-row prime terms in `O.Bad = {g1, g2, q1, dd} ∪ O.sm` stay in `O.Cb * O.B0` (via `LeafBad`), and in `on_core_sharp_of_jrec7` the `totalBound` tail terms remain uncollapsed; `on_core_sharp_of_jrec7_of_rows` adds per-row `Rows` and `Big` to discharge only the `totalBound` tail `≤ 2 m b`.
   - Note also: in the live `ExcSet` caller, `W.Sp = D.host.small ∪ {q, d, pde, pde'}` is first reduced to `W'.Sp = {q, d, pde, pde'}` (card `≤ 4 ≤ 5`) by `ExcSet.sum_exponent_log_le`, so downstream wiring passes that reduced `W'` (with `D.host.small` already accounted for in `O.Bad` / `small_le_lJ`).
3. **Lean 4.33.1 → 4.36.0 compatibility patches (disposable copy only):** To build the Nov 20 dependency closure on Lean 4.36.0, 98 upstream `.lean` files received mechanical Mathlib API port edits only (`Submodule.IsLattice` → `Submodule.IsFullLattice`, `MvPolynomial.coeff` dot-notation / `coeff_zero` / `coeff_add`, `Finsupp.coe_finsetSum` / `finsetSum_apply` / `mapDomain_apply_of_injective`, `Polynomial.finsetSum_coeff`, `Set.mem_finsetProd`, `Prime.dvd_finsetProd_iff`, `padicValNat` → `multiplicity`, `Real.posLog_le_posLog` `-1 ≤ x`, `MultilinearMap` `RingHom.id`, `PiLp.single_apply`/`norm_single`, `maxRecDepth`/`whnf` guards in `CountSuccLe`/`WorkedExample`/`FockQRowDivAdj`/`Wlocal`).
4. **Stopped before `ErrX5at` and `UBar5`**, left for your downstream pass.

---

### **4. Verbatim `#print axioms` Output (Lean 4.36.0)**

```
text
```

'Formalism.L2.Indef.Tree.on_core_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]

'Formalism.L2.Indef.Tree.on_core' depends on axioms: [propext, Classical.choice, Quot.sound]

'Formalism.CohomologicalDescent.DyadicJrec7.recursion_sum_exceptional_dyadic' depends on axioms: [propext,

&#x20;Classical.choice,

&#x20;Quot.sound]

'Formalism.CohomologicalDescent.DyadicJrec7.sum_jrec7_log_le_of_cut_dyadic' depends on axioms: [propext,

&#x20;Classical.choice,

&#x20;Quot.sound]

'Formalism.L2.Indef.Tree.on_core_sharp_of_jrec7' depends on axioms: [propext, Classical.choice, Quot.sound]

'Formalism.L2.Indef.Tree.on_core_sharp_of_jrec7_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
