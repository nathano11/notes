# Reimann proof checkpoints

The ordinary-zeta work has a Lean project and a declaration-by-declaration verifier. Open the folder containing `lean-toolchain` in VS Code. The original submission pins Lean **4.33.1**. The seven modules tracked by `checkpoints.py` use only Lean's bundled standard library.

The original seven-module Lake target built on **Lean 4.36.0**, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The original package includes the per-declaration results in `verification.json` and the output of `#print axioms` for all 90 theorem declarations in `axiom-audit.txt`. Of these, 65 have no axiom dependencies. The remaining 25 use only Lean's standard `propext`, `Classical.choice`, or `Quot.sound`. The current full `ReimannWindow` Lake target, including the dyadic imports and the new conductor-69 residue theorems, has since built on both 4.36.0 and the pinned **4.33.1**. A complete 4.33.1 per-declaration replay of the original seven-module suite remains separate. The new formal conductor-69 modules have source-matched ledgers on both compilers. See [the conductor-69 proof status](formal/PROOF_STATUS.md#circular-unit-specialization-at-conductor-69).

## Running a breakpoint

```powershell
python checkpoints.py --list
python checkpoints.py --check-version 4.36.0 --through Baseline.character_filter
python checkpoints.py --check-version 4.36.0 --module BottomUnit --through BottomUnit.resultantOne
python checkpoints.py --check-version 4.36.0
```

Omit `--check-version` for the 4.33.1 replay. The runner elaborates the source up to each declaration and stops at the first error. Warnings are fatal. Each pass records the source-prefix digest, compiler version and compiler digest. Rerunning the command resumes at the first unmatched checkpoint. `--fresh` forces a replay. A successful result for one compiler version cannot satisfy a checkpoint for another.

## What the modules establish

| Module | Checked proposition or calculation | Next mathematical dependency |
|---|---|---|
| Baseline | The signed-character identity, its four signs, the cubic discriminant and the small modular calculations from the original checkpoint | Interpret the character filter in the analytic window and the cubic as a Galois extension |
| BottomUnit | Conjugate multiplication, monic polynomial division, Sylvester determinant 1, the three reductions modulo 9, their norms and a nonzero minor modulo 3 | Identify these computations with norms at the three completions and apply the ambiguous class number formula |
| FirstLayer | Exhaustive counts of reduced pairs and first-return cycles for seven discriminants, plus the explicit norm-one Pell solution and split residues | Identify reduced cycles with ordinary ideal classes and implement the prime-to-3 descent |
| LocalConditions | Vanishing of first torsion propagates to every power. Integral identities cancel the local coefficients at 3 and 277. A nontrivial residue projection excludes a power with the specified order condition. A nonzero coordinate generates its whole line modulo 277 | Derive the scalar conditions from localization and reciprocity, and identify the coordinates with the actual unit lines |
| Prime277 | Four complete Stickelberger residue rows for weights 1–274, the exceptional residue 275 and the split-unit arithmetic. The trial-divisor bound implies the divisor definition of primality for 277, 114679 and 649843 | Connect the integral annihilator and the reflected Kummer component to the class group in Lean |
| CircularUnits | The binary powering algorithm equals ordinary exponentiation modulo every natural modulus. Finite-field logarithm witnesses, the zero sets at the first residue prime, witnesses at the second, the true-conductor term and coverage of all 551 nontrivial characters | Identify the sums with reductions of projected circular units, prove saturation and import or prove Greither's class-group comparison |
| Window | A cyclic exponent list satisfies the truncation bound, and a prime-dependent depth allocation satisfies a finite sum inequality over dyadic blocks | Supply bounds for the actual strict groups, account for the remaining powers and primes, and prove the asymptotic budget for the selected fields |

The numerical calculations and elementary implications have separate names in Lean. In particular, `CircularUnits.all_551_character_checks` concludes an assertion about finite lists and evaluations. The paper conclusion about the class group requires the intervening theorems in the right column. These distinctions also apply to computations independently reproduced by the Python scripts.

For the conductor-69, tame-exponent-zero row, the formal project now identifies the signed products with the two quadratic period expressions and excludes a 277th root in the integral presentation after adjoining a primitive 277th root. Its explicit degree-22 multiplication matrix gives the labeled positive product, and the change of 44 coordinates has a two-sided integer inverse. The field-norm application still needs the standard cyclotomic power basis instantiated for the actual number field. [Conductor-69 declarations and arithmetic inputs](formal/PROOF_STATUS.md#signed-product-relative-determinant-and-nonpower)

## Breakpoints for the arithmetic argument

1. **Specialize the source definitions.** The release defines `Formalism.GaloisCohomology.qzTw`, `Sha` and `shaLen` in `src/Formalism/GaloisCohomology/Statement.lean`. The kernel used there is `ReciprocityTheory.Gal.Sha1` in `src/ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean`. Instantiate the selected field, cyclotomic character, primes and localization maps. Identify the complementary eigenspace with `UpperTheory.V.ShaPlus`, defined in `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean`.
2. **Pass to finite coefficients with the local conditions intact.** At a nontrivial tame twist, prove the local and global invariant groups vanish. At a trivial tame twist, compute the local connecting homomorphisms. They are the reason two split primes require the unit calculation.
3. **Descend the strict characters.** Trace the release theorem `UpperTheory.V.Kum.shaZm` in `GaloisLibrary/KummerTheory/ShaFrom.lean`. It supplies the class-character comparison in twist zero under its hypotheses. Prove compatibility with restriction, the coefficient twist and the chosen complex conjugation over the field where the coefficients become trivial. Identify the required ordinary or localized class-character summand.
4. **Interpret the numerical certificates.** At 3 this requires the cubic-unit norm computation, the class group in the first cyclotomic cubic layer, the reduced-ideal classification, and the split local boundary. At 277 it requires the character decomposition of the ordinary unit lattice, circular-unit norms, equivariance of their reductions, and the class-number comparison. Section 3 of the paper gives an alternative Stickelberger argument with its own arithmetic inputs.
5. **Prove the fixed-field statements at all weights.** Combine these specialized arithmetic lemmas with the finite checks and the passage from first torsion to every power. Verify the exact field and the choice of sign in the resulting theorem.
6. **Return to the moving window.** The release's `UpperTheory.V.Kum.plusLen_le_of_cl` uses bounds at cofinally many cyclotomic levels. The window ranges over all relevant primes and weights for the same selected auxiliary data. A single example at 3 or 277 supplies no cofinal or uniform bound. The estimate for the omitted prime powers and the end-to-end deduction remain open.

Each item above requires its own Lean declarations before it can be used as a completed formal step. The supplied modules do not declare these open obligations as axioms. The original dyadic Iwasawa presentation, interpolation, and the full signed-twist selection argument in the previous notes also require their own formal proofs.
