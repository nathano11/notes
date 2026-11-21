# Results of the frozen predictions, 2026-11-21

Every prediction in `PREDICTIONS_STAGE_A.md` and `PREDICTIONS_STAGE_B.md` was
tested as declared. None failed. The statements and proofs are in
`../Dyadic_Residue_Shape.md`.

## What was frozen, and when

| file | SHA-256 | recorded | before |
|---|---|---|---|
| `PREDICTIONS_STAGE_A.md` | `135df69a88761eafd4c6f89a1b73e409d9ac116f29d23b2b840803dbf020726c` | 2026-11-21T14:39:28 | any test code existed |
| `PREDICTIONS_STAGE_B.md` | `f7e33af1c06863343615cf4ab4336a865c150ee14d4fcbea60a25398eee46400` | 2026-11-21T15:00:51 | any ideal-class code was run |

The ledger is `freeze_ledger.txt`. Neither file was edited afterwards.

Test set: all 14,022 pairs (q, d) with q ≡ 3 (mod 8), d ≡ 7 (mod 16) and
5000 < qd < 10^6. In sample, and never counted as a test: Mizusawa's 101 pairs
below 5000 and the project fields (3,7), (3,23), (11,263).

Stage B predicts individual fields. Its three out-of-sample fields are the pair
of smallest qd above 5000 of each shape, as declared in Stage A before they
were known: (227,23) shape I, (739,7) shape IIa, (11,503) shape IIb.

## Stage A

| item | prediction | test | result |
|---|---|---|---|
| S1 | (q/d) = −1 ⟹ (C_0, C_1) ≡ (2, 0) mod 4 | Stickelberger row at level 10, C_0, C_1 mod 512 (`scan_shape.py`) | 7038 pairs, 0 exceptions |
| S2 | (q/d) = +1 ⟹ (C_0, C_1) ≡ (0, 2) mod 4 | same | 6984 pairs, 0 exceptions |
| S3 | class numbers h(−4m), h(−8m) mod 8 and mod 16 | reduced binary forms, no L-values (`check_class_numbers.py`) | 14,022 pairs, 0 exceptions; equal to 2Φ(0), 2Φ(−2) for every pair |
| S4 | weight profile (k, l, h) at r = 1 | Bernoulli sums of Appendix A.3 only, class numbers by reduced forms, first 150 pairs in increasing qd, 5173 to 13909 (`check_weight_profile.py`) | 80 pairs (1,1,3); 34 pairs (2,2,2); 36 pairs with k, l ≥ 3 and h = 2; 0 exceptions |
| S5 | 2-class groups of Q(√2, √−m) and of F' = Q(√(−m(2+√2))) | explicit ideals, principal-ideal tests (`test_quartic.py`) | all ten groups as predicted, table below |
| S6 | (q/d) = −1 ⟹ A(k_2) ≅ C_2 ⊕ C_4 ⊕ C_8 | degree-8 field, explicit ideals (`test_layer2_group.py`) | (227,23): order 64, factors [2, 4, 8] |

S6 also states the ratio law |A(k_{n+1})|/|A(k_n)|. On the whole test set that
is a consequence of S1 to S3 and the analytic class number formula; it was not
tested separately beyond the five fields below.

## Stage B: five fields, quartic and degree-8 class groups

Predicted from the analytic side only (C_0, C_1 to 13 binary digits), then
computed with ideals. "found" is the invariant-factor list of the 2-class group.

| field | shape | A(Q(√2,√−m)) predicted / found | A(F') predicted / found | A(k_2) predicted / found |
|---|---|---|---|---|
| (3,23), m = 69 | IIa | [2,4,4] / [2,4,4] | [2,2,2] / [2,2,2] | [2,8,8] / [2,8,8] |
| (11,263), m = 2893 | IIb | [2,8,8] / [2,8,8] | [2,2,2] / [2,2,2] | [2,16,16] / [2,16,16] |
| (227,23), m = 5221 | I | [2,2,2] / [2,2,2] | [2,2,4] / [2,2,4] | [2,4,8] / [2,4,8] |
| (739,7), m = 5173 | IIa | [2,4,4] / [2,4,4] | [2,2,2] / [2,2,2] | [2,8,8] / [2,8,8] |
| (11,503), m = 5533 | IIb | [2,4,32] / [2,4,32] | [2,2,2] / [2,2,2] | [2,8,64] / [2,8,64] |

In every case the group found has the order given by the analytic class number
formula, and the classes of the ramified primes generate a subgroup of order 8
in the quartic fields. In k_2 the class of the prime above 2 has order two and
the quotient by it has the predicted factors [8,8], [16,16], [4,8], [8,8],
[8,64] (`layer2_group_run.log`).

### The marked relation at layer two

For a prime 𝔭 of degree one in k_2 let c be the 2-part of its class. The
prediction is the exact set of pairs (a, b) modulo the exponent E with
γ²c + aγc + bc ∈ {0, [𝔭_2]}, where γ is the automorphism ζ ↦ ζ^5; on a class
that generates the module over Λ this set is {(−τ, Δ)} up to the listed
ambiguity. All E² pairs were tried for each prime (`test_layer2.py`).

| field | E | predicted set | primes where the set found is equal | primes where it is larger |
|---|---|---|---|---|
| (3,23) | 8 | {(4,7)} | 17, 79, 113 | 47 |
| (11,263) | 16 | {(0,7)} | 47, 191, 193, 241 | none |
| (227,23) | 8 | {(2,3), (6,7)} | 17, 79 | 31, 127 |
| (739,7) | 8 | {(0,3)} | 31, 97 | 113, 127 |
| (11,503) | 64 | 8 pairs: (4,43), (12,3), (20,27), (28,51), (36,11), (44,35), (52,59), (60,19) | 17, 31 | 79 |

A larger set occurs exactly when the class of the prime does not generate the
module (its order is smaller, or it lies in a proper submodule); the predicted
set is contained in it every time, as it must be. No prime gave a set that
misses a predicted pair. The value was 0, not [𝔭_2], in every solution.

For 2893 this is the marked relation asked for in the brief: γ² ≡ 9 on the
2-class group of k_2 modulo ⟨[𝔭_2]⟩, that is (a, b) = (0, 7) modulo 16, the
only one of 256 pairs, for four independent primes. The engine's coefficients
(4776, 2834) mod 2^13 reduce to the project's (40, 18) mod 64.

Orientation. Replacing γ by its inverse changes (a, b) = (−τ, Δ) to
(−τ/Δ, 1/Δ). For (227,23) that pair is (6, 3), which is not in the set found:
there the test confirms the forward generator ζ ↦ ζ^5 acting on ideal classes
and excludes its inverse. For the other four fields the inverse pair lies in
the predicted set, so layer two cannot tell the two orientations apart. For
2893 in particular the orientation is not decided here: with r_0 ≡ 7 and
r_1 ≡ 3 (mod 8) the two orientations give Δ ≡ 23 and Δ ≡ 7 (mod 32), so they
first differ at layer three (degree 16), which was not computed.

## Checks of the consolidation (not predictions)

`check_tree.py` (log `tree_run.log`), all assertions pass:

* Smith form against content and the form n: 20,000 random integer cases.
* Theorem 6, the ideals of Corollary 8, the path of the vertex, the zeros and
  the conductor formula: 400 + 400 + 600 random coefficient pairs of shapes I,
  IIa, IIb and 300 of class (2,2) at 40 binary digits; 109,200 + 23,400 cases.
  Class (0,0) mod 4, excluded from Theorem 6: comparison with A.2 only.
* The 14,022 test fields at 9 digits: 350,659 cases decided, 98,045 not decided
  at that precision, no disagreement. Shapes: 7038 I, 3539 IIa, 3445 IIb.
* (3,7), (3,23), (11,263), (227,23), (739,7), (11,503) at 13 digits.
* Wheel sizes 3·2^{n−1}; v_2(F_k) for k < 12288; rank of apparition and Pisano
  period of 2^n for n ≤ 12; the group turning wheel n for n ≤ 7; the golden
  unit of (3,23), φ = 772 + 1053·(T/2) mod 2^11.

## Lean

| module | breakpoints | Lean 4.36.0 (611c117b) | Lean 4.33.1 (819816b2) |
|---|---|---|---|
| `Reimann/DyadicResidueShape.lean` | 28 | all checked | all checked |
| `Reimann/DyadicContent.lean` | 22 (20 ledger keys) | all checked | all checked |
| `Reimann/DyadicShapeBridge.lean` | 6 | all checked | all checked |

Ledgers: `../formal/compat-<version>-<module>.json`. Axioms reported: propext,
Classical.choice, Quot.sound. Combined target `lake --rehash build` on 4.36.0:
494 jobs, passed (`lake_combined_4.36.0_phase2.log`). The combined target was
not run on 4.33.1; on that version the three modules and the dependency closure
of the bridge were built and replayed (`lean_replay_phase2.log`).

## Commands

    python shape_engine.py                       # self-test of the engine
    python scan_shape.py 5000 1000000 10 scan_5000_1e6.csv
    python check_class_numbers.py
    python check_redei_symbols.py
    python check_weight_profile.py scan_5000_1e6.csv 150
    python predict_stage_b.py                    # writes the Stage B file
    python test_quartic.py 227 23 739 7 11 503 3 23 11 263
    python test_layer2.py 3 23 8 4               # q d E primes; likewise 11 263 16, 227 23 8, 739 7 8, 11 503 64 3
    python test_layer2_group.py 227 23           # likewise 3 23, 739 7, 11 263, 11 503
    python check_tree.py scan_5000_1e6.csv
    cd ../formal
    python checkpoint.py --compat-version 4.36.0 --lean <path to lean 4.36.0> --module DyadicContent
    elan run leanprover/lean4:v4.36.0 lake --rehash build

Python 3.14.0, numpy 2.3.5, no other package. Class groups of CM fields are
computed by `cm_classgroup.py`: an ideal 𝔞 with 𝔞𝔞̄ = (ν), ν totally positive,
is principal exactly when the form Tr(αᾱ/ν) on 𝔞 has minimum [K⁺:Q]; exact
integer LLL and Fincke–Pohst enumeration. Logs: `class_numbers_run.log`,
`weight_profile_run.log`, `quartic_run.log`, `quartic_rerun.log`,
`layer2_run.log`, `layer2_group_run.log`, `tree_run.log`.

## What did not hold, and what was corrected

No frozen prediction failed. Four working conjectures of mine were discarded
or corrected; none was in a frozen file:

1. "The second digit of (C_0, C_1) is also a congruence condition on d." False.
   On the test set the four values modulo 8 occur 1722 : 1785 : 1707 : 1824 in
   shape I and 1757 : 1688 : 1729 : 1810 in shape II. For q = 3 and q = 11,
   every residue class of d modulo 16q, 32q, 64q and 128q that contains at
   least two test fields (with the Legendre symbol fixed) contains two
   different values. Corrected claim: only the first digit pair is a
   congruence wheel (`../Dyadic_Residue_Shape.md` §2).
2. "γ^{2^a} fixes exactly the ball of radius a + 1 around x in shape IIa."
   False: γ² already fixes the ball of radius 1 + v(τ) ≥ 3. Corrected claim:
   Z_2[γ^{2^a}] = Z_2 + 2^{a−1+v(τ)}O for a ≥ 1, in every shape (§7).
3. "φ sweeps each wheel exactly once." False from wheel 3 on: the orbit of φ on
   wheel n has 3·2^{n−2} of its 3·2^{n−1} vertices. Corrected claim in §8(d).

4. "Layer two cannot see the orientation of γ." False for (227,23), true for
   the other four fields; see the paragraph on orientation above.

One computational fault: the first ideal-class runs in degree 8 stalled because
a naive Hermite reduction let integer entries grow without bound. Reducing
modulo the ideal norm fixed it; the quartic test, rerun with the new code,
gives identical groups in 3 seconds instead of 11 minutes
(`quartic_rerun.log`).

Not done: layer three; any computation in rank three (the module H upstairs);
a formal proof of the class-field inputs of Theorem 1.
