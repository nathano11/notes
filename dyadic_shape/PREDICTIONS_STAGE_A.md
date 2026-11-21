# Stage A predictions, fixed before any computation on the test set

Written 2026-11-21, before `shape_engine.py`, `scan_shape.py` or any class-number
code in this directory existed or had been run. The SHA-256 of this file is
recorded in `freeze_ledger.txt` before the first test run. This file is not
edited afterwards; corrections go in `RESULTS.md`.

## Family and notation

Pairs of primes (q,d) with q ≡ 3 (mod 8), d ≡ 7 (mod 16); m = qd;
k = Q(√−m); k_n the layers of the cyclotomic Z_2-extension; γ the generator
acting on 2-power roots of unity by ζ ↦ ζ^5. Mizusawa's polynomial
P(T) = T² + C_1 T + C_0 = det((1+T) − γ | X(k_∞)/torsion), C_0, C_1 ∈ 2Z_2
(J. Théor. Nombres Bordeaux 22 (2010), Theorem 2.2), and (P) = (Φ) with
L_2(u,ψ) = 2Φ(5^u − 1), ψ the character of Q(√m).
Project notation (Prime_Power_Window.md, Appendix A): τ = 2 − C_1,
Δ = 1 − C_1 + C_0, f(Z) = P(Z − 1), s = 5^{−r}, k = v(f(s)), l = v(f(−s)),
h = v(f(is) f(−is)).

## What was known when this was written (in sample)

* Mizusawa's Example (p. 134): for qd < 5000 only, 48 pairs with (q/d) = −1
  have P ≡ T² + 2 (mod 4) and 53 pairs with (q/d) = +1 have P ≡ T² + 2T (mod 4).
  Stated there as a numerical observation.
* Project fields: (3,7), (3,23), (11,263).

Nothing else was computed. The statements below were derived by hand from
Rédei matrices over Q(√2) (argument recorded in `../Dyadic_Residue_Shape.md`).

## Test set (out of sample)

T1: every pair in the family with 5000 < qd < 1 000 000.
None of these pairs lies in Mizusawa's range or among the project fields.

## Predictions

S1. If (q/d) = −1 then C_0 ≡ 2 and C_1 ≡ 0 (mod 4). No exception in T1.

S2. If (q/d) = +1 then C_0 ≡ 0 and C_1 ≡ 2 (mod 4). No exception in T1.

S3. Class numbers of imaginary quadratic fields, tested by counting reduced
forms (no L-function code involved):
  (a) (q/d) = −1 ⇒ h(−4m) ≡ h(−8m) ≡ 4 (mod 8).
  (b) (q/d) = +1 ⇒ 8 | h(−4m), 8 | h(−8m) and h(−4m) ≡ h(−8m) (mod 16).

S4. Weight profile at r = 1, computed directly from generalized Bernoulli
sums (formula of Appendix A.3, independent of P), on the first 150 pairs of T1
in increasing qd:
  (q/d) = −1 ⇒ (k,l,h) = (1,1,3);
  (q/d) = +1 and h(−4m) ≡ 8 (mod 16) ⇒ (k,l,h) = (2,2,2);
  (q/d) = +1 and 16 | h(−4m) ⇒ k ≥ 3, l ≥ 3, h = 2.
Consequently the strict groups A_{2,r}(E_a), r odd, are
  (q/d) = −1: 0, C_2, then C_{2^a} ⊕ C_{2^a} for a ≥ 2, for every pair and weight;
  (q/d) = +1, h(−4m) ≡ 8 (16): C_{2^a} ⊕ C_{2^{a+1}} for every a ≥ 0 and weight
  (C_1 ⊕ C_2 at a = 0).

S5. Structure of 2-class groups of two quartic fields over Q(√2), with
x = v_2(h(−4m)) − 1, y = v_2(h(−8m)) − 1:
  A(Q(√2,√−m)) ≅ C_2 ⊕ (C_{2^x})²                       if x = y,
  A(Q(√2,√−m)) ≅ C_2 ⊕ C_{2^{min(x,y)−1}} ⊕ C_{2^{max(x,y)+1}}  if x ≠ y;
  for F' = Q(√(−m(2+√2))) (cyclic quartic, conductor 16m):
  A(F') ≅ C_2 ⊕ C_2 ⊕ C_4 if (q/d) = −1, and (C_2)³ if (q/d) = +1.
In particular the 4-rank of A(Q(√2,√−m)) is 0 or 2 according to (q/d) = −1 or +1,
and h_2(F') = 16 or 8.
To be tested by explicit ideal-class computation on the pair of smallest qd > 5000
of each of the three types [(q/d) = −1], [(q/d) = +1, h(−4m) ≡ 8 (16)],
[(q/d) = +1, 16 | h(−4m)], whichever pairs those turn out to be.

S6. Layer-two orders: (q/d) = −1 ⇒ |A(k_2)| = 64 and A(k_2) ≅ C_2 ⊕ C_4 ⊕ C_8;
ratios |A(k_{n+1})| / |A(k_n)| are 2, 8, 4, 4, 4, … ; for (q/d) = +1 they are
2^{y}, 4, 4, 4, … (y as in S5).

## What would count as failure

Any pair in T1 violating S1, S2 or S3; any tested pair violating S4, S5.
A failure is to be recorded in `RESULTS.md` with the pair and the corrected claim.
