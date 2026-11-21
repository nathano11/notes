# The residue shape of the dyadic towers

Status, 2026-11-21. Paper proof of Theorem 1 below, with every elementary
identity in it machine-checked on 14,123 pairs and its two conclusions tested
on 14,022 pairs that were fixed in advance and had never been computed
(`dyadic_shape/PREDICTIONS_STAGE_A.md`, hash in `dyadic_shape/freeze_ledger.txt`).
The class-field inputs are not formalized; their exact obligations are in
`formal/PROOF_STATUS.md`. Lean kernels: `formal/Reimann/DyadicResidueShape.lean`.

Sections 6 to 9 consolidate the strict groups of all layers and weights into
one rule (Theorem 6) and one picture (a tree with three kinds of motion). Their
algebra is checked in `formal/Reimann/DyadicContent.lean` and numerically by
`dyadic_shape/check_tree.py`; section 10 says what is proved, what is tested
and what is only an analogy.

Notation is that of `Prime_Power_Window.md`, Appendix A: primes q ≡ 3 (mod 8),
d ≡ 7 (mod 16), m = qd, k = Q(√−m), k_n its cyclotomic layers,
P(T) = T² + C_1T + C_0 Mizusawa's polynomial for the generator γ ↔ 5,
τ = 2 − C_1, Δ = 1 − C_1 + C_0, f(Z) = P(Z−1), s = 5^{−r}.

## 1. Statement

**Theorem 1 (residue shape).** For every pair (q,d) in the family,

* (q/d) = −1 ⟹ C_0 ≡ 2 and C_1 ≡ 0 (mod 4), so P ≡ T² + 2 (mod 4);
* (q/d) = +1 ⟹ C_0 ≡ 0 and C_1 ≡ 2 (mod 4), so P ≡ T² + 2T (mod 4).

Mizusawa records exactly this for qd < 5000 as a numerical observation
(J. Théor. Nombres Bordeaux 22, p. 134) and proves the statements about C_0.
The new content is the congruence for C_1, for all pairs.

*Equivalent classical forms, and earlier work.* Given Mizusawa's theorem and
the analytic class number formula, the two halves of the C_1 statement say:

* (q/d) = +1: 16 divides h(−4qd) exactly when 16 divides h(−8qd);
* (q/d) = −1: the cyclic quartic field Q(√(−qd(2+√2))) of conductor 16qd has
  2-class number 16. (When (q/d) = +1 it is 8, whatever C_1 is.)

Congruences modulo 16 between h(−4pq) and h(−8pq) for pq ≡ 1 (mod 4) were
studied by K. Hardy and K. S. Williams in the 1980s (for instance
"Congruences modulo 16 for the class numbers of complex quadratic fields",
J. Number Theory, 1987). I found these references by a search on 2026-11-21 but
could not read them (scanned pages), so I do not know whether the first form
is covered there for q ≡ 3 (mod 8), d ≡ 7 (mod 16). It may be a known
congruence reached here by a different route. I found no source for the second
form; the search was not exhaustive. "New" in this document means: not in
Mizusawa's paper, where it is an observation.

**Corollary 2 (the table of Appendix A.2 has only two rows).** For every odd
weight r:

* (q/d) = −1: (k,l,h) = (1,1,3). The strict group A_{2,r}(E_a) is
  0, C_2, and C_{2^a} ⊕ C_{2^a} for a ≥ 2. It depends on nothing but a.
* (q/d) = +1: k,l ≥ 2 and h = 2, so A_{2,r}(E_a) ≅ C_{2^{m+a−2}} ⊕ C_{2^{M+a−1}}
  for a ≥ 1 with m = min(k,l), M = max(k,l), and C_{2^{k−1}} at a = 0.
  Moreover k = l = 2 for every odd r exactly when h(−4m) ≡ 8 (mod 16);
  then the groups are C_{2^a} ⊕ C_{2^{a+1}} for all a ≥ 0.

*Proof.* Insert Theorem 1 in A.2. In the first case τ ≡ 2, Δ ≡ 3 (mod 4), so
u = s² − Δ and τ both have valuation one and h = 3. In the second τ ≡ 0,
Δ ≡ 3 (mod 4), so 1 + Δ ≡ τ (mod 4), which is the criterion k,l ≥ 2 of A.2.
Finally P(s−1) ≡ 8 + C_0 (mod 16) and P(−s−1) ≡ C_0 (mod 8) when C_1 ≡ 2 (mod 4),
and h(−4m) = 2Φ(0) = 2C_0·(unit). ∎

**Corollary 3 (class numbers).** If (q/d) = +1 then
h(−4qd) ≡ h(−8qd) (mod 16), both divisible by 8. If (q/d) = −1 both are
≡ 4 (mod 8). (h(−8m) = 2Φ(−2) = 2P(−2)·unit and P(−2) = C_0 − 2C_1 + 4.)

**Corollary 4.** The hypothesis "C_1 ≡ 0 (mod 4)" in Mizusawa's Proposition 4.3 and Lemma 4.4 holds
for every pair with (q/d) = −1. Hence A(K_n) ≅ (Z/2^n)³ and |G(k_n)| = 2^{3n+2}
for all n ≥ 2 and all such pairs, with K = k(√q,√d).

**Corollary 5 (two quartic fields over Q(√2)).** Put x = v_2(h(−4m)) − 1,
y = v_2(h(−8m)) − 1 and F' = Q(√(−m(2+√2))), the cyclic quartic field of
conductor 16m in k_2. Then

* A(Q(√2,√−m)) ≅ C_2 ⊕ (C_{2^x})² if x = y, and
  C_2 ⊕ C_{2^{min−1}} ⊕ C_{2^{max+1}} otherwise;
* A(F') ≅ C_2 ⊕ C_2 ⊕ C_4 if (q/d) = −1, and (C_2)³ if (q/d) = +1;
* A(k_2) ≅ C_2 ⊕ C_4 ⊕ C_8 if (q/d) = −1.

## 2. The shape

Write O = Z_2[T]/(P). The torsion-free quotient of X(k_∞) is O, with γ acting
as 1+T (Mizusawa: γb = bc, so c = Tb). The dual strict group is 𝔪/ω_{a,r}O with
𝔪 = (2,T) and

    ω_{a,r} = (1+T)^{2^a} − s^{2^a} = ∏_{ζ^{2^a} = 1} (1 + T − ζ s).

So a strict group is a product over the 2^a spokes ζ of a wheel; the weight
moves a point s = 5^{−r} along each spoke, and each spoke contributes the
distance from that point to the two zeros of f. Theorem 1 says the zero pair
has one of three shapes, and the first split is a single Legendre symbol:

| shape | condition | O | zeros of f | spokes ±1 | ring ±i | every outer ring |
|---|---|---|---|---|---|---|
| I (Eisenstein) | (q/d) = −1 | ramified DVR, uniformizer T | conjugate, \|Z−1\| = 2^{−1/2}, in Q_2(√±2) or Q_2(√±6) | 1, 1 | 3 | 2 |
| IIa (inert) | (q/d) = +1, h(−4m) ≡ 8 (16) | Z_2 + 2W(F_4) | conjugate over Q_2(√5), \|Z−1\| = 1/2 | 2, 2 | 2 | 2 |
| IIb (split) | (q/d) = +1, 16 \| h(−4m) | Z_2 + 2(Z_2 × Z_2) | Z_0 = 5^{−r_0} on spoke +1, Z_1 = −5^{−r_1} on spoke −1 | 3 + v(r−r_0), 3 + v(r−r_1) | 2 | 2 |

Entries are the 2-adic valuations contributed by the spoke or ring.
In shape IIb each of L_2(u,ψ) and L_2(u,ψχ_8) has exactly one zero in Z_2,
at u = −r_0 and u = −r_1, and h_2(−4m) = 2^{4+v(r_0)}, h_2(−8m) = 2^{4+v(r_1)}.
In shapes I and IIa neither has a zero in Z_2.

Consequences that hold in every shape:

* **Outer wheels are rigid.** Every ring of primitive 2^j-th roots with j ≥ 3
  contributes exactly 2 (A.2, last paragraph). By Theorem 1 the ring ±i is
  rigid too. All arithmetic variation sits on the two real spokes, and only in
  shape IIb.
* **Ratio law.** |A(k_{n+1})| / |A(k_n)| is 2, 8, 4, 4, 4, … in shape I and
  2^{y}, 4, 4, 4, … in shape II. The Iwasawa formula |A(k_n)| = 2^{2n+ν} is
  exact from n = 2 (shape I, ν = 2) or n = 1 (shape II, ν = x + y − 1).
* **The first wheel is a congruence wheel.** For fixed q the shape I/II
  depends on d modulo 16q only. For q = 3: d ≡ 7 (mod 48) is shape I,
  d ≡ 23 (mod 48) is shape II.
* **The second wheel is not.** Within each shape the next digit pair
  (C_0 mod 8, C_1 mod 8) takes its four possible values with frequencies
  1722 : 1785 : 1707 : 1824 (shape I) and 1757 : 1688 : 1729 : 1810 (shape II)
  on the test set; IIa/IIb is the classical 16 | h question, governed by a
  non-abelian Frobenius class, not by a residue class of d.
* **The two zeros behave independently.** On the 3445 test pairs of shape IIb,
  the joint frequency of (v(r_0), v(r_1)) = (i, j) matches 2^{−(i+1)} 2^{−(j+1)}:
  871, 427, 418, 233 observed for (0,0), (0,1), (1,0), (1,1), against
  861, 431, 431, 215. This is a statistical observation, not a theorem.

What predicts what:

* *Strict groups, all layers, all odd weights:* (q/d); if it is +1, whether
  16 | h(−4m); if so, the two 2-adic integers r_0, r_1 to the precision
  v(r − r_i) requires.
* *Marked class action on A(k_n)/⟨[𝔭_2]⟩ ≅ O/ω_nO:* the pair (C_0, C_1) modulo
  ω_nO, about n+1 and n binary digits. Group orders and invariant factors do
  not see these digits; the relation (γ−1)² + C_1(γ−1) + C_0 = 0 does.
* *Upstairs, K_∞ = k_∞(√q,√d):* nothing further. H = X(K_∞) has basis
  α = a², β = b², c with γα = α, γβ = −α + β + 2c,
  γc = (C_1/2)α − (C_0/2)β + (1−C_1)c, from Mizusawa's relations
  ([b,c] = a², b inverts a). The commutator of b with the inertia generator
  is α − c. By Theorem 1, H is Λ-cyclic exactly in shape I: modulo 2 the
  operator γ − 1 is a single nilpotent block when C_1/2 is even and C_0/2 odd,
  and has rank one when C_1/2 is odd and C_0/2 even.

## 3. Proof of Theorem 1

The statements about C_0 are Mizusawa's: A(k) = X/TX ≅ Z/2 ⊕ Z_2/C_0, and
4 ∤ h_2(−4m)/2 exactly when (q/d) = −1. We prove the statements about C_1.

### 3.1 Three quotients of one module

X = X(k_∞) ≅ Z/2 ⊕ O as a module over Gal(k_∞/Q) = γ^{Z_2} × ⟨σ⟩, where σ is
complex conjugation. σ acts by −1, because the layers of Q_∞ have odd class
number. The prime 2 is totally ramified in k_∞/Q. Hence for any subfield M of
k_∞ with k_∞/M a Z_2-extension topologically generated by g,
A(M) ≅ X/(g−1)X (Washington, Proposition 13.22, one totally ramified prime).

* M = k_1 = Q(√2,√−m), g = γ²: A(k_1) ≅ Z/2 ⊕ O/(T(T+2)).
* M = F' = Q(√(−m(2+√2))), g = γ²σ acting as −γ²: A(F') ≅ Z/2 ⊕ O/((1+T)²+1).

In the Z_2-basis 1, T of O, the two ideals are the lattices

    L  = ⟨ (C_0, C_1−2), (0, C_0−2C_1+4) ⟩,
    L' = ⟨ (2−C_0, 2−C_1), (−C_0(2−C_1), 2−C_0−C_1(2−C_1)) ⟩.

**Lemma A** (`DyadicResidueShape.split_lattice_iff`,
`DyadicResidueShape.eisenstein_lattice_iff`). If 4 | C_0 and C_1 is even, then
L ⊆ 4Z² ⟺ C_1 ≡ 2 (mod 4). If C_0 ≡ 2 (mod 4) and C_1 is even, then
L' ⊆ 4Z² ⟺ C_1 ≡ 2 (mod 4).

A quotient Z²/L of 2-rank two has 4-rank two exactly when L ⊆ 4Z². So:

* if (q/d) = +1, then C_1 ≡ 2 (mod 4) ⟺ 4-rank A(k_1) = 2;
* if (q/d) = −1, then C_1 ≡ 0 (mod 4) ⟺ 4-rank A(F') ≤ 1.

### 3.2 Genus theory over F = Q(√2)

Let K = F(√D) be k_1 (D = −m) or F' (D = −mβ, β = 2 + √2 = √2·ε, ε = 1 + √2).
F has class number one and its totally positive units are squares. K/F is
ramified at √2, at q (inert in F), at the two primes π, π' above d, and at
both real places.

(a) σ acts by −1 on A(K), so A(K)[2] is the group of ambiguous classes. By
Chevalley's formula it has order 2^{4+2−1}/[E_F : E_F ∩ N K^×] = 2^5/4 = 8, and
since N E_K = E_F² as well, every ambiguous class contains an ambiguous ideal.
Thus A(K)[2] is generated by the classes of the four ramified primes, with the
single relation coming from (√D): for k_1 it is 𝔔_q 𝔓_π 𝔓_π' ∼ 1, for F' it is
𝔓_2 𝔔_q 𝔓_π 𝔓_π' ∼ 1.

(b) Unramified quadratic extensions of K are K(√δ) with δ in a group Δ_K of
rank 3. Write d = x² − 2y² with x, y > 0 odd, π = x + y√2, and
π* = (−1/y)·ε·π. Then N(π*) = −d and π* ≡ 1 or 3 + 2√2 (mod 4), a square
modulo 4, so F(√π*)/F is ramified at π and at no other finite prime. Therefore

    Δ_{k_1} = ⟨ −1, π*, π'* ⟩,        Δ_{F'} = ⟨ −q, π*, π'* ⟩.

(c) The character χ_δ of A(K) attached to K(√δ) is a square of a character
exactly when it is trivial on A(K)[2]. Hence 4-rank A(K) = 3 − rank(R_K) over
F_2, where R_K has rows δ in a basis of Δ_K, columns a basis of A(K)[2], and
entries χ_δ(𝔓). For a ramified prime 𝔓 over 𝔭, χ_δ(𝔓) = 1 exactly when 𝔭
splits in the quadratic subextension of F(√D,√δ)/F in which 𝔭 is unramified;
that subextension is F(√δ) or F(√(Dδ)).

### 3.3 The symbols

All are elementary; write (·/π) for the Legendre symbol in O_F/π = F_d.

1. d ≡ 7 (mod 16) forces x ≡ ±3 (mod 8), so (2/x) = −1
   (`DyadicResidueShape.x_residue`).
2. (π*/π') = (π'*/π) = (2/x) = −1. Indeed modulo π' one has √2 ≡ x/y, so
   π ≡ 2x and ε ≡ (x+y)/y; quadratic reciprocity gives (x/d) = (2/x),
   (y/d) = (−1/y), ((x+y)/d) = 1, and the sign (−1/y) contributes (−1/y) again.
3. π* is not a square in Q_2(√2): the squares of units modulo 4√2 are 1 and
   3 + 2√2 modulo (8, 4√2), and π* = (−1/y)((x+2y) + (x+y)√2) has rational
   part ≡ 5 or 7 (mod 8) (`DyadicResidueShape.pistar_nonsquare_pos`,
   `pistar_nonsquare_neg`). Equivalently,
   this is the product formula for the Hilbert symbol (π*, √2).
4. (β/π) = (β/π') = (2/x) = −1: (√2/π) = −(2/x)(−1/y) and (ε/π) = −(−1/y),
   while (√2/π') = (2/x)(−1/y) and (ε/π') = (−1/y).
5. At the inert prime q every element z of O_F has (z/q) = (N z/q). So
   (π*/q) = (−d/q) = (q/d) and (β/q) = (2/q) = −1.
6. (−1/π) = −1; √2 is inert in F(√m)/F because m ≡ 5 (mod 8), and inert in
   F(√−q)/F because −q ≡ 5 (mod 8).

`dyadic_shape/check_redei_symbols.py` evaluates each of these from its
definition for all 14,123 pairs with qd < 10^6; all hold.

### 3.4 The two matrices

Put c = 0 if (q/d) = +1 and c = 1 if (q/d) = −1; entries are in F_2,
0 for χ = +1.

For k_1 (rows −1, π*, π'*; columns 𝔓_2, 𝔓_π, 𝔓_π'), using −m·π* ≡ q·π'*
modulo squares:

    R = [ 1  1    1   ]
        [ 1  c+1  1   ]
        [ 1  1    c+1 ]

For F' (rows −q, π*, π'*; columns 𝔔_q, 𝔓_π, 𝔓_π'), using D·π* ≡ q·π'*·β and
D·(−q) ≡ d·β modulo squares:

    R' = [ 1  c+1  c+1 ]
         [ c  c    1   ]
         [ c  1    c   ]

If (q/d) = +1 then R is the all-ones matrix, of rank 1, so 4-rank A(k_1) = 2
and C_1 ≡ 2 (mod 4). If (q/d) = −1 then R' has rows (1,0,0), (1,1,1), (1,1,1),
of rank 2, so 4-rank A(F') = 1 and C_1 ≡ 0 (mod 4)
(`DyadicResidueShape.rank_split`, `DyadicResidueShape.rank_eisenstein`). ∎

The other two ranks are consistent with the module: R has rank 3 when
(q/d) = −1 (A(k_1) ≅ C_2³) and R' has rank 3 when (q/d) = +1 (A(F') ≅ C_2³).

## 4. Tests

Frozen before any computation: `dyadic_shape/PREDICTIONS_STAGE_A.md`,
SHA-256 135df69a…0726c, recorded 2026-11-21T14:39:28. Test set: all 14,022
pairs with 5000 < qd < 10^6. In sample: Mizusawa's 101 pairs below 5000 and the
project fields (3,7), (3,23), (11,263).

| test | method | result |
|---|---|---|
| engine validation (in sample) | `shape_engine.py selftest`; row from its definition; (3,7) against Mizusawa's P mod 2^15; 101 pairs below 5000 | 48 and 53, as published |
| S1, S2 residue shape | Stickelberger row at level 10, Weierstrass factor, C_0, C_1 mod 512 | 7038 pairs (q/d) = −1 all (2,0); 6984 pairs (q/d) = +1 all (0,2) mod 4; 0 exceptions |
| S3 class numbers | reduced binary forms, no L-values | 0 exceptions in 14,022; agrees with 2Φ(0), 2Φ(−2) for every pair |
| symbols of §3.3, ranks of §3.4 | `check_redei_symbols.py` | all identities, 14,123 pairs |
| S4 weight profile at r = 1 | Bernoulli sums of A.3 only, class numbers by reduced forms, first 150 pairs of the test set (`check_weight_profile.py`) | 80 pairs (1,1,3); 34 pairs (2,2,2); 36 pairs with k, l ≥ 3 and h = 2; 0 exceptions |
| S5 two quartic 2-class groups | explicit ideals and principal-ideal tests (`test_quartic.py`), smallest pair above 5000 of each shape and the two project fields | all ten groups as predicted |
| S6 and Stage B, layer two | degree-8 field k_2, explicit ideals (`test_layer2.py`, `test_layer2_group.py`) | group structure and the marked relation γ² + aγ + b = 0 as predicted in all five fields |

Python 3.14.0, numpy 2.3.5. Exact commands, logs, the Stage B file and its hash
are in `dyadic_shape/RESULTS.md`. No prediction failed.

## 5. What is and is not proved

* Theorem 1 is a paper proof. It uses Mizusawa's Theorem 2.2 (the module
  X(k_∞)), Chevalley's ambiguous class formula, and class field theory for
  quadratic extensions of Q(√2). None of these is formalized here.
* The identification (P) = (Φ) is used only to *test* Theorem 1 (via the
  Stickelberger row) and in Corollaries 2 and 3, as in Appendix A.1.
* The second-wheel statements of §2 marked "observation" are data.
* Shape IIb needs r_0, r_1; no closed rule for them is claimed.

## 6. One rule for every shape, layer and weight

Let T_1, T_2 be the roots of P in an algebraic closure of Q_2, with v(2) = 1,
and Z_i = 1 + T_i the zeros of f. An element ω of O has two values ω(T_1),
ω(T_2). Recall X = 𝔪 = (2, T) with basis (2b, c) and Y = O with basis (b, c).

**Theorem 6 (valuation rule).** Let C_0, C_1 ∈ 2Z_2 with
(C_0, C_1) ≢ (0, 0) (mod 4), and let ω ∈ 𝔪 be a non-zero-divisor. Let
ν_min ≤ ν_max be the valuations of ω(T_1) and ω(T_2). Then

    𝔪/ωO ≅ C_{2^{e_1}} ⊕ C_{2^{e_2}},     e_1 = ⌈ν_min⌉ − 1,     e_2 = ⌊ν_max⌋.

By Theorem 1 the hypothesis holds for every pair of the family. For
ω = ω_{a,r} the two valuations are sums over the spokes,

    ν_i = Σ_{ζ^{2^a} = 1} v(Z_i − ζ·5^{−r}),

so a strict group is read from the distances of the two zeros to the 2^a marked
points: round the smaller total up and subtract one, round the larger down.

*Proof.* Write ω = A + BT with A even, and (A/2, B) = g·(a, b) with (a, b)
primitive. In the bases (1, T) of O and (2, T) of 𝔪 the matrix of ω is
g·[[a, −cb], [b, 2a − C_1 b]] with c = C_0/2 (A.2). If xa + yb = 1, the
unimodular matrices U = [[x, y], [−b, a]] and V = [[1, xcb − y(2a − C_1 b)], [0, 1]]
bring it to g·diag(1, n) with n = 2a² − C_1 ab + c b²
(`DyadicContent.strict_smith`). Hence e_1 = v(g) and
e_1 + e_2 = 2v(g) + v(n) = v(Nω) − 1 = ν_1 + ν_2 − 1.

Now ν_i = v(g) + v(2a + bT_i), and both T_i have positive valuation. If b is
even then a is odd and v(2a + bT_i) = 1. If b is odd and some v(T_i) < 1, then
v(2a + bT_i) = v(T_i) for that i. If b is odd and both v(T_i) ≥ 1, then 4 | C_0,
so C_1 ≡ 2 (mod 4) by hypothesis, and U_i = T_i/2 are the roots of
U² + (C_1/2)U + C_0/4, which modulo 2 is U² + U + 1 or U(U + 1); so a + bU_i is
a unit for at least one i and min_i v(2a + bT_i) = 1. In every case
0 < min_i v(2a + bT_i) ≤ 1, that is ⌈ν_min⌉ = v(g) + 1 = e_1 + 1. Finally
e_2 = ν_1 + ν_2 − ⌈ν_min⌉. If the ν_i are integers this is ν_max. Otherwise P
is irreducible and ramified, the two values are conjugate, ν_1 = ν_2 ∈ ½ + Z,
and e_2 = 2ν − (ν + ½) = ⌊ν⌋. ∎

The content formula e_1 = v(A/2, B) and the determinant sum are the proof of
A.2. What is added is the closed form in the two zeros, valid in every case at
once, and Theorem 1, which says which cases occur.

**Corollary 7 (all strict groups).** For odd r, with r_0, r_1 as in §2:

| shape | ν_1, ν_2 at layer a ≥ 2 | A_{2,r}(E_a), a ≥ 2 | a = 0 | a = 1 |
|---|---|---|---|---|
| I | a + ½, a + ½ | C_{2^a} ⊕ C_{2^a} | 0 | C_2 |
| IIa | a + 1, a + 1 | C_{2^a} ⊕ C_{2^{a+1}} | C_2 | C_2 ⊕ C_4 |
| IIb | a + 2 + v(r − r_0), a + 2 + v(r − r_1) | C_{2^{a+1+μ}} ⊕ C_{2^{a+2+M}} | C_{2^{2+v(r−r_0)}} | as for a ≥ 2 |

with μ, M the smaller and larger of v(r − r_0), v(r − r_1). Per zero, the two
real spokes contribute ½ + ½ (I), 1 + 1 (IIa), and (2 + v(r − r_0)) + 1 or
1 + (2 + v(r − r_1)) (IIb); the ring ±i contributes 3/2 (I) or 1 (II); every
outer ring contributes 1.

**Corollary 8 (the ideal, hence the module).** For odd r:

* shape I: ω_{0,r}O = 𝔪, ω_{1,r}O = 2O, and ω_{a,r}O = 2^a 𝔪 for a ≥ 2. The
  strict dual at layer a ≥ 2 is 𝔪/2^a 𝔪 ≅ O/2^a O: free of rank two over Z/2^a,
  generated over Λ by one element, with the single relation
  γ² − τγ + Δ = 0.
* shape IIa: ω_{a,r}O = 2^{a+1}O for a ≥ 1. The strict dual is
  2O'/2^{a+1}O ≅ O'/2^a O, where O' = Z_2[T/2] is the maximal order. It needs
  two generators over Λ.
* shape IIb: ω_{a,r}O = (2^{ν_0}, 2^{ν_1})·O inside O' = Z_2 × Z_2, for a ≥ 1.

So in shapes I and IIa the strict dual of layer a, as a Λ-module in the
presentation of A.1, is the same at every odd weight: the weight is invisible.
In shape IIb two odd weights with the same v(r − r_0) and v(r − r_1) give the
same module.

*Proof.* (1+T)² = (1 − C_0) + (2 − C_1)T (`gamma_sq`). In shape I,
ω_{1,r} = (1+T)² − s² has both coordinates ≡ 2 (mod 4), so it is twice a unit
(`eisenstein_layer_one`); the quartic factor Φ_2 = (1+T)² + s² is 2(2a + bT)
with b odd, twice a generator of 𝔪 (`eisenstein_quartic_factor`). In shape IIa,
ω_{1,r} = 4(u + βT) with u odd (`inert_layer_one`), four times a unit of O. In
shape II, Φ_2 = 2(u + 2βT) with u odd (`split_quartic_factor`). For j ≥ 3 the
factor Φ_j = z² + t² with z = (1+T)^{2^{j−2}} ≡ 1 (mod 2O) and t odd is twice a
unit, for all coefficients (`sq_one_mod_four`, `higher_layer_twice_unit`). In
shape IIb the units of O' are units of O. ∎

**Corollary 9 (the sum over weights; A.4 made exact).** Let t ≥ 2, a ≥ 2,
N_odd = ⌊t/2⌋ and N_even = t − 1 − N_odd. Then Σ_{1≤r<t} log_2 |A_{2,r}(E_a)| is

* N_even + 2a·N_odd in shape I,
* N_even + (2a + 1)·N_odd in shape IIa,
* N_even + (2a + 3)·N_odd + Σ_{r odd, r<t} (v(r − r_0) + v(r − r_1)) in shape IIb.

In shapes I and IIa the sum does not depend on q and d at all. In shape IIb
each inner sum is at most 2t plus one exceptional term v(r_* − r_i), where r_*
is the odd weight below t closest to the zero; that term is k − 3 or l − 3 at
r_* and is the only place where the size of an L-value, hence log(2qd), enters
the bound of A.4.

## 7. The tree: three shapes, three motions

Lattices in the plane V = O ⊗ Q_2, up to scaling, are the vertices of a tree
with three edges at every vertex; two classes are joined when one lattice has
index 2 in the other (Serre, *Trees*, II.1). If L' ⊆ L with
L/L' ≅ C_{2^{e_1}} ⊕ C_{2^{e_2}}, the distance from [L] to [L'] is e_2 − e_1.
The pair x = [𝔪], y = [O] is one edge. The algebra E = Q_2[T]/(P) acts on the
tree by multiplication, and

    e_2 − e_1 = d(x, ω·y),        e_1 + e_2 = v(Nω) − 1.

A strict group is a size and a distance. An automorphism of a tree does one of
three things: it swaps the ends of an edge, it fixes a vertex, or it shifts a
line. The three shapes are these three motions.

| shape | E | what E^× does | where x and y sit | d(x, ω·y) |
|---|---|---|---|---|
| I | ramified field, disc. exponent 3 | T swaps x and y; units fix both | the swapped edge | 0 if v(Nω) is odd, 1 if even |
| IIa | Q_2(√5) | fixes x; T/2 turns the three neighbours of x | x is the centre, y on the first wheel | 1 |
| IIb | Q_2 × Q_2 | shifts a line through x; (2^i, 2^j) shifts by i − j | x on the line, y the neighbour of x off it | 1 + \|ν_1 − ν_2\| |

Size and distance give back Theorem 6 in each row. Theorem 1 reads: (q/d) = −1
exactly when the motion is a swap, and then E is one of the four ramified
fields Q_2(√±2), Q_2(√±6); (q/d) = +1 exactly when nothing swaps x and y (E is
unramified or split), and then O has index 2 in the maximal order and the
units of the maximal order fix x.

**The path of the vertex.** ω_{a,r} = Φ_0 Φ_1 ⋯ Φ_a with Φ_0 = (1+T) − s and
Φ_j = (1+T)^{2^{j−1}} + s^{2^{j−1}}. Start at y and apply the factors in turn.

* I: Φ_0 swaps (y to x), Φ_1 swaps back, Φ_2 swaps again; distances 0, 1, 0.
* IIa: Φ_0 turns the first wheel by one third, Φ_1 by two thirds, back to y;
  the distance is always 1.
* IIb: Φ_0 shifts the foot of y along the line by k − 2 = 1 + v(r − r_0), Φ_1
  shifts it back by l − 2 = 1 + v(r − r_1); distances k − 1, then 1 + |k − l|.

From the quartic step on the vertex is frozen in every shape: each further
layer multiplies by twice a unit, a pure dilation, which adds one to both
exponents. The two real spokes move the vertex in opposite senses, the ring ±i
moves it only in shape I, and no outer wheel moves it.

**Wheels.** The wheel of radius n around a vertex is its set of 3·2^{n−1}
vertices at distance n, the points of the projective line over Z/2^n. In shape
I the centre of symmetry is the midpoint of the edge xy; in shape IIa it is the
vertex x, and the units of O' turn every wheel rigidly; in shape IIb it is a
line, and wheels slide along it.

**The tower walks down a ray.** For a ≥ 1,
Z_2[γ^{2^a}] = Z_2 + 2^{a−1+v(τ)}O: the ring generated by the generator of
Γ_a = Γ^{2^a} is the vertex at depth a − 1 + v(τ) on the ray of orders
Z_2 + 2^n O below y. One layer is one step. (γ^{2^a} = A_a + B_a T with
B_1 = τ and B_{a+1} = B_a(2A_a − C_1 B_a).)

**The weight line is a tree too.** A weight r ∈ Z_2 is an end of the binary
tree of residues r mod 2^n, and v(r − r_0) is the depth at which the branch of
r leaves the branch of the zero r_0. In shape IIb the group at weight r is read
from where r leaves the two marked branches r_0 and r_1; the residue classes of
r modulo 2^n are the wheels of the weight line. Shapes I and IIa have no marked
branch, which is Corollary 8.

## 8. The pictures, the golden ring, higher rank

**(a) The cube and its two tetrahedra.** For the quartic fields of §3 the
ambiguous classes A(K)[2] form F_2³: eight classes, the corners of a cube. The
Rédei matrix is a linear map of this cube and the 4-rank is the dimension of
its kernel, the set of ambiguous classes that are squares in A(K). For k_1 in
shape II the matrix R is the all-ones matrix and its kernel is
{v_1 + v_2 + v_3 = 0}: the four corners of even weight, one of the two
tetrahedra inscribed in the cube. For F' in shape I the kernel of R' is
{000, 011}, one edge of that tetrahedron. In the other two cases it is the
single corner 000. Theorem 1 in one sentence: for (q/d) = +1 the square
ambiguous classes of Q(√2, √−m) fill a tetrahedron, for (q/d) = −1 those of F'
fill an edge.

**(b) One lattice seen along different axes.** The proof of Theorem 1 looks at
one module X through three quotients, by ⟨γ²⟩, ⟨σ⟩ and ⟨γ²σ⟩, and gets
A(k_1), A(Q(√2)) = 0 and A(F'). Section 7 looks at one tree through the three
kinds of symmetry it admits. A compound of two tetrahedra in a cube has the
same list: a quarter turn exchanges the two tetrahedra (as T exchanges x and
y), a third turn about a diagonal keeps each and cycles three corners (as T/2
turns the first wheel), and the lattice of cubes has its translations.

**(c) What does not carry over.** Angles, spheres and regular solids as metric
objects. The 2-adic distance is the distance of a tree; every triangle is
isosceles. The pictures model which elements swap, turn or shift, and nothing
about length.

**(d) The golden ring.** Q_2 has one unramified quadratic extension, and it is
Q_2(√5) = Q_2(φ), φ² = φ + 1, with integers Z_2[φ] (x² − x − 1 is irreducible
modulo 2). Hence in shape IIa

    O' = Z_2[T/2] ≅ Z_2[φ],     O = Z_2 + 2O' ≅ Z_2[√5],     X = 𝔪 = 2O',

the golden ratio acts on X, and the two zeros of f are a conjugate pair of
Q_2(φ). For (3,23), φ = 772 + 1053·(T/2) modulo 2^11. The residue field is
F_4 = {0, 1, φ, φ²} and φ is the third of a turn of the first wheel. Since
φ^k = F_k φ + F_{k−1}, the power φ^k fixes the vertex Z_2 + 2^n Z_2[φ] exactly
when 2^n divides the Fibonacci number F_k: the depth to which φ^k fixes the
ray of orders is v_2(F_k), and the period of φ on wheel n is the rank of
apparition of 2^n, namely 3, 6, 6, 12, 24, …. So φ sweeps wheels 1 and 2
completely and exactly half of each later wheel; the other half is reached by
√5 = 2φ − 1 (the group turning wheel n ≥ 3 is Z/3 × Z/2 × Z/2^{n−2}). Wheel n has
3·2^{n−1} vertices, the Pisano period of 2^n.

This is exact, but it is a property of the prime 2, not a new invariant of the
fields: it names the ring of shape IIa and gives closed formulas for the
rotations. The logarithmic spiral of the real plane has no role. In three
dimensions the same fact reads: over Q_2(φ) the tree has five edges at each
vertex, the directions are the five points of the projective line over F_4,
and their symmetry group PGL_2(F_4) is the rotation group of the icosahedron.
Three of the five directions are the rational ones; the other two are a
conjugate pair and span a line. Over the golden field shape IIa has an axis
exactly as shape IIb has, and d = 1 + |ν_1 − ν_2| holds for both; in shape IIa
the two zeros are conjugate, so ν_1 = ν_2 and nothing slides.

**(e) Higher rank.** For a module of Z_p-rank λ the lattices up to scaling are
the vertices of the building of PGL_λ(Q_p), the Smith form of X/ωY is the
relative position of two vertices, and the shape of the characteristic
polynomial is its splitting type over Q_p. For λ = 2 this is the tree. For
λ = 3 the flats (apartments) are planes tiled by triangles; the module
H = X(K_∞) of §2 has rank 3 and lives there. For λ = 4 the flats are 3-space, the vertices of a flat
form the body-centred cubic lattice, and the fourteen neighbours of a vertex
are the eight corners of a cube, split into two tetrahedra (sublattices of
index p and p³), and the six face centres (index p²). The star of a vertex is a
compound of two tetrahedra in a cube. The Weyl group S_4 is the symmetry group
of each tetrahedron, and an unramified splitting type is a conjugacy class of
it: a mirror (2+1+1), a half turn (2+2), a third turn (3+1), a quarter turn
with reflection (4). Nothing in rank three or four is computed here.

## 9. Packaged implications

For every pair (q, d) of the family, with the shape read from (q/d) and
h(−4qd) mod 16:

1. *Strict groups* at every layer and odd weight: Corollary 7.
2. *Their Λ-module structure* and independence of the weight in shapes I and
   IIa: Corollary 8.
3. *Even K-groups, conditionally.* If A_{2,r}(E_a)^∨ ≅ X/D_a Y (A.1) and
   K_{2r}(O_{E_a}){2} ≅ H²(O_{E_a}[1/2], Z_2(r+1)) (Rognes–Weibel), then
   Poitou–Tate duality with two dyadic places and H⁰ = Z/2 locally and globally
   gives |K_{2r}(O_{E_a}){2}| = 2·|A_{2,r}(E_a)| for odd r: 2^{2a+1} in shape I
   and 2^{2a+2} in shape IIa for a ≥ 2, for every such field and weight.
4. *Class groups of the first layers:* Corollary 5, the ratio law of §2, and at
   layer two the group and its marked relation (`dyadic_shape/RESULTS.md`).
5. *Class numbers:* h(−4qd) ≡ h(−8qd) (mod 16) when (q/d) = +1.
6. *Zeros of the 2-adic L-functions:* none in Z_2 in shapes I and IIa; one for
   each of L_2(·, ψ), L_2(·, ψχ_8) in shape IIb, with
   h_2(−4m) = 2^{4+v(r_0)}, h_2(−8m) = 2^{4+v(r_1)}.
7. *Mizusawa's hypothesis* C_1 ≡ 0 (mod 4): Corollary 4.
8. *The matrix chain of the formal project* holds for every pair of shape IIa,
   not only (3,23): `DyadicShapeBridge.samples_iff_inert_shape`.
9. *The sum over weights:* Corollary 9.
10. *Scale.* On the 14,022 test pairs the shapes I, IIa, IIb occur 7038, 3539,
    3445 times, close to ½ : ¼ : ¼; the four ramified fields of shape I occur
    1682, 1735, 1810, 1811 times; the two zero depths of shape IIb are
    independent and geometric (§2). These are observations. They suggest that
    the classification has the same proportions at every size of qd.

## 10. Status of sections 6 to 9

* Theorem 6 and Corollaries 7, 8, 9 are algebra about the pair 𝔪 ⊂ O, with
  complete proofs above. Their kernels are Lean theorems in
  `formal/Reimann/DyadicContent.lean` (22 breakpoints, Lean 4.36.0 and 4.33.1):
  `strict_smith`, `eisenstein_distance`, `inert_distance`, `split_distance`,
  the layer theorems named in the proof of Corollary 8, and
  `unit_mul_parity`. The induction over layers and the passage from integer
  identities to 2-adic lattices are on paper.
* `dyadic_shape/check_tree.py` tests the rule, the ideals, the path, the
  conductor formula and the comparison with A.2 on 1700 random coefficient
  pairs at 40 binary digits (all three residue classes of Theorem 6), on the
  14,022 test fields at 9 digits and on six named fields at 13 digits; all
  pass. On the excluded class (0,0) mod 4 only the comparison with A.2 is run. It also checks the wheel sizes, the
  Fibonacci statements and the golden unit of (3,23).
* The arithmetic meaning of 𝔪/ω_{a,r}O is the descent of the main text and
  Mizusawa's theorem; neither is formalized. Item 3 of §9 is conditional as
  stated.
* §7 restates Theorem 6 with standard facts about the tree. §8(a), (b), (d) are
  exact; §8(e) and the icosahedral remark quote standard mathematics as
  orientation and make no new claim.
* The proportions in item 10 of §9 are data.
