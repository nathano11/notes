# Two calculations for the complementary odd-prime group

**Research checkpoint · 20 November 2026**

Write \(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\) and \(E_a=Q_a(\sqrt{-q},\sqrt{-d})\). For an odd prime \(p\), put \(M=\mathbb Q_p/\mathbb Z_p(-r)\) and let \(A_{p,r}(E_a)\) be the kernel of localization of \(H^1(G_{E_a,S_p},M)\) at every place over \(p\), with ramification allowed only at \(S_p\). Superscript \(\mathrm{comp}\) selects the complex-conjugation eigenvalue \((-1)^r\). All weights here are positive integers.

There are two paper conclusions. For \((q,d)=(19,16871)\), adjoining \(\sqrt2\) to \(E_0\) adds no complementary classes at 3, at any weight. For \((q,d)=(3,23)\) the entire complementary group at 277 over \(E_0\) vanishes at every weight. These are fixed-field calculations. The equations below distinguish their numerical inputs from the cohomological identifications required for a Lean proof. The accompanying README lists the outstanding formal steps.

## 1. From the bottom field to the first dyadic layer at 3

Put \(D=320549=19\cdot16871\). The bottom-layer result in §6 of *Dyadic Window Orders* is an input here. It gives \(C_3\) for even weights and zero for odd weights. Restriction and half the corestriction split the restriction map at each quadratic step. Equivalently, averaging the two Galois actions projects onto the part from the lower field. A new nonzero 3-primary summand would contain an element of order 3. It therefore suffices to test its 3-torsion.

| Sector at the first layer | Fundamental discriminant | Lengths of reduced-ideal cycles | Ordinary class number |
|---|---:|---|---:|
| Even, adjoining \(\sqrt2\) | 8 | 1 | 1 |
| Even, adjoining \(\sqrt{2D}\) | 2564392 | 400, 424 | 2 |
| Odd, adjoining \(\sqrt{114}\) after the twist | 456 | 6, 10 | 2 |
| Odd, adjoining \(\sqrt{101226}\) after the twist | 404904 | 148, 168 | 2 |

For a fundamental discriminant \(d_0\), put \(h=\lfloor\sqrt{d_0}\rfloor\). Enumerate \(1\le P\le h\) and positive even \(Q\) with \(h+1-P\le Q\le h+P\) and \(2Q\mid d_0-P^2\). Iterate \(P'=\lfloor(h+P)/Q\rfloor Q-P\), \(Q'=(d_0-P'^2)/Q\). The four rows above contain 1, 824, 16 and 316 reduced pairs, respectively. The table uses ordinary ideal classes. The continued-fraction identification underlying the enumeration is described in §3.3 of the following reference. [Reduced ideals and quadratic irrationals](https://doi.org/10.1007/s00605-026-02202-5)

**Even weights.** Descent under complex conjugation gives the strict group of \(R_1=\mathbb Q(\sqrt2,\sqrt D)\). Its three nontrivial quadratic characters come from \(\sqrt2,\sqrt D,\sqrt{2D}\). The middle character is already present at layer zero. For \(\mathbb Q(\sqrt2)\), the unique place above 3 is unramified, its cyclotomic image is the global image, and its class number is one. A global boundary removes its one possible local boundary. Finite strict characters then factor through the class group.

The subtle case is \(K=\mathbb Q(\sqrt{641098})\). The prime 3 splits into two places. For even \(r\), the residual coefficient is trivial and the global and local invariant groups in \(M\) have order \(3^{1+v_3(r)}\). The exact sequence for multiplication by 3 identifies a local boundary line in \(H^1(K_v,\mathbb F_3)\). Up to the same nonzero scalar at both places, its generator is the cubic cyclotomic character on units modulo 9. Indeed, if \(\kappa\) is the cyclotomic character, a generator is represented by \((\kappa^{-r}-1)/3^{1+v_3(r)}\bmod3\). Evaluation at a generator of \(1+3\mathbb Z_3\) shows that it is nonzero, also when \(3\mid r\).

The continued-fraction convergent of \(\sqrt{641098}\) at zero-based index 423 gives \(X^2-641098Y^2=1\) with \((X,Y)=(8,3)\bmod9\). The two embeddings send the square root to \(1,-1\bmod9\). The unit \(X+Y\sqrt{641098}\) has images \(2,5\bmod9\), inverse to each other, each nontrivial modulo signs. If the local restrictions of a mod-3 lift have coefficients \(b_1,b_2\) on the two boundary lines, global reciprocity evaluated on this unit gives \(b_1=b_2\). Ramification is allowed only at 3, so units at all other finite places contribute zero. One global boundary now removes both local restrictions. The resulting everywhere unramified character is zero since \(h(K)=2\). This proves that both new even-weight character components vanish. [Milne, *Class Field Theory*, Chapters III and VIII](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**Odd weights.** The cyclotomic sign at 3 makes \(H^0(M)\) zero both globally and at the unramified completions of \(E_1\). Thus order-three classes are exactly the finite-coefficient strict classes. Adjoin \(\mu_3\) to trivialize the twist. Equivariance under complex conjugation selects even ideal classes, and equivariance under the automorphism negating \(\mu_3\) selects the nontrivial sign there. At layer zero the real quadratic pieces have discriminants 57 and 50613. Their class numbers are 1 and 5. Twisting these two characters by the character of \(\mathbb Q(\sqrt2)\) gives exactly the last two rows of the table. All intervening character projections use groups of order a power of 2, so norm and extension identify the indicated components at 3 even at primes ramified in a quadratic step. With both new class numbers prime to 3 the odd sector vanishes. Together the two parities give
\[
 A^{\mathrm{comp}}_{3,r}(E_1)\simeq
 \begin{cases}C_3&r\text{ even},\\0&r\text{ odd}.\end{cases}
\]

## 2. A rank test at a large unramified prime

Let \(E=E_a\), \(p\nmid 2qd\), \(J=E(\mu_p)\), \(K=J^+\). Write \(\Delta=\operatorname{Gal}(J/E)\) and let \(\omega\) be its mod-\(p\) cyclotomic character. The \(p\)-adic completions of \(E\) are unramified over \(\mathbb Q_p\). The cyclotomic extension is totally ramified, so its decomposition group above every such place is all of \(\Delta\simeq\mathbb F_p^\times\).

Suppose \(p-1\nmid r\). The cyclotomic action makes \(H^0(M)\) vanish globally and at every place over \(p\). The multiplication-by-\(p\) sequence therefore identifies \(A[p]\) with the finite-coefficient strict group. Restriction to \(J\) is exact on taking \(\Delta\)-invariants because \(|\Delta|\) is prime to \(p\). Over \(J\) the twist is trivial. Class field theory identifies strict characters with characters of the ideal class group after inverting \(p\). The prime classes removed by localization are fixed by \(\Delta\), so they have zero projection to the nontrivial character \(\omega^{-r}\). For the complementary sign the sign on the coefficients cancels the sign on the homomorphism, leaving conjugation-fixed ideal classes. Norm and extension for \(J/K\) identify these with classes of \(K\) at odd \(p\). This proves the support criterion
\[
 A^{\mathrm{comp}}_{p,r}(E)\ne0
 \quad\Longleftrightarrow\quad
 \bigl(\mathrm{Cl}(K)/p\bigr)^{\omega^{-r}}\ne0 .
\]
Every nonzero \(p\)-primary group contains an element of order \(p\), which accounts for the whole group on the left. Higher-level class-group descriptions of even \(K\)-groups are given in [Lim, Theorems 4.2 and 4.5](https://arxiv.org/pdf/2210.00168).

Let \(U\) be the units of \(K\) and \(C\) its group of circular units in the sense of Sinnott. The degree \([K:\mathbb Q]\) is prime to \(p\). Greither's Corollary 4.15 equates the composition factors of \((U/C)\{p\}\) with those of \(\mathrm{Cl}(K)\{p\}\). Thus the support test is equivalent to a rank test on the inclusion of circular units in ordinary units modulo \(p\), in the indicated component. Equality of composition factors suffices for this vanishing test. It does not specify the individual cyclic factors. [Greither, Corollary 4.15](https://www.numdam.org/item/10.5802/aif.1299.pdf)

## 3. All 551 character lines at \(p=277\)

Take \(E=\mathbb Q(\sqrt{-3},\sqrt{-23})\) and \(p=277\). Then \(K=(E(\mu_{277}))^+\) has degree 552. Its Galois group has exponent dividing 276. Consequently every character splits over \(\mathbb F_{277}\). Dirichlet's unit theorem gives a one-dimensional unit space for each nontrivial character and dimension zero for the trivial character. One circular unit with nonzero image on each line proves that \(277\nmid[U:C]\).

Use conductors \(f=1,3,23,69\) and the corresponding quadratic characters \(\eta_f\), with \(\eta_1=1\). For \(1\le s\le275\), take even \(s\) at \(f=1,69\) and odd \(s\) at \(f=3,23\). Set \(m=277f\). Choose a prime \(\ell\equiv1\bmod m\), a primitive root \(g\bmod\ell\), and \(z=g^{(\ell-1)/m}\). Define \(L(y)\in\mathbb F_{277}\) by
\[
 y^{(\ell-1)/277}=(g^{(\ell-1)/277})^{L(y)}\pmod\ell .
\]
The computed projection is
\[
 T_{\ell,f,s}=\sum_{a\in(\mathbb Z/m)^\times}\eta_f(a)\,a^s L(1-z^a)
 \pmod{277}.
\]
Indeed the projection idempotent sums over conjugates with inverse character weights. Grouping first over the kernel of the character takes the norm down to its character field. The normalization denominator is a unit modulo 277. A \(277\)-th power reduces to zero under \(L\), so a nonzero sum certifies a nonzero unit component. At composite conductor \(m\) with at least two distinct prime divisors, \(1-\zeta_m\) is a unit. At \(m=277\) use \((1-\zeta_m^5)/(1-\zeta_m)\). This multiplies the sum by \(5^{-s}-1\ne0\) since 5 is primitive modulo 277. Norms of these elements down to the real character fields give circular units. The sign convention only exchanges inverse characters in the exhaustive test.

| \(f\) | Exponents checked | Zero sums at \(\ell=114679,\ g=6\) | Their values at \(\ell=649843,\ g=2\) |
|---:|---:|---|---|
| 1 | 137 | none | — |
| 3 | 138 | 115, 169 | 45, 34 |
| 23 | 138 | 87 | 228 |
| 69 | 137 | 126 | 5 |

The four rows cover 550 characters. The remaining nontrivial character has \(s=0,f=69\). At its true conductor \(m=69\), the sum is 41 at the first prime. That gives all 551 character lines. The ordinary unit index and the class number of \(K\) are therefore prime to 277. Section 2 disposes of every weight outside \(276\mid r\).

For \(276\mid r\), the complementary sign is positive. Descent gives \(R=\mathbb Q(\sqrt{69})\), whose class number is prime to 277 by norm and extension to \(K\). The two roots of 69 modulo \(277^2\) are 26839 and 49890. The norm-one unit \((25+3\sqrt{69})/2\) takes the values 40271 and 36483. Their Fermat quotients \((u^{276}-1)/277\bmod277\) are respectively 58 and 219. For any such weight the boundary character on local units is a common nonzero scalar times this Fermat quotient. This follows from \(v_{277}((1+277)^{-r}-1)=1+v_{277}(r)\) and the binomial expansion on \(1+277\mathbb Z_{277}\). Reciprocity again forces the two boundary scalars to agree. Removing their common value leaves a character of a class group of order prime to 277. This proves on paper
\[
 A^{\mathrm{comp}}_{277,r}\bigl(\mathbb Q(\sqrt{-3},\sqrt{-23})\bigr)=0
 \qquad(r\ge1).
\]

The second finite certificate in *Prime277.lean* uses Stickelberger sums. For \(m=277f\), \(b=622\), multiply \(\lfloor bu/m\rfloor\) by \(\eta_f(u)u^{-r-1}\) and sum over units \(u\bmod m\). For \(1\le r\le274\) of the indicated parity the products of the sums in conductor order \(1,3,23,69\) are \(86,172,96,98\bmod277\). Each is nonzero. The reflected exponent is \(r+1\) because Kummer theory identifies the coefficient twist after tensoring with \(\mu_p\). A strict Kummer class has principal ideal a \(p\)-th power and maps to the reflected class group. Its odd unit kernel consists of roots of unity at \(p\), which have tame character \(\omega\) and are excluded in these weights. Extending the reflected component to the cyclotomic field of conductor \(277f\) preserves it since the intervening index is prime to 277. The displayed sum evaluates the integral annihilator \((b-\sigma_b)\theta_m\). At \(r=275\) the reflected tame character is trivial and descent is to \(E\). Minkowski gives an ideal representative of norm at most 10 in each class since \(|D_E|=69^2\). The number of ideals of norm at most 10 is at most \(\sum_{n\le10}d_4(n)=89<277\). This alternative route agrees with the circular-unit calculation. [Stickelberger's theorem and its integral annihilator](https://doi.org/10.1365/s13291-021-00233-5)

## 4. What the general window still costs

The finite calculations concern two fixed fields. For the moving fields, the per-prime argument in §7 of *Dyadic Window Orders* gives a logarithmic cost \(\ll tg\,k_p p\log(2Fp)\) for the portion killed by \(p^{k_p}\), summed over the weights. Here \(F=2^{a+2}qd\) and \(g=[E_a:\mathbb Q]\). Write \(X=x^\varepsilon\) and \(B=\lfloor\exp(X/2-\sqrt X)\rfloor\). Allocate \(k_p=\lfloor B/p^2\rfloor\) for odd primes \(p\le\sqrt B\). Since \(p k_p\le B/p\), the sum of the costs is
\[
  \ll tg B\,\log(2FB)(1+\log B)=o(\exp(X/2))
\]
under the existing polynomial bounds on \(t,g,\log F\) for fixed \(\varepsilon>0\). The finite dyadic-block inequality behind this allocation is the subject of *Window.lean*. The arithmetic estimate for the pieces above \(p^{k_p}\) and for primes above \(\sqrt B\) remains open. The rank test in §2 decides support one prime at a time. A window proof also requires uniform control on the lengths of the groups that survive.
