# Prime powers in the arithmetic window

**Reimann research checkpoint · November 20, 2026**

For the same auxiliary primes \(q,d\) selected in the signed-twist argument, the full strict-group contribution fits the prescribed budget on a growing range of dyadic layers and weights. Put \(Q_b=\mathbb Q(\zeta_{2^{b+2}})^+\), \(E_b=Q_b(\sqrt{-q},\sqrt{-d})\), and \(h=[E_b:\mathbb Q]=4\cdot2^b\). For \(0<\varepsilon<1/52\), fixed \(0<\eta<4/5\), and \(b\le a\),
\[
 hR^2\le x^{(4/5-\eta)\varepsilon}
 \quad\Longrightarrow\quad
 \sum_{1\le r\le R}\sum_{p\ {\rm prime}}\log |A_{p,r}(E_b)|
   =o\!\left(\exp(x^\varepsilon/2)\right).
\]
Here \(A_{p,r}\) consists of classes unramified outside \(p\) that restrict to zero at every place above \(p\). The odd primes are treated at every depth by the transfer argument below. Appendix A supplies the estimate at 2. For example, the bottom field with the moving \(q,d\) admits every weight through \(\lfloor x^{\varepsilon/3}\rfloor\). This is an asymptotic assertion for sufficiently large \(x\).

The target for the ordinary zeta problem uses the required full field \(E_a\) and all \(1\le r<\lfloor x^{401}\rfloor\). The geometric estimate below has \(r^2\) in its exponent. At the largest required weights this bound exceeds the budget even for a field of fixed degree. The odd-prime descent gives separate finite tests for the unresolved part. Both the mathematical derivations and their Lean status matter here. The file **PROOF_STATUS.md** lists the external inputs, outstanding formalizations and checker state.

Three finite computations illustrate the distinctions. Appendix A determines the invariant factors of the dyadic strict groups throughout the family from three special-value valuations at an odd weight. Appendix B gives the entire complementary group at 3 for \(q=19,d=16871\) through the first dyadic layer, and computes the real class groups up the associated cyclotomic 3-tower. The Bernoulli test gives a large-prime exclusion in the field with \(q=3,d=23\).

## Full odd-primary orders on a growing range of weights and layers

Let \(L/\mathbb Q\) be a finite abelian extension of degree \(h\), with absolute discriminant \(D_L\). It is either totally real or CM. Let \(F\) be any common multiple of its character conductors. In the window application \(Q_b=\mathbb Q(\zeta_{2^{b+2}})^+\), \(L=E_b=Q_b(\sqrt{-q},\sqrt{-d})\), \(h=4\cdot2^b\), and one can use \(F=2^{b+2}qd\). For \(r\ge1\) and odd \(p\), write \(A_{p,r}(L)\) for the kernel of localization at all places above \(p\) in \(H^1(G_{L,S_p},\mathbb Q_p/\mathbb Z_p(-r))\). All logarithms are natural.

**Full-order estimate.** With an absolute constant \(C\), for every \(r\ge1\),
\[
 \sum_{p>2}\log |A_{p,r}(L)|
 \ \le\ \exp\!\left(C r^2h\,[\log(2rh)+\log(2F)]\right).
 \tag{A}
\]
This includes both conjugation eigenspaces and all powers of every odd prime. We use the quantitative cell estimates of Alejandro de la Torre Durán as a theorem from the November 2026 preprint. The passage to the small-prime part below uses finite-index transfer and a uniform Hurewicz exponent bound. [De la Torre Durán, Theorems 3.9, 3.10 and 4.5](https://arxiv.org/html/2611.06300v2)

**The large primes.** Put \(m=2r\), \(N=2m+1=4r+1\), and \(B=hN+1\). By Poitou–Tate and Quillen–Lichtenbaum, \(A_{p,r}(L)^\vee\) embeds into \(K_m(\mathcal O_L)\{p\}\), as in §2 of *Arithmetic Window Integer*. These groups are finite. Theorem 4.5 of the preprint, with the general cutoff \(B\) from Lemma 4.3, gives
\[
 \sum_{p>B}\log |A_{p,r}(L)|
 \ \le\ \exp\!\left(C_1N^2[h\log(2Nh)+\log D_L]\right).
 \tag{B}
\]
[Weibel, *The K-book*, VI.8.2 and 8.4](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.VI.pdf) · [Validire, §2, étale wild kernels](https://www.numdam.org/item/10.5802/jtnb.681.pdf) · [De la Torre Durán, §4.2](https://arxiv.org/html/2611.06300v2#S4.SS2)

**An integral bound on the homology of a congruence subgroup.** Let
\[
 \Gamma=\mathrm{GL}_N(\mathcal O_L),\qquad
 \Gamma'=\ker\!\left(\Gamma\to\mathrm{GL}_N(\mathcal O_L/3\mathcal O_L)\right),
 \qquad I=[\Gamma:\Gamma']\le3^{hN^2}.
\]
The last inequality counts all \(N\times N\) matrices over a ring of size \(3^h\). In the integral regular representation, \(\Gamma'\) lies in the principal congruence subgroup of level three in \(\mathrm{GL}_{Nh}(\mathbb Z)\), which is torsion-free. For a direct check, a nonidentity element of prime order in the latter group could be written \(1+3^u T\), with \(u\ge1\) and \(T\not\equiv0\bmod3\). Raising to the power \(\ell\) for a prime \(\ell\ne3\) gives leading term \(\ell3^uT\) modulo \(3^{u+1}\). Cubing gives leading term \(3^{u+1}T\) modulo \(3^{u+2}\). Both exclude the identity.

If \(L\) has signature \((r_1,r_2)\), the symmetric space has dimension \(s=r_1N(N+1)/2+r_2N^2-1\). Its orientation character is trivial. The complex factors are connected, and on each real space of symmetric matrices the action \(X\mapsto AXA^t\) has determinant \((\det A)^{N+1}>0\) since \(N\) is odd. Quotienting by positive simultaneous scalings preserves this orientation character. For a congruence subgroup of \(\mathrm{GL}_N(\mathcal O_L)\) over a general number field, the Voronoi–Koecher complex computes cohomology in reversed degrees up to the subgroup's torsion primes. For \(\Gamma'\) there are none. Thus \(H^{m+1}(\Gamma',\mathbb Z)\simeq H_{s-m-1}(\mathrm{Vor}_{\Gamma'},\mathbb Z)\) integrally. The integral universal coefficient sequence identifies the order of its torsion with that of \(H_m(\Gamma',\mathbb Z)_{\rm tors}\). [Ash, Gunnells, McConnell and Yasaki, §2.1 and Theorem 2.2](https://math-sites.uncg.edu/sites/yasaki/publications/tonsoftorsion.pdf)

Put \(j=s-m\). Theorem 3.9 of the preprint applies at \(hN-1\le j\le s\). Indeed \(j-(hN-1)\ge hN(N-2)/2-m\ge0\) as \(h\ge1\), \(m\ge2\) and \(N=2m+1\). It bounds the number \(c_j\) of \(\Gamma\)-orbits of the relevant cells, including all orientations. Theorem 3.10 bounds the number \(f_j\) of facets of any such \(j\)-cell. Every original orbit splits into at most \(I\) orbits for \(\Gamma'\). For each new generator the sum of the absolute values of its cellular boundary coefficients is at most \(f_j\), since the coefficients sum signed incidences of its facets. In particular each Euclidean column norm is at most \(f_j\). The elementary determinant bound on the torsion in the cokernel of this boundary map now gives
\[
 \log |H_m(\Gamma',\mathbb Z)_{\rm tors}|
 \le I\,c_j\log\max(2,f_j)
 \le \exp\!\left(C_2N^2[h\log(2Nh)+\log D_L]\right).
 \tag{C}
\]
For the first inequality, homology embeds in this cokernel, and a nonzero maximal-rank minor is at most the product of the column norms by Hadamard. For the second, apply the cell and facet bounds exactly as in the proof of Theorem 4.5 and absorb \(\log I\le hN^2\log3\) in the exponent. [De la Torre Durán, §§1.3, 3.3 and 4.2](https://arxiv.org/html/2611.06300v2)

**The small primes.** Apply Hurewicz and then the homology transfer to the finite subgroup
\[
 T=\bigoplus_{2<p\le B} A_{p,r}(L)^\vee
  \ \hookrightarrow\ K_m(\mathcal O_L)
  \ \longrightarrow\ H_m(\Gamma,\mathbb Z)
  \ \longrightarrow\ H_m(\Gamma',\mathbb Z).
\]
Here \(B\mathrm{GL}(\mathcal O_L)^+\) is the connected component of the algebraic \(K\)-theory infinite loop space. The plus construction preserves integral homology, and homological stability identifies the stable homology in degree \(m\) with that of \(\Gamma\) at \(N=2m+1\). For odd \(p\), Mathew's Theorem 6.3 with connectivity parameter \(1\) kills the \(p\)-part of the Hurewicz kernel by \(p^{u_p}\), where
\[
 u_p=\left\lceil\frac{m+2}{2p-2}\right\rceil+1.
\]
Including the subgroup after transfer multiplies by \(I\). Thus an element of the \(p\)-part of the composite kernel is killed by \(p^{v_p(I)+u_p}\). Taking \(k=\lceil hN^2\log_2 3\rceil+m+3\) suffices simultaneously for every \(p\le B\), including all prime divisors of \(I\) in that range. Primes above \(B\) were treated in (B). [Mathew, *Torsion exponents in stable homotopy and the Hurewicz homomorphism*, Theorem 6.3](https://msp.org/agt/2016/16-2/agt-v16-n2-p12-s.pdf) · [Homological stability in the stated range, §4.2](https://arxiv.org/html/2611.06300v2#S4.SS2)

To see the cost of this kernel, use the finite-coefficient estimate from §7 of *Dyadic Window Orders*. At a single weight it gives
\[
 \sum_{2<p\le B}\log |A_{p,r}(L)[p^k]|
 \ll h k B^2 \bigl(\log(2F)+\log(2B)\bigr).
 \tag{D}
\]
Indeed \(A_{p,r}[p]\) is an image of a subspace of \(H^1(G_{L,S_p},\mathbb F_p(-r))\) by the coefficient sequence. Restriction to \(J=L(\mu_p)\) is injective on this latter space since \([J:L]\mid p-1\). Over \(J\) the coefficients identify with \(\mu_p\). Kummer theory bounds its order by the product of the \(S_p\)-unit group modulo \(p\)-th powers and the order of the \(p\)-torsion of the \(S_p\)-class group. If \(d_J=[J:\mathbb Q]\le hp\), the unit factor is at most \(p^{2d_J}\). Minkowski's bound on ideal representatives gives \(h(J)\le |D_J|\zeta_J(2)\le(Fp)^{d_J}\zeta(2)^{d_J}\) by the conductor-discriminant formula. Thus \(\log |A_{p,r}[p]|\ll hp(\log(2F)+\log(2p))\). The cyclic decomposition of a finite abelian \(p\)-group gives \(\log |A_{p,r}[p^k]|\le k\log |A_{p,r}[p]|\). Summing yields (D). A finite group and its character dual have the same invariant factors, so (D) bounds the logarithm of the kernel order above.

The finite-group image of the composite is contained in \(H_m(\Gamma',\mathbb Z)_{\rm tors}\), so (C) bounds its log order. Combining (B), (C) and (D), the polynomial in \(h,N,\log(2F)\) in (D) is absorbed in (A), using \(D_L\le F^h\) by the conductor-discriminant formula. This proves (A).

**The range on the window.** Fix \(0<\varepsilon<1/52\), \(0<\eta<4/5\), and the prescribed window parameters. Assume \(b\le a\), \(R\ge1\), and
\[
 hR^2\le x^{(4/5-\eta)\varepsilon}.
\]
The previously established conductor estimate is \(\log(2F)\ll_\varepsilon x^{\varepsilon/5}(1+\log^2 x)+\log(2x)\) for the full layer and hence also for every sublayer. Then \(R^2h(\log(2Rh)+\log(2F))=O_{\varepsilon,\eta}(x^{(1-\eta)\varepsilon}(1+\log^2 x))=o(x^\varepsilon)\), uniformly on this range. Summing (A) at all \(1\le r\le R\), the extra factor \(R\) has logarithm \(O_\varepsilon(\log x)\). Hence
\[
 \sum_{1\le r\le R}\sum_{p>2}\log |A_{p,r}(E_b)|
 \ \le \ \exp(o(x^\varepsilon))
 \ =\ o\!\left(\exp(x^\varepsilon/2)\right).
 \tag{E}
\]
For example \(b=0\) admits \(R=\lfloor x^{\varepsilon/3}\rfloor\) for all sufficiently large \(x\). For odd \(p\), restriction and corestriction between \(E_b\) and \(E_a\) preserve the strict local conditions and unramifiedness outside \(p\). This last assertion follows locally from the Mackey formula: the corestriction of an unramified class restricts trivially to inertia since the inducing class is trivial on every conjugate inertia intersection. Their composite on the lower group is multiplication by \(2^{a-b}\), a unit on \(p\)-groups. Thus the groups in (E) are direct summands of the full-layer groups, with a single choice of \(q,d\). Formula (E) bounds these summands jointly across primes and weights. We obtain no estimate of the required strength for all the remaining components through \(r=\lfloor x^{401}\rfloor-1\).

### Field conductors and individual character contributions

There is also a full \(K\)-group version of (A). For an abelian CM field \(L\), the same right-hand side bounds \(\log|K_{2r}(\mathcal O_L)|\), including 2. For a totally real abelian field the following argument bounds its odd part. Here are the additional steps. Put \(U_p=K_{2r}(\mathcal O_L)\{p\}\). Weibel VI.8.3 identifies \(U_p/pU_p\) with the degree-two étale cohomology of \(\mathcal O_L[1/p]\) with coefficients \(\mu_p^{\otimes(r+1)}\), also at 2 for the totally imaginary fields. Restriction to \(J=L(\mu_p)\) is injective by transfer because the degree divides \(p-1\). The coefficients there are isomorphic to \(\mu_p\). The Kummer sequence bounds the size by
\[
 |\operatorname{Pic}(\mathcal O_J[1/p])/p|\,
 |\operatorname{Br}(\mathcal O_J[1/p])[p]|.
\]
The first factor is at most the class-number bound used in (D). The Brauer group injects into a sum of local groups at the primes over \(p\) and the real places. For odd \(p\) the real-place groups have zero \(p\)-part; for \(p=2\) the CM field has none. Thus the second factor is at most \(p^{[J:\mathbb Q]}\). This proves the bound in (D) for \(U_p[p^k]\) as well, since \(|U_p[p]|=|U_p/pU_p|\). For \(p=2\), Mathew's Theorem 6.3 gives depth at most \(\lceil(m-1)/2\rceil+3\) for the Hurewicz kernel. The same transfer, with \(k\) increased by two if necessary, now works on the entire small-prime part of \(K_{2r}\); (B) already covers its remaining primes. These steps also give the asserted strict-group estimate at 2 in the CM case independently of the sharper dyadic computation. [Weibel, Chapter VI, 8.1.1 and Corollary 8.3](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.VI.pdf) · [Rognes and Weibel, Kummer and Brauer sequences](https://sites.math.rutgers.edu/~weibel/archive/papers-dir/RognesWeibel.pdf) · [Mathew, Theorem 6.3](https://msp.org/agt/2016/16-2/agt-v16-n2-p12-s.pdf)

For odd \(p\), one can compute the above range with the conductor and degree of each character's own field. Let \(\theta\) be a complex character of \(\operatorname{Gal}(E_a/\mathbb Q)\), \(K=E_a^{\ker\theta}\), \(h_\theta=[K:\mathbb Q]\), and \(F_\theta\) its conductor. Every \(p\)-primary component with this kernel or a larger kernel descends to \(K\). Indeed on absolute \(H^1\), restriction identifies the lower group with the invariants because \([E_a:K]\) is prime to \(p\). This identifies strict groups too. At primes above \(p\) local restriction is injective. Away from \(p\), inertia acts trivially on the coefficients and a character of inertia which vanishes after restriction to a subgroup of index prime to \(p\) vanishes already. Thus (A) may be applied with \(h_\theta,F_\theta\). Over \(\mathbb Z_p\) the corresponding invariant projector is averaging over \(\ker\theta\), so its image is a direct summand. One may group conjugate characters by their common kernel, or take the smaller isotypic summands inside that image.

In particular the summand from \(Q_b\) alone has \(h_\theta\) replaced by \(2^b\) and \(F_\theta\) by \(2^{b+2}\); it is independent of \(q,d\). At \(b=0\) the entire rational summand, at all odd primes, fits the budget whenever \(R^2\log(2R)=o(x^\varepsilon)\). In general the same follows from \(R^2h_\theta\log(2Rh_\theta F_\theta)=o(x^\varepsilon)\). Summing polynomially many such components costs only \(O(\log x)\) in the exponent provided the little-oh bound is uniform. This distinction between a character's own conductor and the full field conductor enlarges the range for the low-conductor components.

## Odd-prime descent to finite real class groups

Let \(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\) and \(E=Q_a(\sqrt{-q},\sqrt{-d})\) for distinct primes \(q\equiv3\bmod8,\ d\equiv7\bmod16\). Fix an odd prime \(p\), integers \(r,n\ge1\), and let \(S\) consist of the places of \(E\) above \(p\). Put \(M=\mathbb Q_p/\mathbb Z_p(-r)\), \(D=M[p^n]\), and
\[
 A_{p,r}(E)=\ker\left(H^1(G_{E,S},M)\longrightarrow\bigoplus_{v\mid p}H^1(E_v,M)\right).
\]
Write \(A^{\rm comp}_{p,r}\) for the eigenspace on which complex conjugation acts by \((-1)^r\). For \(m\ge1\), let \(J_m=E(\mu_{p^m})\), \(G_m=\operatorname{Gal}(J_m/E)\), \(J_m^+\) its maximal real subfield, and \(h=|G_1|\).

### A finite class group at each depth

Take \(m=n\) if \(h\nmid r\), and \(m=n+1\) if \(h\mid r\). There are isomorphisms
\[
 A_{p,r}(E)[p^n]\simeq
 \operatorname{Hom}_{G_m}(\mathrm{Cl}(\mathcal O_{J_m}[1/p]),D),\qquad
 A^{\rm comp}_{p,r}(E)[p^n]\simeq
 \operatorname{Hom}_{G_m}(\mathrm{Cl}(\mathcal O_{J_m^+}[1/p]),D).
 \tag{1}
\]
At \(h\nmid r\), both localized class groups in (1) can be replaced by the ordinary class groups. The higher choice \(m=n+1\) works for every \(r\). The \(G_m\)-action on \(D\) is the inverse \(r\)-th power of the cyclotomic character modulo \(p^n\).

**Cyclotomic images.** For \(p\nmid qd\), \(E\) is unramified at \(p\), so \(h=p-1\). For \(p=q,d\), \(E\) contains the quadratic subfield \(\mathbb Q(\sqrt{-p})\) of \(\mathbb Q(\mu_p)\), and the remaining generators of \(E\) are unramified at \(p\). The local ramification index is exactly two, so \(h=(p-1)/2\). At each finite cyclotomic level the global intersection and every local intersection with the corresponding cyclotomic field consequently have the same degree (one or two). Each \(p\)-adic place has full decomposition group \(G_m\) and is totally ramified in \(J_m/E\). More explicitly its completion is the compositum of the relevant cyclotomic field with an unramified local field. The common global and local infinite cyclotomic image is a subgroup with tame part of order \(h\) and principal part \(1+p\mathbb Z_p\).

**Inflation and boundaries.** The module \(D\) is trivial over \(J_m\). From multiplication by \(p^n\) on \(M\), every \(p^n\)-torsion cohomology class has a lift to \(H^1(G_{E,S},D)\). The ambiguity in a lift is the injective boundary from \(H^0(E,M)/p^n H^0(E,M)\). The same assertion holds at each completion. We claim these boundary subgroups are exactly the images of \(H^1(G_m,D)\) by inflation, both globally and locally.

If \(h\nmid r\), a generator of the tame subgroup acts on \(D\) by a scalar \(u\) with \(u-1\) invertible. Its invariants vanish and its positive cohomology vanishes by its prime-to-\(p\) order. Inflation–restriction gives \(H^1(G_m,D)=0\), and the same unit difference gives \(H^0(E,M)=H^0(E_v,M)=0\).

If \(h\mid r\), put \(w=1+v_p(r)\) and take \(m=n+1\). Globally and locally \(H^0(M)=M[p^w]\), by \(v_p((1+p)^{-r}-1)=w\). A \(p^n\)-preimage of an element of \(M[p^w]\) belongs to \(M[p^{n+w}]\) and is fixed over \(J_{n+1}\), since \(v_p(z^{-r}-1)\ge n+w\) for \(z\in1+p^{n+1}\mathbb Z_p\). Thus the boundary restricts to zero and is contained in the inflation subgroup. The tame part acts trivially, and the \(p\)-Sylow of \(G_{n+1}\) is cyclic of order \(p^n\). For its generator acting by \(\alpha=(1+p)^{-r}\), the norm \(1+\alpha+\cdots+\alpha^{p^n-1}\) has valuation \(n\), by the lifting-the-exponent identity. Hence the cyclic cohomology formula gives
\[
 H^1(G_{n+1},D)=D/(\alpha-1)D,\qquad |H^1(G_{n+1},D)|=p^{\min(w,n)}.
\]
Inflation is injective and the boundary has this same order, which proves the claim. [Milne, *Class Field Theory*, Chapter II](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**Descent.** Restrict a finite-coefficient lift of a strict class to \(J_m\). The boundary calculation proves independence of the lift and triviality at each prime above \(p\). This gives an equivariant character of \(\mathrm{Cl}(\mathcal O_{J_m}[1/p])\) by class field theory. If the character is zero, the lift is a global inflation, hence a global boundary. Conversely take any equivariant character of this class group, regarded as a class on \(G_{J_m,S}\). Its transgression in \(H^2(G_m,D)\) maps to zero in the local inflation–restriction sequence, since the character at a place over \(p\) is zero. The comparison map on \(H^2(G_m,D)\) is the identity by full decomposition. The transgression is therefore zero and the character has a global finite-coefficient lift. At every \(p\)-adic place this lift inflates from \(H^1(G_m,D)\) and hence is a boundary there. Its image in \(H^1(G_{E,S},M)\) is strict. This proves the first isomorphism in (1). [Milne, *Class Field Theory*, Chapters II and V](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

On a character \(f\), conjugation acts by \((cf)(z)=(-1)^r f(cz)\). The complementary condition is therefore \(f(cz)=f(z)\). Since \(2\) is invertible on \(p\)-groups, norm and extension of ideals identify the plus part of the \(p\)-primary localized class group with the \(p\)-primary localized class group of \(J_m^+\) (their composites are \(2\) and \(1+c\)). This gives the second isomorphism. All primes over \(p\) in \(J_m\) are fixed by \(G_m\). Their contractions to \(J_m^+\) are fixed as well. At \(h\nmid r\), a character of the required type vanishes on the classes of these primes, as \(D^{G_m}=0\), proving the assertion for ordinary class groups.

### Support, exponents and weight periodicity

At \(n=1\) write \(\omega:G_1\hookrightarrow\mathbb F_p^\times\) for the cyclotomic character. For \(h\nmid r\), the \(p\)-rank of the complementary group is exactly the dimension of the \(\omega^{-r}\)-eigenspace in \(\mathrm{Cl}(J_1^+)/p\). The whole \(p\)-primary complementary group vanishes precisely when this eigenspace vanishes. For \(p>2t\) this test applies to every \(1\le r<t\), including when \(p=q\) or \(d\). At \(h\mid r\) the corresponding support test is the trivial-character quotient of the localized real class group at \(J_2^+\), modulo \(p\) and coinvariants under \(G_2\).

At arbitrary \(n\), (1) depends on the weight only modulo \(h p^{n-1}\) as an abstract group: use the common field \(J_{n+1}\) and the common character modulo \(p^n\). If \(b_n=\log_p|A^{\rm comp}_{p,r}(E)[p^n]|\) and \(b_0=0\), then \(b_n-b_{n-1}\) counts cyclic factors of order at least \(p^n\) for a finite group. In particular \(b_n=b_{n+1}\) certifies the entire group is killed by \(p^n\). The same finite test certifies all weights congruent to \(r\bmod hp^n\), with identical full invariant factors. For another treatment of weight periodicity in terms of logarithmic class groups, see [Jaulent and Michel, Theorems 3 and 4](https://www.math.u-bordeaux.fr/~jjaulent/Articles/NoyauxEtales.pdf).

### Reflection into the ordinary minus class group

Write \(\kappa\) for the cyclotomic character modulo \(p^n\), take \(J=J_m\) as in (1), and put \(C^-=\mathrm{Cl}(J)\{p\}^{c=-1}\). There is an injection of abelian groups
\[
 A^{\rm comp}_{p,r}(E)[p^n]\hookrightarrow
 \{z\in C^-[p^n]\mid gz=\kappa(g)^{r+1}z\ \text{for all }g\in G_m\}.
 \tag{3}
\]
The map uses a basis for \(D\) and a primitive \(p^n\)-th root of unity. Changing these choices scales the map by a unit modulo \(p^n\).

Take \(f\) from the first isomorphism of (1) in the complementary sign. In additive coordinates \(f(cz)=f(z)\) and \(f(gz)=\kappa(g)^{-r}f(z)\). Turn it into the Kummer character \(\beta(z)=\zeta_{p^n}^{f(z)}\) of the absolute Galois group of \(J\), via the unramified class group quotient. Under the usual action on characters, \(g\beta(z)=g(\beta(g^{-1}z))=\beta(z)^{\kappa(g)^{r+1}}\), and \(c\beta=\beta^{-1}\). The Kummer isomorphism sends \(\beta\) to a radical \(x\in J^\times/J^{\times p^n}\) with the same actions. The extension obtained by adjoining a \(p^n\)-th root of \(x\) is unramified at all finite places and split at every place above \(p\). At any finite place the valuation of that root is integral in the unramified extension. Thus \(p^n\mid v(x)\) everywhere, and at every place above \(p\), \(x\) is a local \(p^n\)-th power. Associating to \(x\) the class of the unique fractional ideal \(I\) satisfying \((x)=I^{p^n}\) gives an equivariant map to \(\mathrm{Cl}(J)[p^n]\). Changing a representative for \(x\) changes \(I\) by a principal ideal. [Sharifi, Kummer duality, Theorem 2.5.13](https://math.ucla.edu/~sharifi/notes/groupcoh-ch02.html)

The kernel on these radicals is trivial. A radical in the kernel is represented by a global unit. Its minus part modulo \(p^n\)-powers is represented by a root of unity, since the minus projector is \((1-c)/2\) and \(u/(cu)\) for a CM unit \(u\) has absolute value one at all embeddings, hence is a root of unity. At any place \(w\mid p\), the injection of global roots of unity into \(J_w\) stays injective modulo \(p^n\)-powers on the \(p\)-primary roots: a local \(p^n\)-th root of a root of unity is a root of unity itself, and the global and local \(p\)-power roots of unity both stop at \(\mu_{p^m}\). Indeed \(J_w\) is an unramified extension of \(\mathbb Q_p(\mu_{p^m})\), whereas adjoining \(\mu_{p^{m+1}}\) to the latter is totally ramified. Local splitting therefore kills the unit kernel. This proves (3).

In particular \(|A^{\rm comp}_{p,r}(E)[p^n]|\) divides the \(p\)-part of \(h^-(J)=h(J)/h(J^+)\). The equality \(|C^-|=p^{v_p(h^-(J))}\) follows by the same norm and extension argument for ordinary classes. Here \(J/\mathbb Q\) is abelian, so \(h^-(J)\) is accessible via the relative class number formula \(h^-(J)=Q_J|\mu(J)|\prod_{\chi\ {\rm odd}}(-B_{1,\chi}/2)\), over the primitive characters attached to \(J\), where the Hasse unit index \(Q_J\) is one or two. In particular, for \(p>2t\), the single condition \(p\nmid h^-(E(\mu_p))\) excludes that prime from the entire complementary weight window. The converse would require control of the real eigenspaces. [Relative class number formula](https://doi.org/10.1017/S0027763000007959)

### Counting all weights in the elementary cap

For \(t\ge2\) integral, \(P\ge2\), \(k\ge1\) integral, \(g=[E:\mathbb Q]\) and \(F=2^{a+2}qd\), one has
\[
 \sum_{1\le r<t}\ \sum_{2<p\le P}\log |A_{p,r}(E)[p^k]|
 \ \ll\ kg\,\frac{P(t+P)}{\log(2P)}\,\log(2FP).
 \tag{2}
\]
The constant is absolute and the estimate includes both conjugation signs. To see this, put \(J=J_1\), \(\Delta=G_1\), and \(V=H^1(G_{J,S},\mathbb F_p)\) with constant coefficients. Since \(|\Delta|=h\) is prime to \(p\), \(H^1(G_{E,S},\mathbb F_p(-r))\) identifies with the \(\omega^r\)-eigenspace of \(V\). The signs of the exponents in this statement and in (1) differ because \(V\) is a space of characters. The multiplication-by-\(p\) sequence bounds \(\log_p|A_{p,r}[p]|\) by the dimension of this eigenspace, and the interval sees each eigenspace at most \(\lceil (t-1)/h\rceil\) times. Multiplying by \(k\) bounds the order at depth \(k\).

Over \(J\) the dimension of \(V\) equals that of the Kummer group for \(p\)-units and \(p\)-classes. For \(m=[J:\mathbb Q]=gh\) the \(p\)-unit factor has size at most \(p^{2m}\). Minkowski's bound and counting ideals using \(\zeta_J(2)\) give \(h_J\le |D_J|\zeta(2)^m\). The conductor–discriminant formula gives \(|D_J|\le(Fp)^m\). Thus \(\dim V\log p\ll gh\log(2Fp)\). At each \(p\), all weights together contribute \(\ll kg(t+h)\log(2Fp)\). Finally \(h\le p-1\) and the Chebyshev bound \(\pi(P)\ll P/\log(2P)\) give (2). [Kummer exact sequence](https://doc.sagemath.org/html/en/reference/number_fields/sage/rings/number_field/selmer_group.html) · [Minkowski bound](https://www.math.ucla.edu/~sharifi/notes/algnum.pdf) · [Conductor–discriminant formula, Theorem 5.8](https://kconrad.math.uconn.edu/blurbs/gradnumthy/cfthistory.pdf)

Formula (2) saves the repeated payment for the same class and unit group across weights. Formula (1) supplies a finite class group test for the residual primes and for each successive power. Bounding the selected real class groups in aggregate, uniformly in the moving field and weight window, remains open.

## A Bernoulli test for the complementary group at a large prime

Let \(E=E_a\), let \(F=2^{a+2}qd\) be its common character modulus, and let \(c_E\) be complex conjugation on \(E\). Suppose \(1\le r<t\) and \(p>\max(F,2t+1)\) is prime. Write \(A^{\mathrm{comp}}_{p,r}\) for the \((-1)^r\)-eigenspace of \(c_E\) in the strict group and set \(k=p-1-r\). If \(A^{\mathrm{comp}}_{p,r}\ne0\), some primitive Dirichlet character \(\chi\) belonging to \(E\), with \(\chi(-1)=(-1)^r\), satisfies
\[
                 B_{k,\chi}\equiv0\pmod{\mathfrak p}
\]
at some prime \(\mathfrak p\mid p\) of its coefficient field. Here \(B_{k,\chi}\) is the generalized Bernoulli number at the **primitive conductor**. Thus failure of the divisibility for every eligible \(\chi,\mathfrak p\) excludes the entire complementary group at \(p\), including elements of higher order.

**Proof.** Write \(J=E(\mu_p)\), \(G=\operatorname{Gal}(E/\mathbb Q)\), and \(\Delta=\operatorname{Gal}(\mathbb Q(\mu_p)/\mathbb Q)\). Then \(\operatorname{Gal}(J/\mathbb Q)=G\times\Delta\). Use the Teichmüller character \(\omega\) on \(\Delta\), extended trivially on \(G\). Since \(E\) is unramified at \(p\), both \(E\) and every \(E_v\) above \(p\) have full mod-\(p\) cyclotomic image. Since \(0<r<p-1\), the invariants of \(M=\mathbb Q_p/\mathbb Z_p(-r)\) vanish globally and locally. The exact sequence for multiplication by \(p\) identifies \(A_{p,r}[p]\) with strict cohomology for \(M[p]=\mathbb F_p(-r)\). Restricting to \(J\) preserves strictness and is injective since \([J:E]=p-1\).

After extending residue-field scalars, choose a nonzero \(G\)-eigenvector of character \(\lambda\) in the complementary \(p\)-torsion. Then \(\lambda(c_E)=(-1)^r\). Its restriction is fixed by \(\Delta\) with the coefficient action included. Over \(J\), tensor its coefficient line by \(\mathbb F_p(r+1)\) to identify the corresponding line in \(H^1(J,\mu_p)\). Its character is
\[
              \eta=\lambda\,\omega^{r+1}.
\]
The same symbols denote the unique prime-to-\(p\) lifts of these characters. The absolute complex conjugation in \(G\times\Delta\) has coordinates \((c_E,-1)\), so \(\eta\) is odd. Moreover \(\eta\ne\omega\) already on \(\Delta\).

Kummer theory sends this line into classes of \(z\in J^\times/(J^\times)^p\) whose valuations are multiples of \(p\) at every finite place. Indeed the associated extension is unramified away from \(p\) and split at \(p\). The map \((z)=\mathfrak a^p\mapsto[\mathfrak a]\in\mathrm{Cl}(J)[p]\) has kernel the units modulo \(p\)-th powers. In a CM field \(u/\bar u\) is a root of unity for every unit \(u\), by Kronecker's theorem; since \(2\) is invertible modulo \(p\), the odd part of the unit group modulo \(p\)-th powers is generated by roots of unity. Its only possible character is \(\omega\), because \(J\) contains \(\mu_p\) and \([J:\mathbb Q]\) is prime to \(p\). Consequently \(\mathrm{Cl}(J)[p]^\eta\ne0\).

Set \(\chi=\lambda^{-1}\), take its primitive conductor \(f\mid F\), and put \(m=fp\). Then \(\eta^{-1}=\chi\omega^{-r-1}\) is primitive of conductor \(m\), as \(p\nmid f\) and \(0<r+1<p-1\). The \(\eta\)-classes descend by norm to the character field \(K=J^{\ker\eta}\) and extend injectively to \(\mathbb Q(\mu_m)\) on \(p\)-parts. Indeed extension after norm on the invariant component is multiplication by \([J:K]\), and norm after extension from \(K\) is multiplication by \([\mathbb Q(\mu_m):K]\). Both indices are prime to \(p\), since \([J:\mathbb Q]\) and \(\varphi(f)(p-1)\) are prime to \(p\) under \(p>F\).

Apply the cyclotomic Stickelberger theorem in \(\mathbb Q(\mu_m)\). For \(b\) prime to \(m\), the integral annihilator \((b-\sigma_b)\sum_{(a,m)=1,\,1\le a\le m}(a/m)\sigma_a^{-1}\) acts on the \(\eta\)-part by \((b-\eta(b))B_{1,\eta^{-1}}\). Choose \(b\equiv1\bmod f\) with \(b\bmod p\) a primitive root. Its smoothing factor is a \(p\)-unit since \(0<r<p-1\). The surviving class forces \(B_{1,\chi\omega^{-r-1}}\equiv0\bmod\mathfrak p\). Using \(m=fp\) here avoids extraneous Euler factors from primes dividing \(F/f\). [Stickelberger, 1890](https://doi.org/10.1007/BF01721360) · [Sharifi, Theorem 4.5.6 and the character calculation following Theorem 4.5.7](https://www.math.ucla.edu/~sharifi/notes/iwasawa-ch04.html)

Finally \(\theta=\chi\omega^k\) is even and nontrivial on \(\Delta\). Its Kubota–Leopoldt power series is integral because \(\theta\) has prime-to-\(p\) order and a smoothing element with \(\theta(b)-1\) a unit. Hence \(L_p(\theta,0)\equiv L_p(\theta,1-k)\bmod\mathfrak p\), since both power-series arguments lie in \(p\mathbb Z_p\). Interpolation at the two integers reads
\[
 L_p(\theta,0)=-B_{1,\chi\omega^{-r-1}},\qquad
 L_p(\theta,1-k)=-(1-\chi(p)p^{k-1})B_{k,\chi}/k .
\]
The first character is ramified at \(p\), and in the second expression both \(k\) and \(1-\chi(p)p^{k-1}\) are units at \(p\). This proves the test. [Kubota and Leopoldt, 1964](https://doi.org/10.1515/crll.1964.214-215.328) · [Sharifi, Proposition 5.3.15, Proposition 5.4.3 and Remark 5.4.4](https://www.math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

The handoff has \(\log F\ll\log(2x)+x^{\varepsilon/5}(1+\log^2x)\), \(t\le x^{401}\) and \(P=\exp(x^\varepsilon/8)\). For each fixed \(\varepsilon>0\), every \(p>P\) satisfies the hypotheses for all sufficiently large \(x\). The converse divisibility implication and an upper bound on the total contribution of the primes which pass the test remain open here.

**Finite checkpoint.** At \(E_0=\mathbb Q(\sqrt{-3},\sqrt{-23})\), \(r=1\), \(p=277\), the two eligible characters have conductors \(f=3,23\). The coefficients of \((b-\sigma_b)\Theta_{fp}\) at \(\sigma_a^{-1}\) are \(\lfloor ba/(fp)\rfloor\). Thus its eigenvalue modulo 277 can also be computed directly as
\[
 \sum_{a\in(\mathbb Z/fp)^\times} \left\lfloor\frac{ba}{fp}\right\rfloor
           \chi(a)\,a^{274}\pmod{277},
\]
using least positive representatives. The respective residues are \(250\) for \(b=31\) and \(184\) for \(b=24\). Both are nonzero, so the paper argument gives \(A^{\rm comp}_{277,1}(E_0)=0\). The exact sums are recorded as \(\texttt{conductor_three_residue}\) and \(\texttt{conductor_twenty_three_residue}\) in the Lean module \(\texttt{Reimann.Bernoulli}\). The passage from class groups to the sums is a paper proof.

## Appendix A. All dyadic invariant factors and the weight average

Let \(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\), \(E_a=Q_a(\sqrt{-q},\sqrt{-d})\), where \(q,d\) are distinct primes with \(q\equiv3\bmod8\) and \(d\equiv7\bmod16\). Let \(A_{2,r}(E_a)\) be the kernel of dyadic localization on \(H^1(G_{E_a,S},\mathbb Q_2/\mathbb Z_2(-r))\), with \(S\) the places above 2. Write \(C_n=\mathbb Z/n\mathbb Z\), \(C_1=0\), and \(v=v_2\), where \(v(2)=1,\ v(0)=+\infty\).

### A.1. Three low-conductor values

For a positive odd weight \(r\), let \(s=5^{-r}\), let \(\psi\) correspond to \(\mathbb Q(\sqrt{qd})\), and let \(\rho_z\) be the even character modulo 16 determined by \(\rho_z(5)=z\) for \(z=1,-1,i,-i\). Write
\[
 B_z=\tfrac12 L^{(2)}(-r,\psi\rho_z),\qquad
 k=v(B_1),\quad l=v(B_{-1}),\quad h=v(B_i B_{-i}).
\]
The superscript removes the Euler factor at 2 from the primitive value. The two real values are rational and \(B_{-i}=\overline{B_i}\). All four are nonzero by their parity and the Dirichlet functional equation.

The preceding dyadic descent identifies the dual group with \(X/D_aY\), where \(Y=\mathbb Z_2b\oplus\mathbb Z_2c\), \(X=\mathbb Z_2(2b)\oplus\mathbb Z_2c\), and
\[
 J=\begin{pmatrix}1&-C_0\\1&1-C_1\end{pmatrix},\qquad
 D_a=J^{2^a}-s^{2^a}I,\qquad C_0,C_1\in2\mathbb Z_2.
\]
Put \(\tau=2-C_1\), \(\Delta=1-C_1+C_0\), and \(f(Z)=Z^2-\tau Z+\Delta=P(Z-1)\). Thus \(\tau\) is even and \(\Delta\) odd. Mizusawa's normalization \(L_2(u,\psi)=2\Phi(5^u-1)\) and identity \((P)=(\Phi)\) give equality of valuations at these specializations. Twisting by \(\rho_z\) replaces \(s\) by \(z^{-1}s\). The interpolation sign character to the power \(r+1\) is trivial for odd \(r\). Interchanging the two quartic characters leaves their product invariant. Hence
\[
 k=v(f(s)),\qquad l=v(f(-s)),\qquad
 h=v(f(is)f(-is))=v\big((\Delta-s^2)^2+s^2\tau^2\big).
\]
[Mizusawa, Theorem 2.2 and the normalization on p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Sharifi, Chapter 5, interpolation and twisting](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

### A.2. The classification

Write the strict group as \(C_{2^{e_1}}\oplus C_{2^{e_2}}\), where \(0\le e_1\le e_2\). Put \(m=\min(k,l)\), \(M=\max(k,l)\).

| Layer and condition | \(e_1\) | \(e_2\) |
|---|---:|---:|
| \(a=0\) | \(0\) | \(k-1\) |
| \(a=1\) | \(m-1\) | \(M\) |
| \(a\ge2,\ k,l\ge2\) | \(m+a-2\) | \(M+a-1\) |
| \(a\ge2,\ k=l=1\) | \(\lceil h/2\rceil+a-2\) | \(\lfloor h/2\rfloor+a-1\) |

The last two cases exhaust the possibilities. The first has \(h=2\), and the second has \(h\ge3\). The earlier descent gives \(C_2\) at every positive even weight and every layer.

**Proof.** Put \(T=J-I\). For any endomorphism \(A I+B T\) taking \(Y\) into \(X\), its matrix with the displayed domain and target bases is
\[
 \begin{pmatrix}A/2&-C_0B/2\\ B&A-C_1B\end{pmatrix}.
\]
The ideal of entries is \((A/2,B)\). Its valuation gives the smaller Smith exponent. The sum of the exponents is the determinant valuation in \(Y\) minus one because \([Y:X]=2\). The character group has the same invariant factors.

At \(a=0\), \(D_0=(1-s)I+T\) has \(B=1\), proving cyclicity. At \(a=1\), Cayley–Hamilton gives \(D_1=\tau(J-sI)-f(s)I\). Since \(s-1\in4\mathbb Z_2\), the entry ideal is \((f(s)/2,\tau)\). From \(f(-s)-f(s)=2s\tau\) this equals \((f(s)/2,f(-s)/2)\). Its valuation is \(m-1\), and the determinant valuation in \(Y\) is \(k+l\). This proves the second row.

Next, \(f(s)\equiv f(-s)\bmod4\) and both are even. Divisibility by four is equivalent to \(1+\Delta\equiv\tau\bmod4\), since \(s\equiv1\bmod4\). Equivalently, precisely one of \(\Delta-s^2\) and \(\tau\) is \(2\bmod4\). The sum-of-squares formula in A.1 then gives \(h=2\). In the other case both quantities are \(2\bmod4\), or both are divisible by four. This gives \(h\ge3\) and \(k=l=1\).

Since \(J^2\equiv I\bmod2\), the matrices \(D_1\) and \(F=J^2+s^2I\) are even. If \(h=2\), then \(v(\det F)=2\), so \(FY=2Y\). Therefore \(D_2Y=2D_1Y\), increasing both Smith exponents by one.

If \(k=l=1\), \(v(\det D_1)=2\) gives \(D_1Y=2Y\), and \(D_2Y=2FY\) by commutativity. Write \(u=s^2-\Delta\), so \(F=(u+\tau)I+\tau T\). Applying the entry ideal formula to \(2F\) gives the smaller exponent
\[
 e_1=\min\{v(u+\tau),1+v(\tau)\}.
\]
If \(v(u)\ne v(\tau)\), put \(j=\min(v(u),v(\tau))\). Then \(e_1=j\) and \(h=2j\). If both valuations equal \(j\), then \(e_1=j+1\), and \(h=2j+1\) since the squares of odd units are \(1\bmod8\). The possibility \(u=\tau=0\) is excluded by the nonzero quartic values. Thus \(e_1=\lceil h/2\rceil\), and the sum of the exponents is \(k+l+h-1=h+1\).

Finally \(J^2\equiv I\bmod2\) implies \(J^4\equiv I\bmod4\). For \(a\ge2\), \(J^{2^a}+s^{2^a}I\equiv2I\bmod4\), so this factor is twice an automorphism of \(Y\). Factoring \(D_{a+1}\) gives \(D_{a+1}Y=2D_aY\). Multiplying a full sublattice by two increases both Smith exponents in \(X\) by one.

### A.3. Two uniform profiles

Mizusawa gives \(P(T)\equiv T^2+15604T+26266\bmod 2^{15}\) for \(q=3,d=7\). Thus \(\tau\equiv2\) and \(\Delta\equiv3\bmod4\). Every odd \(r\) gives \(k=l=1\) and \(h=3\). The group is trivial at \(a=0\), is \(C_2\) at \(a=1\), and is \(C_{2^a}\oplus C_{2^a}\) at every \(a\ge2\). For \(q=3,d=23\), the two real values at \(r=1\) force \(C_0\equiv4\bmod8\) and \(C_1\equiv2\bmod4\) as in the preceding checkpoint. This gives \(k=l=2,\ h=2\) at every odd weight, recovering \(C_{2^a}\oplus C_{2^{a+1}}\) for all \(a\). [Mizusawa, p. 134, numerical example](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

An independent check at \(r=1\) uses \(m_0=16qd\), \(\psi(b)=(b/q)(b/d)\) on units, and \(\rho_z(b)=z^j\) for \(b\equiv\pm5^j\bmod16\). The normalized value is the sum over \(1\le b\le m_0\) coprime to \(m_0\) of
\[
 -\psi(b)\rho_z(b)\frac{6b^2-6m_0b+m_0^2}{24m_0}.
\]

| \((q,d)\) | \(B_1\) | \(B_{-1}\) | \(B_i\) | \((k,l,h)\) |
|---|---:|---:|---:|---:|
| \((3,7)\) | \(-6\) | \(-54\) | \(-66-142i\) | \((1,1,3)\) |
| \((3,23)\) | \(-36\) | \(-308\) | \(-404-862i\) | \((2,2,2)\) |

### A.4. The uniform sum over weights

For \(t\ge2\), with natural logarithms, one has the strengthened estimate
\[
 \sum_{1\le r<t}\log |A_{2,r}(E_a)|
 \ll t\bigl(a+\log(2qd)+\log(t+1)\bigr)
\]
with an absolute implied constant.

**Proof.** Let \(G(S)=\det(J^4-S^4I)\), a monic polynomial of degree eight over \(\mathbb Z_2\). Its roots \(\alpha\), counted with multiplicity in \(\overline{\mathbb Q}_2\), are integral. For each root choose an odd \(r_*\in[1,t)\) maximizing \(v(5^{-r}-\alpha)\). None of the samples is a root by A.1. If \(r\ne r_*\), the ultrametric inequality and the choice of \(r_*\) yield
\[
 v(5^{-r}-\alpha)\le v(5^{-r}-5^{-r_*})
 =2+v(r-r_*).
\]
The last identity is the lifting-the-exponent formula for 5. Summing over the other sample weights costs \(O(t)\) per root, since \(\sum_{1\le j\le n}v(j)=v(n!)\le n\) on either side of \(r_*\).

The one exceptional contribution per root is at most \(v(G(5^{-r_*}))\), since all root terms are nonnegative. This valuation equals \(k+l+h\) at weight \(r_*\). To record the height bound explicitly, put \(n=r_*+1\), \(m_0=16qd\), and inflate all four characters to \(m_0\). Each depleted value is
\[
 -\frac{m_0^{n-1}}n \sum_{b=1}^{m_0}(\psi\rho_z)(b)B_n(b/m_0).
\]
After expanding the Bernoulli polynomial, multiplying each normalized value by \(2nm_0(n+1)!\) makes it an algebraic integer, since \((j+1)!B_j\) is integral. The bound \(|B_j|\le j!\) gives absolute values \(O(m_0^n n!)\) at every complex embedding before scaling. The product of the four scaled values is a nonzero rational integer. Its logarithmic size is \(O(n(\log(2qd)+\log(n+1)))\), and bounds \(v(G(5^{-r_*}))\) up to an absolute factor. Thus the eight exceptional terms together cost \(O(t(\log(2qd)+\log(t+1)))\). [NIST DLMF, Dirichlet–Hurwitz formula](https://dlmf.nist.gov/25.15#E3) · [Hurwitz values at negative integers](https://dlmf.nist.gov/25.11#E14)

For odd \(r\), the determinant valuation at \(a\le2\) is at most \(v(G(5^{-r}))\), by factoring \(G(5^{-r})\) into the lower-layer determinant and integral factors. Every step above \(a=2\) adds exactly two to this valuation. Each even weight contributes \(\log 2\). Summation proves the bound.

## Appendix B. The complementary group at 3 in the first dyadic layer

Take \(q=19,\ d=16871,\ D=qd=320549\). Put \(R=\mathbb Q(\sqrt D)\), \(E_0=\mathbb Q(\sqrt{-q},\sqrt{-d})\), \(E_1=E_0(\sqrt2)\), \(K=E_1^+=R(\sqrt2)\), and \(T_n=\mathbb Q(\zeta_{3^{n+1}})^+\) for \(n\ge0\). Let \(A_{3,r}(F)\) be strict degree-one cohomology for \(M=\mathbb Q_3/\mathbb Z_3(-r)\), unramified outside 3 and zero at every completion above 3. Its complementary eigenspace over a CM field has complex-conjugation eigenvalue \((-1)^r\).

**Theorem.** For every positive even \(r\), \(A_{3,r}^{\rm comp}(E_1)\simeq C_3\). For every positive odd \(r\), it vanishes. For every \(n\ge0\), extension of ideals gives
\[
 \mathrm{Cl}(RT_n)\{3\}\ \xrightarrow{\;\sim\;}\ \mathrm{Cl}(KT_n)\{3\}\simeq C_3 .
\]
If \(H\) is the splitting field of \(Z^3-164Z+801\), the respective Hilbert 3-class fields are \(HT_n\) and \(HKT_n\).

### Reproducible finite certificates

For each positive fundamental discriminant \(\Delta\) below, enumerate integer pairs \((Q,P)\) with \(0<P<\sqrt\Delta\), \(Q>0\) even, \(\sqrt\Delta-P<Q<\sqrt\Delta+P\), and \(2Q\mid\Delta-P^2\). Iterate \(P'=\lfloor(\lfloor\sqrt\Delta\rfloor+P)/Q\rfloor Q-P,\ Q'=(\Delta-P'^2)/Q\). The reduced-ideal cycles are the ordinary ideal classes. Each entry gives a cycle length followed by its lexicographically least \((Q,P)\). [Mollin, section 1](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/FACF38CC28A803AF5A06B806D3392812/S000497270001354Xa.pdf)

| Discriminant | Class number | Cycles |
|---:|---:|---|
| 8 | 1 | \(1\ (2,2)\) |
| 320549 | 3 | \(36\ (2,565),\ 36\ (10,557),\ 36\ (10,563)\) |
| 2564392 | 2 | \(424\ (2,1600),\ 400\ (4,1600)\) |
| 57 | 1 | \(6\ (2,7)\) |
| 50613 | 5 | \(4\ (2,223),\ 6\ (26,219),\ 6\ (26,223),\ 8\ (38,205),\ 8\ (38,213)\) |
| 456 | 2 | \(6\ (2,20),\ 10\ (6,18)\) |
| 404904 | 2 | \(168\ (2,636),\ 148\ (4,636)\) |

The third quadratic subfield \(V=\mathbb Q(\sqrt{641098})\) of \(K\) has discriminant 2564392 and two primes over 3. The following Pell certificate gives a norm-one unit \(u+v\sqrt{641098}\). At the two places \(\sqrt{641098}\equiv\pm1\bmod9\), so its residues are 2 and 5.

~~~python
from math import isqrt

d = 641098
a0 = a = isqrt(d)
p, q = 0, 1
u0, u, v0, v = 0, 1, 1, 0
for _ in range(424):
    u0, u = u, a*u + u0
    v0, v = v, a*v + v0
    p = q*a - p
    q = (d - p*p) // q
    a = (a0 + p) // q
assert u*u - d*v*v == 1 and (u % 9, v % 9) == (8, 3)
~~~

### Class groups throughout the cyclotomic 3-tower

The cubic \(f(Z)=Z^3-164Z+801\) is irreducible modulo 5 with positive squarefree discriminant \(D\). Its totally real \(S_3\)-splitting field \(H\) is cyclic cubic over \(R\). At the ramified primes \(q,d\), the tame cyclic inertia group has even order, hence order two. Thus \(H/R\) is the unramified cubic extension supplied by \(h(R)=3\). Also \(3\nmid h(H)\). Otherwise a further unramified cubic extension of \(H\) and its conjugates over \(R\) would give a finite unramified 3-group over \(R\) of order at least nine with cyclic abelianization of order at most three. A finite \(p\)-group with cyclic abelianization is cyclic.

The three primes of \(H\) above 3 have unramified quadratic completions. For distinct roots \(x,y\) of \(f\), the bottom-layer unit is \(\eta=U(x)+W(x)y\), where
\[
\begin{aligned}
U(x)&=-6546564915489+518244484752x+65084790424x^2,\\
W(x)&=961424555660-76109400788x-9558264431x^2 .
\end{aligned}
\]
The relative norm \(U^2-xUW+(x^2-164)W^2\) reduces modulo \(f(x)\) to \(B=-1831220x^2+27096052x-99597647\), with \(\operatorname{Res}(f,B)=1\). Thus the algebraic integer \(\eta\) is a unit. Modulo 9 take \(s^2=2\) and \((x,y)=(0,s),(s,0),(s,-s)\) at the three places. The residues of \(\eta\) are \(8s,8,5s\), with local norms \(7,1,4\bmod9\).

The three primes are totally ramified in \(HT_n/H\), cyclic of degree \(3^n\). All other finite primes are unramified. At each place take the local norm to \(\mathbb Q_3\), then its residue in \((\mathbb Z/3^{n+1})^\times/\{\pm1\}\simeq\mathbb Z/3^n\). Cyclotomic reciprocity and transitivity show that a global unit which is a norm from \(HT_n\) has trivial image in all three coordinates. In exponents with generator 4, the reductions of the unit vector and a cyclic conjugate are \((2,0,1)\) and a rotation. A two-by-two minor is nonzero modulo 3, hence invertible modulo \(3^n\). The index of the norm units in \(\mathcal O_H^\times\) is therefore divisible by \(3^{2n}\) for every \(n\ge1\). Chevalley's ambiguous class number formula gives
\[
 |\mathrm{Cl}(HT_n)^{\operatorname{Gal}(HT_n/H)}|
 =\frac{h(H)3^{2n}}{[\mathcal O_H^\times:\mathcal O_H^\times\cap N_{HT_n/H}(HT_n)^\times]}.
\]
Its 3-part is trivial. Any nontrivial finite abelian 3-group acted on by a 3-group has a nontrivial fixed subgroup, by orbit counting. Consequently \(3\nmid h(HT_n)\). The unramified cubic \(HT_n/RT_n\) is its full Hilbert 3-class field. Its degree is three because \(RT_n/\mathbb Q\) is abelian and \(R\) is the maximal abelian subfield of \(H\). [Yu, the ambiguous class number formula for cyclic extensions](https://ncts.ntu.edu.tw/upload/blistfs1602103542127806.pdf) and [Milne, local and global reciprocity](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

Apply the same formula to \(\mathbb Q,\mathbb Q(\sqrt2),V\) after adjoining \(T_n\). The first two have class number one and one totally ramified prime over 3. For \(V\), the two totally ramified primes give a numerator factor \(3^n\) after division by the extension degree. The Pell unit has residue \(2\bmod9\) at one place, hence its class generates the cyclic norm-residue quotient of order \(3^n\). The norm-unit index absorbs \(3^n\). All three towers have trivial 3-class groups.

The four character idempotents of \(\operatorname{Gal}(KT_n/T_n)\simeq C_2^2\) split the 3-class group. Extension of ideals identifies the invariant 3-classes for each subgroup with the classes from its fixed field, since composing extension and norm in the two orders gives multiplication by the subgroup order and the sum of its elements. The only nonzero component comes from \(RT_n\). Since \(KT_n/\mathbb Q\) is abelian, \(HKT_n/KT_n\) remains cubic and unramified by base change. This proves both tower claims.

### Strict descent

For even \(r\), prime-to-3 quadratic descent identifies \(A_{3,r}^{\rm comp}(E_1)\) with \(A_{3,r}(K)\). Such descent respects the strict local conditions. At primes away from 3 the coefficients are unramified, and restriction to an inertia subgroup of prime-to-3 index detects ramification.

Put \(l=1+v_3(r)\). The global and local cyclotomic images for \(K\) at 3 are \(\mathbb Z_3^\times\), since \(K\) is unramified at 3. Hence \(H^0(M)=M[3^l]\) globally and at every prime over 3. For \(j\ge1\), lift a class of \(A_{3,r}(K)[3^j]\) to cohomology with coefficients \(M[3^j]\) by the multiplication sequence. Its local restrictions at 3 are boundaries from \(H^0(M)/3^j\). After adjoining \(T_j\), the cyclotomic action on \(M[3^{j+l}]\) is trivial by evenness of \(r\) and the binomial valuation for units congruent to \(\pm1\bmod 3^{j+1}\). All local boundaries and the global ambiguity of the lift thus vanish. The restricted lift gives a character of \(\mathrm{Cl}(KT_j)\) into \(M[3^j]\). This assignment is injective. If the character is zero, the original \(M\)-class inflates from \(H^1(\operatorname{Gal}(KT_j/K),M^{G_{KT_j}})\). At any prime above 3 the local quotient is this full Galois group and its coefficient invariants are identical to the global ones, so local inflation detects the class. The tower result now bounds each \(|A_{3,r}(K)[3^j]|\) by three.

The bottom-field \(C_3\) survives by restriction from \(R\) because \([K:R]=2\). Indeed the nonzero unramified cubic mod-3 character of \(R\) is strict, as the only prime \((3)\) over 3 is principal. It gives a nonzero \(M\)-class because global and local \(H^0(M)/3\) agree and the local boundary map is injective. This proves the even case.

For odd \(r\) the residual cyclotomic action is nontrivial globally and at each 3-adic place of \(E_1\). Therefore all these \(H^0(M)\) vanish and strict 3-torsion is strict cohomology with \(\mathbb F_3(-r)\) coefficients. Over \(J=E_1(\mu_3)\), this is a character of the 3-integer class group with the appropriate signs. Complex conjugation acts on the coefficients by \(-1\), so its complementary sign selects even ideal classes from \(J^+=\mathbb Q(\sqrt D,\sqrt{57},\sqrt2)\). The involution of \(J/E_1\) negates \(\mu_3\) and selects the minus sign on ideal classes. The four corresponding quadratic fields have discriminants \(57,50613,456,404904\). The norm and extension identities apply since the Galois group has 2-power order. Their class numbers \(1,5,2,2\) show their 3-integer class groups have trivial 3-part. Thus the odd complementary group has no element of order 3 and vanishes.

The theorem fixes dyadic layer one throughout the \(T_n\)-tower. Determining the complementary groups at dyadic layers \(a\ge2\) remains open here.
