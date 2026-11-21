# The exact contribution at 2

**Ordinary zeta arithmetic window · November 20, 2026**

Let \(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\), \(a\ge0\), and let
\[
 E_a=Q_a(\sqrt{-q},\sqrt{-d}),\qquad
 q\equiv3\pmod8,\quad d\equiv7\pmod{16}
\]
for distinct odd primes \(q,d\). For \(r\ge1\) put \(M_r=\mathbb Q_2/\mathbb Z_2(-r)\). The group studied here is
\[
 A_{2,r}(E_a)=\ker\!\left(H^1(G_{E_a,S},M_r)\longrightarrow
             \bigoplus_{v\mid2}H^1(E_{a,v},M_r)\right),\qquad S=\{v:v\mid2\}.
\]
Here \(G_{E_a,S}\) allows ramification only above 2. “Strict” means that the class vanishes at every listed completion. The previous note computed the local correction between this group and the 2-part of \(K_{2r}(\mathcal O_{E_a})\). We now compute the order of the strict group itself.

## 1. The result

**Every even weight gives \(A_{2,r}(E_a)\simeq\mathbb Z/2\mathbb Z\), at every layer.** For odd \(r\), set \(N=2^a\), let \(\psi\) be the quadratic character of \(\mathbb Q(\sqrt{qd})\), and let \(\rho\) range over the \(N\) characters of \(Q_a/\mathbb Q\). Write \(L^{(2)}\) for the Dirichlet \(L\)-value with the Euler factor at 2 removed, using the primitive character before removal. With \(v_2(2)=1\),
\[
 \boxed{\displaystyle
 \log_2 |A_{2,r}(E_a)| =
 v_2\!\left(\prod_{\rho}L^{(2)}(-r,\psi\rho)\right)-N-1
 \quad(r\ {\rm odd}).} \tag{1}
\]
The product is a nonzero rational number. There is a shorter form using only the two real fields. Write \(R_a=Q_a(\sqrt{qd})=E_a^+\). Abelian factorization gives \(\zeta_{R_a}(s)/\zeta_{Q_a}(s)=\prod_\rho L(s,\psi\rho)\). Only the trivial \(\rho\) has an Euler factor at 2, and deleting it multiplies the value at \(-r\) by \(1+2^r\), an odd integer. Thus (1) is equivalently
\[
 \log_2|A_{2,r}(E_a)|
   =v_2\!\left(\frac{\zeta_{R_a}(-r)}{\zeta_{Q_a}(-r)}\right)-2^a-1
 \qquad(r\ {\rm odd}).
\]
[Sharifi, Chapter 4, abelian zeta factorization](https://www.math.ucla.edu/~sharifi/notes/iwasawa-ch04.html)

At fixed \(q,d\), **each layer increase \(a\to a+1\), starting at \(a=2\), multiplies the odd-weight order by exactly four**. In fact three independent exact evaluations determine the whole odd-weight sequence. Set \(B_z=L^{(2)}(-r,\psi\rho_z)/2\), where \(\rho_z(5)=z\), for \(z=1,-1,i\). The omitted fourth value is \(\overline{B_i}\). At layers \(0\) and \(1\) the orders are \(2^{v_2(B_1)-1}\) and \(2^{v_2(B_1B_{-1})-1}\). For every \(a\ge2\) they are
\[
 4^{a-2}\,2^{v_2(B_1 B_{-1} B_i\overline{B_i})-1}.
\]
The three values set the starting sizes. The proof of the universal multiplier uses the quadratic polynomial in §4.

Uniformly for \(t\ge2\),
\[
 \sum_{1\le r<t}\log |A_{2,r}(E_a)|
 \ll t(a+1)+t^2\bigl(\log(2qd)+\log(t+1)\bigr). \tag{2}
\]
Unsubscripted logarithms are natural. With \(t=\lfloor x^{401}\rfloor\), \(a=O(\log x)\), and the auxiliary primes of the signed-twist window, the right side is polynomial in \(x\) for fixed \(\varepsilon>0\). It is \(o(\exp(x^\varepsilon/2))\). The dyadic factor of the window integer is therefore within budget, with the same primes already selected for the analytic estimates.

Section 8 determines both cyclic factors for every prime pair selected by the analytic window from two rational evaluations at each odd weight. It also improves (2) to \(O(t(a+\log(2qd)+\log(t+1)))\). Section 5 gives the stronger weight-one shortcut for \(q=3,d=23\). Section 6 computes the entire complementary group at 3 at every weight of the bottom field for \(q=19,d=16871\).

## 2. The two lattices

Put \(Q_\infty=\bigcup_j Q_j\), \(k=\mathbb Q(\sqrt{-qd})\), \(k_\infty=k Q_\infty\), and
\[
 L=E_a(\mu_{2^\infty})=Q_\infty(i,\sqrt q,\sqrt d).
\]
This one field \(L\) works for every \(a\). It is the cyclotomic tower of the genus field \(k(\sqrt q,\sqrt d)\). Mizusawa's Theorem 2.2 and its proof apply with exactly the two residue conditions above. We use the unconditional presentation in that theorem. [Mizusawa, *On the maximal unramified pro-2-extension over the cyclotomic \(\mathbb Z_2\)-extension of an imaginary quadratic field*, §§2, 4.2, especially pp. 117–119 and 126–131](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

Here are the pieces of that presentation needed in the proof. Let \(G\) be the Galois group of the maximal unramified pro-2-extension of \(k_\infty\). Denote the paper's generators by \(A,B,C\), in that order, to distinguish the generator \(A\) from the layer \(a\). The subgroup fixing \(L\) is the abelian group \(H=\langle A^2,B^2,C\rangle\simeq\mathbb Z_2^3\). The decomposition subgroup above 2 in \(G\) is the normal group \(\langle A\rangle\). Killing it gives
\[
 Y=G/\langle A\rangle=\mathbb Z_2 b\oplus\mathbb Z_2 c,\qquad
 X=H/(H\cap\langle A\rangle)=\mathbb Z_2(2b)\oplus\mathbb Z_2 c\subset Y, \tag{3}
\]
where \(b,c\) are the images of \(B,C\). The group \(X\) classifies abelian pro-2 extensions of \(L\) unramified everywhere with both dyadic primes split. Indeed \(L/k_\infty\) is an unramified Galois 2-extension, so unramified pro-2 extensions over \(L\) lie in the same maximal tower by taking their normal closures. Inside \(H\) the dyadic decomposition subgroup is \(\langle A^2\rangle\).

The image of \(B\) interchanges the two primes above 2 in \(L\). In fact \(G/H\) has order four, and its dyadic decomposition subgroup is generated by \(AH\), while \(BH\) lies outside it. Both primes already occur in \(E_a\). At 2, \(-q\) generates the unramified quadratic extension, \(-d\) is a square, and the real cyclotomic factor is totally ramified. Thus the local degree of \(E_a/\mathbb Q\) is \(2^{a+1}\), half its global degree. Each prime has full decomposition group in \(L/E_a\). One can also see this from the local cyclotomic image, which equals the global image \(\{\pm1\}(1+2^{a+2}\mathbb Z_2)\).

Write \(U=\operatorname{Gal}(L/E_a)=\langle\sigma\rangle\times\langle g\rangle\), with cyclotomic characters \(-1\) and \(5^N\), respectively. Here the second factor is procyclic and \(g=\gamma^N\), where \(\gamma\) acts by 5 in the cyclotomic tower and fixes the genus field. On \(Y\) the presentation gives
\[
 \gamma b=b+c,\qquad \gamma c=-C_0 b+(1-C_1)c,\qquad
 P(T)=\det((1+T)I-\gamma)=T^2+C_1T+C_0, \quad C_0,C_1\in2\mathbb Z_2. \tag{4}
\]
The involution \(\sigma\) acts as \(-1\) on \(Y\). It fixes \(Q_\infty\) and negates \(\sqrt{-qd}\). In each finite layer \(kQ_j/Q_j\), an ideal class times its conjugate is the extended norm. The 2-part of the class group of \(Q_j\) is trivial by Weber's odd-class-number theorem. Thus conjugation acts by inversion on the 2-class groups and on their inverse limit. The quotient of that limit by its torsion is \(Y\). This also proves the sign on the sublattice \(X\). [Mizusawa, §§2, 3.1, 4.2](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Miller, §2, on Weber's theorem](https://www.impan.pl/shop/publication/transaction/download/product/83125)

## 3. What the two local conditions impose

Over \(L\) the twist is trivial. Restriction sends a strict class to an equivariant continuous homomorphism \(f:X\to M_r\), where equivariance refers to \(U\). This map is injective. Its kernel would inflate from \(H^1(U,M_r)\), and restriction to just one dyadic place detects that inflation because its decomposition group is all of \(U\).

Conversely every \(f\in\operatorname{Hom}_U(X,M_r)\) lifts to a global cohomology class with ramification allowed above 2. To see this, inflate \(f\) on the subgroup fixing \(L\) and consider its transgression in \(H^2(U,M_r)\) in the five-term inflation–restriction sequence. It restricts to zero on a dyadic decomposition group above \(L\), by the splitting condition. Naturality thus sends the transgression to zero under the identity \(H^2(U,M_r)\to H^2(U,M_r)\) for the local quotient. This proves the lifting assertion. The lifts differ by a global inflation from \(H^1(U,M_r)\). [Milne, *Class Field Theory*, Chapter II, inflation–restriction](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

Each of the two local restrictions of a lift inflates from \(H^1(U,M_r)\). Their difference is the obstruction to choosing a single lift zero at both primes. It has the following explicit representative:
\[
 \delta_f(t)=f((1-t)b),\qquad t\in U. \tag{5}
\]
For the verification, take an absolute lift of \(B\) over \(k_\infty\). For each \(t\), take a lift \(s_t\) in the first dyadic decomposition group. At the second place use \(Bs_tB^{-1}\). Both project to \(t\), since \(L/\mathbb Q\) is abelian. Their quotient \(Bs_tB^{-1}s_t^{-1}\) fixes \(L\) and maps to \(b-tb\) in \(Y\). This lies in \(X\). The cocycle identity gives (5), since the quotient acts trivially on the coefficients. Changing the global lift adds the same local inflation on both sides. The image of the strict group consists exactly of the \(f\) for which \(\delta_f\) is a coboundary.

**Odd weights.** Here \(\sigma\) acts by \(-1\) on both \(Y\) and \(M_r\). Equation (5) is a coboundary exactly when some \(y\in M_r\) satisfies \(f((1-t)b)=(1-t)y\) for every \(t\). At \(t=\sigma\) this reads \(f(2b)=2y\). Hence assigning \(b\mapsto y\) extends \(f\) to a homomorphism on \(Y\); the equations for \(t\in U\) are precisely its equivariance conditions. Conversely every equivariant extension supplies such a \(y\). We obtain
\[
 A_{2,r}(E_a)\simeq
 \operatorname{im}\!\left(\operatorname{Hom}_U(Y,M_r)
          \longrightarrow\operatorname{Hom}_U(X,M_r)\right).
\]
The restriction kernel consists of the two maps from \(Y/X\simeq\mathbb Z/2\) to \(M_r[2]\). On \(Y\) only the \(g\) condition remains. Set \(w=5^{-rN}\), the action of \(g\) on \(M_r\). The homomorphisms in question are the characters of the finite module \(Y/(g-w)Y\); nonvanishing of its determinant follows in §4. The Smith normal form over \(\mathbb Z_2\) gives
\[
 |A_{2,r}(E_a)|=2^{v_2(\det(\gamma^N-5^{-rN}I))-1}. \tag{6}
\]
Here the divisor two is the index-two lattice in (3) as measured by restriction of characters.

**Even weights.** Now \(\sigma=-1\) on \(X\) and \(+1\) on \(M_r\), so every equivariant \(f\) takes values in \(M_r[2]\). We have \(\delta_f(\sigma)=f(2b)\). A coboundary at \(\sigma\) is zero. Conversely if \(f(2b)=0\), choose \(y\in M_r\) with \((1-w)y=\delta_f(g)\). Such a \(y\) exists since \(w\ne1\) and \(M_r\) is divisible. Subtracting this coboundary kills \(\delta_f\) on \(g\) and on \(\sigma\), hence on \(U\). Therefore \(f(2b)=0\) is the exact remaining condition. Its solutions send \(c\) to either element of \(M_r[2]\). Both are \(\gamma\)-invariant by (4): \(\gamma(2b)=2b+2c\) and \(\gamma c=-(C_0/2)(2b)+(1-C_1)c\). This proves the even-weight assertion, including \(a=0\).

## 4. Why each higher layer multiplies the answer by four

For odd \(r\), factor the determinant in (6) over the \(N\)-th roots of unity. Up to a 2-adic unit its valuation is the sum of \(v_2(P(\zeta5^{-r}-1))\) over \(\zeta^N=1\). In fact the monic factorization gives equality of these valuations directly. Mizusawa identifies \(P\) up to a unit in \(\mathbb Z_2[[T]]\) with \(\Phi\), normalized by \(L_2(s,\psi)=2\Phi(5^s-1)\). Specialization at \(\zeta5^{-r}-1\) gives
\[
 2\Phi(\zeta5^{-r}-1)=L_2(-r,\psi\rho)=L^{(2)}(-r,\psi\rho),
 \qquad \rho(5)=\zeta^{-1}.
\]
In the interpolation formula the character correction is \(\omega^{-(r+1)}\), which is trivial here because \(r+1\) is even and \(\omega\) is the mod-4 sign. These complex special values are nonzero by the Dirichlet functional equation and their parity. Their product is rational by Galois symmetry. Substituting proves (1). [Mizusawa, p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Sharifi, Propositions 5.3.15 and 5.4.3](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html) · [NIST, Dirichlet functional equations](https://dlmf.nist.gov/25.15)

For \(\zeta\) of exact order \(2^j\), \(j\ge3\), put \(T=\zeta5^{-r}-1\). Then \(v_2(T)=v_2(\zeta-1)=2^{1-j}<1/2\), since \(5^{-r}-1\in4\mathbb Z_2\). In (4), \(T^2\) has strictly smaller valuation than either \(C_1T\) or \(C_0\). Thus \(v_2(P(T))=2^{2-j}\). There are \(2^{j-1}\) such roots. They contribute exactly **two** to the valuation in (6), multiplying the group order by four.

To bound the terms of order dividing four, inflate the characters to modulus \(m=16qd\) and put \(n=r+1\). Their depleted values are
\[
 -\frac{m^{\,n-1}}{n}\sum_{b=1}^{m}\chi(b)B_n(b/m).
\]
There are at most four of them. Each has absolute value at most \(\mathrm e m^n n!\) at every complex embedding. Multiplication by \(nm(n+1)!\) makes each integral, by the Bernoulli recurrence. Indeed \((j+1)!B_j\) is integral and \(|B_j|\le j!\). The product over orders dividing \(\min(4,N)\) is a nonzero rational number. Clearing denominators this way bounds its numerator logarithm by \(O(n(\log(2qd)+\log(n+1)))\), which also bounds its positive 2-adic valuation up to an absolute factor. Adding the exact higher-layer contributions and summing over weights proves (2). [NIST, Dirichlet–Hurwitz formula](https://dlmf.nist.gov/25.15#E3) · [NIST, Hurwitz zeta at negative integers](https://dlmf.nist.gov/25.11#E14)

## 5. Exact finite check

Take \(q=3,d=23,r=1\). With common modulus \(m=16\cdot69=1104\), the four values \(L^{(2)}(-1,\psi\rho)/2\) for \(\rho(5)=1,-1,i,-i\) are respectively
\[
 -36,\qquad -308,\qquad -404-862i,\qquad -404+862i.
\]
They follow from summing \(-\chi(b)(6b^2-6mb+m^2)/(24m)\) over the units modulo \(m\). One can assign \(\rho(b)=\rho(5)^j\) using \(b\equiv\pm5^j\bmod16\). The sum gives the same answers after inflating the modulus to 2208. The first two valuations are 2 and 2, and the conjugate pair has total valuation 2. Direct cyclotomic norms for characters of exact orders 8 and 16 give valuation 2 in each case as well.

| Layer \(a\) | Determinant valuation | \(\lvert A_{2,1}(E_a)\rvert\) | \(\lvert A_{2,2}(E_a)\rvert\) |
|---:|---:|---:|---:|
| 0 | 2 | 2 | 2 |
| 1 | 4 | 8 | 2 |
| 2 | 6 | 32 | 2 |
| 3 | 8 | 128 | 2 |
| 4 | 10 | 512 | 2 |

The previous note gave \(\lvert K_{2r}(\mathcal O_{E_a})\{2\}\rvert=\lvert A_{2,r}(E_a)\rvert h_{2,r}\), where braces indicate the 2-primary subgroup, \(h_{2,r}=2\) for odd \(r\), and \(h_{2,r}=2^{a+2+v_2(r)}\) for even \(r\). In odd weights this local multiplier two cancels the index-two divisor in (6). In even weights the 2-part of the \(K\)-group has order exactly \(2^{a+3+v_2(r)}\).

### Two real values give the entire group in this example

Use the additive lattice bases of (3). Write \(J\) for the matrix of \(\gamma\) on \(Y\) and \(u=5^{-r}\). At odd weights (5) identifies the dual of the strict group with
\[
 X/(J^{2^a}-u^{2^a}I)Y.
\]
Indeed, the strict group consists of restrictions of the characters of \(Y/(J^{2^a}-u^{2^a})Y\), and \((J^{2^a}-u^{2^a})Y\subset X\) since both operators agree on \(Y/X\simeq C_2\).

The two **real** normalized values at \(r=1\) are \(-36,-308\), each of valuation two. By §4 these are the valuations of \(P(5^{-1}-1)\) and \(P(-5^{-1}-1)\). The first argument is \(4\bmod8\) and the second is \(2\bmod8\). Since \(P(T)=T^2+C_1T+C_0\) is distinguished, the first value forces \(C_0\equiv4\bmod8\), and then the second forces \(C_1\equiv2\bmod4\).

For any odd \(r\), \(u\equiv5\bmod8\). From (4),
\[
 J^2-u^2I=\begin{pmatrix}
 1-C_0-u^2 & C_0(C_1-2)\\
 2-C_1 & 1-C_0-u^2+C_1(C_1-2)
 \end{pmatrix}.
\]
Dividing by \(4\) gives a matrix with diagonal \((1,1)\) and upper-right entry zero modulo 2. Its determinant is odd. Thus \((J^2-u^2 I)Y=4Y\). Also \(J^2\equiv I\bmod4\); every further doubling contributes the factor \(J^{2^j}+u^{2^j}I\equiv2I\bmod4\) for \(j\ge1\), which maps \(Y\) onto \(2Y\). Therefore \((J^{2^a}-u^{2^a}I)Y=2^{a+1}Y\) for \(a\ge1\). Using \(X=\langle2b,c\rangle\) gives
\[
 \boxed{\displaystyle A_{2,r}(E_a)\simeq C_{2^a}\oplus C_{2^{a+1}}
 \quad(q=3,\ d=23,\ r\ {\rm odd}).}
\]
At \(a=0\), \(P(u-1)\) has valuation two since \(u-1\equiv4\bmod8\), so (6) gives \(C_2\); the first factor in the boxed formula is then trivial. In particular the order-eight group is \(C_2\oplus C_4\).

The same proof applies to any pair for which the two normalized real values at \(r=1\) both have valuation two. The prime congruences on their own allow other behaviours. For example \(q=11,d=263\) gives \(B_1=-10416\) at \(r=1\) and \(B_1=42946927776\) at \(r=3\), from the finite Bernoulli formula. Their valuations are four and five, so at layer zero the strict orders are respectively eight and sixteen.

## 6. The complementary group at 3 for the cubic example

Take \(q=19,d=16871\), \(D=qd=320549\), \(R=\mathbb Q(\sqrt D)\), and \(E_0=\mathbb Q(\sqrt{-19},\sqrt{-16871})\). Let \(A_{3,r}^{\mathrm{comp}}\) be the eigenspace on which complex conjugation acts by \((-1)^r\). At the bottom layer the full answer is
\[
 A_{3,r}^{\mathrm{comp}}(E_0)\simeq
 \begin{cases} \mathbb Z/3,&r\text{ even},\\ 0,&r\text{ odd}.\end{cases} \tag{8}
\]
The even-weight group persists as a direct summand over \(E_a\) by restriction and corestriction, since \([E_a:E_0]\) is a power of two. Determining the other summands at higher dyadic layers is a separate question.

### The first cyclotomic cubic layer of the real field

The ordinary class number of \(R\) is three. For a reproducible computation, enumerate the reduced irrationals \((P+\sqrt D)/Q\) with \(0<P<\sqrt D\), \(Q>0\) even, \(\sqrt D-P<Q<\sqrt D+P\), and \(2Q\mid D-P^2\). The continued-fraction successor is
\[
 P'=\left\lfloor(\lfloor\sqrt D\rfloor+P)/Q\right\rfloor Q-P,\qquad Q'=(D-P'^2)/Q.
\]
The 108 pairs form three cycles of length 36, with least \((Q,P)\) equal to \((2,565),(10,557),(10,563)\). These cycles are ordinary ideal classes. Also \(D\equiv2\bmod3\), so the unique prime of \(R\) above 3 is the principal ideal \((3)\). [Mollin, §1 and Theorem 1.1](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/FACF38CC28A803AF5A06B806D3392812/S000497270001354Xa.pdf/use-of-the-rabinowitsch-polynomial-to-determine-the-class-groups-of-a-real-quadratic-field.pdf)

Let \(H\) be the splitting field of \(f(Z)=Z^3-164Z+801\). It is a totally real \(S_3\)-extension, as the cubic is irreducible modulo 5 and has positive nonsquare discriminant \(D\). Over \(R\) it is cyclic cubic and unramified: at the only candidate primes \(q,d\), tame inertia is cyclic of even order in \(S_3\), hence has order two. At 3 its rational Frobenius is a transposition, so the prime of \(R\) splits completely. Thus \(H/R\) is the Hilbert 3-class field. Moreover \(3\nmid h(H)\). Otherwise a further unramified extension of degree 3 and its conjugates would give an unramified finite 3-group over \(R\) larger than \(C_3\) with cyclic abelianization. A finite \(p\)-group with cyclic abelianization is cyclic, contradicting \(h(R)=3\).

Set \(T=\mathbb Q(\zeta_9)^+\), \(R_1=RT\), \(H_1=HT\). We claim \(\mathrm{Cl}(R_1)\{3\}\simeq C_3\). The following unit gives a short exact certificate. For two distinct roots \(x,y\) of \(f\), put \(\eta=U(x)+V(x)y\), with
\[
\begin{aligned}
 U(x)&=-6546564915489+518244484752x+65084790424x^2,\\
 V(x)&= 961424555660-76109400788x-9558264431x^2 .
\end{aligned}
\]
Using \(y^2+xy+x^2-164=0\), the relative norm is \(U^2-xUV+(x^2-164)V^2\). Its remainder modulo \(f(x)\) is \(-1831220x^2+27096052x-99597647\); the resultant of \(f\) and this remainder is \(1\). Thus \(\eta\) is an algebraic integer of absolute norm \(+1\), hence a unit.

There are three completions of \(H\) above 3, all unramified quadratic over \(\mathbb Q_3\). Modulo 9, \(f(Z)=Z(Z^2-2)\). With \(s^2=2\), the following substitutions give the three places, up to local conjugacy.

| \((x,y)\bmod 9\) | \(\eta\bmod9\) | Local norm to \(\mathbb Q_3\bmod9\) |
|---|---:|---:|
| \((0,s)\) | \(8s\) | 7 |
| \((s,0)\) | \(8\) | 1 |
| \((s,-s)\) | \(5s\) | 4 |

The norm of \(u+vs\) is \(u^2-2v^2\). Each of the three primes is totally ramified of degree three in \(H_1/H\). The norm of a local unit from \(T_3/\mathbb Q_3\) is \(\pm1\bmod9\) by cyclotomic reciprocity. Consequently any global unit of \(H\) which is a norm from \(H_1\) has trivial image in each of the three copies of \((\mathbb Z/9)^\times/\{\pm1\}\). This necessity follows by transitivity of local norms, including for a global norm whose preimage is merely a field element. The total ramification makes that preimage a local unit at each of the three places.

In coordinates with generator \(4\bmod9\), the table gives \((2,0,1)\in\mathbb F_3^3\). A cyclic conjugate of \(\eta\) rotates these entries and supplies a linearly independent vector. The index of the subgroup of units which are norms is therefore divisible by nine. Chevalley's ambiguous class number formula gives
\[
 |\mathrm{Cl}(H_1)^{\operatorname{Gal}(H_1/H)}|
 =\frac{h(H)\,3^3}{3\,[\mathcal O_H^\times:
         \mathcal O_H^\times\cap N_{H_1/H}H_1^\times]} .
\]
This has trivial 3-part. A nontrivial finite 3-group acted on by a group of order three has a nontrivial fixed subgroup when the former group is abelian, by counting orbits. Thus \(3\nmid h(H_1)\). Now \(H_1/R_1\) is an unramified cubic extension, since \(H/R\) is unramified and \(T/\mathbb Q\) ramifies at 3. Any larger abelian unramified 3-extension of \(R_1\) containing \(H_1\) would contradict \(3\nmid h(H_1)\). This proves the claim. [Lemmermeyer, Theorem 1, ambiguous class number formula](https://arxiv.org/pdf/1309.1071) · [Milne, local and global class field theory](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

### Descent at even and odd weights

For even \(r\) put \(M=\mathbb Q_3/\mathbb Z_3(-r)\). Globally and at the unique place above 3, \(R\) has cyclotomic image \(\mathbb Z_3^\times\); its quadratic completion is unramified. Thus the global and local \(H^0(M)/3^j\) agree. The multiplication-by-\(3^j\) sequence identifies \(A_{3,r}(R)[3^j]\) with the strict group for \(M[3^j]\): the sole local boundary of a lift can be removed by the identical global boundary. At \(j=1\) the coefficients are trivial and \((3)\) is principal, so \(A_{3,r}(R)[3]\simeq C_3\) by class field theory.

At \(j=2\), the action on \(M[9]\) becomes trivial over \(R_1\) for every even \(r\), since the residual cyclotomic sign acts trivially in an even twist. Restriction of the strict finite-coefficient group to \(R_1\) is injective. A class in its kernel would inflate from \(\operatorname{Gal}(R_1/R)\); the unique 3-adic place has full decomposition group, and local inflation is injective. Over \(R_1\) the target is the group of characters of the 3-integer class group into \(\mathbb Z/9\). Its order is at most three by the calculation above. It follows that \(A_{3,r}(R)[9]=A_{3,r}(R)[3]\simeq C_3\), which excludes every element of order nine or higher. Quadratic descent identifies \(A_{3,r}(R)\) with the conjugation-fixed part over \(E_0\). The extension \(E_0/R\) is unramified at finite places, and its degree is invertible at 3. This proves (8) for all even weights.

For odd \(r\), put \(J=E_0(\mu_3)\). The mod-3 cyclotomic action over \(E_0\) and its unramified completions at 3 is nontrivial, so the global and local \(H^0(M)\) vanish. Thus the 3-torsion of the strict group is strict cohomology with \(\mathbb F_3(-r)\) coefficients. Over \(J\) this becomes a character of \(\mathrm{Cl}(\mathcal O_J[1/3])\). Taking the required eigenspaces is exact at 3 for these extensions of 2-power degree. Complex conjugation acts by \(-1\) on the coefficients, so the complementary sign on characters selects the even ideal classes, i.e. classes from \(J^+\). The nontrivial element of \(\operatorname{Gal}(J/E_0)\) gives the opposite sign on these ideal classes because it negates \(\mu_3\). The field \(J^+=\mathbb Q(\sqrt D,\sqrt{57})\) is biquadratic. The two quadratic characters with this last sign belong to discriminants \(57\) and \(50613=3\cdot16871\). The same reduced-ideal enumeration gives one cycle of length 6 for the first field, and five cycles of lengths \(4,6,6,8,8\) for the second. Their class numbers \(1\) and \(5\) are prime to 3. The selected 3-torsion vanishes, hence so does the whole complementary group. This completes the proof of (8).

## 7. A uniform bound for the first powers at odd primes

For the moving field write \(g=[E_a:\mathbb Q]\), \(F=2^{a+2}qd\). For any \(P\ge2\) and positive integer \(k\),
\[
 \sum_{r<t,\ r\ge1}\ \sum_{2<p\le P}\log |A_{p,r}(E_a)[p^k]|
 \ll t g k P^2\bigl(\log(2F)+\log(2P)\bigr). \tag{7}
\]
Here \(B[p^k]\) means the subgroup killed by \(p^k\), and the inner sum is over primes. Both conjugation signs are included.

Indeed, multiplication by \(p\) on the discrete coefficients bounds \(|A_{p,r}[p]|\) by the size of \(H^1(G_{E_a,S_p},\mathbb F_p(-r))\). Restrict to \(J=E_a(\mu_p)\). The extension degree divides \(p-1\), so restriction is injective, and over \(J\) the finite coefficients are isomorphic to \(\mu_p\). The Kummer sequence for the ring of \(p\)-integers bounds the size by the product of the \(S_p\)-unit group modulo \(p\)-th powers and the \(p\)-torsion of its ideal class group. Put \(m=[J:\mathbb Q]\le gp\). The first factor has order at most \(p^{2m}\) by the unit theorem. For the second, Minkowski gives an integral ideal of norm at most \(\sqrt{|D_J|}\) in every ordinary class. The number of such ideals is at most \(|D_J|\zeta_J(2)\le (Fp)^m\zeta(2)^m\), using the abelian conductor–discriminant formula and the Euler product. Localizing at \(p\) only takes a quotient of the ordinary class group. For any finite abelian \(p\)-group \(B\), \(|B[p^k]|\le |B[p]|^k\) by its cyclic decomposition. Summing these bounds gives (7). [Finite Kummer groups and \(S\)-units](https://doc.sagemath.org/html/en/reference/number_fields/sage/rings/number_field/selmer_group.html) · [Minkowski's bound, Theorem 4.3.7](https://www.math.ucla.edu/~sharifi/notes/algnum.pdf) · [Conductor–discriminant formula, Theorem 5.8](https://kconrad.math.uconn.edu/blurbs/gradnumthy/cfthistory.pdf)

In particular take \(P=\exp(x^\varepsilon/8)\) and \(k=\lfloor P\rfloor\). The bound in (7) is \(o(\exp(x^\varepsilon/2))\), since \(kP^2\le\exp(3x^\varepsilon/8)\) and the remaining factors grow polynomially in \(x\). Thus the remaining odd-prime estimate can concentrate on primes \(p>P\) and on the powers above \(p^k\) in cyclic factors at smaller odd primes.

## 8. The two invariant factors for all selected prime pairs

The congruence \(d\equiv-1\bmod q\) imposed in the analytic window also controls the integral structure of the dyadic group. For every selected pair and each positive odd weight \(r\), define two integers from rational values,
\[
 \alpha=v_2\bigl(L^{(2)}(-r,\psi)/2\bigr),\qquad
 \beta=v_2\bigl(L^{(2)}(-r,\psi\chi_8)/2\bigr),\qquad
 m=\min(\alpha,\beta),\quad M=\max(\alpha,\beta).
\]
Here \(\chi_8=(2/\cdot)\) is the even primitive quadratic character of conductor eight. Then \(m\ge2\) and
\[
 \boxed{
 A_{2,r}(E_0)\simeq C_{2^{\alpha-1}},\qquad
 A_{2,r}(E_a)\simeq C_{2^{m+a-2}}\oplus C_{2^{M+a-1}}\quad(a\ge1).
 } \tag{9}
\]
Thus both cyclic factors double at each layer from \(a=1\) onward, for every prime pair used in the window. The two evaluations in (9) are made at the weight in question. Section 5 explains why the single weight \(r=1\) suffices for all odd \(r\) in the specific field \(q=3,d=23\). [Prime-pair congruences in §1 of the signed-twist note](https://chatgpt.com/library?file_id=libfile_fde3_f-bbab264e2360819186c97a3c25cc4832_c754b6b7374c8191bd506241562ebfd1&account_id=personal)

**Why the prime selection matters.** The equality \((P)=(\Phi)\), evaluated at zero, gives \(v_2(C_0)=v_2(L_2(0,\psi))-1\). Interpolation at \(s=0\) twists \(\psi\) by the mod-4 sign and gives the primitive character of discriminant \(-4qd\). Its factor at 2 is already absent. The imaginary quadratic class number formula reads \(L(0,\chi_{-4qd})=2h(k)/|\mu(k)|=h(k)\), with \(k=\mathbb Q(\sqrt{-qd})\). Hence
\[
 v_2(C_0)=v_2(h(k))-1. \tag{10}
\]
The three prime discriminants \(-4,-q,-d\) give 2-rank two by genus theory. The factorization \(-4qd=(-d)(4q)\) meets Rédei's criterion for an unramified cyclic quartic extension. Its three Kronecker symbols are \((-d/2)=1\), \((-d/q)=1\), and \((4q/d)=1\). The first follows from \(d\equiv7\bmod8\), the second from \(d\equiv-1\bmod q\), and the third from quadratic reciprocity since \(q,d\equiv3\bmod4\) and \((d/q)=-1\). Consequently the 2-class group has two cyclic factors and at least one has order divisible by four. Thus \(8\mid h(k)\), and (10) gives \(4\mid C_0\). [Mizusawa, p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Sharifi, Proposition 5.3.15](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html) · [Dirichlet class number formula and its functional equation](https://jvoight.github.io/quat-book.pdf) · [Endô, Propositions 1–2, including the symbol at 2](https://www.jstage.jst.go.jp/article/kyushumfs/27/1/27_1_111/_pdf)

**The first-layer calculation.** Put \(u=5^{-r}\), \(J=\gamma|_Y\), \(h=2-C_1\), and \(v=1-C_0-u^2\). Write \(p_+=P(u-1)\) and \(p_-=P(-u-1)\); their valuations are \(\alpha,\beta\). For either sign, \(P(\pm u-1)\equiv C_0\bmod4\), since its argument and \(C_1\) are even and \(u\equiv1\bmod4\). In the domain basis \((b,c)\) and the target basis \((2b,c)\), the matrix of \(J^2-u^2I\) is
\[
 \begin{pmatrix}v/2&-C_0h/2\\ h&v-C_1h\end{pmatrix}.
\]
Its entries generate the ideal \((v/2,h)\). The identities \(p_+=-v-(u-1)h\) and \(p_--p_+=2uh\) give \((v/2,h)=(p_+/2,p_-/2)\) in \(\mathbb Z_2\). Therefore its first Smith exponent is \(m-1\), and its determinant has valuation \(\alpha+\beta-1\), giving second exponent \(M\). At \(a=0\) the lower-left entry of \(J-uI\) in the same bases is \(1\), so the quotient is cyclic with exponent \(\alpha-1\) in logarithmic notation.

**Passing to higher layers.** If \(4\mid C_0\), then \((J^2+u^2 I)/2\) reduces modulo 2 to a lower triangular matrix with both diagonal entries 1; this follows directly from (4), using \(2\mid C_1\). The first doubling factor thus maps \(Y\) onto \(2Y\). For every pair in the larger residue family, \(J^2\equiv I\bmod2\) implies \(J^4\equiv I\bmod4\). At each subsequent doubling \(J^{2^j}+u^{2^j}I\) is \(2I\bmod4\) for \(j\ge2\). Multiplying the image lattice by two adds one to each Smith exponent. This proves (9).

**The other case in the larger family.** If \(C_0\equiv2\bmod4\), then \(\alpha=\beta=1\) at every odd weight. In this case the full group also follows from the three values in §1. Write \(\ell_a=\log_2|A_{2,r}(E_a)|\) as given there. The invariant factors are
\[
 C_{2^{\lfloor\ell_a/2\rfloor}}\oplus C_{2^{\lceil\ell_a/2\rceil}}\quad(a\ge0).
\]
Indeed \(b\) is cyclic for \(J-I\), so \(Y=\mathbb Z_2[T]/(P(T))\) with \(T=J-I\). Here \(P\) is Eisenstein and \(Y\) is the ring of integers of a totally ramified quadratic extension of \(\mathbb Q_2\), with uniformizer \(T\). The lattice \(X=(2,T)\) is its maximal ideal. The group dual to \(A_{2,r}\) is a quotient of two ideals, so it is additively isomorphic to \(Y/T^{\ell_a}Y\); \(T^2Y=2Y\) gives the displayed factors. For example at \(q=3,d=7,r=1\) the normalized low values are \(-6,-54,-66-142i\) and its conjugate. They give the trivial group at layer zero, \(C_2\) at layer one and \(C_4\oplus C_4\) at layer two. This pair meets the mod-8 and mod-16 conditions; the window additionally requires \(d\equiv-1\bmod q\).

### How the weight can change both factors

For selected pairs there is also a weight-one test with a wider range. For either sign, \(T_r=\pm5^{-r}-1\) is constant modulo 8 on odd weights. Since \(T_r+T_1+C_1\) is even, \(P(T_r)-P(T_1)\) is divisible by 16 in \(\mathbb Z_2\). Thus either weight-one valuation below four stays fixed at every odd weight. If both are below four, the full group at every odd weight and all layers follows from the two evaluations at weight one. The example below shows what can happen at four.

For \(q=11,d=263\), the same exact sums used in §5, now with \(B_2\) and \(B_4\) at modulus \(8qd\), give the following. Each rational entry includes depletion at 2 and division by two.

| \(r\) | \(L^{(2)}(-r,\psi)/2\) | \(L^{(2)}(-r,\psi\chi_8)/2\) | \((\alpha,\beta)\) | \(A_{2,r}(E_1)\) |
|---:|---:|---:|---:|---|
| 1 | \(-10416\) | \(-85584\) | \((4,4)\) | \(C_8\oplus C_{16}\) |
| 3 | \(42946927776\) | \(7186575033984\) | \((5,7)\) | \(C_{16}\oplus C_{128}\) |

In fact the orders at layer zero are **unbounded as odd weights vary in this fixed field**. The two valuations at \(r=1\) imply \(C_0\equiv0\bmod8\) and \(C_1\equiv2\bmod4\) by substituting \(u-1\equiv4\) and \(-u-1\equiv2\bmod8\). For either choice of sign and distinct odd integers \(r,s\), set \(T_r=\pm5^{-r}-1\) using the same sign throughout. Then
\[
 v_2(P(T_r)-P(T_s))=
 v_2((T_r-T_s)(T_r+T_s+C_1))=3+v_2(r-s).
\]
The second factor has valuation one, and \(v_2(5^{r-s}-1)=2+v_2(r-s)\). For \(r=1+2j\), the map \(j\mapsto(P(T_{1+2j})-P(T_1))/16\) therefore permutes the residue classes modulo \(2^k\) for every \(k\): equality of outputs modulo \(2^k\) is equivalent to equality of inputs modulo \(2^k\). Since \(16\mid P(T_1)\), exactly one odd weight class modulo \(2^{k+1}\) has \(v_2(P(T_r))\ge4+k\) for each sign. The positive integer weights in these classes give arbitrarily large valuations. No positive odd weight is itself a zero by §4.

### Summing across weights

The same spacing improves the uniform upper bound (2) by a factor of \(t\) in its conductor-dependent term. Uniformly throughout the full residue family,
\[
 \sum_{1\le r<t}\log |A_{2,r}(E_a)|
 \ll t\,\bigl(a+\log(2qd)+\log(t+1)\bigr). \tag{11}
\]
To verify it, fix one of the at most four roots \(\zeta\) of order dividing four that occurs at the layer in question, and one of the two roots \(\theta\) of the monic polynomial \(P\), counted with multiplicity. Put \(x_r=\zeta5^{-r}-1\). Among the positive odd weights in the window choose \(r_*\) maximizing \(v_2(x_r-\theta)\). These valuations are nonnegative and finite. For any other odd \(r\), the ultrametric inequality gives
\[
 v_2(x_r-\theta)\le v_2(x_r-x_{r_*})=2+v_2(r-r_*).
\]
The sum of the right side is \(O(t)\): on each side of \(r_*\) the positive differences are \(2,4,6,\ldots\), and \(v_2(n!)\le n\). At the exceptional weight the valuation is at most \(v_2(P(x_{r_*}))\), because the other root is integral. Section 4 bounds this by \(O(t(\log(2qd)+\log(t+1)))\) using the nonzero rational product of at most four normalized special values; all the associated polynomial valuations are nonnegative. There are at most eight choices of \((\zeta,\theta)\). Higher-order roots of unity contribute \(O(at)\) by §4, and the even weights contribute \(O(t)\). This proves (11).

The remaining uniform arithmetic estimate is the complementary odd-prime contribution beyond §7. The results here are classical; a Lean formalization and an end-to-end deduction of RH remain open in this work.
