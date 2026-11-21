# The two dyadic primes and the strict group

November 20, 2026 · Companion to *Dyadic Window Orders*

Let \(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\) and \(E_a=Q_a(\sqrt{-q},\sqrt{-d})\), where \(q,d\) are distinct primes with \(q\equiv3\bmod8\) and \(d\equiv7\bmod16\). Write \(M=\mathbb Q_2/\mathbb Z_2(-r)\) for a positive integer \(r\). The strict group \(A_{2,r}(E_a)\) consists of classes in \(H^1(G_{E_a,S},M)\), unramified outside \(S=\{v:v\mid2\}\), whose restriction is zero at every \(v\in S\). Write \(C_n=\mathbb Z/n\mathbb Z\), including \(C_1=0\).

**Theorem.** At every layer \(a\ge0\) and every positive even weight, \(A_{2,r}(E_a)\simeq C_2\) throughout this family. When \(q=3,d=23\), every positive odd weight satisfies
\[
 A_{2,r}(E_a)\simeq C_{2^a}\oplus C_{2^{a+1}}.
\]
Two rational character sums at \(r=1\) determine the odd-weight result at all layers.

## 1. Comparing the two restrictions

Let \(N=2^a\), \(Q_\infty=\bigcup_j Q_j\), \(k=\mathbb Q(\sqrt{-qd})\), \(k_\infty=kQ_\infty\), and \(L=E_a(\mu_{2^\infty})=Q_\infty(i,\sqrt q,\sqrt d)\). Write \(U=\operatorname{Gal}(L/E_a)=\langle\sigma\rangle\times\langle g\rangle\), where \(\sigma\) has cyclotomic character \(-1\), and \(g=\gamma^N\) has cyclotomic character \(5^N\). The second factor is a copy of \(\mathbb Z_2\).

Here are the arithmetic inputs to the descent. In Mizusawa's unramified pro-2 tower over \(k_\infty\), write \(A,B,C\) for the generators of Theorem 2.2. The group fixing \(L\) is \(H=\langle A^2,B^2,C\rangle\), and the full dyadic decomposition subgroup in the tower over \(k_\infty\) is the normal subgroup \(\langle A\rangle\). Killing it gives the lattices
\[
 Y=\mathbb Z_2 b\oplus\mathbb Z_2 c,\qquad X=\mathbb Z_2(2b)\oplus\mathbb Z_2 c\subset Y,
\]
where \(b,c\) are the images of \(B,C\) and \(X\) is the image of \(H\). Thus \(X\) is the group of the maximal unramified abelian pro-2 extension of \(L\) in which the dyadic primes split. The action on \(Y\), using column vectors in the basis \(b,c\), is
\[
 \gamma=\begin{pmatrix}1&-C_0\\1&1-C_1\end{pmatrix},\qquad
 P(T)=\det((1+T)I-\gamma)=T^2+C_1T+C_0,\qquad C_0,C_1\in2\mathbb Z_2.
\]
The involution acts on \(Y\) by \(-1\). Indeed \(Y\) is the torsion-free quotient of the unramified Iwasawa module of \(k_\infty\). At finite level the product of a class and its conjugate is extended from its norm to \(Q_j\), whose class number is odd. On \(Y\) the action factors through the automorphisms of \(k_\infty\) since \(Y\) is abelian. [Mizusawa, Theorem 2.2 and §4.2, especially pp. 129–130](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

At 2, \(-d\) is a square and \(\sqrt{-q}\) gives the unramified quadratic extension. The real cyclotomic layer is totally ramified. Hence \(E_a\) has two dyadic primes. At either one the intersection of the completion with the local 2-power cyclotomic tower is the local real layer \(Q_{a,2}\): the additional quadratic extension over that layer is unramified and the cyclotomic tower above it is totally ramified. Thus the decomposition group in \(L/E_a\) at either prime is all of \(U\). The element \(B\) interchanges the primes in \(L\), since its coset in \(\operatorname{Gal}(L/k_\infty)\) is outside the image of the dyadic decomposition subgroup.

Restriction sends a strict class injectively to a continuous equivariant character \(f:X\to M\). Indeed a class in the kernel inflates from \(H^1(U,M)\), and local inflation at either prime detects it. Conversely every such \(f\) lifts to a global class allowing ramification at 2. In the inflation–restriction sequence, its transgression restricts to the transgression of zero at a dyadic prime, because \(f\) kills the local group over \(L\). The map on the targets is the identity on \(H^2(U,M)\), so the global transgression vanishes. [Milne, *Class Field Theory*, Chapter II](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

The two restrictions of a lift inflate from classes on \(U\). A change of lift shifts both by the same class. To compare them for \(t\in U\), choose a lift \(s_t\) at the first prime and \(Bs_tB^{-1}\) at the second, taking an absolute lift of \(B\). Both project to \(t\), since \(L/\mathbb Q\) is abelian. Their quotient maps to \((1-t)b\in X\). The difference of the two restricted cocycles is therefore
\[
 \delta_f(t)=f((1-t)b).
\]
The character descends to a strict class exactly when this is a coboundary, equivalently when a single \(y\in M\) satisfies \(\delta_f(t)=(1-t)y\) for all \(t\in U\).

**Even \(r\).** The involution acts by \(-1\) on \(X\) and by \(+1\) on \(M\), forcing \(f(X)\subset M[2]\). At \(\sigma\) the coboundary condition is \(f(2b)=0\). Once it holds, choose \(y\) solving \((1-5^{-rN})y=\delta_f(g)\). The multiplier is nonzero and \(M\) is divisible. The two cocycles then agree on both topological generators. With \(f(2b)=0\), either choice in \(M[2]\) for \(f(c)\) is equivariant, by the displayed matrix. This gives \(C_2\).

**Odd \(r\).** At \(\sigma\) the condition is \(2y=f(2b)\). Thus \(b\mapsto y\) extends \(f\) additively to \(Y\), and the remaining conditions are precisely equivariance of the extension. Put \(s=5^{-r}\), \(D_a=\gamma^{2^a}-s^{2^a}I\). Equivariant characters of \(Y\) are all characters of \(Y/D_aY\). We have \(D_aY\subset X\), since \(\gamma\) and \(s\) both induce the identity on \(Y/X\simeq C_2\). Restricting these characters to \(X\) gives the whole character group of \(X/D_aY\) by divisibility of \(\mathbb Q_2/\mathbb Z_2\) (equivalently extend a character across the index-two inclusion by taking a half of its value on \(2b\)). This identifies the dual strict group:
\[
 A_{2,r}(E_a)^\vee\simeq X/D_aY.
\]
In particular, when \(\det D_a\ne0\), the strict order is \([Y:D_aY]/2\).

## 2. Two reproducible integer sums for \(q=3,d=23\)

Write \(\psi(b)=(b/3)(b/23)\) for the even quadratic character of conductor 69, and \(\chi_8=(2/\cdot)\) for the even character of conductor 8. For either primitive character \(\chi\) below, put \(S_j=\sum_{b=1}^f\chi(b)b^j\) at its conductor \(f\). The Bernoulli formula gives \(L(-1,\chi)=-S_2/(2f)\), since \(S_0=S_1=0\). Depleting at 2 multiplies by \(1-2\chi(2)\). [NIST DLMF, §25.15(i)](https://dlmf.nist.gov/25.15) · [Hurwitz zeta at negative integers](https://dlmf.nist.gov/25.11#E14)

| \(\chi\) | \(f\) | \(S_0\) | \(S_1\) | \(S_2\) | \(1-2\chi(2)\) | \(L^{(2)}(-1,\chi)/2\) |
|---|---:|---:|---:|---:|---:|---:|
| \(\psi\) | 69 | 0 | 0 | 3312 | 3 | −36 |
| \(\psi\chi_8\) | 552 | 0 | 0 | 680064 | 1 | −308 |

The following uses only integer arithmetic in Python.

~~~python
from math import gcd

def legendre(b, p):
    value = pow(b, (p - 1) // 2, p)
    return -1 if value == p - 1 else value

for conductor in (69, 552):
    moments = [0, 0, 0]
    for b in range(1, conductor + 1):
        if gcd(b, conductor) != 1:
            continue
        chi = legendre(b, 3) * legendre(b, 23)
        if conductor == 552 and b % 8 in (3, 5):
            chi = -chi
        for j in range(3):
            moments[j] += chi * b**j
    print(conductor, moments)
~~~

Mizusawa normalizes \(L_2(z,\psi)=2\Phi(5^z-1)\) with \((P)=(\Phi)\) in \(\mathbb Z_2[[T]]\). The trivial and quadratic finite-order twists at \(z=-1\) therefore give \(v_2(P(1/5-1))=v_2(-36)=2\) and \(v_2(P(-1/5-1))=v_2(-308)=2\). A power-series unit evaluates to a unit at both arguments. [Mizusawa, p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Sharifi, *Iwasawa Theory*, Chapter 5](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

The first argument is in \(4\mathbb Z_2\), so \(P(1/5-1)\equiv C_0\bmod8\). The second is \(2\bmod4\), so its square is \(4\bmod8\). Since a number of valuation two is \(4\bmod8\), the two evaluations force
\[
 C_0\equiv4\pmod8,\qquad C_1\equiv2\pmod4.
\]
These congruences are independent of \(r\). For any \(s=5^{-r}\) we have \(s-1\in4\mathbb Z_2\) and \(-s-1\equiv2\bmod4\), so both \(P(s-1)\) and \(P(-s-1)\) have valuation two.

## 3. Reading off the invariant factors

At \(a=0\), \(\det D_0=P(s-1)\) has valuation two. Thus \([X:D_0Y]=2\). At \(a=1\) the determinant factors as \(P(s-1)P(-s-1)\), of valuation four. The coefficient congruences give
\[
 \gamma\equiv\begin{pmatrix}1&0\\1&-1\end{pmatrix}\pmod4,
 \qquad \gamma^2\equiv I\pmod4.
\]
Hence \(D_1Y\subseteq4Y\). Both have index 16 in \(Y\), proving \(D_1Y=4Y\).

For \(a\ge1\), factor
\[
 D_{a+1}=D_a(\gamma^{2^a}+s^{2^a}I).
\]
The second factor is \(2I\bmod4\), hence is twice an automorphism of \(Y\). It follows inductively that \(D_aY=2^{a+1}Y\) for every \(a\ge1\). The inclusion \(X=\langle 2b,c\rangle\subset Y=\langle b,c\rangle\) now gives
\[
 X/2^{a+1}Y\simeq C_{2^a}\oplus C_{2^{a+1}}.
\]
Finite abelian groups and their character groups have the same invariant factors. The rank-two structure thus holds from \(a=1\), with the same formula giving \(C_2\) at \(a=0\).

| Layer \(a\) | Positive even weight | Positive odd weight for \(q=3,d=23\) | Odd-weight order |
|---:|---|---|---:|
| 0 | \(C_2\) | \(C_2\) | 2 |
| 1 | \(C_2\) | \(C_2\oplus C_4\) | 8 |
| 2 | \(C_2\) | \(C_4\oplus C_8\) | 32 |
| 3 | \(C_2\) | \(C_8\oplus C_{16}\) | 128 |
| 4 | \(C_2\) | \(C_{16}\oplus C_{32}\) | 512 |
