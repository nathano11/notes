# Tame restriction and strict class-group characters

## The interface at a nontrivial tame weight

Let \(E\) be a number field, \(S\) the places over an odd prime \(p\), \(r,n\ge1\), \(M=\mathbb Q_p/\mathbb Z_p(-r)\), and \(D=M[p^n]\). Write \(a=\kappa^{-r}\bmod p^n\). Let \(G=G_{E,S}\), let \(K/E\) be the extension cut out by \(a\), and put \(N=G_{K,S_K}\), \(\Delta=G/N\). Suppose the tame cyclotomic image acts nontrivially on \(M[p]\) globally and at each \(v\mid p\). The arithmetic target at this weight is the additive isomorphism

\[
\ker\!\left(H^1(G,M)\longrightarrow\prod_{v\mid p}H^1(E_v,M)\right)[p^n]
 \ \simeq\ 
 \operatorname{Hom}_{\Delta}\!\left(\mathrm{Cl}(\mathcal O_K[1/p]),D\right).
\]

The target includes the inverse twist: \(f(\sigma x)=a(\sigma)f(x)\). All cohomology and Galois characters here are continuous. For the project fields the cyclotomic decomposition subgroup at each \(p\)-adic place is the full quotient. In the general setting one only needs a suitable local tame scalar at each place. The group and coefficient calculations below have Lean proofs. Realizing their inputs for these number fields and the Artin reciprocity identification are separate obligations, listed in [the shared proof status](formal/PROOF_STATUS.md).

### A formula that works for a nonsplit extension

Choose a tame lift \(t\in G\) such that \(a(t)-1\) is a unit modulo \(p^n\). Its image in \(\Delta\) is central. Write \(i=(a(t)-1)^{-1}\). For an equivariant homomorphism \(f:N\to D\), set
\[
 c_f(g)=i\,f([t,g]),\qquad [t,g]=tgt^{-1}g^{-1}.
\]

1. The commutator is in \(N\), and \([t,gh]=[t,g]\,g[t,h]g^{-1}\). Additivity and equivariance give \(c_f(gh)=c_f(g)+a(g)c_f(h)\).
2. For \(x\in N\), \(f([t,x])=(a(t)-1)f(x)\). Hence \(c_f(x)=f(x)\).
3. For any crossed homomorphism \(c\), direct comparison of \(tg\) with \([t,g]gt\) gives
\[
c([t,g])=(a(t)-1)c(g)-(a(g)-1)c(t).
\]
Thus \(c-c_{c|_N}\) is the single coboundary \(g\mapsto(a(g)-1)i\,c(t)\). The formula is additive in \(f\).
4. With the subspace topology on \(N\), the commutator map into \(N\) is continuous. Composition with a continuous \(f\) and multiplication by \(i\) preserve continuity.
5. In a local decomposition group \(P\), choose a local tame lift \(t_P\) with invertible difference. If \(f\) vanishes on \(P\cap N\), then \(c|_P\) is the coboundary with primitive \((a(t_P)-1)^{-1}c(t_P)\). Every local coboundary vanishes on \(P\cap N\). This proves the strict condition even when the chosen global lift \(t\) lies outside \(P\).

### Coefficients and the Artin quotient

Multiplication by \(p^n\) on \(M\) is surjective. If \(p^n c\) is the coboundary of \(b\), choose \(b'\) above \(b\). Then \(c-\delta b'\) has values in \(D\). If a \(D\)-valued cocycle is a coboundary of \(b\) in \(M\), then \(p^n b\) is invariant. The tame unit difference forces this invariant to vanish. Thus \(b\in D\), globally and at every \(p\)-adic place, yielding the required finite coefficient comparison.

Upstairs, \(N\) acts trivially on \(D\). Its characters in this argument are unramified outside \(S_K\) by the definition of \(G\) and split at every prime in \(S_K\) by the local condition. Global class field theory identifies the resulting abelian quotient with \(\mathrm{Cl}(\mathcal O_K[1/p])\). Equivalently one quotients the ordinary class group by the classes of primes above \(p\). If a stabilizer of each such prime has an invertible tame difference, equivariance kills that prime class, so ordinary and localized class characters agree. In the CM case, the complementary sign \((-1)^r\) selects the characters fixed on their **argument** by complex conjugation; passing this part to \(K^+\) requires the norm and extension maps of ideal classes. The arithmetic reciprocity inputs and the realization of those maps in Lean remain open. [Milne, *Class Field Theory*, Chapters II and V](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

The theorem `TameGaloisInterface.continuous_strict_class_correspondence` uses the continuous Artin kernel test and proves both inverse identities on the quotient of locally principal cocycles. `TameAdditivity.toCharacter_add` and `fromCharacter_add` prove that both maps respect addition. The corrected finite representative, equality of finite classes, and local principality are checked in `TameCoefficients`.

### Interface to the certificate at 277

At \(p=277\), the 275 nonzero residue classes of weights modulo 276 have invertible tame difference at every coefficient depth. With \(\sigma_5\) acting on roots of unity by the fifth power and \(r=1\), \(5^{-1}=111\bmod277\). Evaluation on \(\sigma_5x\) multiplies the character by 111. Precomposition by \(\sigma_5^{-1}\) on the untwisted dual multiplies it by 5. These are distinct operations. The orientation and the vanishing on a separated eigenline are checked in `TameOrientation`. Invertibility for all 275 weights is checked in `TameTwist277`. Continue Conversation owns the identification with projected circular units. The weight \(276\mid r\) belongs to the exceptional boundary calculation.

For this field, the two square roots of \(-3\) modulo 277 are 44 and 233. The square roots of \(-23\) are 114 and 163. `TameLimitRoots277.four_root_pairs` identifies the four independent sign pairs with all simultaneous roots in the inverse-limit ring of 277-adic integers.

Put \(R=\mathbb Z[\sqrt{-3},\sqrt{-23}]\). The four signed evaluations onto \(\mathbb F_{277}\) give all four primes \(P\) of \(R\) above 277. An element lies in \(P^{n+1}\) exactly when its evaluation vanishes modulo \(277^{n+1}\). The completion of \(R\) at each \(P\) is therefore the inverse-limit ring \(\mathbb Z_{277}\). Each evaluation is faithful on \(R\), and the induced fraction maps preserve addition and multiplication. These steps are checked in `TamePrimePowers277`, `TameLocalOrders277`, `TameOrderFaithful277` and `TameFractionCompletion277`.

For \(E=\mathbb Q(\sqrt{-3},\sqrt{-23})\), `TameEmbeddings277.four_embeddings` classifies all rational embeddings into a target field supplied with both roots and a rational coefficient map. The field comparison must realize the fraction model in the standard \(\mathbb Q_{277}\) and identify the four finite places and their completed fields. Arithmetic strict descent then requires the Galois decomposition maps and the continuous Artin quotient.

## What changes at the exceptional weights

Write \(h\) for the order of the tame cyclotomic image and \(j=v_p(r)\). Suppose the full principal image is \(1+p\mathbb Z_p\). On coefficients of order \(p^{s+1}\), the wild generator acting with weight \(r\) has period \(p^{\max(0,s-j)}\). Its inverse has the same period. For \(h\nmid r\), the finite field cut out by \(D\) has degree
\[
 \frac{h}{\gcd(h,r)}\,p^{\max(0,n-1-j)}.
\]
Descent to this field follows directly from the tame argument above, even when the kernel discarded from a full cyclotomic field has order divisible by \(p\).

For \(h\mid r\) put \(w=1+j\). The invariant group in \(M\) has order \(p^w\). A generator has a \(p^n\)-preimage of exact order \(p^{n+w}\). Every preimage has that order. A subgroup kills its boundary exactly when it fixes some such preimage, equivalently when it acts trivially on the whole cyclic group \(M[p^{n+w}]\). At this depth the tame action is trivial and the wild order is exactly \(p^n\). The smallest extension over which all coefficient boundaries vanish is consequently \(EX_n\), where \(X_n\) is the degree-\(p^n\) layer of the rational cyclotomic \(\mathbb Z_p\)-extension. This field interpretation uses the project fields' global and local cyclotomic images.

There is a direct check of the single missing layer. A cyclic subgroup of order \(p^k\) acting by \(1+pt\) has a generator value \(y\) admissible on coefficients of order \(p^n\) precisely when \(p^{\max(0,n-k)}\mid y\). At \(k=n-1\) every such value is divisible by \(p\). At \(k=n\) every value occurs. Writing the generator scalar as \(u=1+p^w c\) with \(p\nmid c\), the boundary of a lower numerator \(b\) has generator value \(cb\). Changing the lift changes this by a principal cocycle, and the number of classes is \(p^{\min(w,n)}\). The finite cocycle construction, numerator quotient, and subgroup fixed-lift criterion have separate Lean declarations.

At depth one the coefficient twist is trivial on the exceptional tame class. If the class-field comparison is applied, its complementary support is detected by the \(p\)-part of \(\mathrm{Cl}(\mathcal O_{E^+X_1}[1/p])\). Indeed the action \(T\) of the cyclic group of order \(p\) on that class group modulo \(p\) satisfies \((T-1)^p=0\), so its coinvariants vanish exactly when the module vanishes. `CoinvariantSupport` proves the operator identity and quotient criterion.

## The four signs above 277

In the biquadratic base field with radicals $X^2=-3$ and $Y^2=-23$, the four rational embeddings in the standard 277-adic field have distinct residue pairs for $(X,Y)$. The two positive branch residues are 44 and 114. Each pair specifies the comparison of absolute values on every element of the field. The metric completion for that comparison is isometrically isomorphic to the standard 277-adic field. The rational constants already have dense image. The checked comparisons are `TamePadicEmbeddings277.four_padic_embeddings`, `TamePadicPlaces277.equiv` and `TamePadicPlaces277.completion_at` in the Lean 4.36.0 project under `formal/Mathlib277`.

The decomposition group at each of these four primes in the bottom extension over the rationals is trivial. Its arithmetic Frobenius fixes the biquadratic field. On the residue field of order 277 it sends each element to its 277th power. For the strict comparison one must describe characters of the absolute Galois group of the field cut out by the finite twist. After imposing unramifiedness at finite primes away from 277 and splitting above 277, the remaining global input is the Artin map from invertible fractional ideals of its localized integer ring, with principal kernel and the specified Galois action.

## A rank-two example at infinitely many weights

At a nonzero tame weight \(a\bmod h\) let \(K\) be its tame character field in \(E(\mu_p)\). On the maximal real subfield \(K^+\), let \(B\) be the equivariant character group of the ordinary \(p\)-class group into \(\mathbb Q_p/\mathbb Z_p\) with the tame target action \(\omega^{-a}\) (Teichmüller lift). If \(B\) has exponent \(p^e\), then at weights \(r\equiv a\bmod h\) and \(p^e\mid r\) both coefficient depths \(e\) and \(e+1\) see the same tame field and the same group \(B\). The inclusion of the two torsion subgroups is an equality by their orders, so the entire complementary group is isomorphic to \(B\). If \(e=0\), vanishing at depth one suffices. These deductions use the arithmetic character comparison above.

For \(E=\mathbb Q(\sqrt{-107},\sqrt{-503})\) and \(p=3\), take odd \(r\). The two quadratic lines with nontrivial tame action in \((E(\mu_3))^+\) arise from discriminants 321 and 1509. The third quadratic line is tame fixed. On the 3-primary part the quadratic norm/extension composites split the eigenspaces since 2 is invertible. Both relevant ordinary quadratic class groups are \(C_3\). For each discriminant Lean verifies exactly 16 reduced pairs forming three cycles of lengths \(4,6,6\). The comparison between reduced cycles and ordinary ideal classes is an external arithmetic input. Each field has narrow class number 6. Hence \(B=C_3\oplus C_3\) and \(e=1\). The paper deduction gives this entire complementary 3-group at **every weight \(r\equiv3\bmod6\)**. The numerical field records independently give both class groups. [Discriminant 321](https://www.lmfdb.org/NumberField/2.2.321.1) · [Discriminant 1509](https://www.lmfdb.org/NumberField/2.2.1509.1)

The original full arithmetic-window bound at the weights required for ordinary RH remains open.
