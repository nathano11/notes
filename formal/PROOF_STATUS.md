# Proof status and restart instructions

## Continue Mathematical Analysis — local orders and the conductor-69 projection

### Round 4. Absolute tower, ideal classes and genus coordinates

Continue Mathematical Analysis also owns `DyadicBottomPrime69.two_dyadic_primes` for the two bottom roots, `DyadicNativeEmbedding69.root_embedding` for realizing the coordinate field at chosen square roots, and `DyadicMizusawaHandoff69.field_commutator_coordinates` for the image of the actual field commutator in the marked coordinates.

Continue Mathematical Analysis reserves `DyadicPrimeGalois69.absolute_decomposition_image` for restriction of native automorphisms stabilizing a native prime in the integral closure.
The same owner joins the literal subfields \(E_a\) and \(L\) to the coordinate field and root tower in `DyadicCyclotomicModel69.cyclotomic_model`.
**DyadicCenterCriterion69.centered_of_generator** is reserved for recovering the entire bottom center from the positive-value test at the one labelled generator.
**DyadicArtinSquare69.square_from_ideal_classes** compares the closed commutator subgroup in the presentation with order-two dyadic ideal classes at finite Artin stages.
**DyadicTwistedControl69.samples_of_two_bottom_controls** is the two-bottom coefficient comparison for the generators \(\gamma\) and \(\tau\gamma\) on the common cyclotomic field of \(\mathbb Q(\sqrt{-69})\) and \(\mathbb Q(\sqrt{-138})\). **DyadicClassNorm69.numberField_norm_mk0** owns the norm map between native finite ideal class groups.
**DyadicFiniteModel69.stage_generation** specializes field generation to each actual lower stage \(E_a(\zeta_{a+n})\). **DyadicHilbertStage69.hilbert_stage** joins arithmetic prime Frobenii and native fractional ideals to the finite Artin stages.
**DyadicHilbertTransition69.native_transition** joins native relative ideal norms and Galois restriction on globally unramified number-field squares to the norm-compatible Artin limit.
**DyadicAbsoluteCenters69.both_dyadic_primes_surject** is the native target for simultaneous restriction at both labelled primes, for every \(a\), with \(\Omega/\mathbb Q\) an algebraic closure.
**DyadicUnramifiedClosure69.maximal_unramified_normal** is reserved for the fixed field of the intersection of normal open 2-power-index subgroups containing all finite-place inertia, and invariance under ambient conjugation preserving \(k_\infty\).
**DyadicMizusawaPlaces69.both_primes_in_maximal_unramified** specializes both restriction maps to this one intrinsic upper field. **DyadicClassArtinLimit69.continuous_class_artin** is the ordinary ideal-class norm limit with its product topology, at the arithmetic fields themselves.
**DyadicGenusInertia69.inertia_fixes_marked_genus** tests inertia on the integral half-roots at 3 and 23 and the fourth root at 2. The native bottom ideal-class certificate starts at **DyadicQuadraticClass69.ring_of_integers** for fundamental discriminant −276.
**DyadicGenusContainment69.full_cyclotomic_le_maximal** is the relative 2-power-index and inertia calculation placing the genus field in the intrinsic upper field.
**DyadicPrimeGeneratorValue69.prime_generator_value** matches the two core generators with \(w=(1+y)/2\) and \(1-w\) in the native field. **DyadicTowerCenters69.all_real_layer_centers** contracts one pair of ambient primes simultaneously through the real layers.

Its local comparison reserves `DyadicNativeValue69.normalized_prime_value` for the rational normalization of the native height-one valuation at a finite dyadic place.

Continue Mathematical Analysis reserves `DyadicNativeFrob69.frobenius_at_contracted_prime` for independence of the arithmetic Frobenius at lifts of an ideal in an abelian extension. The finite ideal norm proof is `DyadicArtinResidueNorm69.frobenius_norm_at_prime`.

**Fields, actions and range.** Put \(k=\mathbb Q(\sqrt{-69})\), \(K=k(\sqrt3,\sqrt{23})\), \(Q_n=\mathbb Q(\zeta_{2^{n+2}})^+\), \(k_n=kQ_n\), \(K_n=KQ_n\). Write \(k_\infty,K_\infty\) for their unions and \(M\) for the maximal unramified pro-2 extension of \(k_\infty\). Here \(G=\mathrm{Gal}(M/k_\infty)\), \(H=\mathrm{Gal}(M/K_\infty)\), and the radical description identifies \(K_\infty=E_0(\mu_{2^\infty})\), with \(E_0=\mathbb Q(\sqrt{-3},\sqrt{-23})\). The local restriction is over \(E_a=E_0Q_a\) for each \(a\ge0\), at either prime above 2. In \(k_\infty\) there is one dyadic place. In the two-place argument one chooses a place in \(M\) and its translate by \(B\). The forward generator \(\gamma\) acts by exponent 5 on real cyclotomic traces and by left conjugation. The local lifting and the arithmetic Artin map carry no weight parameter. The matrix result allows all natural \(a,r\). Identifying the arithmetic strict dual with that matrix quotient requires positive odd \(r\).

**The coefficient input has a paper proof at the requested precision.** Write \(P=T^2+C_1 T+C_0\) for Mizusawa's actual monic polynomial. In the abelianization, Theorem 2.2 gives \(X=\langle [A]\rangle_{2}\oplus\mathbb Z_2 b\oplus\mathbb Z_2 c\) with \((\gamma-1)b=c\), \((\gamma-1)c=C_1[A]-C_0 b-C_1c\), \((\gamma-1)[A]=0\). The example on printed p. 134 gives \(C_1\equiv2\pmod4\) for this pair (\(3\equiv7^2\bmod23\)). Thus \(X/(\gamma-1)X\cong C_2\oplus\mathbb Z_2/(C_0)\). The bottom control on printed p. 130 identifies the coinvariants with the 2-class group of \(k\), of order eight. This forces \(v_2(C_0)=2\). Consequently the class of \(P\) modulo \((2,T)^3\) is exactly \(4+2T+T^2\), the class of the explicit series computed in **DyadicOneSided69.canonical_jet**. In particular the requested one-sided containment follows there. [Mizusawa, Theorem 2.2, §3.3 and Example](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Class group of the field of discriminant −276](https://www.lmfdb.org/NumberField/2.0.276.1)

**Checked coefficient implication.** **DyadicControlJet69.relation_is_forward_coinvariant** identifies the actual reductions of the three forward columns in the row calculation. With even \(C_1\), **enumeration_count** gives \(2\gcd(8,C_0\bmod8)\) classes. **control_of_form_correspondence** takes a map from the reduced forms of discriminant −276 to the finite coinvariants, injective on the enumerated forms and onto that quotient. **samples_from_bottom_control** takes their common cardinality and \(C_1\bmod4=2\). **oriented_weighted_jet_from_bottom_control** yields the finite-ideal containment and the ordered raw numerators \((-2208,2208)\) at residues \((13,5)\). At order four in the forward-5 basis the inverse-exponent coefficient at exponent one uses 13, giving normalized value −1; the direct exponent 5 gives +1. **SignedCommonNormalization.gamma_normalization_69** and **SignedOrientationWitness.first_orientation_witness** are the shared orientation checks. The remaining Lean inputs for the actual polynomial are the marked forward action and bottom control on the *arithmetic* class groups, the comparison with reduced forms, and the printed mod-4 coefficient calculation. This route requires no equality of the full characteristic and analytic ideals. [Control and orientation](Reimann/DyadicControlJet69.lean) · [Finite ideal criterion](Reimann/DyadicOneSided69.lean)

**Reciprocity at the finite stages.** Apply full Hilbert reciprocity at each totally imaginary \(k_n\), and independently at each \(K_n\), followed by restriction to its 2-primary part. The expected targets are \(G^{\mathrm{ab}}\) and the abelian group \(H\), respectively. For the full Hilbert class field the fractional-ideal kernel is the principal subgroup. For the 2-Hilbert field it is the inverse image of the odd-order ideal classes. **DyadicArtinResidueNorm69.frobenius_norm_at_prime** checks the residue degree power using arithmetic Frobenius and trivial inertia. **DyadicArtinLimit69.transition_from_prime_norms** extends norm compatibility to fractional ideals given prime generators and the ideal norms. **continuous_artin** gives mutually inverse continuous homomorphisms on the coordinatewise 2-primary limits, for full finite symbols surjective with the stated full kernel and compatible with norm/restriction. Its topology is the finite-coordinate cylinder topology. The identification of the finite Hilbert towers with these named subextensions of \(M\), and the equality with their Krull topology, require arithmetic specialization. [Artin norm](Reimann/DyadicArtinResidueNorm69.lean) · [Continuous Artin isomorphism](Reimann/DyadicArtinLimit69.lean)

**The Frobenius tests.** In the coordinate order \(\mathbb Z[\sqrt{-69}]\), **DyadicRamifiedClass69.dyadic_class_order_two** proves primality of \(\mathfrak p=(2,1+\sqrt{-69})\), equality \(\mathfrak p^2=(2)\), and nonprincipality. The certificate is in the quadratic order's explicit ideal predicates. The layerwise argument still needs the comparison with its native ideals, total ramification at 2 in \(k_n/Q_n\), and the principal generator for the prime of \(Q_n\). These give \(\mathfrak p_n^2=(2-\zeta_{2^{n+2}}-\zeta_{2^{n+2}}^{-1})\). Residue degree one makes the dyadic classes norm-compatible. The unramified quadratic factor \(\mathbb Q_2(\sqrt{69})\) in the genus field gives the nonidentity Frobenius image. Full unramified local reciprocity identifies its closed cyclic subgroup with the decomposition group. [Bottom ideal](Reimann/DyadicRamifiedClass69.lean) · [Mizusawa, §3.1 and proof of Proposition 3.5](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

**Marked groups and the field commutator, checked on 4.36.0.** **DyadicMizusawaCoordinates69.marked_field_handoff** constructs the quotient coordinates from powers of \(A,Z=A^{-1}C,B\), with \(Z\) central and \(B^vA^uB^{-v}=A^{(-1)^vu}\). It needs the three genus tests \(A\mapsto(1,0), B\mapsto(0,1), C\mapsto0\), independence and spanning of \(A^uZ^wB^{2v}\) on the index-two subgroup, and a procyclic local Frobenius subgroup whose generator has square in the closed derived group and nonzero genus image. It proves \(D=\overline{\langle A\rangle}\), \(H\cap D=\overline{\langle A^2\rangle}\), \([B]=(1,0)=b\), and \(\mathrm{im}(H)=\mathbb Z_2(2b)\oplus\mathbb Z_2c\). **quotient_precision** also determines every finite-coordinate congruence. **forward_generator_columns** sends the two forward conjugates to \((1,1)\) and \((-C_0,1-C_1)\). [Coordinates and forward action](Reimann/DyadicMizusawaCoordinates69.lean)

**DyadicMizusawaHandoff69.field_commutator_coordinates** applies **split_artin_commutator** to field automorphisms. It takes the marked data above on the unramified group acting on the upper field, a characteristic-zero lower field with its generated root tower, its unital ring embedding upstairs, \(i^2=-1\), pointwise fixation of \(i\sqrt{-3}\sqrt{-23}\) and the real traces, and the equivalence between trivial genus restriction and fixing both \(i\sqrt{-3},i\sqrt{-23}\). For a lift \(d\) fixing the chosen prime over 2 and preserving the unramified group by conjugation, \(BdB^{-1}\) fixes the translated prime and restricts to the same \(t\). The image of the literal field commutator \(BdB^{-1}d^{-1}\) under \(H/(H\cap D)\to G/D\to\mathbb Z_2^2\) is \((1,0)-Y(t[B])\). **DyadicGenusSwitcher69.mizusawa_switcher** derives the exchange from \(B\) fixing \(k_\infty(\sqrt{23})\) and moving the genus field. Its proof derives the signs of \(i,\sqrt{-3},\sqrt{-23}\). To instantiate the named \(M\), use Mizusawa's actual marked generators and the layerwise Artin Frobenii above. The abstract marking test alone does not construct the maximal unramified field. [Literal commutator](Reimann/DyadicMizusawaHandoff69.lean) · [Genus signs](Reimann/DyadicGenusSwitcher69.lean)

**Unconditional absolute restriction.** **DyadicAbsoluteCenters69.both_dyadic_primes_surject** takes only a characteristic-zero field \(\Omega\) with `IsAlgClosure ℚ Ω`. It chooses \(x^2=-3, y^2=-23\), compatible primitive \(2^{n+2}\)-th roots \(\zeta_n\), the integer \(w=(1+y)/2\), and two distinct maximal ideals \(P,Q\) of \(\mathcal O_\Omega\). The *same pair* contracts distinctly at every \(E_a=\mathbb Q(x,y,\zeta_a+\zeta_a^{-1})\); \(w\in P\), \(1-w\in Q\). For \(J=P,Q\) it proves the surjectivity of

\[
 \operatorname{Stab}_{\operatorname{Gal}(\Omega/E_a)}(J)
 \longrightarrow \operatorname{Gal}(E_a(\mu_{2^\infty})/E_a).
\]

**chosen_roots_both_primes** allows given roots with those equations. **surjects_in_normal_field** restricts the resulting lifts to the stabilizer of the contracted prime of any \(M/E_a\) normal and containing the full cyclotomic field. Both hypotheses on this particular \(M\) are explicit in that corollary. These declarations use native `IntermediateField`, `Ideal`, `AlgEquiv.restrictNormalHom` and `MulAction.stabilizer`. [Two simultaneous absolute restrictions](Mathlib69/ReimannNative69/DyadicAbsoluteCenters69.lean)

The cofinal tower **DyadicNormalTower69.cofinal_normal_tower** enumerates a countable algebraic Galois upper field over its countable base and takes successive finite normal closures, with every prescribed root included at its own stage. **finite_cyclotomic_stages** gives the lower fields, their inclusions and their exact union. **DyadicTowerCenters69.all_real_layer_centers** contracts the two maximal ideals of the absolute integer ring; **DyadicIntegerPrime69.adjacent_integer_contraction** checks the stage maps. The two ideals come from reduction of \(\mathbb Z[w]\) at 0 and 1 modulo 2 and integral lying-over. **DyadicCenterCriterion69.centered_of_generator** derives the full center from membership of just \(w\) or \(1-w\), proving nonnegativity on localized algebraic integers by their monic equations. **DyadicPrimeValueTower69.centered_union_of_generator** constructs the rational normalized valuation on the infinite union and recovers its integral support by contraction. **DyadicPrimeGalois69.absolute_decomposition_image** uses transitivity of the relative Galois group on integral primes to lift each automorphism stabilizing the lower prime. No discreteness is imposed on the value group at the infinite layer. [Cofinal finite fields](Mathlib69/ReimannNative69/DyadicNormalTower69.lean) · [Single-generator center](Reimann/DyadicCenterCriterion69.lean) · [Valuation on the union](Mathlib69/ReimannNative69/DyadicPrimeValueTower69.lean) · [Restriction and correction](Mathlib69/ReimannNative69/DyadicPrimeGalois69.lean)

**From ideals to the closed commutator test.** **DyadicArtinSquare69.commutator_quotient_iso** identifies the quotient of the marked group by its closed derived subgroup with \(C_2\times\mathbb Z_2^2\), with coordinates \((u\bmod2,v,w)\). **square_from_ideal_classes** takes norm-compatible dyadic ideals with principal squares, jointly faithful restrictions of that marked abelianization to finite Hilbert stages, and equality of its Frobenius with the symbols of these ideals or their inverses. It supplies the derived-square condition on \(F\). Inverting a Frobenius of order two and replacing it by an odd power both preserve its symbol in these abelian quotients. The projected Frobenius in \(G^{\mathrm{ab}}\) may have order two even when its lift in \(G\) has infinite order. [Abelianization and finite Artin squares](Reimann/DyadicArtinSquare69.lean)

**A second coefficient test using two finite bottoms.** The common cyclotomic field \(k_\infty=\mathbb Q(\sqrt{-138})Q_\infty\) contains \(\sqrt2\). The generators over \(\mathbb Q(\sqrt{-69})\) and \(\mathbb Q(\sqrt{-138})\) are \(\gamma\) and \(\tau\gamma\) respectively, where \(\tau\) is complex conjugation. For the actual 2-primary classes, inversion by \(\tau\) follows from the odd class numbers of the real cyclotomic layers via the norm to the real subfield. **DyadicTwistedControl69.companion_conjugacy** checks the integral change \(b'=b,\ c'=-2b-c\) for the action \(-\gamma\); its constant coefficient is \(P(-2)=4-2C_1+C_0\). With even \(C_1\), **samples_of_two_bottom_controls** and **weighted_jet_of_two_bottom_controls** require complete nonrepeating finite quotient enumerations of cardinalities equal to the reduced-form counts for discriminants −276, −552. They imply \(P(0)\equiv P(-2)\equiv4\bmod8\) and the same finite conductor-69 ideal membership. **lattice_order_of_two_bottom_controls** gives mutually inverse maps to \(\operatorname{Fin}(2^{2a+1})\) for all natural \(a,r\). The comparison of each finite quotient with its actual bottom 2-class group, the two class-number calculations for native ideals, and inversion under complex conjugation are the arithmetic inputs to this route. The published coefficient test on p. 134 provides the independent route above. [Two-bottom control](Reimann/DyadicTwistedControl69.lean) · [Second bottom class group](https://www.lmfdb.org/NumberField/2.0.552.1) · [Weber's theorem on the real tower](https://doi.org/10.5802/jtnb.720)

### Round 3. Local restriction and the Artin discrepancy at conductor 69

Use \(x=\sqrt{-3}\), \(y=\sqrt{-23}\), \(E_0=\mathbb Q(x,y)\), \(w=(1+y)/2\), \(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\), \(E_a=E_0 Q_a\), and \(L=E_0(\mu_{2^\infty})\). The primes at the bottom are \((2,w)\) and \((2,1-w)\). The parameter \(a\) is any natural number, including zero. The local field and Artin statements do not use a weight.

**From the completed factors to the whole tower.** In the odd-denominator order \(S\) of \(E_0\), let \(\alpha\) be the second generator of the chosen prime and let \(\beta=1-\alpha\). The identity \(\alpha\beta=6\) makes \(\beta\) a unit at the chosen place. For each \(s\in(2,\alpha)\) the proof constructs \(s'\in S\) with \(\beta s=2s'\), lowering the value by one. Descent proves that all normalized valuations centered at that prime agree in \(\mathbb Z\) on nonzero field coefficients, including fractions. The definition of **Centered** requires nonnegativity on \(S\) and equality of its positive-value-or-zero ideal with the selected residue kernel. [DyadicBottomValue69.agree_integral_on_bottom](Reimann/DyadicBottomValue69.lean) · [DyadicEmbeddedBase69.base_subfield](Reimann/DyadicEmbeddedBase69.lean)

For \(z^{2^n}=-1\), set \(\pi=1-z\). The identity \((1-z)(1+z)=1-z^2\) and \(v(2)=1\) give \(v(\pi)=2^{-n}\). Nonzero terms \(c_j\pi^j\), \(0\le j<2^n\), have distinct values modulo \(\mathbb Z\). The least-valued term therefore determines the value of their sum. Field generation gives a quotient of two such sums for **every** element of \(E_0(z)\), with a nonzero denominator. These steps require neither a presumed power basis nor a presumed uniqueness-of-prolongation theorem. [DyadicDecomposition69.cyclotomic_place_unique](Reimann/DyadicDecomposition69.lean) · [DyadicCyclotomicSpan69.cyclotomic_normal_form](Reimann/DyadicCyclotomicSpan69.lean)

**Restriction at a specified absolute prime.** For a compatible tower with \(z_n^{2^n}=-1\) and \(z_{n+1}^2=z_n\), **finite_layer_place_unique** identifies any two normalized extensions with the same bottom center on \(E_0(z_n)\). **generated_tower_iff_union** and **infinite_layer_place_unique** do so on \(L\). Hence **relative_decomposition_surjective** proves that the relative stabilizer is all of \(\operatorname{Gal}(L/E_a)\). It uses the presentation of \(L\) by generators and the definition of a valuation centered at the selected prime. The theorem supplies the local uniqueness. On paper, take an extension \(g\) of \(t\in\operatorname{Gal}(L/E_a)\) to \(\Omega=\overline{E_a}\). If \(p\) is the chosen prime in \(\Omega\), then \(gp,p\) agree on \(L\). Some \(h\in\operatorname{Gal}(\Omega/L)\) sends \(gp\) back to \(p\). Thus \(hg\in D_p\) and \((hg)|_L=t\). This works independently at either prime and at every \(a\). The same argument applies to a chosen normal Galois extension \(\Omega/E_a\) containing \(L\). **absolute_decomposition_surjective** checks this deduction under extension, kernel transitivity, and equivariance of restriction. [DyadicLocalRestriction69](Reimann/DyadicLocalRestriction69.lean) · [Extension of field automorphisms, Stacks 0BME](https://stacks.math.columbia.edu/tag/0BME) · [Transitivity on primes, Stacks 0BRK](https://stacks.math.columbia.edu/tag/0BRK)

**An absolute lift from finite Galois data.** **DyadicAbsolutePlace69.decomposition_lifts_every_automorphism** constructs an automorphism \(d\) on the upper field with \(d|_L=t\) and \(d(p)=p\). Its lower field is an embedded \(E_0\) with the displayed cyclotomic generators. Its upper field is an exhausted countable union of fields, with injective compatible embeddings of the finite integral orders. The chosen finite prime predicates are residual maximal ideals, contract along the tower, and restrict to the specified bottom-centered valuation on the lower orders. Upper automorphisms are listed at each finite stage. Their relative kernel fixes the lower order, contains the identity, and its orbit norms land in that order. Each \(t\) has compatible restrictions to the lower orders and **ordinary** upper lifts separately at each stage. Each lower field element is a fraction of elements of one lower order. These are inputs to the finite presentation. None requires finding a prime-stabilizing lift. The proof constructs the correction by a finite orbit-norm argument, selects compatible corrected lifts by finite compactness, proves independence of the choice of layer in the glued field map, and checks its bijectivity and prime preservation. **union_prime_contracts** recovers the selected finite prime at every layer. [DyadicAbsolutePlace69](Reimann/DyadicAbsolutePlace69.lean) · [DyadicFiniteRestriction69](Reimann/DyadicFiniteRestriction69.lean) · [DyadicKernelLift69](Reimann/DyadicKernelLift69.lean)

For a field-native instantiation take cofinal finite Galois \(K_n/E_a\) in the chosen absolute or maximal allowed extension, each containing \(L_n=E_a(\zeta_{2^{n+2}})\) after reindexing. Use the inclusions of the rings of integers, ordinary extension of \(t|_{L_n}\) to \(K_n\), and the fact that norms from \(\mathcal O_{K_n}\) land in \(\mathcal O_{L_n}\). The absolute prime on the integral closure is the union of its finite contractions. The general Galois theorems justify these choices on paper. Formalizing this concrete tower, its integral-order embeddings, automorphism lists, norm descent, and the prime contractions is the outstanding realization step for the absolute map. [Stacks 0BME](https://stacks.math.columbia.edu/tag/0BME) · [Stacks 0BRK](https://stacks.math.columbia.edu/tag/0BRK)

**Change to Mizusawa’s field.** Over a common characteristic-zero field take \(i^2=-1\), \(x^2=-3\), \(y^2=-23\). The paper’s genus generators are \(ixy,ix,iy\), of squares \(-69,3,23\). They recover \(i=-(ixy)/((ix)(iy))\). At each nontrivial complex layer a primitive root is recovered from its real trace and \(i\). In particular **embedded_mizusawa_field_change** proves the equality of generated fields \(E_a(\mu_{2^\infty})=K\mathbb Q_\infty\), \(K=k(\sqrt3,\sqrt{23})\), at every \(a\). This identifies the base of the unramified group \(H\). [DyadicGenusField69](Reimann/DyadicGenusField69.lean) · [Mizusawa, §4.2](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

**The Artin image of the second local lift.** Write \(G=\operatorname{Gal}(M/k_\infty)\) for Mizusawa’s unramified tower, \(D=\langle A\rangle\) for its closed dyadic decomposition subgroup, and \(H=\operatorname{Gal}(M/L)=\langle A^2,B^2,C\rangle\). Then \(G/D=Y\) and \(H/(H\cap D)\) maps injectively onto the image of \(H\) in \(Y\). If \(d\) is a first-place lift of \(t\), the second lift by the switching element is \(BdB^{-1}\). Their discrepancy \(BdB^{-1}d^{-1}\) restricts trivially to the genus field whenever the two restricted automorphisms commute. In the indicated subgroup quotient its image is exactly \([B]-t[B]\). **switchClass_is_local_discrepancy** identifies the same word used by the strict local condition. **switchClass_independent** removes the choice of lift of \(t\) if the kernel elements act by inner conjugations on the abelian quotient. Replacing \(B\) by \(Bh\) with \(h\in H\) adds \((1-t)[h]\). A character therefore changes the common primitive by one fixed value for all \(t\). [DyadicArtinImage69](Reimann/DyadicArtinImage69.lean) · [DyadicArtinCommutator69](Reimann/DyadicArtinCommutator69.lean)

**The literal field-automorphism word.** **DyadicArtinPlace69.split_artin_commutator** takes a field lift \(d\) as returned by **decomposition_lifts_every_automorphism**, the chosen upper prime \(p\), a swap candidate \(B\in N\), and the restrictions of \(B,d\) to \(L\). Here \(N\) denotes the paper's full unramified group \(G\) for this application. In the theorem \(D\) is defined as the stabilizer of \(p\) in \(N\) and \(H\) as the subgroup of \(N\) fixing the embedded \(L\) pointwise. The hypotheses require \(D\) normal in \(N\) and conjugation by \(d\) to preserve \(N\). Preservation of \(D\) by \(d\) follows from \(dp=p\). The proof shows, on field elements, that \(BdB^{-1}\) restricts to the same \(t\), stabilizes \(Bp\), and that \(BdB^{-1}d^{-1}\) lies in \(H\). Its class in \(H/(H\cap D)\) maps into \(N/D\) as \((1-t)[B]\), with \(t\) acting by conjugation on the quotient. **DyadicAbelianTower69.automorphisms_commute** proves the necessary commutation on \(L\). **switched_prime_contracts** identifies \(Bp\) with the opposite lower prime by testing the sign of \(B\) on \(\sqrt{-23}\). It handles contraction on the integral-order test domain. [DyadicArtinPlace69](Reimann/DyadicArtinPlace69.lean) · [DyadicAutomorphism69](Reimann/DyadicAutomorphism69.lean) · [DyadicAbelianTower69](Reimann/DyadicAbelianTower69.lean)

At unramified primes the finite calculation **unramified_prime_transport** derives conjugacy of arithmetic Frobenius from its \(N\mathfrak p\)-power action on residues and trivial relative inertia, using the norm of the contracted prime. **arithmetic_commutator** applies this to products of Frobenii and inverses. **coherent_artin_classes** and **coherent_commutator** require compatibility of source classes under restriction, allowing individual lifts to vary. Changing to geometric Frobenius for the same prime ideal classes negates the projected difference. Mizusawa writes the word \(B^{-1}d^{-1}Bd\), whose projection is \(-b+t^{-1}b=t^{-1}(1-t)b\) with the forward action. These two sign conventions are independent. [DyadicArtinFrobenius69](Reimann/DyadicArtinFrobenius69.lean) · [Mizusawa, pp. 129–130](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

**First field input remaining on the Artin side.** Construct the continuous Artin map for the actual unramified tower. Factor the finite arithmetic Frobenius maps through principal ideals, compare norms with restrictions, identify the inverse-limit class representing the chosen \(B\), and transport the resulting quotient and action to Mizusawa's basis. In this basis \(D=\langle A\rangle\), \(H\cap D=\langle A^2\rangle\), \([B]=b\), and the image of \(H\) is \(2\mathbb Z_2b+\mathbb Z_2c\). One must identify the coset of \(B\) as the place switcher and \(\gamma\) as the forward generator acting by \(J\). With \(b\) so identified the computed difference is \((1-t)b\) for every \(t\). The checked finite transport and quotient calculations give the implication for any such realization. The complete arithmetic reciprocity isomorphism and its topology are paper inputs here. Verify Lean Proofs owns the general continuous strict cohomology/class-character interface. [Mizusawa, pp. 117–119, 129–130](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

**Analytic and strict boundaries.** In the forward orientation \(\chi_{\rm cyc}(\gamma)=5\), take \(P(T)=\det((1+T)I-J)=T^2+C_1T+C_0\) on \(Y\). It suffices to put this actual \(P\) in the ideal of the conductor-69 series in \(\mathbb Z_2[[T]]/(8,4T,2T^2,T^3)\). The series has image \(4+2T+T^2\). **DyadicOneSided69.weighted_jet_iff_samples** then gives \(C_0\equiv4\bmod8\), \(C_1\equiv2\bmod4\). Math Idea Review reports **DyadicMatrixHandoff.lattice_invariant_factors** for all \(a,r\in\mathbb N\) under these samples. The strict arithmetic comparison takes **positive odd** \(r\), \(M_r=(\mathbb Q_2/\mathbb Z_2)(-r)\), both local restrictions principal, and one primitive on the entire second local group. Its required identification is \(X/(J^{2^a}-5^{-r2^a}I)Y\), with \(Y=\mathbb Z_2b+\mathbb Z_2c\), \(X=2\mathbb Z_2b+\mathbb Z_2c\). The conditional invariant factors are \(2^a,2^{a+1}\), hence the order is \(2^{2a+1}\). At \(a=0\) the first factor is trivial. The conductor-2893 coefficients belong to the separate signed branch. [DyadicOneSided69](Reimann/DyadicOneSided69.lean) · [DyadicPlaceProduct.strict_iff_conjugate_discrepancy](Reimann/DyadicPlaceProduct.lean)

**Identifying the switcher from the lattice.** **DyadicArtinPlace69.outside_class_switches_prime** shows that \([B]\notin X=\operatorname{im}(H\to N/D)\) forces \(B\) to exchange the two lower primes. Indeed, if the lower prime were fixed, extension and transitivity on prolongations would give \(d\in D\) with the same restriction as \(B\). Then \(Bd^{-1}\in H\) and \([B]=[Bd^{-1}]\in X\). Thus the single arithmetic basis identification \(Y=\mathbb Z_2b+\mathbb Z_2c,\ X=2\mathbb Z_2b+\mathbb Z_2c,\ [B]=b\) supplies the switcher test as well. Directly computing the sign on \(\sqrt{-23}\) gives the same conclusion. [DyadicArtinPlace69](Reimann/DyadicArtinPlace69.lean) · [DyadicPrimeExchange69](Reimann/DyadicPrimeExchange69.lean)

**Compiler record for round 3.** All 499 breakpoints in the 22 modules in this round passed on Lean **4.36.0**, Windows x86_64, commit **611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9**. The total comprises 342 named theorem proof terms, 99 definitions, 30 structures, three abbreviations, three inductives and 22 whole-source checks. There are zero standalone executable guards in this count. The declaration-prefix digests, final imported-source digests and per-module compatibility ledgers were audited. No checked output in those ledgers reported **sorryAx** or **Lean.ofReduceBool**. The last named breakpoint was **Reimann.DyadicArtinPlace69.outside_class_switches_prime**, followed by **DyadicArtinPlace69.complete**. The combined **Reimann** target passed in 446 Lake jobs and **ReimannWindow** in 30. Both toolchain files pin **4.33.1**. These are exclusively **4.36.0** results. [Absolute lift ledger](compat-4.36.0-DyadicAbsolutePlace69.json) · [Artin ledger](compat-4.36.0-DyadicArtinPlace69.json) · [Genus-field ledger](compat-4.36.0-DyadicGenusField69.json)

### Field and normalization checkpoints for (3,23), November 20

Let \(E_0=\mathbb Q(\sqrt{-3},\sqrt{-23})\), \(e=(1+\sqrt{-3})/2\), \(w=(1+\sqrt{-23})/2\), and \(O=\mathbb Z[e,w]\). The imaginary quadratic Iwasawa base is \(k=\mathbb Q(\sqrt{-69})\). The even Dirichlet character \(\psi\) has conductor 69 and belongs to the real field \(\mathbb Q(\sqrt{69})\). The following computations use these three indicated fields.

| Lean source | Field-specific content |
|---|---|
| [DyadicFieldTrace69](Reimann/DyadicFieldTrace69.lean) | **field_pairings_embed** and **trace_as_conjugate_sum** identify the regular trace in the rational field model with the four multiplication traces against \(1,e,w,ew\) and the sum over sign conjugations, respectively. **field_trace_saturation** treats \(2^n y\in O\) with all four traces integral. |
| [DyadicOrderIntegral69](Reimann/DyadicOrderIntegral69.lean) | **quartic_annihilates_embed** gives an explicit monic integer polynomial for each \(x\in O\). **order_is_integral** supplies the lower inclusion \(O\subseteq\mathcal O_{E_0}\). |
| [DyadicIntegralCriterion69](Reimann/DyadicIntegralCriterion69.lean) | **embed_homogenize**, **even_numerator**, **odd_denominator** implement descent on a positive common denominator. For an even denominator, a monic equation reduces to a power of the numerator in \(\mathbb F_4\times\mathbb F_4\). Each coordinate vanishes, allowing division of the integer numerator by two. |
| [DyadicOrderCompletion69](Reimann/DyadicOrderCompletion69.lean) | **embed_integerProduct**, **integer_reduction_eq_iff**, **integer_reduction_surjective**, **completion_algebra_iso** realize \(O\) inside the rational field and identify its completed order with the earlier four dyadic coordinates. At depth \(m\ge1\) the integer reduction has kernel \(2^mO\). |
| [DyadicDistribution69](Reimann/DyadicDistribution69.lean) and [DyadicProgression69](Reimann/DyadicProgression69.lean) | **coefficient_exact**, **positive_row_pushforward**, **literal_bernoulli_row** prove integer divisibility and two-child compatibility for the half-normalized coefficient. For \(D=2^n\), \(4\mid D\), \(0<t<D\), \(t\equiv1\bmod4\), it equals \(-\sum_{j=0}^{68}j\psi(t+Dj)/69\). The opposite progression supplies the \(\chi_{-4}\) twist. **conductor_normalization** and **stickelberger_row_comparison** give exactly \((4,0)\) at \(D=8\), hence \((8,0)\bmod16\) for the doubled row. |

**Arithmetic localization.** In [DyadicArithmetic69](Reimann/DyadicArithmetic69.lean), **positive_denominator** clears a common denominator for every element of the rational biquadratic field. **integral_odd_denominator** allows it to be chosen odd for any root of a monic integer polynomial. **integers_localized_at_two** proves \((\mathcal O_{E_0})_{(2)}=O_{(2)}\) as subsets of this field, with no trace or integrality hypothesis supplied by the caller. **localized_integer_order** constructs the additive and multiplicative closure for that localized ring.

**Arithmetic series.** [DyadicGammaDistribution69](Reimann/DyadicGammaDistribution69.lean) proves **representative_product**, **gamma_row_refines**, **group_row_bernoulli**, and **level_one_marks**. At exponent \(h\bmod 2^a\), the coefficient is indexed by \(5^{-h}\bmod 2^{a+2}\) in \(1+4\mathbb Z_2\). [DyadicMahler69](Reimann/DyadicMahler69.lean) constructs **series** from those coherent rows by expanding \(X=1+T\), using **SignedTaylor.taylorAt_stable** and **SignedTaylorScalar.coefficient_at_level**. At level \(a=4\) the integer coefficients in degrees 0 through 3 are \(4,22,225,1269\). Their stable residues modulo eight are \(4,6,1,5\). **canonical_half_row** and **DyadicArithmetic69.unhalved_row_552** establish the half-row and doubled-row comparisons unconditionally for this explicit series. **lattice_order_of_canonical_series** takes the principal ideal equality for that series and the monic characteristic quadratic as its only arithmetic premise. In Mizusawa's notation the normalization to transport is \(L_2(s,\psi)=2\Phi(5^s-1)\), with the actual \(\Gamma\)-action \(T=\gamma-1\). [Mizusawa, p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Sharifi, Remark 5.4.10 and Lemma 5.4.11](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

**Smallest coefficient comparison used by the count.** Write \(\Lambda=\mathbb Z_2[[T]]\), \(\mathfrak m=(2,T)\) and \(P=T^2+C_1T+C_0\). It suffices to prove that the image of the actual characteristic polynomial \(P\) belongs to the ideal generated by the constructed series in \(\Lambda/\mathfrak m^3\). Here \(\mathfrak m^3=(8,4T,2T^2,T^3)\). The series has class \(4+2T+T^2\). Every element of \(\mathfrak m\) annihilates that class, so its only multiples are zero and the class itself. Monicity excludes zero. **DyadicOneSided69.weighted_jet_iff_samples** proves that this precise containment is equivalent to **WeightOneSamples**, or \(C_0\equiv4\bmod8,\ C_1\equiv2\bmod4\). **lattice_order_of_weighted_jet** then supplies the lattice bijection at all \(a,r\in\mathbb N\). In the finer quotient \(\Lambda/(8,T^3)\), **forward_jet_iff** gives \(C_1\equiv6\bmod8\) as well. Full-series forward divisibility suffices directly. Reverse divisibility suffices if \(C_0,C_1\) are both even. The ideal comparisons in these sentences are field inputs for the actual \(P\). [DyadicOneSided69](Reimann/DyadicOneSided69.lean)

**The two ideals in the bottom field.** On \((\mathcal O_{E_0})_{(2)}\), **DyadicArithmetic69.prime_generated_by_two_and_root**, **primes_above_two** and **residue_fields** identify the two distinct ideals as \((2,w)\) and \((2,1-w)\), each with residue field \(\mathbb F_4\). They use **DyadicPrimeClassification69.same_residue_iff** for divisibility of a difference by two inside the ring. **DyadicPlaceAction69.odd_denominator_action** and **odd_denominator_stabilizer** give the action on the actual odd-denominator field elements: changing the sign of \(\sqrt{-23}\) exchanges the ideals, and changing the sign of \(\sqrt{-3}\) fixes each and induces residue Frobenius. **frobenius_on_e** sends \(\bar e\) to \(\bar e+1\). Identifying Mizusawa's group generator \(B\) as a lift of the prime-exchanging automorphism is a subsequent field obligation. [DyadicArithmetic69](Reimann/DyadicArithmetic69.lean) · [DyadicPrimeClassification69](Reimann/DyadicPrimeClassification69.lean) · [DyadicPlaceAction69](Reimann/DyadicPlaceAction69.lean)

**All finite depths of the actual localized integers.** For \(n\ge0\), **DyadicLocalizedCompletion69.level_eq_iff_two_power_difference** proves that two field elements have the same four residues exactly when their difference belongs to \(2^{n+1}(\mathcal O_{E_0})_{(2)}\). **DyadicLocalOperations69.level_add** and **level_mul** give addition and multiplication on those quotients. In **DyadicCompletedIntegers69**, **class_inverses**, **read_lower**, **completion_inverses** and **completed_order_at_two** identify the inverse limit of the residue classes of actual localized field elements with the four integral dyadic coordinates. The transition sends the class of \(z\) to the class of the same \(z\) at lower precision. **two_completed_factors** gives mutually inverse maps to two copies of \(\mathbb Z_2[e]\), \(e^2=e-1\), and verifies multiplication in both factors. This supplies the bottom-field completion previously reserved under **DyadicArithmetic69.completed_order_at_two**. Its checked name is **Reimann.DyadicCompletedIntegers69.completed_order_at_two**. [DyadicLocalizedCompletion69](Reimann/DyadicLocalizedCompletion69.lean) · [DyadicLocalOperations69](Reimann/DyadicLocalOperations69.lean) · [DyadicCompletedIntegers69](Reimann/DyadicCompletedIntegers69.lean)

**Galois action at the bottom field.** Every rational algebra endomorphism of \(E_0\) is one of the four independent radical sign changes. Each is an involution. **DyadicGalois69.all_rational_endomorphisms**, **distinct_actions**, **rational_end_involution**, and **full_prime_stabilizer** prove that the full stabilizer of either dyadic prime over \(\mathbb Q\) has order two. Its nonidentity element fixes \(\sqrt{-23}\) and negates \(\sqrt{-3}\), acting on \(\mathbb F_4\) by squaring. These statements have no weight parameter. [DyadicGalois69](Reimann/DyadicGalois69.lean)

**Verification for these field and normalization checkpoints.** All 331 breakpoints in the 17 modules introduced in this report passed on Lean **4.36.0**, Windows x86_64, commit **611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9**. This includes 226 named theorem proof terms, 80 definitions, five structures, three abbreviations and 17 whole-source checks. There are zero standalone executable guard checks in this count. Closed computations with **decide** are kernel proof terms. Each source prefix and the recorded imported-source fingerprints match the per-module **compat-4.36.0-Module.json** ledger. In particular, **DyadicCompletedIntegers69.classes_are_ideal_congruences**, **fieldPoint_sum**, **fieldPoint_product**, and **fieldPoint_dense** connect the residue-class completion directly to congruences modulo the powers of two, field operations and density. The last Galois theorem and whole-source breakpoint are **Reimann.DyadicGalois69.full_prime_stabilizer** and **DyadicGalois69.complete**. The combined **Reimann** target passed in 298 Lake jobs. The sibling **ReimannWindow** target passed in 30. Both toolchain files still pin **4.33.1**. These 331 checks contribute only a **4.36.0** result. [Completion ledger](compat-4.36.0-DyadicCompletedIntegers69.json) · [Finite ideal ledger](compat-4.36.0-DyadicOneSided69.json) · [Galois ledger](compat-4.36.0-DyadicGalois69.json)

**Report 5 starting point.** Round 3 above gives the newer local and Artin checkpoints. For \(a\ge0\) take \(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\), \(E_a=E_0 Q_a\), \(L=E_a(\mu_{2^\infty})\), \(U=\operatorname{Gal}(L/E_a)\), and \(M_r=(\mathbb Q_2/\mathbb Z_2)(-r)\). The local target at this breakpoint was the surjectivity of the actual restriction \(D_v\to U\) for each \(v\mid2\). One field proof is \(E_{a,v}\cap\mathbb Q_2(\mu_{2^\infty})=Q_{a,2}\) inside a common algebraic closure. In the unramified tower over \(k_\infty=kQ_\infty\), the decomposition subgroup in Mizusawa's notation is \(\langle A\rangle\). Its intersection with \(H=\langle A^2,B^2,C\rangle\) over \(L\) is \(\langle A^2\rangle\). Over \(L\), reciprocity must identify the everywhere-unramified quotient split at both places with \(X=\langle 2b,c\rangle\subset Y=\mathbb Z_2 b\oplus\mathbb Z_2 c\). With the forward generator \(\gamma\) of cyclotomic image 5, prove that the discrepancy \(B s_t B^{-1}s_t^{-1}\) at the second place maps to \((1-t)b\). The primitive of this discrepancy must work for every \(t\in U\). Use **DyadicPlaceProduct.strict_iff_conjugate_discrepancy** for the abstract equivalence. Continuous restriction, the Artin quotient, and the comparison on both places remain field obligations. [Mizusawa, pp. 117–119 and §4.2](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

For **positive odd** \(r\), identify the underlying finite abelian strict dual with \(X/(J^{2^a}-5^{-r2^a}I)Y\), where \(J\) is forward \(\gamma\)-action in the ordered basis \((b,c)\). This identification gives order \(2^{2a+1}\) once the actual Iwasawa coefficients satisfy **DyadicOrder.WeightOneSamples**. The dual Tate twist matters for an equivariant formulation. The index \([Y:X]=2\) comes from the two-place calculation. The normalization \(L_2(s,\psi)=2\Phi(5^s-1)\) comes from the analytic construction. For positive even \(r\), the checked local model instead forces \(f(2b)=0\) and takes \(f(c)\) in \(M_r[2]\). Verify Lean Proofs owns the general continuous class-character interface. Its tame invertibility hypothesis at 277 does not apply to the scalar \(-2\) here. [Mizusawa, p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Sharifi, Remark 5.4.10 and Lemma 5.4.11](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

### The two primes over 2 in the integral presentation

For the quadratic generators take \(e=(1+\sqrt{-q})/2\) and
\(w=(1+\sqrt{-d})/2\), with \(q\equiv3\pmod8\) and \(d\equiv7\pmod{16}\).
For the number-field application q and d are distinct primes. The Lean
coordinate statements accept any natural q,d with these congruences. The
base field of interest is \(E_0=\mathbb Q(\sqrt{-3},\sqrt{-23})\).
In the completed order with basis \(1,e,w,ew\), write an element as A+Bw
with A,B in the quadratic order for e. Reduction at the two primes is
explicit: it sends A+Bw to the residue of A or the residue of A+B in
\(\mathbb F_4\). Both maps are surjective. An ideal is prime and contains
2 exactly when it is one of these two kernels. The involution w↦1−w
exchanges them. These local calculations are independent of weight.

| Sources in `formal/Reimann` | Checked declarations |
|---|---|
| [DyadicSplitRoot](Reimann/DyadicSplitRoot.lean), [DyadicInert](Reimann/DyadicInert.lean) | `coherent_split_roots`, `split_roots_of_prime_residue` give two compatible roots of w²−w+(d+1)/4 with invertible difference. `unit_iff_nonzero_residue`, `residue_kernel`, `residue_field_inverse` prove the e-order has residue field of size four and maximal ideal generated by 2. |
| [DyadicPlaceAlgebra](Reimann/DyadicPlaceAlgebra.lean) | `evaluate_product`, `interpolate_evaluations`, `evaluations_interpolate`, `evaluate_add`, `evaluate_one`, `conjugate_exchanges_factors`, `two_dyadic_factors` give the two integral factors and both inverse maps. |
| [DyadicFiberPrimes](Reimann/DyadicFiberPrimes.lean), [DyadicFiberDescent](Reimann/DyadicFiberDescent.lean), [DyadicIntegralPlaces](Reimann/DyadicIntegralPlaces.lean) | `prime_iff_coordinate_kernel` in each of the first two namespaces, then `reduction_surjective`, `equal_reductions_differ_by_double`, `primes_above_two`, `two_distinct_kernels_3_23`. The prime classification applies to the coherent integral presentation itself. |
| [DyadicTraceOrder](Reimann/DyadicTraceOrder.lean) | `trace_formula`, `pairings_tensor`, `parameter_discriminant`, `trace_integral_iff`, `trace_order_3_23`. The trace determinant is \((qd)^2\), or 4761 at (3,23). At any denominator \(2^n\), integral pairings with the four basis elements force each coefficient to be integral at 2. |
| [DyadicRealLayer](Reimann/DyadicRealLayer.lean), [DyadicCyclotomicImage](Reimann/DyadicCyclotomicImage.lean) | `real_cyclotomic_root`, `monic_degree`, `monic_coefficients_eval`, `low_coefficients_even`, `constant_mod_four`, `prime_pullback`. At a≥1 the real-layer polynomial is monic of degree \(2^a\), constant 2 mod 4 and all lower coefficients even. An element with expansion r+xv belongs to a fiber prime exactly when r does. `layer_generator_period`, `signed_layer_class`, `signed_image_iff` classify the finite signed cyclotomic units, with the exact exponent period at every precision. |
| [DyadicPlaceProduct](Reimann/DyadicPlaceProduct.lean) | `factor_iff_covers_image` and `localProduct` construct the previously required KD factorization as soon as the first-place image equals the global quotient image. `strict_iff_conjugate_discrepancy` and `ambient_discrepancy` identify the obstruction using the commutator with a place-swapping element in the ambient group. |
| [DyadicBasisComparison](Reimann/DyadicBasisComparison.lean) | `evaluation_comparison`, `integer_image`, `same_coset_iff`, `sixteen_cosets`, `basis_comparison_277`. The raw basis used at 277 generates an index-16 sublattice of the integral dyadic basis. The change X=2e−1, Y=2w−1 is invertible modulo every positive power of 277. The exact image in integral coordinates has even e,w coefficients and ew coefficient divisible by 4. |

**Next field declaration.** Construct the map from the actual dyadic
completion of the order generated by e,w to the coordinate presentation,
identifying its basis trace with the field trace. Transport the two kernel
maps to \(\mathcal O_{E_0}\). For \(E_a=E_0Q_a\), identify the integral
real cyclotomic generator and its order after adjoining it to each factor.
Use the resulting full local image in \(U=\mathrm{Gal}(L/E_a)\) to instantiate
`DyadicPlaceProduct.localProduct`. The remaining class-field input is the
continuous map from the kernel over L to X, sending the actual commutator
\([B,s_t]\) to \((1-t)b\). The checked w-involution specifies the swap on
the base presentation. Its prescribed lift B in Mizusawa's tower still
requires arithmetic identification. With these inputs the strict dual at
positive odd r is \(X/D_aY\). The even-weight comparison uses +1 for the
action of σ on the coefficients.

### Independent calculations for the polynomial of Q(√−69)

The zero-weight calculation uses ψ of conductor 69 for the real quadratic
field Q(√69). The sign correction at zero gives the two odd characters of
discriminants −276 and −552. In [DyadicZeroValues](Reimann/DyadicZeroValues.lean),
`support_on_units`, `characters_multiplicative`, `primitive_276` and
`primitive_552` check their defining finite data. `moments_276` and
`moments_552` give signed first moments −2208 and −4416. `half_values`
gives 4 at both signs from the two depleted Bernoulli expressions at zero.
Here zero is the analytic interpolation argument. The strict-group claims
in this project continue to require r>0.

In [DyadicClass69](Reimann/DyadicClass69.lean), `membership_iff`,
`reduced_forms_276`, `reduced_forms_552`, and `two_form_counts` check
all reduced primitive positive binary quadratic forms of those discriminants,
eight for each. `samples_of_zero_and_minus_two` constructs the earlier
`WeightOneSamples` predicate from P(0)≡P(−2)≡4 mod 8.
`samples_of_two_layer_counts` gives the alternative algebraic route if
class-group control identifies the bottom and first layer orders with
\(2\cdot 2^{v_2(P(0))}=8\) and
\(2\cdot 2^{v_2(P(0))+v_2(P(-2))}=32\), with the indicated odd parts.
The form–ideal correspondence, the quartic class number formula including
its unit index, and the control theorem are inputs on this route.
Mizusawa's p. 134 example independently reports the polynomial modulo 4 for
this family. `mizusawa_example_69` verifies its numerical hypotheses for
(3,23), including 7²≡3 mod 23. The bottom field for this calculation is
\(k=\mathbb Q(\sqrt{-69})\), whose class group has invariants 2 and 4.
[Mizusawa, pp. 119 and 134](https://www.numdam.org/item/10.5802/jtnb.707.pdf) ·
[Sharifi, Remark 3.2.12](https://math.ucla.edu/~sharifi/notes/iwasawa-ch03.html) ·
[LMFDB, field 2.0.276.1](https://www.lmfdb.org/NumberField/2.0.276.1)

**The shorter analytic input.** At \(552=69\cdot8\) take the quotient of
the cyclotomic group generated by γ=5 of order two. In the basis
\(([1],[\gamma])\) the inverse-generator Stickelberger row is exactly
\((8,0)\). The numerator sums by coset are −4416 and 0, and both zeroth
moments vanish. Divide the integral row by two **before** reducing modulo 8.
This gives \((4,0)\) in \(R=(\mathbb Z/8)[C_2]\). In this quotient
inversion fixes each group element. The generator convention must still
agree with the actual tower. The scalar character in the row is
\(\psi\omega^{-1}\), with the global minus sign from the Stickelberger
specialization. Sharifi gives the finite formula and its equality with the
interpolating series. Mizusawa gives the half-normalization and the equality
of principal ideals. [Sharifi, Remark 5.4.10 and Lemma 5.4.11](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html) ·
[Mizusawa, p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

With \(T=[\gamma]-1\), the projected row of \(P=T^2+C_1T+C_0\) is
\((C_0-C_1+2, C_1-2)\) modulo 8. The exact finite statement needed is
that this row and \((4,0)\) generate the same ideal of R.
\(P(0)\equiv P(-2)\equiv4\pmod8\) then implies the coefficient residues
and the original weight-one congruences. The two ideal inclusions suffice
with unrestricted multipliers.
[DyadicStickelberger69](Reimann/DyadicStickelberger69.lean) checks
`signed_row_exact`, `half_row_exact`, `polynomial_row_coordinates`,
`signed_evaluations_of_ideal`, `samples_of_projected_ideal`, and
`lattice_order_of_projected_ideal`.

[DyadicSeriesProjection](Reimann/DyadicSeriesProjection.lean) constructs
the projection on arbitrary coherent Z₂-valued power series and proves
that it preserves the Cauchy product. In R the element T satisfies
T²=−2T, T³=4T and T⁴=0. Thus only the first four coefficients matter.
The named steps are `all_truncations_stabilize`, `evaluate_convolution`,
`evaluate_quadratic`, `project_mutual_divisibility` and
`projected_ideal_of_full_series`. They transport a full-series ideal
identity to `ProjectedIdeal69` with the same coefficient conventions.
The remaining source theorem must build the true series Φ for ψ,
identify its projected Stickelberger row with the finite calculation at
552 and provide the two multipliers realizing (P)=(Φ) for the true
characteristic polynomial of \(k_\infty/k\). The map between formal
series and the finite quotient is now checked.

**Latest analytic endpoint.** [DyadicHalfPrecision](Reimann/DyadicHalfPrecision.lean)
checks `double_word_lift_independent`, `double_word_injective`,
`all_truncations_double` and `half_row_iff_unhalved`. In (Z/16)[C₂]
the terms \(2T^j\) vanish at every \(j\ge4\). The unhalved row (8,0) mod 16
therefore recovers (4,0) mod 8 uniquely. The theorem
`Reimann.DyadicHalfPrecision.lattice_order_of_unhalved` constructs the
bijection with \(\operatorname{Fin}(2^{2a+1})\) for every a≥0.
Its exact hypotheses are an actual choice of coherent coefficients C₀,C₁,
a series Φ, multipliers witnessing (P)=(Φ) by convolution, and the single
identity `partialDouble phi 4 = literalRow16`. The intended next arithmetic
declaration, `DyadicArithmetic69.unhalved_row_552`, should prove this last
identity for the genuine normalized series using the finite Stickelberger
projection formula. The local counterpart,
`DyadicArithmetic69.completed_order_at_two`, should identify the two
coordinate maps above with those on the completion of the global order.
These two proposed declarations have no checked field construction yet.

**Replay and compiler.** The 16 modules in this continuation passed
**301 breakpoints** on Lean 4.36.0, commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`: 193 named theorem proof
terms, 79 definitions, 9 abbreviations, 4 structures and 16 whole-source
checks. The count contains no executable `#guard` checks. Every accepted
prefix hash and imported local-source hash matched the final sources.
The combined `Reimann` build passed (174 Lake jobs). The analytical
endpoint passed through `DyadicHalfPrecision.complete`; the coordinate
comparison passed through `DyadicBasisComparison.complete`. Replay each
from `formal` with `python checkpoint.py --compat-version 4.36.0 --lean
C:/Users/natha/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean.exe
--module DyadicHalfPrecision` (replace the module name for other entries).
The combined check is `elan run leanprover/lean4:v4.36.0 lake --rehash build`.
Both project toolchain files pin 4.33.1. The compatibility ledgers for this
continuation use filenames `compat-4.36.0-<module>.json`.

The other signed branch works with (11,263) and a different row. Its
conditional product-valuation spectrum (8 and all integers ≥11) and
modulus-256 candidate check belong to that owner. The factors above are
for (3,23). The project coordinator collects messages in
[COORDINATION.md](COORDINATION.md).

## Dyadic handoff to Continue Conversation — the two places above 2

**First missing specialization from the checked base moments.** For
`q=3, d=23`, construct `Reimann.DyadicOrder.WeightOneSamples c0 c1` for
the coefficients of the characteristic polynomial of the actual unramified
Iwasawa module of `k∞ = Q(√−69) Q∞`. The parameter is `T=γ−1`, with γ
acting by 5 on the real cyclotomic tower and by left conjugation on the
module. The characteristic polynomial is `P(T)=T²+C₁T+C₀`.
At weight one the two arguments are −4/5 and −6/5. The character ψ has
conductor 69 and corresponds to the **real** field Q(√69). The second
character is ψχ₈, with χ₈(5)=−1 and conductor of the product 552.
The primitive signed second moments are 3312 and 680064, both zeroth and
first moments vanish, and the Euler factors at 2 are 3 and 1.
The resulting half-values are −36 and −308. Independently, the formal
module derives them from the common-modulus 1104 theorem `Dyadic.values_3_23`.

Mizusawa gives `(P)=(Φ)` in Z₂[[T]] and `L₂(s,ψ)=2Φ(5ˢ−1)`.
At s=−1 use finite twists with ρ(5)=ζ⁻¹ for ζ=1,−1. The correction
ω⁻² is trivial. The desired Lean input consists of two congruences modulo 8
between P at the indicated arguments and the half-values multiplied by odd
units. The units are the two evaluations of P/Φ and may differ. This
identification fixes the orientation of γ and the factor 2 in the analytic
normalization. See Mizusawa, *J. Théor. Nombres Bordeaux* 22 (2010),
pp. 117–119, Theorem 2.2 and §4.2, pp. 126–131, and Sharifi, *Iwasawa Theory*,
Propositions 5.3.15 and 5.4.3.
[Mizusawa](https://www.numdam.org/item/10.5802/jtnb.707.pdf) ·
[Sharifi](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

**First missing field map for the strict order.** Let a≥0 and let q,d be
distinct primes with q≡3 (mod 8) and d≡7 (mod 16). Put
\(Q_a=\mathbb Q(\zeta_{2^{a+2}})^+\), Eₐ=Qₐ(√−q,√−d), k=Q(√−qd),
k∞=kQ∞, and \(L=E_a(\mu_{2^\infty})=Q_\infty(i,\sqrt q,\sqrt d)\). For each integer r≥1 take
M=Q₂/Z₂(−r). The desired map restricts classes from
\(\ker(H^1(G_{E_a,S},M)\to\bigoplus_{v\mid2}H^1(E_{a,v},M))\) to continuous
equivariant characters of X. Here S consists of **both** primes over 2. Identify X with
the abelian pro-2 group over L classifying extensions unramified everywhere
and split at both primes. In the notation A,B,C of the tower presentation,
the group over L is H=⟨A²,B²,C⟩ and the decomposition subgroup over k∞ is
⟨A⟩. Quotienting gives Y=Z₂b⊕Z₂c and X=⟨2b,c⟩⊂Y with b,c the images of B,C.
Verify these identifications and the action on this same lattice. In the
ordered basis (b,c) the required columns are γb=b+c and
γc=−C₀b+(1−C₁)c. For σ, restriction to k∞ is conjugation over Q∞.
At each finite layer the class times its conjugate is an extended norm,
and the odd class number of Qⱼ gives inversion on the 2-class group.
The passage to its torsion-free inverse-limit quotient supplies σ=−1 on Y.

In Eₐ, −d is a square locally at 2 and √−q gives the unramified quadratic
extension, while Qₐ at 2 is totally ramified. At either prime prove the
surjection onto U=Gal(L/Eₐ)=⟨σ⟩×⟨g⟩ with cyclotomic images −1 and
5^{2^a}, and identify B as interchanging the primes. For a first-place
lift s_t, the second-place lift B s_t B⁻¹ has quotient B s_t B⁻¹ s_t⁻¹
with image (1−t)b. Thus one global lift is locally trivial at both places
precisely when f((1−t)b)=(1−t)y for a single y and all t∈U. Construct this
with the actual continuous restriction/inflation maps and the quotient topology.
Equality on the topological generators σ,g must be transported to equality
of continuous cocycles on U. Then identify the finite character group with
the Pontryagin dual of the displayed lattice quotient. The abstract lifting and coordinate declarations
below can then be applied. These obligations belong to this dyadic field.
Verify Lean Proofs owns the general class-character interface. Continue
Conversation owns the circular units at 277.

For **odd** r the target for the strict dual is X/DₐY, where
Dₐ=γ^{2^a}−5^{−r2^a}I. The relation includes Dₐ applied to b as well as
to c. The index [Y:X]=2 accounts for the divisor two in the order. It has
a separate origin from the half-value in the interpolation formula.
For **even** r the involution acts as +1 on M and the character lands in
M[2]. The two local conditions force f(2b)=0 and allow either value for
f(c). These local assertions apply across the stated prime family. The
specific odd-weight count 2^{2a+1} below uses the moments for (3,23).

### Checked declarations and restart point

All nine modules below passed their whole-source `.complete` breakpoints on
Lean **4.36.0**, Windows x86_64, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
The aggregate `Reimann` build passed (110 Lake jobs), as did the sibling
`ReimannWindow.DyadicChecks` target (13 jobs). The nine new per-module
ledgers contain **155 breakpoints**: 100 named theorems, 41 definitions,
five structures and nine whole-source checks. All 100 theorems have proof
terms. There are no executable `#guard` checks in that count. Both
4.33.1 toolchain files retain their pin. This handoff adds results only for
4.36.0. The earlier pinned ledger is `checkpoint-state.json`.

The following names are relative to the `Reimann` namespace. Each linked
file contains the exact signatures. Each `compat-4.36.0-<Module>.json`
contains the ordered source lines, prefix hashes, recorded compiler and
theorem axiom reports. The live listing uses `python checkpoint.py --module
<Module> --list` from this directory.

| Source | Named breakpoints and the claims to reuse |
|---|---|
| [DyadicMoments](Reimann/DyadicMoments.lean) | `normalized_real_moments_3_23`, `sample_is_companion_determinant`, `coefficient_residues_of_mizusawa_samples`. The two half-moments and the unit congruences force C₀≡4 mod 8 and C₁≡2 mod 4. The primitive-conductor cross-checks in the sibling package are `conductor69Moments`, `conductor552Moments`, `normalized69`, and `normalized552`. |
| [DyadicLift](Reimann/DyadicLift.lean) | `extend_product`, `extend_cocycle`, `normalized_unique`, `strict_lift_iff`, `continuous_quotient_descent`. If the global group is KD with K normal, the first decomposition subgroup D maps onto the quotient, K acts trivially on M, and the equivariant character f kills K∩D, then c(kd)=f(k) is the unique lift vanishing on D. At the second subgroup D′, local triviality is existence of b with f(k)=(kd)b−b for all kd∈D′. Continuity follows once K×D→KD is shown to be a quotient map and f is continuous. |
| [DyadicLocal](Reimann/DyadicLocal.lean) | `difference_on_two_lifts`, `commutator_projects_to_difference`, `common_inflation_iff`, `difference_columns_in_X`, `primitive_iff_extension`, `odd_two_places_iff_annihilates_image`, `restriction_kernel_coordinates`, `restriction_kernel_equivariant`. At odd weight the two-generator test is precisely annihilation of DₐY. Denominator 2n suffices for a primitive of a character given at denominator n. The two characters vanishing on X both satisfy equivariance. |
| [DyadicEven](Reimann/DyadicEven.lean) | `involution_forces_half`, `cyclotomic_common_primitive`, `even_local_conditions_iff`, `even_solution_bijection`, `discrepancy_by_layer`. With the even-weight involution the coordinate solutions (0,f(c)) are in bijection with `Fin 2` for every a≥0 and r>0. The discrepancy at g is f(c) at a=0 and vanishes at each higher layer. |
| [DyadicLattice](Reimann/DyadicLattice.lean) | `odd_scalar_inverse`, `odd_det_surjective`, `scaled_matrix_image`, `normalized_image`. Compatible finite inverses give surjectivity of an odd-determinant matrix on the full inverse limit Y=Z₂². |
| [DyadicBottom](Reimann/DyadicBottom.lean) | `coherent_bottom_image`, `coherent_bottom_classes`, `coherent_bottom_quotient_of_residues`. At a=0, D₀Y=4Z₂b⊕Z₂c, and (2x,y)↦x mod 2 classifies the quotient in X. |
| [DyadicLayers](Reimann/DyadicLayers.lean) | `first_square_image`, `positive_normalization`, `positive_layer_image_of_residues`. Assuming the two coefficient residues and s≡1 mod 4, D₁Y=4Y and DₐY=2^{a+1}Y for all a≥1. |
| [DyadicQuotient](Reimann/DyadicQuotient.lean) | `residue_eq_iff_multiple`, `sameCoset_iff_residuePair`, `residuePair_section`, `residuePair_add`, `quotient_classification`, `quotient_cardinality`. Reduction in the X-basis gives the two cyclic factors of orders 2^a and 2^{a+1} at a≥1, with addition and both inverse identities checked. |
| [DyadicOrder](Reimann/DyadicOrder.lean) | `WeightOneSamples`, `five_power_mul_inverse`, `inverse_weight_mod_four`, `moment_coefficient_bits`, `positive_coset_of_samples`, `lattice_order_of_weight_one_samples`. The last theorem constructs a bijection from X/DₐY to `Fin (2^(2*a+1))` at **every** a≥0 given the two field-specialization congruences. It uses the coherent scalar s=5⁻ʳ. Its algebra allows every natural r. The application to the arithmetic strict dual here is for positive odd r. |

**Last passing endpoint:** `DyadicOrder.lattice_order_of_weight_one_samples`,
then `DyadicOrder.complete`. Replay from `formal` with
`python checkpoint.py --lean C:/Users/natha/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean.exe --compat-version 4.36.0 --module DyadicOrder`
and `elan run leanprover/lean4:v4.36.0 lake --rehash build`.
The paper field constructions in [Strict Dyadic Invariant Factors](../Strict_Dyadic_Invariant_Factors.md)
§§1–2 remain to be supplied. The next analytic declaration should construct
`WeightOneSamples` from the actual tower polynomial for −69. The next local
declaration should construct `DyadicLift.LocalProduct` with the true kernel
of restriction to L and the image of the first dyadic decomposition group,
and identify the second subgroup with the conjugate place described above.

## Finite Stickelberger coefficients and multiplication for the conductor 2893

**All-level analytic construction.** The coefficient formula below extends to every \(D=2^{n+2}\). In `SignedTowerMeasure`, the integral moments obey binary refinement and the paired numerator equals \(2D\cdot2893\) times its normalized coefficient. `SignedGammaTower.sibling_fibres` identifies the two exponents over each inverse-generator class. `SignedTowerRows.normalized_tower` and `SignedTaylorScalar.coefficient` then construct the distribution and its power series \(F\) in \(T=X-1\). The specialization of \(F\) at order 64 is the certified row, coefficient by coefficient, by `SignedCanonicalProjection.arithmetic_projection`. The specialization respects the full Cauchy product by `SignedSeriesMap.evaluate_convolution`. In the order-64 ring modulo 64, \((X-1)^{224}=0\), and the coefficient row of \((X-1)^{223}\) has every entry equal to 32.

**Analytic preparation.** `SignedAnalyticDegree.mu_zero_lambda_two` proves that the first two coefficients of \(F\) are even and the third is odd. `SignedQuadraticLift.lift_matches` lifts a quadratic and cofactor from modulus \(m\) to \(2m\) with all previous digits preserved. `SignedAnalyticPreparation.prepared` uses these lifts at every precision to construct \(Q=T^2+C_1T+C_0\) and \(U\) with \(F=QU\). The two coefficients of \(Q\) are even and the constant coefficient of \(U\) is odd. `SignedSeriesUnit.two_sided_inverse` gives a two-sided formal inverse to \(U\). The only uniqueness claim needed for the six-bit coefficients is the earlier finite enumeration of the 1,024 even pairs.

The even character \(\psi\) is the product of the quadratic characters at 11 and 263. Its conductor is \(11\cdot263=2893\). The imaginary quadratic tower in the comparison theorem starts at \(k=\mathbb Q(\sqrt{-2893})\). The even Dirichlet character belongs to the real field \(\mathbb Q(\sqrt{2893})\). Take the cyclotomic generator 5 and set \(X=1+T\). The versioned ledgers use Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The named checkpoints and aggregate replays for the analytic continuation are recorded below by compiler.

For \(D=64,256\), put \(t_j=5^{-j}\bmod D\), \(0\le j<D/4\). The finite coefficients are
\[
c_j=-\frac{1}{2893}\sum_{h=0}^{2892}h\,\psi(t_j+Dh),\qquad H_D(X)=\sum_j c_jX^j .
\]
The inverse exponent comes from the action in the finite Stickelberger projection. Pair \(a=t_j+Dh\) with \(2893D-a\). The character is even and the mod-four sign changes. Their contribution to the negative weighted numerator is \((2893D-2a)\psi(a)\). The unweighted sum in the fibre vanishes, leaving \(-2D\sum h\psi(a)\). This explains the normalization by \(2D\cdot2893\) before taking residues. The level-256 group has order 64. The two signs at weight three specialize \(X\) to \(125^{-1}\) and \(-125^{-1}\). [Sharifi, Ch. 5, Remark 5.4.10, Lemma 5.4.11, and Proposition 5.4.12](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

**Field comparison still required.** For \(k=\mathbf Q(\sqrt{-2893})\), construct the unramified Iwasawa module \(X(k_\infty)\), its action by the forward generator \(\gamma=5\), and \(P(T)=\det((1+T)I-\gamma)\) on its rationalization. Identify the explicit inverse-power, half-normalized distribution defining \(F\) with the Stickelberger series in the convention \(L_2(s,\psi)=2\Phi(5^s-1)\), up to a unit if appropriate. Transport Mizusawa's equality \((P)=(\Phi)\) to this realization of \(\mathbb Z_2[[T]]\). The forward ideal inclusion supplies a series \(W\) with \(F=PW\). For distinguished quadratic \(P\), `SignedArithmeticProjection.coefficients_of_analytic_factor` applies directly to this equality. The finite projection and the explicit analytic factor are constructed in Lean. Strict-group orders require the separate local reciprocity and lattice comparisons. [Mizusawa, pp. 117–119](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

The common-prime criterion `SignedProduct.common_odd_divisor_iff` holds for fixed integer representatives, all integers \(a\), and every odd divisor. An odd divisor of both cleared signed samples is exactly an odd divisor of both \(C_1-2\) and \(1+(C_0-1)a^2\). Different integral lifts of dyadic coefficients can have different odd factors. Under `WeightThree`, `product_valuation_spectrum` proves that 8 and every integer at least 11 occur as finite product valuations at positive odd weights. To deduce order \(2^{n+2a-3}\) at layer \(a\ge1\) from product valuation \(n\), `order_from_product` requires the displayed Smith exponents and strict-group cardinality.

**Signed product over the dyadic integers.** For the prepared coefficients and \(a=5^r\), put \(N_s=(s-a)^2+C_1a(s-a)+C_0a^2\) for \(s=1,-1\). Then \(N_s=a^2Q(s/a-1)\). The finite valuation \(v_2(N_+N_-)=n\) means that the low \(n+1\) bits of the coherent product are exactly \(2^n\). `SignedAdicProduct.transfer` identifies this test in both directions for any coefficient representatives at the required precision. `SignedAdicProduct.product_valuation_spectrum` proves
\[
  (\exists r\ge1,\ r\ {\rm odd},\ v_2(N_+N_-)=n)\quad\Longleftrightarrow\quad n=8\ \text{or}\ n\ge11
\]
from the two six-bit coefficient words. This statement concerns finite valuations and allows the precision of the representatives to depend on \(n\). The odd-prime criterion below still applies only after fixing integer representatives.

**Quadratic factors.** `SignedArithmeticProjection.analytic_mutual_divisibility` gives \(F=QU\), an explicit cofactor \(U\) and a two-sided inverse \(V\), with \(Q=VF\). `analytic_coefficient_bits` gives \(C_0\equiv40\) and \(C_1\equiv18\pmod{64}\). `analytic_linear_factors` provides coherent \(R,S\) with \(Q(x)=(x-R)(x-S)\) for every \(x\in\mathbb Z_2\), and `analytic_labelled_roots` verifies two distinct zeros with \(R\equiv4,\ S\equiv2\pmod8\). In Mizusawa’s example, the pair \(11,263\) falls in the square-residue branch because \(96^2\equiv11\bmod263\). His reported polynomial modulo 4 agrees with the reduction of this analytic quadratic. [Mizusawa, p. 134](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

**Versioned replay for the analytic continuation.** The 18 modules from `SignedTowerMeasure` through `SignedArithmeticProjection` contain 304 named breakpoints and 18 complete-source checks on Lean 4.36.0 (`611c117b`). The combined checkout target passed in 290 Lake jobs on that compiler. A clean signed aggregate containing the final arithmetic endpoint and its 47 transitive source files also passed Lean 4.33.1 (`819816b2`). The final named theorem `SignedArithmeticProjection.analytic_product_valuation_spectrum` applies the valuation equivalence to the prepared coefficients without a field-comparison hypothesis. On 4.33.1, all 104 breakpoints across seven selected modules passed, including the final named theorem and both product-module completions. Individual compiler ledgers identify the exact prefixes checked on each version.

### Common arithmetic normalization and the remaining field comparison

Use the forward generator \(\gamma=5\) and \(X=\gamma=1+T\). In the row of order \(2^n\), \(D=2^{n+2}\), the arithmetic representative \(t\) satisfies \(5^j t\equiv1\pmod D\). Put \(m=69\) or \(2893\), \(M=Dm\), and \(a=t+Dk\). For a signed character \(g\), the two numerators use the weights \(-a\,g(a)\) and \((M-2a)g(a)\), with both \(a\) and \(M-a\) included in each sum. Under \(a\le M\), \(g(a)=f(k)\), \(g(M-a)=-g(a)\), \(\sum_{k<m}f(k)=0\), and \(-\sum_{k<m}k f(k)=mc\), the raw numerator is \(2Mc\) and the centered Bernoulli numerator is \(4Mc\). The two halves encode the same integral coefficient. `SignedBernoulliPairing.fibre_normalization` is the generic proof. Both concrete adapters `SignedCommonNormalization.gamma_normalization_69` and `gamma_normalization_2893` use the actual project characters, at every inverse representative. `raw_fibre_eq_stickelberger_2893` and `literal_fibre_eq_bernoulli_69` compare the generic expressions to the earlier literal sums. [Sharifi, Ch. 5, Remark 5.4.10](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html)

In the order-four quotient at \(D=16\), exponent one tests \(t=13\) for inverse orientation and \(t=5\) for forward orientation. The corresponding coefficients are \(-1,1\) at 69 and \(2,-18\) at 2893. Order two cannot distinguish the choices. `SignedOrientationWitness.first_distinguishing_bits` detects the difference modulo 4 and modulo 8, respectively. This fixes the sign convention for comparing literal distributions. Identifying the Galois action or an ideal requires its own construction.

For odd \(m\), \(D=2^d\), and \(s=1,2\) for the raw and centered conventions, two numerators of the form \(2^{d+s}mc\) agree modulo \(2^{p+d+s}\) precisely when their normalized coefficients agree modulo \(2^p\). `SignedNormalizationPrecision.residues_of_numerator_difference` also permits a common additive offset. `precision_sharp` provides integer witnesses for the loss of one bit if only \(p+d+s-1\) numerator bits are retained, for \(p\ge1\). At \(m=2893,D=256,p=6\), the exact numerator moduli are \(32768\) raw and \(65536\) centered. These are ordinary integer numerator comparisons made before division.

**Field proof obligation at a single finite level.** Construct the actual Iwasawa module over \(k=\mathbb Q(\sqrt{-2893})\), the forward action of \(\gamma=5\), and its distinguished monic \(P=T^2+p_1T+p_0\) with even coefficients. Realize the series \(\Phi\) of Mizusawa in the project's scalar model. Supply \(U\) such that \(\Phi=PU\) and at every \(j\in\mathbb Z/64\) show that \(2\cdot256\cdot2893\) times the least six-bit representative of the \(j\)th coefficient of the cyclic projection of \(\Phi\) agrees modulo \(32768\) with the literal raw sum in the fibre \(5^{-j}\bmod256\). The centered Bernoulli version compares \(4\cdot256\cdot2893\) times that representative modulo \(65536\). Proving the full equality of the field series with the explicit analytic series would also supply the row comparison. Mizusawa states the principal-ideal equality and half-normalization for the field-theoretic series. The conductor-69 route only requires the weighted monic jet from its own handoff. [Mizusawa, pp. 117–119](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

**Checked finite and all-level interfaces.** `SignedNormalizationComparison.level256_numerators_iff` and `projected_row_of_raw256` link the two integer numerator moduli to the actual 2893 row. `characteristic_bits_at_256` gives \((p_0,p_1)=(40,18)\bmod64\) directly from the 64 congruences, evenness and one field ideal inclusion. For the separate goal of identifying whole power series, `series_eq_of_numerator_comparisons` assumes compatible integral candidate rows and agreement at each requested coefficient precision on a whole row at arbitrarily deep levels. Its actual specializations are `series_eq_2893_of_raw_rows` and `series_eq_69_of_literal_rows`. These formulas establish sufficient finite and cofinal tests. The project still needs the field evidence specified above. The 4.36.0 checkout build checked the updated aggregate in 350 jobs.

**Round 3 compiler ledgers.** Across the five common-normalization modules, all 63 named breakpoints and five complete-source checks passed on both Lean 4.33.1 (`819816b2`) and 4.36.0 (`611c117b`), including `SignedNormalizationComparison.characteristic_bits_at_256`. The same focused aggregate with 57 local source modules passed in 60 and 118 Lake jobs respectively.

Continue Agent Notes also reserves `SignedFieldGroupRing2893.projected_group_numerator` for the character-weighted sum in the group ring of the actual field automorphisms.
Its rank-two specialization uses `SignedLinearGammaPowers2893` for the compatible cube roots of the actual linear generator and `SignedAdicDistinguished2893` for the determinant and trace.

### Finite-layer test for the quadratic relation at conductor 2893

In the primary norm limit let \(b=(b_n)_n\), \(A=\gamma-1\), and \(y=A^2 b+c_1 A b+c_0 b\), where \(c_0,c_1\in\mathbb Z_2\). For a local class \(x=b_n\) killed by \(2^{k_n}\), put \(D_n x=\gamma_n(x)/x\). The coordinate of \(y\) is the finite group element

\[
 D_n(D_n x)\,(D_n x)^{c_1\bmod 2^{k_n}}\,x^{c_0\bmod 2^{k_n}}.
\]

`SignedFiniteAnnihilation2893.residual_coordinate` proves this identity in every primary class group. `ideal_from_local_powers` takes the prepared coefficients of the 2893 candidate, an integral norm-coherent \(b\), a rational basis \((1\otimes b,A(1\otimes b))\), and one \(s\) such that the displayed element has order dividing \(2^s\) for **all** \(n\). Its conclusion identifies the actual forward characteristic polynomial with an integral quadratic whose power-series ideal contains the native candidate. Each \(k_n\) exists by membership in the primary group. The outstanding field-specific constructions are the cyclic basis and the uniform bound. The scalar-to-power coordinate identity and rationalization of torsion apply to another primary tower with its own coefficients and action. Source `formal/Mathlib2893/Reimann2893/SignedFiniteAnnihilation2893.lean`, native Lean 4.36.0.

`rational_relation_iff_coordinates` proves that uniform boundedness of the residual orders is equivalent to vanishing of the quadratic relation after rationalization. For the reverse direction, `oneTensor_zero_iff` obtains a nonzero dyadic annihilator by localization and writes it as a unit times a power of two. This equivalence needs neither finite rank nor cyclicity.

### Forward field action and signed character sum at conductor 2893

Put \(k=\mathbb Q(\sqrt{-2893})\), \(D=2^{n+2}\), \(M=2893D\), and \(k_n=k(\zeta_D+\zeta_D^{-1})\). The finite forward action fixes the specified embedding of \(k\) and sends \(z+z^{-1}\) to \(z^5+z^{-5}\). `SignedFieldLayers2893.step_degree_two`, `SignedForwardPeriod2893.forward_period` and `SignedForwardGenerator2893.relative_generator` prove that each layer doubles in degree and that the relative automorphisms are exactly the powers \(\gamma_n^j\) with \(0\le j<2^n\), each occurring once. The last theorem takes a ring automorphism together with a proof that it fixes every embedded bottom-field element. `SignedCyclotomicEmbedding2893.image_generated` identifies the field image for any compatible roots and radical. These results use mathlib on Lean 4.36.0.

The coefficient of \(\gamma_n^j\) uses arithmetic units \(a\equiv\pm5^{-j}\pmod D\). Write \(\psi\) for the even quadratic character of conductor 2893 and \(\chi=\psi\omega^{-1}\) for the odd quadratic character of conductor \(4\cdot2893\). The full coefficient of the normalized candidate is

\[
  -\frac{1}{2M}\!
  \sum_{\substack{0\le a<M,\ (a,M)=1\\a\equiv\pm5^{-j}\ (D)}} a\,\chi(a).
\]

`SignedStickelbergerCandidate.unit_supported_sum`, `series2893_eq`, `raw_congruences_256` and `centered_congruences_256` prove the full-interval formula, agreement with the prepared analytic series and both comparisons for every \(j:\mathrm{Fin}\,64\). The raw modulus is 32768 and the centered modulus is 65536. These are proof terms with no arithmetic input about a class group. The order-four check `orientation_check` gives \((13,5)\mapsto(2,-18)\) at 2893 and \((-1,1)\) at 69. The two new core modules have 37 passing breakpoints on each of Lean 4.33.1 and 4.36.0. Their signed aggregate dependencies are recorded per release. The mathlib constructions use only 4.36.0, mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

**Algebraic and analytic ideal obligations.** In native \(\mathbb Z_2[[T]]\), `SignedNativeSeries2893.prepared_principal_ideal` identifies the ideals of the candidate and its explicitly prepared quadratic \(Q\), with no field assumptions. For the arithmetic polynomial take \(X=\varprojlim_n\operatorname{Cl}(k_n)[2^\infty]\) along relative ideal norms, \(V=\mathbb Q_2\otimes_{\mathbb Z_2}X\), \(A=\gamma-1\) on \(V\), and \(P_X=\det(T-A)\). The native determinant convention is `SignedRationalCharacteristic2893.determinant_convention`. Its quadratic shape needs finite dimension and \(\dim V=2\). To use the direct coefficient comparison supply integral even lower coefficients and \(\Theta\in(P_X)\). `SignedCyclicCriterion2893.ideal_from_generator` gives an alternative sufficient arithmetic input. Exhibit a basis \((b,Ab)\) of \(V\) and prove \(A^2b+q_1 Ab+q_0 b=0\) for the actual prepared coefficients of \(Q\). Checking more digits of the analytic sum does not supply that relation.

**Identification using the published theorems.** Mizusawa identifies the norm-limit module, the direction of the field automorphism and the forward determinant on p. 117, and gives the distinguished polynomial and \((P_X)=(\Phi)\), with \(2\Phi(5^s-1)=L_2(s,\psi)\), on pp. 117–119. Sharifi's Remark 5.4.10 gives the raw and centered finite projections of \(f_\psi\) at every level, with the inverse group element and leading minus sign in the displayed sum. Taking the generator \(u=5\), Theorem 5.4.13 gives \(f_\psi(5^s-1)=L_2(s,\psi)\). Thus the finite sums for \(2\Theta\) are exactly the projections of \(f_\psi\), and the normalized \(\Phi\) is \(\Theta\). Under these published results \((P_X)=(\Theta)\), and the computed residues \((40,18)\bmod64\) apply to \(P_X\). A Lean proof of this arithmetic inclusion must still instantiate the analytic identification and the field theorem, or establish the cyclic-generator relation. Kida's Theorem 1 gives \(\lambda=-1+1+2=2\) from the odd prime divisors 11 and 263. The finite torsion is of order two and disappears upon rationalization. [Mizusawa, pp. 117–119](https://www.numdam.org/item/10.5802/jtnb.707.pdf) · [Sharifi, §§5.4.8–5.4.13](https://math.ucla.edu/~sharifi/notes/iwasawa-ch05.html) · [Kida, Theorem 1 and the note on p. 91](https://www.jstage.jst.go.jp/article/tmj1949/31/1/31_1_91/_pdf/-char/en)

**Conductor 69.** The same inverse-generator projection has \(M=69D\), signed character of conductor 276 and native series `SignedNativeSeries2893.candidate69`. For a native monic quadratic, `conductor69_samples_of_native_membership` takes \(P\in(\Theta_{69})\) and returns `WeightOneSamples`. The existing `DyadicOneSided69.weighted_jet_iff_samples` allows its field owner to supply just the membership modulo \((2,T)^3\) in the project's weighted coefficient coordinates. The order-four values and the direction of that membership are specific to conductor 69.

### Passing declarations for the conductor-2893 factorization

**Two hypotheses suffice for the rank-two comparison.** The construction `SignedLinearGammaPowers2893.exists_cube_tower` raises the forward action to dyadic exponents \(3^{-j}\) and rationalizes it, giving invertible \(G_j\) with \(G_0=\gamma\) and \(G_{j+1}^3=G_j\). The inputs are the two-primary groups, their compatible maps and generator, and the finite-level period dividing \(2^n\). In any rank-two \(\mathbb Q_2\)-space, `SignedAdicDistinguished2893.distinguished_of_cube_roots` proves that \(\det((1+T)I-G_0)\) has integral even lower coefficients. The determinant has valuation zero because its valuation is indefinitely divisible by three. A negative trace valuation would likewise be indefinitely divisible by three by the two-dimensional trace-of-a-cube identity. Reduction of that identity modulo two then forces even trace. Thus integrality and parity follow from the dyadic action once rank two is established. This reduction applies also to the conductor-69 action. The arithmetic inputs left for the direct 2893 comparison are rank two for the actual norm limit and \(\Theta\in(P_X)\).

An independent executable check enumerated the full interval with the ordinary Jacobi algorithm for \((-11572/a)\) and reproduced all 64 integral coefficients in `SignedMeasure256.row`. At indices 0 through 3 the raw residues modulo 32768 were 12288, 19456, 15360 and 29184. The corresponding centered residues modulo 65536 were 24576, 38912, 30720 and 58368. This check is separate from the proof terms `raw_congruences_256` and `centered_congruences_256`.

In \(R=(\mathbb Z/64)[X]/(X^{64}-1)\), the explicit row \(H_{256}(X)\) generates the same ideal as \(X^2+16X+23\). With \(T=X-1\), this is \(T^2+18T+40\). The constant and linear coefficients are each determined modulo 64. The linear coefficient was previously determined only modulo 32. The row's quotient and cyclic inverse are the integer lists `SignedFiniteFactor.quotient` and `SignedFiniteFactor.inverse`. Their product is 1 in \(R\); multiplying the row by the inverse recovers the quadratic. Every distinguished degree-two divisor reduces to this same pair of coefficients. In particular, for every natural \(r\), the cleared difference \(N_+(r)-N_-(r)\) is \(32\bmod128\) for such a divisor.

The twelve modules below passed 203 named declarations and twelve complete-source checks on Lean 4.36.0. The shared `formal` Lake target passed in 166 jobs. The finite tables use kernel reduction, the algebraic identities have proof terms, and the versioned `compat-4.36.0-<module>.json` files record each checked prefix and its imported source digests. The Lean declarations give the exact hypotheses. Independently replay a module from `formal` with `python checkpoint.py --module <module> --lean <path-to-4.36.0-lean> --compat-version 4.36.0`.

| Module | Named proof to resume from | Content or hypothesis |
|---|---|---|
| DyadicEulerFactor | `normalized_euler_factors`, `no_descent_to_proper_divisor` | The primitive untwisted moments \(-3472\) and \(4771880864\) acquire factors 3 and 9 on removing the even residues. The character on units requires both conductor primes. |
| SignedMeasure | `coefficient_formula`, `normalized_coefficients` | All 16 coefficients at modulus 64 from the two integer moments. The signed evaluations are \(32,0\bmod64\). |
| SignedMeasure256 | `signed_coverage`, `mass_zero`, `row_coefficients` | The two signs of the inverse-generator powers cover every odd residue exactly once. Both weight-three evaluations agree with the independent Bernoulli calculation, \(160,128\bmod256\). |
| SignedProjection | `moment_refine`, `paired_normalization` | Refinement of the integral first moment under a periodicity and two zero-sum hypotheses. The paired raw numerator is \(2D m\) times the row entry for conductor \(m\). |
| SignedStickelberger | `raw_coefficient`, `normalized_coefficient`, `odd_lift_coverage` | The paired negative \(\psi\omega^{-1}\)-weighted first-power numerator divided by \(2\cdot256\cdot2893\) gives the actual indexed row entry. The field-level Galois action has to realize this finite construction. |
| SignedRowDescent | `level256_pushes_to_level64`, `first_odd_coefficient` | Order-64 cyclic coefficients project to the order-16 row, then to \([25,2,-1,-18]\) at order four. In \(T\) the last row is \(8-54T-55T^2-18T^3\), with first odd coefficient at degree two. |
| SignedPreparation | `cyclic_factor_remainder` | For even \(c_0,c_1\), ideal membership in \((Q(X-1),X^{64}-1,64)\) implies zero quadratic remainder. |
| SignedCoefficients | `finite_quadratic_test`, `coefficients_of_cyclic_factor`, `weight_three_of_cyclic_factor`, `signed_difference_mod128` | All 1,024 pairs are tested. Both coefficient residues, the earlier signed input, and the seventh bit of the difference follow. |
| SignedFiniteFactor | `ordinary_factor`, `quotient_unit`, `mutual_divisibility` | Explicit polynomial witnesses for both inclusions, with no field-interpolation hypothesis. |
| SignedProduct | `product_valuation_spectrum`, `order_from_product`, `common_odd_divisor_iff` | The odd-weight spectrum assumes `WeightThree`. The odd-divisor criterion is unconditional for fixed integer coefficients. |
| SignedRoots | `signed_factorization`, `valuation_from_near_factor`, `even_weight_pair` | For fixed integer coefficients satisfying `WeightThree`, the two compatible integral root lifts factor the signed numerator at every precision. Even-weight polynomial valuations are both 3. |
| SignedAdicRoots | `labelled_scalar_factorization` | For coherent 2-adic coefficients \(C_1=2b,C_0=4c\) with \(b=1,c=2\bmod4\), the same two roots, \(4,2\bmod8\), give an exact scalar factorization for all signed inputs. The companion root contributes a single factor of 2 to each signed sample. |

**Next field statement.** Construct the actual characteristic coefficients \(p_0,p_1\) and prove that they are even and that `SignedArithmeticProjection.analyticSeries = DyadicSeriesProjection.convolution (DyadicSeriesProjection.quadraticSeries p0 p1) W` for some series `W`. Exact divisibility in the order-64 row follows by `SignedArithmeticProjection.finite_factor_of_analytic_factor`. Applying the finite certificate then gives \(p_0\equiv40\) and \(p_1\equiv18\pmod{64}\).

## Signed dyadic polynomial handoff for Continue Mathematical Analysis

**The positive branch is untwisted \(\psi\). The negative branch is \(\psi\chi_8\).** For \(q=11,d=263\), write \(P(T)=T^2+C_1T+C_0\), \(u=5^{-r}\), and \(a_r=5^r\). The signed samples are \(P(u-1)\) and \(P(-u-1)\), in that order. Lean's `PairedSigns.positiveBranch` and `negativeBranch` compute the integer numerators \(N_\pm(r)=a_r^2P(\pm a_r^{-1}-1)\) for integer representatives of the coefficients. The common denominator \(a_r^2\) is odd.

At weight three the kernel evaluated both signed sums over all 11,572 odd residues modulo 23,144. After dividing by \(240\cdot23144\), the positive value is \(42{,}946{,}927{,}776\) and the negative value is \(7{,}186{,}575{,}033{,}984\). Their valuations are 5 and 7. At weight one the corresponding sums give \(-10{,}416,-85{,}584\), both of valuation 4. `Character2893.normalized_table` is a theorem proved by kernel reduction. `Character2893.valuation_factors` proves the exact valuations with odd integer witnesses.

**Input for the residue split.** `PairedSigns.WeightThree c0 c1` means precisely \(N_+(3)\equiv32\pmod{64}\) and \(N_-(3)\equiv0\pmod{64}\). These six bits force \(C_0\equiv40\pmod{64}\) and \(C_1\equiv18\pmod{32}\). In particular \(v_2(C_1-2)=4\). The signed difference identity is
\[
P(u-1)-P(-u-1)=2u(C_1-2),\qquad
N_+(r)-N_-(r)=2a_r(C_1-2).
\]
For every natural \(r\), `PairedSigns.signed_difference_valuation` proves the latter difference has exact valuation 5. This amounts to an explicit odd-factor witness and applies at even weights as well. The valuation statement is about the two evaluations of the same monic polynomial. The normalized special values can carry different odd interpolation units.

| Positive odd weight | \(N_+,N_-\pmod {64}\) | \(v_2(P(u-1)),v_2(P(-u-1))\) | Branch that can grow |
|---|---|---|---|
| \(r\equiv1\pmod8\) | \(16,48\) | \(4,4\) | Neither |
| \(r\equiv3\pmod8\) | \(32,0\) | \(5,\ \ge6\) | Negative, \(\psi\chi_8\) |
| \(r\equiv5\pmod8\) | \(48,16\) | \(4,4\) | Neither |
| \(r\equiv7\pmod8\) | \(0,32\) | \(\ge6,\ 5\) | Positive, \(\psi\) |

`PairedSigns.all_odd_weights` gives the residues even if a sample vanishes. `PairedOrders.signed_valuations` takes two finite exact valuations; `PairedOrders.companion_of_deep` only assumes divisibility by 64 on the large branch. For each fixed integer coefficient pair satisfying `WeightThree`, `PairedOrders.every_high_pair` realizes every finite value \(M\ge6\) in each indicated growing branch. At precision \(2^{4+k}\) there is one root class per sign, indexed by \(i=(r-1)/2\bmod 2^k\). `PairedSigns.paired_root_classes` proves that the two index classes coincide exactly for \(k=0,1\). They first split at precision 64, or weights modulo 8. `WeightClasses.exact_weight_class` identifies one odd weight class modulo \(2^{M-2}\) for exact valuation \(M\ge4\).

**Alternative field comparison via weight three.** The full-series divisibility obligation above now gives the weight-three predicate for every sufficiently precise lift of the field coefficients. The earlier interpolation route proceeds as follows.  For the actual \(2\)-adic Iwasawa coefficients, choose their residues at the precision in use. Supply the two weight-three unit comparisons in `PairedSigns.weight_three_of_interpolation_mod64` between the calculated Bernoulli values and the cleared signed numerators. Precision 64 suffices for the displayed branch table and the exact difference valuation. To transfer a statement about exact valuation \(M\), compatible representatives at precision \(2^{M+1}\) suffice; prove that they compare with the actual evaluations. For the layer order, identify the strict group with the lattice quotient, prove nonvanishing at the weights used, and identify its two Smith exponents as \(\min(\alpha,\beta)+a-2,\ \max(\alpha,\beta)+a-1\) for \(a\ge1\). Conditional on those identifications the order spectrum is \(2^{2a+5}\) and \(2^{2a+8+j}\) for all \(j\ge0\). At layer one this gives 128 and every power of two starting at 1024. The manuscript uses equality of principal ideals and cyclotomic interpolation for the unit comparison. [Project calculation, §8](../Dyadic_Window_Orders.md) · [Mizusawa, §2, p. 119](https://www.numdam.org/item/10.5802/jtnb.707.pdf)

**Ownership.** Continue Mathematical Analysis can use `weight_three_of_interpolation_mod64`, `signed_difference_valuation`, `signed_valuations` and `smith_cases` as entry points. Verify Lean Proofs owns the strict-cohomology interface. Continue Conversation owns the projected circular-unit calculation at 277. The bound for the full moving window remains open.

**Compiler and restart.** Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, checked all 92 named declarations below and all five complete source files. The combined `formal` Lake target passed. The release pin is 4.33.1; the pinned run of these new modules is pending. From `formal`, run `python checkpoint.py --compat-version 4.36.0 --lean <path-to-lean> --module PairedSigns --through PairedSigns.signed_difference_valuation`. Omit `--through` to check the complete module. The versioned ledgers retain the source-prefix hashes, imported local source hashes, compiler and kernel output.

| Source | Named declarations | Last named breakpoint | Last passing breakpoint and ledger |
|---|---:|---|---|
| [Character2893.lean](Reimann/Character2893.lean) | 11 | `Character2893.normalized_table` | [Character2893.complete](compat-4.36.0-Character2893.json) |
| [SampleSpacing.lean](Reimann/SampleSpacing.lean) | 12 | `SampleSpacing.common_denominator_odd` | [SampleSpacing.complete](compat-4.36.0-SampleSpacing.json) |
| [WeightClasses.lean](Reimann/WeightClasses.lean) | 31 | `WeightClasses.signed_exact_level` | [WeightClasses.complete](compat-4.36.0-WeightClasses.json) |
| [PairedSigns.lean](Reimann/PairedSigns.lean) | 24 | `PairedSigns.signed_difference_valuation` | [PairedSigns.complete](compat-4.36.0-PairedSigns.json) |
| [PairedOrders.lean](Reimann/PairedOrders.lean) | 14 | `PairedOrders.order_spectrum` | [PairedOrders.complete](compat-4.36.0-PairedOrders.json) |

<details>
<summary>Character2893 breakpoint names, inputs and hypotheses in source order</summary>

```lean
Character2893.modulus
Character2893.modulus_value
Character2893.oddTwist (b : Nat)
Character2893.scaledB2 (m b : Int)
Character2893.scaledB4 (m b : Int)
Character2893.WeightedSums
Character2893.addOdd (acc : WeightedSums) (b : Nat)
Character2893.residueBlock (acc : WeightedSums) (i : Nat)
Character2893.sums
Character2893.valuation_factors
Character2893.normalized_table
```

</details>

<details>
<summary>SampleSpacing breakpoint names, inputs and hypotheses in source order</summary>

```lean
SampleSpacing.cyclotomicSample_pow (j : Nat)
SampleSpacing.oddPower_pow (x : Int) (k : Nat)
SampleSpacing.power_gap_at_zero (j k : Nat)
SampleSpacing.five_power_mod_four (n : Nat)
SampleSpacing.exactV_mul_odd (x : Int) (j : Nat) (v : Int) (hx : exactV x j)
SampleSpacing.power_gap (n j k : Nat)
SampleSpacing.numerator (c0 c1 ε a : Int)
SampleSpacing.reciprocal_difference_factor (c0 c1 ε a b : Int)
SampleSpacing.reciprocal_slope (c1 ε a b : Int) (hcoeff : ∃ z : Int, c1=2+4*z) (hsign : ε=1 ∨ ε= -1) (ha : ∃ u : Int, a=1+4*u) (hb : ∃ v : Int, b=1+4*v)
SampleSpacing.exactV_mul_twice_odd (x : Int) (j : Nat) (w : Int) (hx : exactV x j)
SampleSpacing.reciprocal_spacing (c0 c1 ε : Int) (hcoeff : ∃ z : Int, c1=2+4*z) (hsign : ε=1 ∨ ε= -1) (n j k : Nat)
SampleSpacing.common_denominator_odd (n m : Nat)
```

</details>

<details>
<summary>WeightClasses breakpoint names, inputs and hypotheses in source order</summary>

```lean
WeightClasses.hit (f : Nat → Int) (k i : Nat)
WeightClasses.SiblingSteps (f : Nat → Int)
WeightClasses.hit_shift (f : Nat → Int) (step : SiblingSteps f) (k i : Nat)
WeightClasses.hit_mod (f : Nat → Int) (step : SiblingSteps f) (k i : Nat)
WeightClasses.hit_parent {f : Nat → Int} {k i : Nat} (h : hit f (k+1) i)
WeightClasses.hit_child_iff_even (f : Nat → Int) (k i : Nat) (u : Int) (hu : f i = (2 : Int)^(k+4)*u)
WeightClasses.sibling_alternative (f : Nat → Int) (step : SiblingSteps f) (k i : Nat) (parent : hit f k i)
WeightClasses.binary_fiber {m j r : Nat} (hj : j < 2*m) (hr : j%m=r)
WeightClasses.RootAt (f : Nat → Int) (k r : Nat)
WeightClasses.lift_root (f : Nat → Int) (step : SiblingSteps f) (k r : Nat) (root : RootAt f k r)
WeightClasses.root_at_every_depth (f : Nat → Int) (step : SiblingSteps f) (seed : hit f 0 0) (k : Nat)
WeightClasses.root_unique {f : Nat → Int} {k r s : Nat} (hr : RootAt f k r) (hs : RootAt f k s)
WeightClasses.root_compatible {f : Nat → Int} {k r s : Nat} (hr : RootAt f k r) (hs : RootAt f (k+1) s)
WeightClasses.sample (c0 c1 ε : Int) (i : Nat)
WeightClasses.seed_even_constant (c0 c1 ε : Int) (hsign : ε=1 ∨ ε= -1) (seed : hit (sample c0 c1 ε) 0 0)
WeightClasses.numerator_difference (c0 c1 ε a b : Int)
WeightClasses.numerator_slope (c0 c1 ε a b : Int) (hc0 : 2 ∣ c0) (hc1 : ∃ w : Int, c1=2+4*w) (ha : ∃ u : Int, a=1+4*u) (hb : ∃ v : Int, b=1+4*v)
WeightClasses.twoPower_eq_pow (k : Nat)
WeightClasses.sample_steps (c0 c1 ε : Int) (hc0 : 2 ∣ c0) (hc1 : ∃ w : Int, c1=2+4*w)
WeightClasses.unique_weight_class (c0 c1 ε : Int) (hc1 : ∃ w : Int, c1=2+4*w) (hsign : ε=1 ∨ ε= -1) (seed : hit (sample c0 c1 ε) 0 0) (k : Nat)
WeightClasses.two_seeds_iff (c0 c1 : Int)
WeightClasses.classes_from_two_seeds (c0 c1 ε : Int) (plusSeed : hit (sample c0 c1 1) 0 0) (minusSeed : hit (sample c0 c1 (-1)) 0 0) (hsign : ε=1 ∨ ε= -1) (k : Nat)
WeightClasses.roots_equal_iff {f g : Nat → Int} {k r s : Nat} (hf : RootAt f k r) (hg : RootAt g k s)
WeightClasses.cancel_five_power (k n : Nat) (z : Int)
WeightClasses.odd_weight_mod (i k : Nat)
WeightClasses.root_odd_weight {f : Nat → Int} {k r : Nat} (root : RootAt f k r) (i : Nat)
WeightClasses.exact_level_iff (f : Nat → Int) (k i : Nat)
WeightClasses.exact_sibling {f : Nat → Int} {k r s : Nat} (parent : RootAt f k r) (child : RootAt f (k+1) s)
WeightClasses.exact_weight_class (f : Nat → Int) (step : SiblingSteps f) (seed : hit f 0 0) (k : Nat)
WeightClasses.every_exact_level (f : Nat → Int) (step : SiblingSteps f) (seed : hit f 0 0) (k : Nat)
WeightClasses.signed_exact_level (c0 c1 ε : Int) (plusSeed : hit (sample c0 c1 1) 0 0) (minusSeed : hit (sample c0 c1 (-1)) 0 0) (hsign : ε=1 ∨ ε= -1) (k : Nat)
```

</details>

<details>
<summary>PairedSigns breakpoint names, inputs and hypotheses in source order</summary>

```lean
PairedSigns.sign_difference (c0 c1 a : Int)
PairedSigns.WeightThree (c0 c1 : Int)
PairedSigns.linear_at_three (c0 c1 : Int)
PairedSigns.weight_three_linear_residues (c0 c1 : Int) (h : WeightThree c0 c1)
PairedSigns.weight_three_linear_coefficient (c0 c1 : Int) (h : WeightThree c0 c1)
PairedSigns.weight_three_constant_coefficient (c0 c1 : Int) (h : WeightThree c0 c1)
PairedSigns.coefficient_reduction (c0 c1 s a : Int) (h : WeightThree c0 c1) (evenDiff : ∃ d : Int, s-a = 2*d)
PairedSigns.argument_reduction (s a : Int)
PairedSigns.five_power_period_eight (r : Nat)
PairedSigns.five_power_mod_weight (r : Nat)
PairedSigns.signed_sample_mod_weight (c0 c1 s : Int) (h : WeightThree c0 c1) (hs : s = 1 ∨ s = -1) (r : Nat)
PairedSigns.representative_table
PairedSigns.all_odd_weights (c0 c1 : Int) (h : WeightThree c0 c1) (r : Nat) (hr : r%2=1)
PairedSigns.normalized_third_residues
PairedSigns.weight_three_of_interpolation_mod64 (c0 c1 u v : Int) (oddPlus : u%2=1) (plus : numerator c0 c1 1 125 % 64 = (u*(Character2893.sums.weightThree/(240*(Character2893.modulus:Int))))%64) (minus : numerator c0 c1 (-1) 125 % 64 = (v*(Character2893.sums.twistedThree/(240*(Character2893.modulus:Int))))%64)
PairedSigns.both_seeds (c0 c1 : Int) (h : WeightThree c0 c1)
PairedSigns.common_class_iff {c0 c1 : Int} {k i j : Nat} (hp : WeightClasses.RootAt (WeightClasses.sample c0 c1 1) k i) (hm : WeightClasses.RootAt (WeightClasses.sample c0 c1 (-1)) k j)
PairedSigns.depth_cutoff (c0 c1 : Int) (h : WeightThree c0 c1) (k : Nat)
PairedSigns.paired_root_classes (c0 c1 : Int) (h : WeightThree c0 c1) (k : Nat)
PairedSigns.positiveBranch (c0 c1 : Int) (r : Nat)
PairedSigns.negativeBranch (c0 c1 : Int) (r : Nat)
PairedSigns.reciprocal_sign_identity (c0 c1 u : Rat)
PairedSigns.coefficient_minus_two_valuation (c0 c1 : Int) (h : WeightThree c0 c1)
PairedSigns.signed_difference_valuation (c0 c1 : Int) (h : WeightThree c0 c1) (r : Nat)
```

</details>

<details>
<summary>PairedOrders breakpoint names, inputs and hypotheses in source order</summary>

```lean
PairedOrders.PairAt (c0 c1 : Int) (r α β : Nat)
PairedOrders.residue_zero_of_deep {x : Int} {n : Nat} (hx : exactV x n) (hn : 6 ≤ n)
PairedOrders.valuation_of_residue {x : Int} {n : Nat} (hx : exactV x n)
PairedOrders.signed_valuations {c0 c1 : Int} (h : WeightThree c0 c1) {r α β : Nat} (hr : r%2=1) (vals : PairAt c0 c1 r α β)
PairedOrders.SmithAt (a α β lo hi : Nat)
PairedOrders.smith_cases {c0 c1 : Int} (h : WeightThree c0 c1) {r α β a lo hi : Nat} (hr : r%2=1) (vals : PairAt c0 c1 r α β) (ha : 1 ≤ a) (smith : SmithAt a α β lo hi)
PairedOrders.order_gap {c0 c1 : Int} (h : WeightThree c0 c1) {r α β a lo hi order : Nat} (hr : r%2=1) (vals : PairAt c0 c1 r α β) (ha : 1 ≤ a) (smith : SmithAt a α β lo hi) (card : order = 2^lo * 2^hi)
PairedOrders.layer_one_gap {c0 c1 : Int} (h : WeightThree c0 c1) {r α β lo hi order : Nat} (hr : r%2=1) (vals : PairAt c0 c1 r α β) (smith : SmithAt 1 α β lo hi) (card : order = 2^lo * 2^hi)
PairedOrders.exact_five_of_residue {x : Int} (h : x%64=32)
PairedOrders.companion_of_deep {c0 c1 : Int} (h : WeightThree c0 c1) {r : Nat} (hr : r%2=1)
PairedOrders.every_high_pair {c0 c1 : Int} (h : WeightThree c0 c1) (j : Nat)
PairedOrders.exact_four_of_residue {x : Int} (h : x%64=16 ∨ x%64=48)
PairedOrders.weight_one_pair {c0 c1 : Int} (h : WeightThree c0 c1)
PairedOrders.order_spectrum {c0 c1 : Int} (h : WeightThree c0 c1) (a order : Nat) (ha : 1 ≤ a)
```

</details>

The same combined target includes three companion calculations. `WindowCertificate.residual_budget_iff` gives the exact remaining integer budget for a finite pairwise-coprime support and verified lower lengths. `LocalCorrection.dyadic_factorial_correction` and `tame_place_correction` sum the given local exponents over the window. `FixedClassDescent.fixedClassIsoAtOddPower` gives the inverse to extension, assuming the norm identities and odd annihilating exponent. Their complete 4.36.0 ledgers are recorded alongside the sources.


## Coordination with Continue Conversation — strict classes and tame characters

**Cross-chat ownership.** These are the assignments in the shared handoffs and the project's recent coordination messages. The last passing declaration and the outstanding input for each dyadic calculation appear in its own section of this file. Report changes here before a second chat starts the same declaration.

Continue Agent Notes reserves `SignedWeightedIdeal69.samples_of_reverse_cube` for the implication from native membership of the conductor-69 candidate in the distinguished quadratic ideal modulo `(2,T)^3` to the two weight-one samples.

**Paper source for Verify Lean Proofs' global input.** Take the field fixed by the kernel of the finite inverse cyclotomic twist and take $S$ to consist of its places above 277 and the infinite places. Sharifi, Definition 1.3.19 and Remark 1.3.21, identifies the localized ideal class group with the Galois group of the Hilbert $S$-class field by the forward Artin isomorphism. The Frobenius convention after Theorem 1.1.10 is the residue-field cardinality power. To use this statement in Lean one must realize the homomorphism on the actual invertible fractional ideals, identify the target with the closed unramified and split quotient, and match conjugation with transport of those ideals. [Sharifi, *Iwasawa Theory*, Chapter 1](https://www.math.ucla.edu/~sharifi/notes/iwasawa-ch01.html)

| Chat | Current work | Handoff to the other chats |
|---|---|---|
| Verify Lean Proofs | Four canonical finite places at 277, their absolute decomposition maps and inverse-twisted strict class characters | Restart from `PadicPlaces.complete` and `BottomGalois.complete` on 4.36.0. Next `TameArithmetic277.four_completions`, then `TameCyclotomicLocal277.restriction` and `TameStrictArtin277.strict_class_character`. The arithmetic ideal symbol, principal kernel and Frobenius normalization are reserved in `Reimann277.ArithmeticSymbol`. |
| Continue Conversation | Conductor 69, tame exponent zero. `CircularCommonField69.canonical_real_specialization` passed on 4.36.0 in a field generated by an element of exact order 19113. Next reserved arithmetic comparison is `CircularConductorComparison69.conductor69_generators_in_sinnott` for the conventional norm generators of the named real field. | The actual determinant norm, the labelled reduction on ℤ[ζ₆₉], and the integral representative of the signed quotient passed on both releases. The positive norm has coordinate 159, its inverse 118, and the quotient 41. Verify Lean Proofs retains the canonical-place and upstairs Artin comparisons. |
| Continue Agent Notes | Signed dyadic factorization for (11,263), actual cyclotomic layers, class groups, and the normalized Stickelberger series. | Next reserved declarations: `SignedFiniteAnnihilation2893.ideal_from_finite_coordinates`, `SignedForwardPeriod2893.forward_period`, `SignedForwardGenerator2893.forward_order`, `SignedFieldLayers2893.forward_five`, `SignedClassAction2893.forward_on_classes`, `SignedLayerClasses2893.forward_on_integral_ideal`, `SignedLayerClasses2893.forward_on_classes`, `SignedLayerClasses2893.primaryForward_period`, `SignedFiniteClasses2893.finite_two_classes`, `SignedProfiniteLimit2893.closed_coherent`, `SignedClassTopology2893.profinite_limit`, `SignedClassTopology2893.continuous_forward`, `SignedAdicDistinguished2893.distinguished_of_cube_roots`, `SignedClassTower2893.forward_on_limit`, `SignedStickelbergerCandidate.raw_congruences_256`, and `SignedFieldComparison2893.characteristic_bits`. Supporting reservations include `SignedNormLimit2893.forward`, `SignedNativeScalar2893`, `SignedCyclotomicEmbedding2893` and `SignedArithmeticTower2893` for the actual specialization. Further reserved breakpoints are `SignedIdealNormEquivariance2893.map_relNorm`, `SignedDiscriminant2893.signed_character_eq_jacobi`, `SignedCyclotomicTrace2893.forward_trace` and `SignedNativeSeries2893.characteristic_bits_of_principal_inclusion`. Concrete targets also include `SignedComplexLayers2893.layer_is_cyclotomic`, `SignedRationalCharacteristic2893.determinant_convention`, `SignedIwasawaCharacteristic2893.coefficient_comparison`, `SignedCyclicCriterion2893.ideal_from_generator`, `SignedAdicAction2893`, `SignedClassScalars2893.limitModule` and `SignedRelativeExponent.exponent_restricts`. The finite-character interpolation checkpoint `SignedFiniteInterpolation2893.fourier_bernoulli_2893` is reserved to Continue Agent Notes. Construct the field action and the inverse-indexed candidate, then identify the class module's characteristic ideal with the candidate's ideal. |
| Math Idea Review | Higher layers and invariant factors for (3,23) | Hand off the checked lattice quotient and its sample hypotheses to the dyadic field-construction work. |
| Continue Mathematical Analysis | Round 4 reserves `DyadicNormalTower69.cofinal_normal_tower` and `DyadicNativePrime69.prime_contraction` in the mathlib bridge, `DyadicMizusawaCoordinates69.split_image` for the generator and subgroup calculation, and `DyadicArtinLimit69.continuous_artin` for the inverse-limit map. `DyadicNativeClass69.class_artin` owns the genuine fractional-ideal and class-group maps, `DyadicControlJet69.samples_from_bottom_control` the bottom coinvariant test, and `DyadicGenusSwitcher69.mizusawa_switcher` the field signs. `DyadicIntegerPrime69.prolong_integer_prime` owns the integral-closure specialization of prime contraction and prolongation. | Resume from `DyadicAbsolutePlace69.decomposition_lifts_every_automorphism` and `DyadicArtinPlace69.complete` on 4.36.0. Reuse the signed orientation and the checked lattice factors. The arithmetic Artin and characteristic-ideal comparisons belong here. |
| Dyadic Shape | Residue shape of Mizusawa's polynomial for every pair (q,d) of the family, the valuation rule for all strict groups, and layer-two class-group tests. `DyadicResidueShape.complete`, `DyadicContent.complete` and `DyadicShapeBridge.complete` passed on 4.36.0 and on 4.33.1. Next reserved declaration: `DyadicContent.strict_groups_of_shape`, the induction over layers that assembles `strict_smith`, the three distance theorems and the layer theorems. | `DyadicShapeBridge.samples_iff_inert_shape` replaces the (3,23) sample hypothesis of the matrix chain by the residue conditions c0 ≡ 4 (mod 8), c1 ≡ 2 (mod 4). The paper theorem gives C_1 mod 4 from the Legendre symbol (q/d) for every pair; it removes the dependence of the conductor-69 coefficient route on the printed example of p. 134. Its formal obligations O1 to O5, the tests and the remaining arithmetic inputs are in the section "Dyadic Shape" at the end of this file. |

Verify Lean Proofs also owns `TameCanonicalDecomposition277.four_absolute_decomposition_maps`, `TameInertia277.same_residue_iff`, `frobenius_lifts_equal`, `TameArithmeticSymbol277.Input` and `reciprocity_equivariant`. In the strict interface the next reusable declaration is `TameResidueCharacter277.realize`: lift an additive, scalar-equivariant residue character of the kernel to integer representatives, then apply the checked commutator extension. `TameStrictReciprocity277.strict_class_character_of_symbol` will consume the normalized ideal symbol and give the unique inverse-twisted class character. The dyadic and conductor-69 results in this restart are owner reports.

**Checked arithmetic quotient and local action at this checkpoint (4.36.0).** Let E = ℚ(√−3,√−23), m = 277^(n+1), N = ker(κ^(−r) mod m), and K be the fixed field of N. `TameArtin277.localRelations` is the union of inertia away from 277 with all conjugates of the four local restriction images of the upstairs kernels. `UnramifiedSplitQuotient` quotients N by the topological closure of the normal subgroup generated by those elements and all commutators. `unramified_away`, `split_at_277`, `quotient_commutes`, and `continuous_split_characters` compiled with the full ArtinBasic target. `IdealAction.complete` checks the action on K, its integers, the localization and its ideal classes. `StrictArtinInput.strict_class_character_of_witness` compiled for a simultaneous tame witness, an inverse class reciprocity isomorphism, and a crossed cocycle continuous modulo m; `ideal_character_twist` takes the additional hypothesis that reciprocity commutes with conjugation. `ClassOrientation` kernel-checked 111^r on forward ideal arguments and 5^r on pullback, assuming the character law and that the chosen local automorphism acts by fifth powers on 277th roots. The construction of such a local automorphism is tracked separately in `TameGenerator`.

**Maximal-order splitting at 277.** The 4.36.0 target `PrimeFactorization` compiled. In the full integer ring of E, `TamePrimeFactorization277.prime_factorization_277` gives (277) = ∏ₛ Pₛ over the four sign pairs. `multiplicity_one s` proves Pₛ divides (277) and Pₛ² does not. Every height-one prime containing 277 has precisely one such label by `prime_over_277`. These results use no class-field hypothesis. `TameFractionalFrobenius277.symbol` is reserved to assemble a forward ideal homomorphism from finite prime multiplicities and the choice-independent Frobenius values. Its surjectivity and kernel of principal fractional ideals are the remaining global reciprocity tests. The standard maximal-ideal completion comparison is still being replayed. `TameStrictArtin277.strict_H1_of_global_laws`, `strict_class_character_of_global_laws`, and `strict_H1_at_frobenius` consume `TameFractionalFrobenius277.GlobalLaws r n` for the particular homomorphism, with no independent twist-commutation or local lifting hypothesis.


Verify Lean Proofs reserves `TameStrictReciprocity277.strict_at_canonical_places` and `canonical_strict_class_character` in `CanonicalStrict`, and `TameStrictCohomology277.strict_class_group_equiv` in `StrictCohomology`. The latter uses pointwise addition of strict continuous cocycles, the subgroup of globally principal cocycles, and the subgroup of inverse-twisted class-group characters. It requires the same normalized arithmetic symbol. `TameQuotientConjugation277` handles ambient conjugation on the closed unramified/split quotient; `ArithmeticNaturality` handles its connection to transports of localized prime ideals. The final `TamePrimeStrict277.strict_cohomology_equiv`, `evaluate_at_prime`, and `strict_class_character` take `TameArithmeticNaturality277.PrimeSymbol`. This requires a surjective forward ideal map with principal kernel and its residue-Frobenius normalization, and the proof derives conjugation from this normalization and ideal factorization. `TameQuotientTransport277.descendEquiv` and `TameQuotientConjugation277.onQuotient_project` provide its intermediate quotient comparisons. The intermediate `TameStrictArtin277.strict_class_character_of_witness` uses a simultaneous tame `Witness r n`, while `strict_class_character` constructs it from 276 ∤ r. The class action will be checked in `TameStrictReciprocity277.forward_class_residue` and `pullback_class_residue`, with 111^r and 5^r respectively after reduction. The `PrimeCRT` reduction at 277 is reserved to Verify Lean Proofs, including `TamePrimeCRT277.residue_product_277`, its component maps and the two radical residues. In `CanonicalKernel`, `completionKernel_fixedField` identifies the local twist-field kernel via the compositum after choosing the closure embedding; comparison with the literal completion of K at each prime above v is a distinct assertion. The maximal-order factorization `prime_factorization_277` belongs to Verify Lean Proofs. The absolute Frobenius construction is divided into `FrobeniusTower`, `FrobeniusFiniteTests`, and `AbsoluteFrobeniusLift` for a prime with nonzero contraction; `TameCutTopology277.kernelAbsoluteHomeomorph` addresses continuity for the twist field. All are 277 work. Latest completed lower breakpoints include `BiquadraticNumberField.complete` (7/7), `IdealArtin.complete` (7/7) and `Inertia.complete` (27/27) on 4.36.0.

The actual prime at each signed embedding can now be used by the other owners. For any number field K and rational algebra embedding f : K →ₐ[ℚ] ℚ_[277], `TameFinitePlaces277.residue_equiv` gives (𝓞 K)/(embeddingPrime f) ≃+* ZMod 277, and `residue_cardinality` gives 277. For E = ℚ(√−3,√−23), `signed_primes_injective` distinguishes the four primes in the full ring of integers. The complete NumberFieldPrime target passed on 4.36.0; its prefix runner separately reached residue_cardinality. `AbsoluteDecomposition.complete` passed 10/10, `GaloisTransport.complete` 5/5, and `CyclotomicRoots.complete` 5/5. The entire `CyclotomicLocal` target now kernel-checks the action of the four genuine signed absolute restrictions on every 277-power cyclotomic character, the finite Galois twist field, and the restrictions on its absolute kernel. Its per-declaration runner and the exhaustive canonical-place comparison are in progress.


The dyadic field work and the 277-adic completion proofs have separate owners. At 277 the four signed kernels and their completed integral orders have passed. The correspondence with the finite places of the number field remains open. The arithmetic dyadic strict group still requires the local and Iwasawa inputs specified in relay 2 below.

Continue Mathematical Analysis also reserves `DyadicRamifiedClass69.dyadic_class_order_two` for the actual bottom ideal of \(\mathbb Z[\sqrt{-69}]\) and `DyadicArtinResidueNorm69.frobenius_norm_at_prime` for norm compatibility at the residue field. Both feed the unramified tower calculation.

**Compiler and last passing theorem.** Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The integrated nontrivial tame theorem is `Reimann.TameGaloisInterface.continuous_strict_class_correspondence`, with last passing source breakpoint `TameGaloisInterface.complete`. It constructs inverse maps between continuous finite-coefficient crossed homomorphisms that are locally principal, modulo global principal differences, and equivariant characters of the supplied Artin quotient. The coefficient action on target values is \(\kappa^{-r}\). The hypotheses are a group with its group topology, a continuous scalar action, a normal cyclotomic kernel, global and local tame lifts with invertible scalar differences, local restriction maps, and `ContinuousArtinInput`. This final structure requires a continuous surjective map to the discrete class quotient, compatibility with conjugation, vanishing of the local kernels, and the reciprocity kernel test **only for continuous characters**. Continuity of the inverse map's cocycle follows from its commutator formula. The coefficient comparison for \(M[p^n]\subset M\) uses `TameCoefficients`.

**Verified at 277.** Put \(R=\mathbb Z[\sqrt{-3},\sqrt{-23}]\) and \(E=\mathbb Q(\sqrt{-3},\sqrt{-23})\). Modulo 277 the roots of \(-3\) are 44 and 233, and the roots of \(-23\) are 114 and 163. The 17 new modules passed 416 breakpoints, including 255 named theorem or lemma proofs, on Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. Each module's ledger records the source prefixes and their imports. The initial congruences use kernel reduction. The following statements have Lean proof terms.

| Step | Passing declarations | Exact scope |
|---|---|---|
| Lift and exhaust roots | `TameLimitRoots277.four_root_pairs` | The four sign pairs are in bijection with all simultaneous roots in `Integer277`, the inverse limit of residues modulo every positive power of 277. |
| Identify all integral primes | `TameBiquadratic277.finite_splitting277`, `TameOrderPrimes277.four_primes_above_277`, `TameLocalOrders277.all_order_primes` | Evaluation splits the finite order at every depth. Every prime of \(R\) containing 277 is a unique signed kernel, with surjective residue map to \(\mathbb F_{277}\). |
| Compare ordinary ideal powers | `TamePrimePowers277.prime_power_iff` | For each \(n\ge0\), membership in \(P_{s,t}^{n+1}\) is equivalent to vanishing under signed evaluation modulo \(277^{n+1}\). |
| Complete each integral order | `TameLocalOrders277.four_integral_completions` | The completion using ordinary powers of each of these four primes has explicit inverse maps to `Integer277`. The earlier `four_evaluation_completions` proves compatibility with addition and multiplication in evaluation coordinates. The four steps above use no class-field or number-field input. |
| Embed the order and pass to fractions | `TameOrderFaithful277.orderImage_injective`, `TameFractionCompletion277.completion_fraction_roundtrips`, `toAdicRatios_sum`, `toAdicRatios_product` | Each map from \(R\) is injective. Equality in both fraction quotients is cross multiplication, and the inverse maps preserve the usual sum and product formulas. |
| Identify the remaining hypotheses | `TameEmbeddings277.four_embeddings`, `TameTraceLattice277.full_order_localization` | Into a field with a rational coefficient map and roots squaring to \(-3,-23\), the four signed embeddings of the constructed rational biquadratic field are exhaustive. An overorder supplied with `OrderBasis` has the same localization at 277 as \(R\). Four integral traces clear the coordinate denominators by 276. |

**Recovered standard p-adic target.** `Reimann.TameArithmetic277.padic_target_realization` was the earlier next breakpoint. The standard-field result and its verification are recorded below.

The comparison has a concrete indexing convention. For \(x:\) `Integer277`, set \(f(0)=0\) and \(f(n+1)=x.\mathrm{residue}(n)\). The input to `PadicInt.ofIntSeq` asks for \(277^i\mid f(i+1)-f(i)\). At \(i=0\) this is divisibility by one. At \(i=n+1\) it is `TameLimit277.step_difference x n`. For the reverse map take the canonical integer representative of `PadicInt.toZModPow (n+1) z` at coordinate \(n\). The remaining Lean obligations use `PadicInt.cast_toZModPow` for coherence and `PadicInt.ext_of_toZModPow` for equality, before passing to fractions.

**Reserved field endpoint (pending).** `Reimann.TameArithmetic277.four_completions` must identify the resulting four \(E\to\mathbb Q_{277}\) embeddings with all finite places \(v\mid277\) of \(E\) and give \(E_v\simeq_{\mathbb Q_{277}}\mathbb Q_{277}\) as complete valued fields at each one. The integral route needs the comparison between the actual maximal order, its local primes and the finite places. The embedding route needs the correspondence with the induced absolute values and density of the image at each place. The relevant mathlib comparison is `NumberField.FinitePlace.equivHeightOneSpectrum` in `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`.

**Current reservations, Verify Lean Proofs.** The standard integer, fraction and signed-embedding comparisons are in `formal/Mathlib277/Reimann277`. The supporting core declarations are `TameCauchy277.cauchy_integer_realization`, `TameFractionTarget277`, `TameSignedEmbeddings277`, the contraction of an extending valuation ring in `TamePlaceRestriction277`, and the prime-to-277 denominator theorem for monic-integral elements in `TameIntegralSaturation277`. Continue Mathematical Analysis retains the analogous work above 2. Continue Conversation reports `CircularAmbient69.signed_nonpowers_in_ambient` for the integral two-generator presentation and `CircularBasis69.relative_basis_at_primitive` under the three root-order tests. The coordinator has since reported their actual relative norm and reduction at 114679. Common-field specialization remains with that team.

**Round 3 checked handoff.** At 277 the finite-prime label `false` denotes the positive root in each coordinate. The abstract field sign for the same root is `true`. `TameSignedEmbeddings277.embedding_on_order` resolves this difference for all elements of the integral order. `TameCauchy277.cauchy_integer_realization` identifies every unrestricted integer Cauchy sequence modulo null difference with one compatible integer. `TameCauchy277.complete_and_separated` gives unique limits, and `TameRationalCauchy277.affine_overlap_iff` handles rational centers. `TameIntegralSaturation277.integral_localization` proves that every monic-integral element has coordinates with a common denominator prime to 277 and that the two localizations agree. None of these requires an integral basis. Under the ordered nonarchimedean comparison laws on \(E\) in `TamePlaceRestriction277.PlaceOrder` and the specified usual 277-adic comparison on integer scalars, `signs_injective` proves uniqueness on the entire field. Last frozen core endpoints include `TameSignedEmbeddings277.complete`, `TameCauchy277.complete`, `TameRationalCauchy277.complete`, and `TamePlaceRestriction277.complete` on 4.36.0. The round 3 dyadic basis comparison and conductor-69 single and quotient coordinates are acknowledged in the coordinator's Report 3.

**Restart, Lean 4.36.0 (611c117b).** The two restored source and dependency fingerprints passed through `PadicPlaces.complete` and `BottomGalois.complete`. The new `TameResidueCharacter277.realize` breakpoint passed. For a positive modulus and tame datum T, an additive residue-valued character on the kernel of T whose conjugate evaluates by the scalar of T yields the integer-representative `TameRestriction.KernelCharacter T`. The next named checks are `extend_at_kernel` and `restrictions_equal_iff_principal`. This permits testing equality of descended characters at the level of cohomology classes. `TameCyclotomicUnits277.inverse_scalar_power` now gives the exact residue `111^r` for every negative-weight power of a unit reducing to 5. The module ledger is 12/12 through `CyclotomicUnits.complete`. The class-field input on the localized cut field is specified in `TameArithmeticSymbol277.Input`: a surjective symbol on invertible fractional ideals with principal kernel, an arithmetic residue-power Frobenius lift realizing each prime ideal at its prolongations, and compatibility of the symbol with transport of fractional ideals and Galois conjugation. The four actual maps are being checked on the local completions. Identifying their ranges with independently defined decomposition stabilizers of absolute primes would require that additional comparison.

**Round 3 core verification.** The first six modules passed 198 breakpoints including 140 named proofs on both pins. The nine-module handoff adds `TameLocalDensity277.rational_dense_at_every_place`, `TameDecomposition277.arithmetic_frobenius_identity` and `TameUnramified277.inertia_fixes`. All nine have identical sources on both compilers and pass 257 breakpoints including 186 named proofs. The 4.36.0 standalone ledger has 1,149 breakpoints and 754 named proofs. The 4.33.1 variant has 1,150 and 755. Both combined targets passed through `TameChecks.complete` (106 and 54 Lake jobs respectively). The shared 4.36.0 target passed 376 jobs.

**Standard arithmetic project on Lean 4.36.0.** `Mathlib277` pins mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The bundled field `TameBiquadraticField277.Biquadratic` and its rational algebra structure have compiled. `TameBiquadraticField277.no_real_embedding` excludes real places, by applying a putative embedding to the square of the first generator. `TameCyclotomicUnits277.five_pow_ne_one` takes `r : Nat` with `¬276 ∣ r`. It tests the order of 5 modulo 277 with a kernel proof. `unit_difference` takes a residue at depth `n+1` whose reduction is different from 1 and proves its difference with 1 is a unit. This module has passed through `CyclotomicUnits.complete`. The next standard p-adic targets are `TamePadicInteger277.integerRingEquiv`, `TameArithmetic277.padic_target_realization`, and `TameArithmetic277.four_completions`, with no arithmetic hypotheses. For `r,n : Nat`, `¬276 ∣ r`, the proposed strict-character target is `TameStrictArtin277.strict_class_character` for a continuous cocycle modulo `277^(n+1)`, unramified away from 277 and locally principal above 277. This implication requires `TameArtin277.ClassReciprocity r n`. Its arithmetic construction must identify the unramified abelian split quotient with the ideal class group of the localized ring of integers of the fixed field, match arithmetic Frobenius with the corresponding prime ideal class, and respect the conjugation action for the inverse twist.

**Standard field and valuation classification, passed.** Lean 4.36.0 compiled `TameArithmetic277.padic_target_realization` against the pinned mathlib p-adic field. It gives simultaneous ring equivalences to the standard p-adic integers and field, preserves every integer residue, and fixes rational constants. `TamePadicEmbeddings277.four_padic_embeddings` classifies every rational algebra homomorphism from the bundled biquadratic field to the standard 277-adic field by one Boolean pair. `norm_le_iff_prime_power` and `norm_lt_one_iff_prime` distinguish the four primes and their powers in the integral order. `TamePadicPlaces277.equiv` classifies all project valuation comparison orders extending the specified absolute value on the rationals. Its theorem `completion_at` identifies the metric completion of each such valuation class isometrically with the standard 277-adic field, extending its labeled embedding on every element. The module build passed 4,206 Lake jobs. The next declaration for the canonical mathlib finite-place type is `TameArithmetic277.four_completions`; its ideal-theoretic comparison has an independent compiler ledger.

**Frobenius and ideal classes checked at the restart.** On 4.36.0 the whole modules `Inertia` and `IdealArtin` compiled. `TameInertia277.inertia_eq_mathlib` identifies the residue definition with inertia for the ideal under the integral automorphism action. For a maximal prime of the absolute integral closure with 277 outside it, `fixes_power_root` fixes every root of unity of order dividing 277^(n+1). `frobenius_lifts_equal` equates the images of two automorphisms acting on every residue as the same q-power, once the homomorphism kills the inertia subgroup at that ideal. `TameIdealArtin277.galoisToClass_symbol` identifies the inverse image of the symbol of I with the class of I for an integral domain and a surjective symbol with principal kernel. The arithmetic assignment of prime symbols is an additional input.

**Reserved ideal-class step.** In the standard project, TameLocalClass277.extendedHom_surjective and localized_class_finite are assigned here to transfer class-group finiteness to the localization. The concrete target is TameLocalClass277.class_finite_away_277 for the localization at 277 of a number field’s ring of integers. TameIdealArtin277.classToGalois takes a surjective ideal symbol on invertible fractional ideals whose kernel consists exactly of principal ideals. The missing arithmetic piece is the construction and Frobenius normalization of that symbol.

**After the local field input.** Instantiate `Places` on the actual decomposition groups for \(K/E\) cut out by \(\kappa^{-r}\bmod 277^n\), for \(n\ge1\) and \(276\nmid r\). Construct the equivariant Artin quotient onto \(\mathrm{Cl}(\mathcal O_K[1/277])\) using the upstairs group unramified outside 277, identifying its split continuous characters. Instantiate divisibility, continuity and vanishing invariants on the actual Tate-twisted \(M=\mathbb Q_{277}/\mathbb Z_{277}(-r)\). The real complementary component additionally requires the field's ideal norm/extension maps. This is the handoff to the projected-unit work; its finite coordinates and class-group identification have different proof obligations.

**Twist convention for the coordinator.** Section `TameOrientation.weight_one_dual` proves that at weight one \(\sigma_5\) acts on evaluations by \(111=5^{-1}\bmod277\); its pullback on the untwisted dual acts by 5. `TameTwist277.tame_fixed_iff_zero` covers all 275 nonzero tame weights modulo 276 at all finite depths. `TameRestriction.fibres_iff` gives the global kernel, `TameLocal` supplies the local principality test, and `TameClassField.ordinary_to_S_unique` handles the classes of primes over 277 once their stabilizers are known.

**Combined check.** The original 20 modules contributed 349 breakpoints, including `TameAdditivity.toCharacter_add` and `TameAdditivity.fromCharacter_add`. The 17 new local modules contributed another 416. On 4.36.0 the shared Lake target passed 206 jobs and the standalone target passed 88. The standalone runner verified all 892 breakpoints across its 42 modules, including imported support, with 568 named theorem or lemma proofs. The last aggregate breakpoint was `TameChecks.complete`. Counts here cover the standalone tame project.

**Separate 4.33.1 build.** The original 4.36.0 sources encounter missing tactic lemmas and different simplifier behavior under the upstream 4.33.1 pin. The separately staged `lean-4.33.1` project passed a clean combined build of all 45 Lake jobs on commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The proof adaptations are in `OddDescent`, `TameBiquadratic277`, `TameOrderPrimes277`, `TameOrderReduction277`, `TameRationalField277` and `TameTraceLattice277`. The four sign maps, the hypotheses and the mathematical statements agree across the two versions. A local lemma computes the value of an integer cast to `Fin n` on the older compiler. The fresh version-specific replay passed all 893 breakpoints and 569 named theorem or lemma proofs, including `TameBiquadratic277.residue_val_intCast`. The combined endpoint is `TameChecks.complete`. The final worker finished at `TameTraceLattice277.complete`. All 1,877 per-prefix dependency hash entries matched the archived source tree.

**Return dependency from Continue Conversation.** Their exponent-zero quadratic character at conductor 69 is self-inverse. Their later report gives positive product coordinate 159 and signed quotient coordinate 41 at 114679. They own the relative norm of \(1-\zeta_{69}\), compatible reduction, and `Reimann.CircularNorm69.positive_product_eq_relative_norm`. The expected return input identifies the coordinate on the specified character line.

**Dyadic relay 2.** Math Idea Review reports `DyadicMatrixHandoff.lattice_invariant_factors` through `DyadicMatrixHandoff.complete` on 4.36.0. Under `Reimann.DyadicOrder.WeightOneSamples c0 c1`, the additive factors of the lattice quotient are \(C_{2^a}\) and \(C_{2^{a+1}}\) for all natural \(r,a\). Applying this to the strict dual needs positive odd \(r\), vanishing at both dyadic places, identification with `Quot (Reimann.DyadicOrder.latticeCoset c0 c1 r a)`, and the actual Iwasawa samples over \(\mathbb Q(\sqrt{-69})\mathbb Q_\infty\). Continue Mathematical Analysis owns these inputs. The coordinator checked the archived report's provenance. Verify Lean Proofs has not replayed this dyadic theorem. Continue Mathematical Analysis also reports the basis change \(X=2e-1,\ Y=2w-1\), invertible modulo every power of 277. The integral proof above uses \(1,X,Y,XY\).

The cyclic norm, exact wild conductors, the exceptional connecting map and the quadratic example remain available alongside this interface. The manuscript [Tame strict descent](../Tame_Strict_Descent.md) distinguishes paper deductions from their Lean inputs.

This is a standalone extension to the Reimann working notes. It uses the same Lean pin as the November 20 public source archive, `leanprover/lean4:v4.33.1`. The Lean project is the `formal` directory. **The manuscript contains paper proofs. A passing Lean declaration proves its displayed statement, including any hypotheses in its signature.** The sections on number fields require substantial dependencies before their full statements can be kernel-checked.

## Math Idea Review - strict dual at positive odd weight for (3,23)

Source: `Reimann/DyadicStrictDualAdapter.lean`, importing `DyadicStrictKernel`, `DyadicStrictRelation`, and `DyadicMatrixHandoff`. Checkpoints include `Reimann.DyadicStrictRelation.strictRelation_iff_latticeCoset`, `Reimann.DyadicStrictKernel.fibres_of_exact_kernel`, and `Reimann.DyadicStrictDualAdapter.strict_dual_invariant_factors`. The last recorded declaration-prefix checkpoint on Lean 4.36.0 (611c117b) is `DyadicStrictDualAdapter.complete`. The adapter and its full dependency closure were also built from the main project's shared source files using Lean 4.33.1 (819816b2) and 4.36.0 (611c117b).

Inputs: `Reimann.DyadicOrder.WeightOneSamples c0 c1` for the arithmetic polynomial, and `Reimann.DyadicStrictDualAdapter.Presentation c0 c1 w a G` for the actual strict dual at positive odd weight. The presentation requires an additive surjection from coordinates in the basis (2b,c) whose kernel is exactly the preimage of $D_aY$ under $i(u,v)=(2u,v)$. Both the arithmetic coefficient test and this Artin/kernel comparison remain with the dyadic owner. The invariant factors are $2^a,2^{a+1}$, including the trivial first factor when $a=0$. The representative reads $(0,u\bmod 2)$ at layer zero and $(u\bmod 2^a,v\bmod 2^{a+1})$ at positive layers.

## Breakpoints

The six-module project passed a combined Lake build on Lean 4.36.0. Individual compatibility ledgers are named `compat-4.36.0-ModuleName.json`. The upstream pin remains 4.33.1 and has its own ledger. To rebuild with the verified newer installation from `formal`, use `elan run leanprover/lean4:v4.36.0 lake build`. For individual steps with that compiler pass `--compat-version 4.36.0 --lean <full-compiler-path> --module <module-name>`.

In the `formal` directory, `python checkpoint.py --list` lists each definition, named proof, executable guard, and module end in source order. `python checkpoint.py` checks successive prefixes with the pinned Lean executable. For example, `python checkpoint.py --module Cubic --through Cubic.norm_remainder` checks the cubic calculation through the relative norm. Use `--lean` with an absolute executable path if needed. The script stops at the first error and atomically records each passing prefix in `checkpoint-state.json`. A changed prefix is rechecked. A complete module is additionally sent to Lean verbatim. `lake build` in the same directory checks that the project builds together. An executable `#guard` checks a computation; a named theorem supplies a proof term. The declaration log records which was executed.

For the next research calculation, write the input objects and the first new identity in Lean, run its prefix, and save that result before using it in another calculation. If the input is an external arithmetic theorem, record the exact source and the precise missing Lean statement. Do not promote a conditional theorem or a finite example to the arithmetic conclusion.

## Correspondence between the manuscript and the formal work

| Paper step | Lean location | Remaining formal work |
|---|---|---|
| Signed filter and its four values | Foundation.character_filter and Foundation.sign_table | Transfer from the arithmetic signal to those sign variables belongs to the preceding analytic argument. |
| Strict dual inside the even \(K\)-group | Transfer uses the maps abstractly | Construct the cohomology objects, instantiate Poitou–Tate, Quillen–Lichtenbaum and localization. |
| Large-prime geometric estimate (B) | External input to the size bound | Formalize de la Torre Durán Theorem 4.5 with the stated stabilizer cutoff. |
| Transfer from integral homology to level three | Transfer.transfer_kernel_depth, primary_index_annihilator, congruence_index_depth | Define the actual congruence subgroup, prove its index and torsion-freeness, construct the transfer and instantiate its identity. |
| Integral cell bound (C) | Paper computation of dimensions and incidence norms | Formalize the relative Voronoi complex, cohomology comparison, orbit splitting, facet and orbit estimates, universal coefficients and the determinant bound. |
| Small-prime Hurewicz kernel | Transfer.transfer_kernel_depth consumes its exponent | Instantiate the stable linear-group identification and Mathew Theorem 6.3. |
| Rank and exponent cost (D) | Transfer.imageKernelBijection, image_kernel_card and order_bound; OddDescent.capped_succ | Formalize the arithmetic \(S\)-unit or \(H^2\) Kummer sequence, discriminant and Minkowski bounds, Brauer calculation, and their sum. |
| Assembling (A), the growing range (E), and character-specific conductors | Transfer.power_budget and bottom_exponent_margin prove discrete inequalities | Construct real logarithms, big-O bounds with uniform constants, summation, character descent, and the link to the window integer. |
| Local cyclotomic image and finite boundary at odd \(p\) | OddDescent.exceptional_cyclic_index | Prove the field intersections, full local decomposition, cyclic cohomology formula and local/global boundary computation. |
| Descent to a finite class group | OddDescent.DescentInputs.strictCorrespondence and preceding lemmas | Supply its inputs from the actual global/local five-term sequences, class field theory and complex conjugation. |
| \(p\)-primary support, successive invariant factors and the plateau test | OddDescent.capped_succ, width_drop, equal_multiplicity_from_caps and plateau_iff | Identify the input list with the invariant factors of the arithmetic group; formalize the absolute-height bounds. |
| Weight periodicity and summation across residues | OddDescent.congruent_weights, large_prime_weight and weight_window_cost | Identify the abstract action period with the cyclotomic period and instantiate the Kummer dimensions. |
| Reflection to minus ideal classes | OddDescent.reflection_kernel, injective_of_difference_kernel, reflected_weight and reflected_conjugation | Prove the Kummer identification, CM-unit property, equality of local and global \(p\)-power roots, and the reflected eigenspace statement. |
| Reflected Bernoulli index and support filter | Bernoulli.reflectedIndex_spec; Foundation.mirror_index_add | Formalize eigenspace descent, integral Stickelberger annihilation, smoothing and Kubota–Leopoldt interpolation. |
| The example at \(277\) | Bernoulli.conductor_three_residue and conductor_twenty_three_residue | Identify these sums with the arithmetic annihilators in the previous row. |
| The dyadic lattice and analytic specializations | DyadicOrder.moment_coefficient_bits and DyadicLocal.odd_two_places_iff_annihilates_image | Construct the actual tower, its two normalized weight-one samples for (3,23), and its strict restriction map. |
| Smith factors at the first two layers | DyadicBottom.coherent_bottom_quotient_of_residues and DyadicLayers.first_square_image for the (3,23) residues. Dyadic.target_content and halves_of_real_values cover integer identities for other coefficients. | Identify the (3,23) lattice with the arithmetic strict dual. The general Smith-factor calculation for other coefficient residues has additional cases. |
| Growth at subsequent layers and the sum over weights | Dyadic matrix squaring, valuation and spacing lemmas | Complete the lattice automorphism argument, full sample spacing, root separation, height bound, and uniform sum. |
| Dyadic examples | Dyadic finite character sums for \(3,7\) and \(3,23\) | Connect exact integer sums to the interpolated \(L\)-values. |
| Cubic roots, unit and Pell certificates | Cubic.cubic_discriminant, no_root_mod_five, norm_remainder, absolute_norm_one, local_rows_independent, pell_certificate and split_unit_residues | Interpret the integral coordinate calculations inside the actual number fields and their completions. |
| Quadratic class numbers | Separate Cubic.certificateAt executable guards for seven discriminants | Prove the reduced-ideal classification and correctness/completeness of the enumeration as a class-group theorem. |
| All cyclotomic \(3\)-layers, then all weights at \(E_1\) | Local rank and residue computations in Cubic; the descent interface in OddDescent | Prove Chevalley's formula, the norm-index and tower deductions, semisimple descent, and all-weight strict group isomorphisms. |
| Whole target at all weights through \(\lfloor x^{401}\rfloor-1\) | Open mathematical step | The paper estimates here do not close this range. |

The pinned original archive and the earlier research notes are independent inputs. This package does not claim a kernel replay of the original submission or a proof of RH.

The sibling Lake target `ReimannWindow.DyadicChecks` checks the two weight-one sums, dyadic matrices, integer lattice quotient, and the independent Pell lifting calculation. The dyadic handoff above verifies normalized surjectivity on the coherent 2-adic lattice. Identifying the actual Galois lattice, interpolation, the strict-cohomology presentation, and the Pell local reciprocity maps remain arithmetic inputs. The sibling suite has its own [dyadic checkpoint index](../Dyadic_Lean_Checkpoints.md).

The odd-prime checkpoint suite in the parent Lake project adds the circular-unit character calculation at 277, an independent Stickelberger calculation, and the split-prime boundary identities. The arithmetic interpretation still requires the identification of finite strict classes with the selected real class-group components and of the projected circular units with the computed residue sums. See [Odd-prime proof obligations](../Lean_Checkpoints.md) and [Odd-prime calculations](../Odd_Prime_Checkpoints.md). Its declaration runner is `../checkpoints.py`.

## Circular-unit specialization at conductor 69

### Common conductor field and real integral units

The ambient field in [CommonAmbient69.lean](Mathlib69/ReimannNative69/CommonAmbient69.lean) is a characteristic-zero quotient field over the previously constructed conductor-69 field. Its element t satisfies tⁿ = 1 exactly when 19113 divides n. The elements x = t²⁷⁷ and z = t⁶⁹ have orders 69 and 277 respectively. The rational evaluation map at t is surjective, so the field is precisely ℚ(t). The real field E used below is the intersection of the involution-fixed field with ℚ(u,v,z), where u² = −3, v² = −23 and uv = 2θ−1 with the original period labelling.

| Source and breakpoint | Verified implication or construction |
|---|---|
| `CommonConjugation69.reciprocal_relation`, `reverse_involutive`, `compatible` | For a finite-order generator t over ℚ the proof uses a rational cyclic pairing and positivity of sums of squares to show that every rational polynomial vanishing at t also vanishes at t⁻¹. Substitution t ↦ t⁻¹ defines a rational field involution. It negates both labelled radicals and inverts every 277th root in the common field. |
| `CommonRootPowers69.root_is_power`, `CommonRealPart69.fixed_three_generator_field` | A nontrivial 277th root generates all the 277th roots in characteristic zero. The project predicate for the real compositum agrees with membership in a Mathlib subfield generated by the three specified elements and intersected with the fixed field. |
| `CircularOrbitFamily69.fixes_at_69_iff`, `orbit_at_69`, `norm_factor_mem` | A substitution fixes the field intersection exactly when it fixes all rational polynomial values in it. At 69 this definition selects precisely the previously enumerated actual automorphisms of ℚ(x) fixing ℚ(x)∩E. The resulting product on 1−xᵃ is a generator of the defined circular numbers for any permitted family containing 69. |
| `CircularCommonField69.positive_is_relative_norm`, `norm_operator_factorization`, `canonical_real_specialization` | In the common field the positive product equals the embedded determinant norm on ℚ(x)/ℚ(√69). It factors over the conductor-69 intersection norms. The positive and negative signed products are inverse integral units belonging to the named circular-unit subgroup built using divisors of 19113. Their monic integer equation is T²−25T+1. |
| `CircularQuotientCoordinate69.quotient_value`, `quotient_coordinate`, `CircularCommonField69.labelled_coordinates` | U₊/U₋ is represented in ℤ[x] by U₊². Its residue at x ↦ 21767 modulo 114679 is 75484 and its 414th power is 42957. The unique log to base 49063 is 41. The separate positive norm has unique log 159. |

**Usual complex conjugation and rings of integers.** For every ring embedding ι of the common field into ℂ, `ComplexCompatibility69.conjugation_on_embedding` proves ι(c(y)) = conj(ι(y)) for all y. The algebraic construction of c is unconditional. For O with `[CommRing O] [Algebra O realField] [IsIntegralClosure O ℤ realField]`, `CircularStandardUnits69.standard_integral_closure_units` constructs w : Oˣ and proves that w and w⁻¹ belong to the pullback of the level-19113 circular numbers. Their images are exactly U₊ and U₋. The comparison uses integrality in E and injectivity of O → E. The more general `signed_units_at_level` needs only 69 ∣ f for the level f divisor family. The stock ring-of-integers type in the pinned mathlib source supplies this integral-closure instance.

**Subfields for the conductor comparison.** `CircularConductorWitness69.quadratic_image_eq_radical_field` identifies the image of the coefficient field with the subfield generated by uv. The element uv is in E, has square 69, and lies outside ℚ. The period equals (1+uv)/2 with this labelling. `root_trace_in_real_field` also puts z+z⁻¹ in E for the primitive 277th root z. These provide explicit field inclusions for a future conductor argument.

**External arithmetic obligation.** To compare with a separately defined Sinnott subgroup, identify its conductor-69 field-norm generators with the proved intersection automorphism products for ℚ(x)/(ℚ(x)∩E). If that definition indexes by divisors of the minimal conductor f(E), discharge 69 ∣ f(E). The conductor-69 contribution alone suffices for membership of these two units. Equality of two entire circular-number groups would require controlling the other conductors as well. Lean gives the ambient level 19113 here. The minimal conductor of E remains open in this checkout. Bulant gives the conventional norm-generator and integral-unit definition in the introduction of [On Washington group of circular units](https://www.math.muni.cz/~bulik/publikace/Washington_group.pdf).

**Return dependency.** The coordinate here is computed on ℤ[x] using the auxiliary prime 114679. The canonical places at 277, the upstairs Artin comparison, and their use in the strict class group remain with Verify Lean Proofs.

**Dual-version core record.** All 1,113 breakpoints across the 54 conductor-69 core modules match the Lean 4.33.1 and 4.36.0 source and import hashes. These include 825 named proof terms and zero executable guards. The 4.33.1 compiler commit is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and the 4.36.0 compiler commit is `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. Both use identical circular-unit sources. The 4.33.1 checkout uses the previously recorded proof adaptation in the imported `TameRationalField277`. The isolated combined projects passed with 58 and 114 jobs respectively. The full shared 4.36.0 core passed with 450 jobs, and the sibling target passed with 30. The native common-field proofs use 4.36.0 with mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

**Native replay and combined build.** All 235 breakpoints in the 12 native conductor modules passed through their `.complete` records on Lean 4.36.0, including 164 named theorem proofs and zero executable guards. The combined `ReimannNative69` target passed 3,081 jobs. The requested specialization ends at `CircularCommonField69.canonical_real_specialization` and `CircularCommonField69.complete`. Its [source](Mathlib69/ReimannNative69/CircularCommonField69.lean) has SHA-256 `5556655a4b148a0134146765322d264f81aa95ac282cbc8ebc0bbed7d2e9e949`. Its [21-breakpoint ledger](Mathlib69/compat-4.36.0-CircularCommonField69.json) has SHA-256 `2c9c88cb5527b36d268509ed52bc8dd61f5319e9754be37687fff15b1d289e16`. Downstream records end at `CircularStandardUnits69.standard_integral_closure_units` and `CircularConductorWitness69.root_trace_in_real_field`, each followed by module completion. An independent axiom inspection of the root-order theorem, complex comparison, compatibility, both unit endpoints and the labelled coordinates found only `propext`, `Classical.choice` and `Quot.sound`.

### Field norm, labelled integral reduction and circular-unit membership

For a primitive 69th root x in any characteristic-zero field, set L = Q(x) and θ = 1 minus the sum of the positive powers of x. The embedded coefficient field F has basis 1, θ over Q, with θ² = θ + 17. Both the determinant of multiplication by 1−x on L over F and the product over its 22 relative automorphisms give the positive circular unit **11 + 3θ**. The other sign gives 14 − 3θ, its inverse. The ambient field and three order tests are the only inputs to the norm theorem.

| Checked breakpoint | What the proof constructs |
|---|---|
| `CircularIrreducible69.no_rational_split`, `CircularIndependence69.primitive_monomials_independent` | Reduction of Φ₆₉ modulo 23 gives (X²+X+1)²². Evaluation at a cube root gives −23ω. A proper integral factorization forces a coefficient divisible by 529. Gauss descent gives the rational factor result, and monic division excludes every rational relation below degree 44 at x. |
| `CircularPolynomialField69.in_generated_subfield_iff`, `CircularFieldBasis69.primitive_relative_coordinates` | Rational polynomial values form the least subfield containing x and Q, including inverses. Each has exactly one expansion in 1 through x²¹ over F. |
| `CircularNormAction69.multiplication_action_value`, `CircularFieldNorm69.norm_one_sub` | For each element y of L the matrix acts on all vectors as multiplication by y. Setting y = 1−x gives the checked determinant 11 + 3θ. |
| `CircularNormIdentification69.autos_complete`, `autos_nodup`, `autos_count`, `Reimann.CircularNorm69.positive_product_eq_relative_norm` | Actual automorphisms of the generated field fixing F correspond bijectively to the 22 positive unit exponents. The determinant and the orbit product agree. The norm theorem lives in `CircularNormIdentification69.lean`. |
| `CircularFieldReduction69.reduction_of_evaluation`, `positive_log_coordinate`, `negative_log_coordinate` | The map Z[x] → F₁₁₄₆₇₉ sends x to 21767, θ to 92746 and 2θ−1 to 70812. U₊ and U₋ reduce to 48891 and 65813. Their 414th powers have unique logarithms 159 and 118 modulo 277 to base 49063. The signed quotient has coordinate 41. |
| `CircularQuadraticNonpower69.signed_power_classes` | For either signed unit ε and every natural n, εⁿ is a 277th power in F exactly when 277 divides n. Two reductions above 1109 handle rational denominators. |
| `CircularRadicals69.radical_product`, `CircularRealUnit69.compatible_real_embedding` | The Gauss sums square to −3 and −23 and their product is 2θ−1 for the chosen labelling. The embedded quadratic field belongs to the real compositum under the specified conjugation. |
| `CircularSinnott69.intersection_exact`, `positive_norm_product`, `real_circular_unit` | In a common characteristic-zero realization, take u²=−3 and v²=−23 and a rational conjugation negating both and inverting every 277th root of unity. The proof gives the product of the conductor-69 norm operators over the actual intersection stabilizer. The positive unit and 25 minus that unit lie in the real field, multiply to one and both satisfy T²−25T+1. |

**Compiler record.** The 52 conductor modules passed 1,095 breakpoints, including 810 named theorem or lemma proofs, on each of Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`). This round adds 38 modules, 766 breakpoints and 581 named proofs to the preceding 14-module release. There are no executable guards in these 52 modules. The compatibility ledgers match every source prefix and every recorded imported-source hash. All circular-unit sources are identical on the two compilers. The 4.33.1 build uses a three-line proof adaptation in the existing imported `TameRationalField277.no_square_neg23_in_quad`; both versions of that dependency accompany the export.

**Builds.** The whole shared `Reimann` target passed on 4.36.0 (444 jobs in this run), as did the sibling `ReimannWindow` target (30 jobs). The isolated 52-module conductor target passed on 4.33.1 and 4.36.0. The numerical labels above concern the single exponent-zero character. Applying the result to the remaining character rows or the continuous strict class group requires their own arithmetic inputs. The norm on L/F is the ordinary determinant in the constructed basis.

**Concrete field, Lean 4.36.0.** The optional `Mathlib69` project chooses a maximal ideal of Q[X] containing the displayed Φ₆₉ and constructs the quotient field. The rational embedding is injective. For ζ the class of X, `Reimann.ConcreteQuotient69.generator_orders` proves its exact order and `all_generated` proves the quotient is Q(ζ) itself. The theorems `positive_product_eq_relative_norm`, `relative_norm_value` and `labelled_period` then give the norm and the period residue without a primitive-root premise. `positive_coordinate` identifies 159 as the unique exponent in Fin 277 for the positive unit's projected residue. The 4.36.0 Lake build passed with mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. This concrete model uses the project's proved determinant norm. Its source is [ConcreteQuotient69.lean](Mathlib69/ReimannNative69/ConcreteQuotient69.lean).

All 33 concrete-field breakpoints passed through `ConcreteQuotient69.complete` on Lean 4.36.0, including 24 named theorem proofs with axiom inspection. The last theorem is `Reimann.ConcreteQuotient69.positive_coordinate`. The separate Lake target passed 2,925 jobs. Source SHA-256 is `e9d2617b17bcb8dd71982f8105fe2338df14e77ae1e9307cc54d251a48a4ceaa`. The versioned [concrete checkpoint record](Mathlib69/compat-4.36.0-ConcreteQuotient69.json) includes all 50 imported fingerprints.

### Earlier checkpoints and calculation history

**Owner: Continue Conversation.** The exponent-zero quadratic row uses conductor 69 itself. Its two factors are
\(U_\pm(x)=\prod_{1\le a<69,\,\eta_{69}(a)=\pm1}(1-x^a)\), with 22 factors in each product. These are the factors in [the original calculation, section 3](../Odd_Prime_Checkpoints.md).

**Verification.** The three formal modules have 56 breakpoints including three whole-source checks, 35 named theorem proofs, and zero `#guard` commands. All 56 source-prefix hashes matched separate passing ledgers for Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`). The last theorem in proof order is `Reimann.CircularPrimitive69.primitive_product_discriminant`, followed by `CircularPrimitive69.complete`. The full shared `Reimann` and `ReimannWindow` targets passed on 4.36.0. On 4.33.1 the three-module target also passed in isolation. The sibling `CircularUnits.lean` passed whole-source with warnings as errors on 4.33.1 and its independent declaration runner passed through `true69_auxiliary_root_orders` on 4.36.0. The four closed residue declarations are proof terms separate from the three-module count.

The full sibling `ReimannWindow` target also passed in an isolated 4.33.1 build. All 16 inputs matched the workspace copy. The 4.33.1 formal aggregate reported above covers the three new modules.

| Reusable proof | Exact hypotheses and conclusion |
|---|---|
| `Reimann.CircularPolynomial69.norm_products_trace`, `norm_products_multiply` | For any commutative ring and any root of the displayed degree-44 polynomial, the products have sum 25 and product 1. `phi_factorization` proves the polynomial times \(1+X+X^2\) is \(1+X^{23}+X^{46}\). |
| `Reimann.CircularPrimitive69.primitive_products_trace`, `primitive_products_norm`, `primitive_product_discriminant` | In a field, assume \(x^{69}=1\), \(x^{23}\ne1\) and \(x^3\ne1\). Then \(U_++U_-=25\), \(U_+U_-=1\), and \((2U_+-25)^2=9\cdot69\). These hypotheses apply to any primitive 69th root. |
| `Reimann.CircularQuadratic69.reduce_product_at_root`, `epsilon_norm_one`, `auxiliary_epsilon`, `split_epsilon` | In integral coordinates \(1,\theta\) with \(\theta^2=\theta+17\), the elements \(11+3\theta\) and \(14-3\theta\) multiply to one. Evaluation at an integer \(t\) respects products modulo \(m\) if \(m\mid t^2-t-17\). At \(t=92746\) modulo 114679 their residues are 48891 and 65813. Evaluating the first element at \(13420,63310\) modulo \(277^2\) gives 40271 and 36483. |
| `ReimannWindow.CircularUnits.true69_signed_products`, `true69_quadratic_residues`, `true69_individual_logarithms`, `true69_auxiliary_root_orders` | Closed arithmetic theorems for the original signed-product routine at \(x=21767\) modulo 114679. Its positive and negative residues are 48891 and 65813. Raising them to 414 gives \(49063^{159}\) and \(49063^{118}\) modulo 114679. The signed quotient gives \(159-118=41\); twice the single positive coordinate is 41 modulo 277. The three primitive-root power tests also hold at this residue. |

**Original field target, completed at every primitive root.** The later `CircularNormIdentification69` proof constructs all 22 relative automorphisms and identifies their product with the field norm. `CircularFieldReduction69` constructs the reduction on the evaluated integral order. The current common-field and class-group obligations are recorded below.

**Character convention for Verify Lean Proofs.** For \(\sigma_a(\zeta)=\zeta^a\), a coefficient \(\eta_f(a)a^s\) in the idempotent sum is the inverse character weight. On the tame factor choose the generator congruent to 5 modulo 277 and 1 modulo \(f\). At weight one the scalar on forward ideal arguments is 111 and the scalar on inverse pullback of the untwisted dual is 5, under the hypotheses of `Reimann.TameOrientation.weight_one_dual`. The conductor-69 exponent-zero computation uses a self-inverse quadratic character. The later strict-group application still needs the four-place specialization and continuous Artin map from Verify Lean Proofs.

`Reimann.CircularAmbient69.signed_nonpowers_in_ambient` handles specialization after adjoining a primitive 277th root. The auxiliary prime 114679 permits both cyclotomic generators to be evaluated at the same place. `Reimann.CircularBasisData69` and `Reimann.CircularBasis69` cover the change of integral coordinates from the 44 ordinary powers to the 22 pairs \((x^j,\theta x^j)\).

### Signed product, relative determinant and nonpower

Continue Conversation owns the conductor-69 field, relative norm, auxiliary reduction and circular-unit identification. The results below supersede the earlier determinant-only status. The specific conductor-19113 realization, projectors in the enlarged field and the arithmetic class-group comparison have their own obligations.

The eleven modules in this continuation passed 273 new declaration and whole-source breakpoints on **both** Lean 4.33.1 (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Lean 4.36.0 (commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`). They include 194 named theorem proofs and zero executable guards. Together with the three earlier formal modules, all 329 breakpoints (229 named proofs) matched the source-prefix and imported-source hashes in both versioned sets of ledgers. The final basis endpoint is `Reimann.CircularBasis69.relative_basis_at_primitive`, then `CircularBasis69.complete`. The whole shared `Reimann` target passed on 4.36.0 (228 Lake jobs in this replay), as did `ReimannWindow` (30 jobs). The isolated fourteen-module conductor-69 target passed on 4.33.1 (17 jobs). These totals count formal source once per compiler.

Let \(P=\Phi_{69}\), \(H=\{a\in(\mathbb Z/69)^\times:\eta_{69}(a)=1\}\), and \(\theta(x)=1-\sum_{a\in H}x^a\). The actions below use \(x\mapsto x^a\). The source of the field application is [section 3 of the project's odd-prime calculation](../Odd_Prime_Checkpoints.md).

| Lean declarations (in namespace `Reimann`) | Hypotheses and scope |
|---|---|
| `CircularKernel69.primitive_positive_stabilizer`, `positive_period_action`, `negative_period_action` | In a characteristic-zero field with \(x^{69}=1\), \(x^{23}\ne1\), \(x^3\ne1\), the units modulo 69 fixing \(U_+(x)\) are exactly the 22 elements of \(H\). The other 22 exchange the signs. The two actions on period sums require only \(x^{69}=1\). |
| `CircularFactor69.period_theta_quadratic`, `positive_factor_at_generator`, `positive_signed_value`, `negative_signed_value` | At any root of \(P\) in a commutative ring, \(\theta^2=\theta+17\), the displayed monic degree-22 positive factor vanishes at \(x\), and \(U_+=11+3\theta\), \(U_-=14-3\theta\). This labels each conjugate before reduction. |
| `CircularNorm69.primitive_companion_columns`, `signed_product_eq_embedded_companion_determinant` | In a field under the three order tests above, each of 22 columns evaluates to \((1-x)x^j\) for \(0\le j<22\). The signed product equals the embedded determinant calculated by Laplace expansion of this explicit matrix. |
| `CircularBasisData69.basis_inverse`, `inverse_basis`, `CircularBasis69.relative_basis_at_primitive` | The integer matrix from the two blocks \(x^j,\theta x^j\), \(0\le j<22\), to the 44 ordinary monomial coordinates has an explicit two-sided integer inverse. The coordinate maps are inverse on **all** vectors over any commutative ring. Under the three order tests in a field the inverse change also preserves evaluation at \(x\). To transfer linear independence to field elements, instantiate the ordinary rational monomial basis in the actual cyclotomic field. |
| `CircularFrobenius69.reduced_factor_root_period`, `reduced_factor_rabin_tests` | In a field of characteristic 5, for \(t^2=t+17\) and either explicit factor zero at \(x\), the Frobenius orbit of \(x\) has exact length 22. In particular it does not close at 2 or 11. |
| `CircularReduction69.reduce_pow`, `reduce_positive`, `reduce_negative`, `signed_classes_multiply_one` | Evaluation at 21767 descends from integer polynomials modulo \(P\) to the ring of residues modulo 114679, preserves powers, and takes the signed classes to 48891 and 65813. The two classes multiply to one already in the source quotient. |
| `CircularNonpower69.signed_nonpowers`, `CircularPowerDescent69.quadratic_units_not_powers`, `signed_classes_not_powers` | For every candidate in the indicated ring, its 277th power differs from each signed element. The three rings are the finite residue ring, the quadratic order in coordinates, and the integral conductor-69 presentation. The finite theorem proves Fermat for arbitrary nonzero residues by descent; it has no order hypothesis on the candidate root. |
| `CircularAmbient69.signed_units_in_ambient`, `signed_nonpowers_in_ambient`, `recover_first_generator`, `recover_second_generator` | In \(B=\mathbb Z[X,Y]/(\Phi_{69}(X),\,1+Y+\cdots+Y^{276})\) in the project's explicit quotient representation, the two signed units are inverse and neither has a 277th root in \(B\). Reduction sends \((X,Y)\) to \((21767,49063)\). The joint generator \(Z=XY^{273}\) reduces to 46656, and its powers \(Z^{277},Z^{69}\) recover the two generators. |
| `CircularPowerDescent69.degree276_norm_obstruction` | An alternative transfer to an overfield takes a norm followed by reduction which respects 277th powers and sends the proposed unit to \(48891^{276}\). The lemma proves nonpower from these two hypotheses. The construction on the actual overfield remains an input. |

**Current arithmetic obligations.** Realize the primitive roots of orders 69 and 277 in a shared characteristic-zero field with its rational conjugation. For the standard conductor-19113 model, take the 277th and 69th powers of a primitive 19113th root, respectively. Verify the conjugation acts by inversion on the roots and takes the two imaginary quadratic generators to their negatives. Instantiate `CircularSinnott69.real_circular_unit` and identify its generated real carrier with the intended real subfield. To compare the intersection norm operators with a library-defined norm, identify the carrier of the intersection and use the finite Galois norm-product formula. For the definition indexed by divisors of the field conductor, also show that 69 divides that conductor. The quadratic subfield has fundamental discriminant 69. To transfer the nonpower result via the degree-276 norm, construct that field norm and its action on embedded quadratic elements. The full projected unit system and class-group comparison remain open. [Sinnott's norm generators, §2](https://www.dml.cz/bitstream/handle/10338.dmlcz/133268/MathSlov_55-2005-1_4.pdf) · [Standard Galois norm-product formula](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Norm/Transitivity.html#Algebra.norm_eq_prod_automorphisms)

## Dyadic Shape — residue shape, valuation rule and layer-two tests for every pair (q,d)

Owner: Dyadic Shape, the session of 2026-11-21 working from `proof-handoff-2026-11-21/READ_FIRST.md`. Manuscript: [Dyadic_Residue_Shape.md](../Dyadic_Residue_Shape.md). Frozen predictions, tests and logs: [dyadic_shape/RESULTS.md](../dyadic_shape/RESULTS.md). No existing module was edited; `checkpoint.py` and `Reimann.lean` each gained the three module names.

### Statements

Let q ≡ 3 (mod 8) and d ≡ 7 (mod 16) be primes, m = qd, and P = T² + C_1 T + C_0 Mizusawa's polynomial of Q(√−m) for the generator γ ↔ 5.

**Theorem 1 (paper proof, manuscript §3).** (q/d) = −1 ⟹ (C_0, C_1) ≡ (2, 0) (mod 4). (q/d) = +1 ⟹ (C_0, C_1) ≡ (0, 2) (mod 4). Mizusawa proves the statements about C_0 and records the ones about C_1 as a numerical observation for qd < 5000 (p. 134).

**Theorem 6 (algebra, manuscript §6).** If (C_0, C_1) ≢ (0, 0) (mod 4) and ω lies in (2, T), then (2,T)/ωO ≅ C_{2^{e_1}} ⊕ C_{2^{e_2}} with e_1 = ⌈ν_min⌉ − 1 and e_2 = ⌊ν_max⌋, where ν_min ≤ ν_max are the 2-adic valuations of ω at the two roots of P. With Theorem 1 and Appendix A.1 this gives every strict group A_{2,r}(E_a), r odd: 0, C_2, then C_{2^a} ⊕ C_{2^a} when (q/d) = −1; C_{2^a} ⊕ C_{2^{a+1}} when (q/d) = +1 and h(−4m) ≡ 8 (mod 16); and C_{2^{a+1+μ}} ⊕ C_{2^{a+2+M}} when 16 | h(−4m), with μ ≤ M the valuations of r − r_0 and r − r_1 at the two 2-adic zeros.

### Lean proof terms

All are named theorems. None is an executable guard. Their hypotheses are the congruences displayed in their signatures and nothing else.

| Module | Declarations | Exact scope |
|---|---|---|
| [DyadicResidueShape](Reimann/DyadicResidueShape.lean), 28 breakpoints | `split_lattice_iff`, `eisenstein_lattice_iff`; `rank_split`, `rank_eisenstein`; `x_residue`, `pistar_norm`, `unit_square_classes`, `pistar_nonsquare_pos`, `pistar_nonsquare_neg`; `eisenstein_profile`, `eisenstein_quartic`, `split_quartic`, `split_profile`, `inert_profile`; `split_shape`, `eisenstein_shape`, `eisenstein_weight_profile`, `inert_weight_profile` | Lemma A: the two lattices lie in 4ℤ² exactly when C_1 ≡ 2 (mod 4). The 𝔽₂-kernels of the two Rédei matrices as functions of one bit. Congruences for d = x² − 2y². The profile (k, l, h) at every odd weight from the residues of (C_0, C_1). |
| [DyadicContent](Reimann/DyadicContent.lean), 22 breakpoints | `smith_two_by_two`, `regular_smith`, `strict_smith`; `eisenstein_distance`, `inert_distance`, `split_distance`; `gamma_sq`, `gamma_sq_one_mod_two`; `eisenstein_layer_one`, `eisenstein_quartic_factor`, `inert_layer_one`, `split_layer_one`, `split_quartic_factor`; `sq_one_mod_four`, `higher_layer_twice_unit`; `unit_mul`, `unit_mul_parity` | Over ℤ: explicit unimodular matrices bringing the matrix of ω to diag(g, g·n), n = 2a² − c1·ab + c·b². The valuation of n in each residue shape. Content and primitive part of ω₁ and of the quartic factor. Every later factor is twice a unit, for all c0, c1. |
| [DyadicShapeBridge](Reimann/DyadicShapeBridge.lean), 6 breakpoints | `InertShape`, `samples_of_inert_shape`, `samples_iff_inert_shape`, `inert_lattice_invariant_factors`, `inert_strict_dual_invariant_factors` | `WeightOneSamples c0 c1 ↔ c0.residue 2 = 4 ∧ c1.residue 1 = 2`, and the two matrix-chain theorems restated under that shape hypothesis. |

Last passing breakpoints: `DyadicResidueShape.complete`, `DyadicContent.complete`, `DyadicShapeBridge.complete`. Lean 4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, and separately Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; ledgers `compat-<version>-<module>.json`. Reported axioms: propext, Classical.choice, Quot.sound. Combined target `elan run leanprover/lean4:v4.36.0 lake --rehash build`: 494 jobs, passed. The combined target was not run on 4.33.1.

### Executable checks (Python 3.14.0, numpy 2.3.5; not proof terms)

Predictions were written and hashed before the code that tests them existed (`dyadic_shape/freeze_ledger.txt`). Test set: the 14,022 pairs with 5000 < qd < 10⁶. None failed.

| Check | Result |
|---|---|
| Theorem 1 on the test set, Stickelberger row at level 10 | 7038 + 6984 pairs, 0 exceptions |
| Class numbers by reduced forms: h(−4m) ≡ h(−8m) (mod 16) for (q/d) = +1, both ≡ 4 (mod 8) for (q/d) = −1 | 14,022 pairs, 0 exceptions |
| Weight profile at r = 1 from Bernoulli sums alone, first 150 test pairs | 0 exceptions |
| The six symbol identities and both matrix ranks of the proof | 14,123 pairs |
| 2-class groups of ℚ(√2, √−m) and of the cyclic quartic field of conductor 16m, by explicit ideals, five fields | all ten as predicted |
| 2-class group of the degree-8 layer k₂, its quotient by the prime above 2, and the marked relation γ² + aγ + b = 0, five fields | all as predicted |
| Theorem 6, its ideals and the path of the vertex: random coefficients at 40 binary digits and all test fields | all assertions pass |

### Formal obligations of the paper proof of Theorem 1

None of these is formalized. A Lean theorem above proves only its displayed algebra.

- **O1.** Mizusawa, Theorem 2.2: X(k_∞) ≅ ℤ/2 ⊕ ℤ₂[T]/(P) as a module over the Iwasawa algebra, with C_0, C_1 ∈ 2ℤ₂, complex conjugation acting by −1, and v(C_0) = v(h(−4m)) − 1.
- **O2.** For a subfield M of k_∞ with k_∞/M a ℤ₂-extension generated by g and totally ramified at the prime above 2: A(M) ≅ X/(g − 1)X (Washington, Proposition 13.22). Used for M = ℚ(√2, √−m) with g = γ², and for the cyclic quartic field F′ = ℚ(√(−m(2+√2))) with g = γ²σ.
- **O3.** Chevalley's ambiguous class formula for K/ℚ(√2), K one of these two fields: A(K)[2] has order 8 and is generated by the classes of the ramified primes with one relation.
- **O4.** Genus theory over ℚ(√2): the unramified quadratic extensions of K are K(√δ) for δ in the rank-three groups ⟨−1, π*, π′*⟩ and ⟨−q, π*, π′*⟩, and 4-rank A(K) = 3 − rank of the 3 × 3 character matrix.
- **O5.** The quadratic-symbol evaluations of manuscript §3.3, items 2, 4, 5 and 6. Items 1 and 3 are `x_residue` and `pistar_nonsquare_pos`, `pistar_nonsquare_neg`. All six are evaluated from their definitions on 14,123 pairs by `dyadic_shape/check_redei_symbols.py`.

A Lean statement of Theorem 1 needs the module of O1 as an object; that construction belongs to the tower work of Continue Mathematical Analysis and Continue Agent Notes.

To apply Theorem 6 to an arithmetic strict group one also needs the identification of Appendix A.1, A_{2,r}(E_a)^∨ ≅ X/D_aY, and (P) = (Φ). For conductor 69 the first is the `Presentation` input traced below.

### Conductor 69: the `Presentation` input traced back

`DyadicStrictDualAdapter.Presentation c0 c1 w a G` asks for an additive surjection `project` from coordinates in the basis (2b, c) onto the strict dual, with kernel the preimage of D_aY.

- **The map.** The limit of the finite-layer Artin maps on the 2-class groups of k_n and K_n, `DyadicArtinLimit69.continuous_artin` (Round 4 above), which gives Y = ℤ₂b ⊕ ℤ₂c, X = ⟨2b, c⟩ and the strict dual X/(J^{2^a} − 5^{−r·2^a})Y at positive odd r.
- **Exact kernel.** For c0 ≡ 4 (mod 8), c1 ≡ 2 (mod 4): D_aY = 2^{a+1}Y for every a ≥ 1 and D_0Y = 4ℤ₂b + ℤ₂c. This is the matrix owner's statement; it now has shape-level proof terms over ℤ in `DyadicContent.inert_layer_one`, `split_quartic_factor` and `higher_layer_twice_unit`, and holds for every pair of that shape. The preimage under (u, v) ↦ (2u, v) is 2^a ℤ₂ × 2^{a+1} ℤ₂, which is `Factors a`.
- **Surjectivity.** 2b and c generate X, so `onto` is surjectivity of the Artin limit onto X. It is the finite-layer statement already assumed in `continuous_artin` ("full finite symbols surjective with the stated full kernel").
- **The coefficient hypothesis.** `WeightOneSamples c0 c1` is equivalent to the two residue conditions (`samples_iff_inert_shape`). Both existing bottom routes are kept. Route one, `DyadicControlJet69.samples_from_bottom_control`, takes C_1 mod 4 = 2 from the printed example of p. 134; Theorem 1 proves that congruence on paper for every pair with (q/d) = +1, here (3/23) = +1. Route two, `DyadicTwistedControl69.samples_of_two_bottom_controls`, takes the reduced-form counts for −276 and −552; in general P(0) = C_0 and P(−2) = C_0 − 2C_1 + 4 determine C_1 modulo 4 exactly when 4 | C_0. When C_0 ≡ 2 (mod 4) the two bottoms do not determine it and a third bottom, the cyclic quartic field F′ with generator γ²σ, is needed; that is how Theorem 1 is proved in that case.
- **The commutator.** `DyadicArtinPlace69.split_artin_commutator` and `DyadicMizusawaHandoff69.field_commutator_coordinates` are reused unchanged. In the coordinates α = a², β = b², c of H = X(K_∞) the commutator of b with the inertia generator is α − c (manuscript §2). Nothing was recomputed.

### Conductor 2893

Shape IIb: 16 | h(−4·2893), the two zeros satisfy r_0 ≡ 7 and r_1 ≡ 3 (mod 8), and `PairedOrders.signed_valuations` is k = 3 + v(r − r_0), l = 3 + v(r − r_1).

A marked relation was tested, not only an order. In the degree-8 layer k₂, with explicit ideals: A(k₂) ≅ C_2 ⊕ C_16 ⊕ C_16, the prime above 2 has class of order two, the quotient is C_16 ⊕ C_16, and for the primes above 47, 191, 193, 241 the pairs (a, b) modulo 16 with γ²c + aγc + bc trivial in the quotient form exactly the predicted set {(0, 7)}: γ² acts as 9. All 256 pairs were tried for each prime.

Prepared analytic ideal against actual characteristic ideal: the coefficients from the Stickelberger row, (4776, 2834) modulo 2^13, which reduce to (40, 18) modulo 64, agree with the ideal classes in group order, invariant factors and the relation modulo 16. This is agreement through layer two only. Layer two does not separate γ from γ^{−1} for this field; the two orientations give Δ ≡ 23 and Δ ≡ 7 (mod 32) and first differ at layer three, which was not computed. `SignedFieldComparison2893.characteristic_bits` remains with Continue Agent Notes.

For (227,23) the same test does fix the orientation: the relation of the inverse generator, (6, 3) modulo 8, is not in the set found.

### Branches not touched

The verified common field of order 19113 and its norm, the Artin comparison at 277, and the cubic branch were not used or changed. The Gemini E1 report is a separate analytic branch: its row bound matches item 1 of `RH_RECONSTRUCTION_HANDOFF_2026-11-21.md` (line 14), the report stops before `ErrX5at` and `UBar5`, and no `.lean` file in this repository contains `on_core_sharp`, `sharpRowBound`, `LeafJSumCap`, `dyadicBracket`, `ErrX5at` or `UBar5`. It has no proof-level consumer here and nothing above depends on it.

### Review of the matrix chain

Fifteen modules from `Dyadic` to `DyadicStrictDualAdapter`, 2222 lines, 145 theorems.

1. Every use of `WeightOneSamples` passes through `DyadicOrder.moment_coefficient_bits`. The chain is a function of two residues and of s ≡ 1 (mod 4). Stating its hypothesis as `InertShape` makes it a theorem about a shape instead of one field.
2. `Dyadic.values_3_23`, a `decide` over 1104 terms with raised recursion and heartbeat limits, is the dominant cost and only feeds the two residues. With the shape hypothesis the chain does not need it.
3. Unused downstream: `Dyadic.values_3_7`, `Dyadic.residue_dichotomy`, and lines 16 to 74 of `DyadicBottom`.
4. The residue-to-parameter conversion is written in three or four places, the encode/decode/add boilerplate three times, and layer zero and the positive layers are separate code paths. `DyadicContent.strict_smith`, one distance theorem and `higher_layer_twice_unit` are a single path for all layers and all three shapes at the level of integer identities. What the chain adds, and what should be kept, is the transport to quotients of `Scalar` lattices with their addition.
5. `DyadicBaseFactors`, `DyadicPositiveFactors`, `DyadicMatrixImage`, `DyadicStrictRelation`, `DyadicStrictKernel`, `DyadicMatrixHandoff` and `DyadicStrictDualAdapter` have no `compat-*.json` ledger in this checkout. Lake built all of them on both compilers as the dependency closure of the bridge, which checks whole modules, not single declarations.
6. A proof pattern that is fast and identical on both compilers: an explicit polynomial witness, then `grind`, then `omega`. `dyadic_shape/poly_witness.py` computes the witnesses. The 56 new breakpoints need no option changes.

### Open, and the next step

- `DyadicContent.strict_groups_of_shape` (reserved above): the induction over layers, then its transport to `Scalar`.
- The structure of K_{2r}(O_{E_a}){2} as a module; only its order is derived, conditionally (manuscript §9, item 3).
- Layer three for 2893, to decide the orientation on class groups.
- The rank-three module upstairs: no computation.
- The second binary digit of (C_0, C_1): no rule was found; on the test set it is equidistributed and is not a function of d modulo 16q, 32q, 64q or 128q for q = 3, 11.
- Earlier work. For (q/d) = +1 the C_1 statement of Theorem 1 is equivalent to: 16 | h(−4qd) exactly when 16 | h(−8qd). Congruences modulo 16 between h(−4pq) and h(−8pq) for pq ≡ 1 (mod 4) were studied by Hardy and Williams (J. Number Theory 1987 and related papers). A search on 2026-11-21 found the references but the scanned text could not be read here, so it is not known whether this case is covered; it may be a known congruence reached by a new route. For (q/d) = −1 the statement is that the cyclic quartic field of conductor 16qd has 2-class number 16; no source was found, and the search was not exhaustive.
