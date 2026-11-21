# Dyadic and Pell proof checkpoints

The Lean project at this level contains the target `ReimannWindow.DyadicChecks`. Its five modules use Lean's core and standard library. Each theorem has a named breakpoint in its source file. Open the project folder in VS Code and place the cursor inside a proof to inspect its state in Lean Infoview.

## What the calculations establish

| Module | Conclusion | Inputs and scope |
|---|---|---|
| `CharacterSums` | The triples of signed moments at conductors 69 and 552 are `(0,0,3312)` and `(0,0,680064)`. The depleted, normalized arithmetic gives −36 and −308. | Exact finite sums. The module proves the denominator-cleared integer equalities. Identifying them with interpolated special values requires the Bernoulli and Iwasawa formulas. |
| `DyadicBaseMatrix` | For a monic quadratic modulo eight, its values at 4 and 2 are both 4 exactly when its constant coefficient is 4 modulo eight and its linear coefficient is 2 modulo four. The normalized first difference has determinant one modulo two. Every later complementary factor is twice the identity modulo four. | All coefficient choices satisfying the displayed residues and every odd scalar. The proof uses repeated squaring and an induction over every positive layer. |
| `DyadicLayerGrowth` | If the first difference is four times a surjection and each complementary factor is twice a surjection, the image at layer $a\ge1$ is exactly the image of $a+1$ doublings. | The theorem takes the two surjectivity statements as hypotheses. It proves the operator identity and the induction. |
| `LatticeQuotient` | In the integer lattice with coordinates $(2x,y)$, reduction by the ambient lattice $2m\mathbb Z^2$ gives independent residues modulo $m$ and $2m$, for $m>0$. | Explicit maps in both directions with proofs of inverseness and addition preservation. Applying this integer model to the strict group requires its arithmetic presentation. For $m=2^a$, the counting bijection gives $2^{2a+1}$ elements. |
| `PellCertificate` | For $D=2\cdot19\cdot16871=641098$, an explicit integral solution of $x^2-Dy^2=1$ has local residues 2 and 5 modulo nine. Removing the signs gives 7 and 4. Each positive integer lift $u$ of either residue satisfies $v_3(u^{3^n}-1)=n+1$ for all $n\ge0$. | Lean checks the large integer witness, the two roots modulo nine, and the induction by cubing. The final statement is expressed as divisibility by $3^{n+1}$ and failure of divisibility by $3^{n+2}$. |

## Running a breakpoint

The upstream project pins Lean 4.33.1. The included compatibility record identifies the Lean 4.36.0 compiler and the SHA-256 hash of every accepted source prefix. The pinned release has its own record. The runner audits each theorem's axiom report and stops at the first failure. Editing a proof changes the hashes of the affected prefixes.

```shell
python check_dyadic_breakpoints.py --list
python check_dyadic_breakpoints.py --comparison-version 4.36.0 --through conductor552Moments
python check_dyadic_breakpoints.py --comparison-version 4.36.0
elan run leanprover/lean4:v4.36.0 lake build ReimannWindow.DyadicChecks
```

For the pinned release, omit `--comparison-version`. Use `--fresh` for a full replay. A single theorem's successful check proves its displayed statement with its stated hypotheses.

## Open arithmetic breakpoints

1. Identify the explicit signed moments with the two interpolated special values, then identify their valuations with those of the actual characteristic polynomial $P$. The finite matrix calculation accepts the resulting congruences. The relevant source for the Iwasawa module and its normalization is [Mizusawa, Theorem 2.2 and §4.2](https://www.numdam.org/item/10.5802/jtnb.707.pdf).
2. On the actual $ℤ_2$-lattice, lift the normalized matrices with invertible reduction to surjective endomorphisms. Instantiate the two surjectivity inputs of `dyadic_difference_image`. Connect the integer residue-coordinate calculation to the $2$-adic lattice quotient.
3. Identify the Pontryagin dual of the strict group with $X/(\gamma^{2^a}-5^{-r2^a}I)Y$, including the comparison of the two local restrictions. The separate base-layer argument and the even-weight descent also need arithmetic formalization.
4. For the Pell example, put the explicit unit in both completions, identify its images under local reciprocity, and apply the cyclic ambiguous class number formula with the base class group and ramification data. The source for that formula is [Li and Yu, Theorem 2.1](https://www.numdam.org/item/10.5802/jtnb.1133.pdf).

The exact examples test the proposed arithmetic mechanism. The moving-field, all-weight estimate for the complementary odd-primary contribution is a separate open mathematical step in the RH argument.
