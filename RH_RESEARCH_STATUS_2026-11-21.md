# Reimann research status — 2026-11-21 UTC

See [the technical handoff](formal/RH_RECONSTRUCTION_HANDOFF_2026-11-21.md) for formulas, dependencies and exact proof status.

- **The arithmetic work does connect to RH.** The `winPairs` route uses analytic prime selection and then a strict-cohomology budget (`VWinAt`) for those same auxiliary primes. Conductors 69 and 2893 and the local example at 277 test specific pieces of that second input; their finite computations do not prove the uniform budget.
- **The sharper geometric estimate is another input to the same overall argument.** The read-only reconstruction tracks the E1 and E2 savings through the determinant and the pointwise error. The slope step can use the actual height gap, but removing its logarithm still requires a bound on spread in the real base lattice.
- **Verification boundary:** old arithmetic proofs and newer standalone checks are not integrated verification of this sharper route. No new end-to-end RH result is claimed here.

Related material: [prime-power window](Prime_Power_Window.md), [dyadic orders](Dyadic_Window_Orders.md), [tame strict descent](Tame_Strict_Descent.md), [compiler and arithmetic status](formal/PROOF_STATUS.md), and [coordination](formal/COORDINATION.md).


## Matrix checkpoint

For the conductor-69 dyadic model, Lean checks the invariant factors of the additive matrix quotient at every layer: C_(2^a) and C_(2^(a+1)), given the coefficient samples. At layer one this is C2 × C4. Applying it to the actual strict group takes a separate class-field identification. See [the proof handoff](formal/RH_RECONSTRUCTION_HANDOFF_2026-11-21.md#matrix-handoff) and [the matrix manuscript](Strict_Dyadic_Invariant_Factors.md).
