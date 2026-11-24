# Lehto: the lower bound `‖𝒮‖_p ≥ p* − 1`

## Source

O. Lehto, *Remarks on the integrability of the derivatives of quasiconformal mappings*, Ann. Acad.
Sci. Fenn. Ser. A I No. 371 (1965). The paper (arXiv:2609.28311, TeX line 320) cites it for the
lower bound in `(eq:BA-sharp-norm)`. The source was not available and has not been read.

## Statement

`External.Lehto.lowerBound` (`LowerBound.lean`): for `1 < p < ∞`,
`ENNReal.ofReal (max p (p / (p − 1)) − 1) ≤ HarmonicAnalysis.beurlingPowNorm 1 p`, where
`beurlingPowNorm 1 p` is the norm of the Beurling–Ahlfors transform (symbol `ξ̄ / ξ`) on `L^p (ℂ)`,
the supremum of `‖𝓑f‖_p / ‖f‖_p` over Schwartz functions `f`.

## Argument used

Not Lehto's. The proof follows Baernstein–Montgomery-Smith (1999, §1; arXiv:math/9709215v2), with
the density lemma of the package `HarmonicAnalysis`:

- The test functions are `f_α (z) = z |z|^{−2α}` on the unit disc, `0 < α < 1/p`: the extremal
  functions of Baernstein–Montgomery-Smith (Guerra's `v_α`, arXiv:2608.23388). Outside the disc
  they are continued by Dragičević's cutoff `g₂` (2011, p. 465) rather than by `1/z̄`
  (`External.Lehto.extremalFun`, `TestFunctions.lean`).
- On the punctured disc, `∂f_α = (1 − α) |z|^{−2α}` and `|∂̄f_α| = α |z|^{−2α}`, so that both
  integrals `∫_Δ |∂f_α|^p`, `∫_Δ |∂̄f_α|^p` equal `π / (1 − αp)` times `(1 − α)^p`, resp. `α^p`.
  The integrals outside the disc stay bounded, and `‖∂f_α‖_p / ‖∂̄f_α‖_p → (1 − 1/p) / (1/p) = p − 1`
  as `α → 1/p`.
- `‖∂f_α‖_p ≤ ‖𝓑‖_p ‖∂̄f_α‖_p`: `𝓑 (∂̄φ) = ∂φ` for Schwartz `φ`, and the density lemma
  `HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto` with `k = 1`, applied to the Schwartz
  functions `φ_k (z) = z K_k (|z|²)`. The profiles `K_k` are those of the package's approximations
  of Dragičević's `f_{2,α}` (`HarmonicAnalysis.BeurlingAhlfors.approxProfile`), unchanged; only
  their first derivatives are used, and dominated convergence gives `∂φ_k → ∂f_α`,
  `∂̄φ_k → ∂̄f_α` in `L^p`.
- Hence `‖𝓑‖_p ≥ p − 1` (`External.Lehto.sub_one_le_beurlingPowNorm_one`). The other half,
  `‖𝓑‖_p ≥ p' − 1 = 1/(p − 1)`, is duality, `‖𝓑‖_p = ‖𝓑‖_{p'}`
  (`HarmonicAnalysis.beurlingPowNorm_conjExponent`), in place of the source's conjugates `f̄_α`.

## Shorter routes and reuse

- Duality replaces the second family `f̄_α` and its approximation.
- The package's `n = 2` approximation machinery applies to `n = 1` as it is, with the monomial `z`
  in place of `z²`. `External.Lehto.sub_one_le_beurlingPowNorm_one` is the `n = 1` case of
  Dragičević's theorem, `κ₁ (p) = p − 1 ≤ ‖𝓑‖_p`, listed as a planned extension of
  `HarmonicAnalysis`, and the two modules here could move there.
