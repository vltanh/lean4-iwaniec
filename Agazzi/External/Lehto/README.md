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

Not Lehto's. The proof (`LowerBound.lean`) has two halves:

- `‖𝓑‖_p ≥ p − 1`: the case `n = 1` of Dragičević's lower bound `‖𝓑^n‖_p ≥ κ_n (p)`
  (O. Dragičević, Arch. Math. 96 (2011), 463–471, Theorem 1.1; `κ₁ (p) = p − 1`), in the package
  `HarmonicAnalysis` (`HarmonicAnalysis.sub_one_le_beurlingPowNorm_one`), which follows
  Dragičević's proof with the test functions of that paper for `n = 1`. On the unit disc these are
  the extremal functions `f_α (z) = z |z|^{−2α}`, `0 < α < 1/p`, of Baernstein–Montgomery-Smith
  (1999, §1; arXiv:math/9709215v2):
  - `∂f_α = (1 − α) |z|^{−2α}` and `|∂̄f_α| = α |z|^{−2α}` on the punctured disc, so that
    `‖∂f_α‖_p / ‖∂̄f_α‖_p → (1 − 1/p) / (1/p) = p − 1` as `α → 1/p`;
  - `‖∂f_α‖_p ≤ ‖𝓑‖_p ‖∂̄f_α‖_p`, by `𝓑 (∂̄φ) = ∂φ` for Schwartz `φ` and Schwartz approximations
    of `f_α` in `W^{1,p}`.
- `‖𝓑‖_p ≥ p' − 1 = 1/(p − 1)`: duality, `‖𝓑‖_p = ‖𝓑‖_{p'}`
  (`HarmonicAnalysis.beurlingPowNorm_conjExponent`), in place of the conjugates `f̄_α` that
  Baernstein and Montgomery-Smith use.

## Shorter routes

Duality replaces the second family `f̄_α` and its approximation.
