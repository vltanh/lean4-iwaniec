# Guerra: the quasiconvexity of `L` for Hessians

## Source

A. Guerra, *Quasiconvexity of the Burkholder function on symmetric matrices*, preprint,
[arXiv:2608.23388v1](https://arxiv.org/abs/2608.23388) (2026), read in part (the TeX source).

## Statement (`TheoremL.lean`)

- `External.Guerra.theorem1_1`: Guerra's Theorem 1.1 (labelled `thm:L` in its TeX), as Guerra
  states it: for every `A ∈ ℝ^{2×2}` and every `u ∈ C_c^∞ (ℝ²)`,
  `∫_{ℝ²} [L (A + D²u) − L (A)] dx ≥ 0`. It is a claim of a preprint.

## How the paper uses it

The paper (arXiv:2609.28311, TeX line 285) remarks that the case `φ = Du`, `u ∈ C^∞_per (Q)`, of its
Theorem 1 "had been proved in [Guerra2026b]". Guerra states it for compactly supported `u` on
`ℝ²`; the two forms are equivalent at every `A` (`Agazzi.theorem1_hessian_iff`; report, E1). No
proof of the paper uses the remark. The paper also cites Guerra's preprint for the details of
Corollary 2; that use is in the package `HarmonicAnalysis` (see `BaernsteinMontgomerySmith/`).

## Argument used

Not Guerra's, which uses Morse theory. The theorem follows from the paper's Theorem 1, for
`φ = Du` (`Agazzi.theorem1_hessian`), and the passage from periodic to compactly supported test
functions, the second-order form of Dacorogna's Proposition 5.13 (*Direct Methods in the Calculus
of Variations*, 2nd ed., 2008), in the package `CalculusOfVariations`
(`CalculusOfVariations.hessian_periodic_iff_hasCompactSupport`).
