# `Agazzi/Basic/`: general mathematics

Lemmas that say nothing about the paper's objects, filed by field. They are in the namespace
`Agazzi` (not the package's, to avoid future clashes) and could be contributed as follows.

| Module | Content | Natural home |
| --- | --- | --- |
| `Analysis/Calculus/Periodic.lean` | for `ℤ^m`-periodic functions on `ℝ^m`, integrals over `(0,1)^m`: translation invariance, `∫_Q ∂_v f = 0`, `∫_Q ∇φ = 0`, the periodic null Lagrangian `∫_Q det (A + ∇ψ) = det A` | lean4-calculus-of-variations |
| `Analysis/Calculus/LipschitzFDeriv.lean` | Lipschitz functions: the derivative vanishes a.e. on the zero set; the derivative of `max (f, g)` is a.e. one of the two derivatives; difference quotients and their integrals converge (dominated convergence) | Mathlib (`Analysis/Calculus/Rademacher`) or lean4-calculus-of-variations |
| `Analysis/Calculus/GradientConstraint.lean` | periodic Lipschitz `ξ` with `p + Dξ ∈ K` a.e.: the slope characterization `ξ (y) − ξ (x) + p · (y − x) ≤ H_K (y − x)`, the uniform Lipschitz bound, pointwise limits of a.e.-convergent equi-Lipschitz periodic sequences | lean4-calculus-of-variations |
| `Analysis/Convex/SupportFunction.lean` | the support function `H_K` of a compact convex `K ⊂ ℝ^m`: attainment, sublinearity, Lipschitz bound, `a ∈ K ⇔ a · y ≤ H_K (y) ∀ y`, `∇H_K ∈ K` | Mathlib (`Analysis/Convex/`) |
| `MeasureTheory/Periodic.lean` | a periodic property that holds a.e. on `(0,1)^m` holds a.e. on `ℝ^m` | Mathlib or lean4-calculus-of-variations |
| `Topology/MetricSpace/Periodize.lean` | `supPeriodize`: the periodization of a function supported in a ball of radius `< 1/2`, Lipschitz with the same constant | lean4-calculus-of-variations |

Together with Lemma 4 (`Agazzi/Proof/ScalarProjection/`), these modules make up the
gradient-constrained `L²` projection on the torus, a standard tool of the calculus of variations;
the package lean4-calculus-of-variations is its natural home.
