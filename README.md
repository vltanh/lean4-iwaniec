# Iwaniec's conjecture in Lean: the quasiconvexity of `L` and the `L^p` norm of the Beurling–Ahlfors transform

The paper formalized here is A. Agazzi, K. Astala, R. Bañuelos, G. Bruno, G. Cassese, D. Faraco, A. Guerra, M. Hormozi, B. Kirchheim, A. Koski, V. Kovač, J. Kristensen, F. Pasqualotto, I. Prause, E. Saksman, V. Šverák, L. Székelyhidi, R. Tione, A. Volberg and H. Yang, *Sharp higher integrability theory, Part I: the `L^p`-norm of the Beurling–Ahlfors transform*, [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311) (preprint, October 2026).
- It claims Iwaniec's conjecture of 1982: the Beurling–Ahlfors transform `𝒮` has norm `p* − 1` on `L^p (ℂ)`, where `p* = max (p, p / (p − 1))`.
- It deduces the conjecture from the quasiconvexity of an integrand `L` on `ℝ^{2×2}` (Theorem 1). Writing `A z = a₊ z + a₋ z̄`, `L (A) = |a₊|² − |a₋|²` if `|a₊| + |a₋| ≤ 1` and `2|a₊| − 1` otherwise.

Every result of the paper is formalized and proved, in Lean 4 with Mathlib. This includes the results the paper cites, and nothing is assumed.
- The proofs follow the paper's, with one departure, which is waiting for the author's decision ([report, Section 7](docs/Agazzi/REPORT.md#7-departures-from-the-papers-proofs)).
- No Palomar preflight has been run, and nothing has been submitted.

## Status

| Part of the paper | Status |
| --- | --- |
| §1, Theorem 1: the quasiconvexity of `L` | proved, for `C^∞` periodic test maps (the paper's statement) and for Lipschitz periodic ones |
| §1, Corollary 2, first assertion: the quasiconvexity of `B_p`, `1 < p < ∞` | proved |
| §1, Corollary 2, second assertion: `‖𝒮‖_p = p* − 1` | proved |
| §2, Lemma 3: the row representation of `L` | proved |
| §2, Lemma 4: the scalar projection lemma | proved |
| Cited results (Kinderlehrer–Stampacchia, Baernstein–Montgomery-Smith, Lehto) | proved |

## Main results

Results marked (C) are theorems of the Challenge, [`palomar/Agazzi/Challenge.lean`](palomar/Agazzi/Challenge.lean).

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1 (C) | [`Agazzi.theorem1`](Agazzi/Theorem1.lean#L401) | `∫_Q [L (A + Dφ) − L (A)] ≥ 0` for every `A ∈ ℝ^{2×2}` and every `C^∞` `ℤ²`-periodic `φ : ℝ² → ℝ²` |
| Theorem 1, Lipschitz form | [`Agazzi.theorem1_lipschitz`](Agazzi/Theorem1.lean#L250) | the same for Lipschitz periodic `φ` |
| Corollary 2 (a) (C) | [`Agazzi.corollary2`](Agazzi/Corollary2/Quasiconvexity.lean#L424) | `∫_Q [B_p (A + Dφ) − B_p (A)] ≥ 0` for `1 < p < ∞` |
| Corollary 2 (b) (C) | [`Agazzi.corollary2_norm`](Agazzi/Corollary2/Norm.lean#L262) | `‖𝒮‖_{L^p (ℂ) → L^p (ℂ)} = p* − 1` for `1 < p < ∞` |
| Lemma 3 | [`Agazzi.lemma3`](Agazzi/Proof/RowRepresentation.lean#L220) | `L (A) = sup_{z ∈ 𝒵 (A¹)} G_z (A¹, A²)` |
| Lemma 4 | [`Agazzi.lemma4_exists`](Agazzi/Proof/ScalarProjection/Existence.lean#L198), [`Agazzi.lemma4`](Agazzi/Proof/ScalarProjection/Main.lean#L748) | the `L² (Q)`-projection on a gradient-constrained class exists, and satisfies `Dw = Dv` or `Dw ∈ ∂K` a.e. and `∫_Q Dw · (Dv − Dw) ≥ 0` |
| (quasiconvexity in the sense of the package CalculusOfVariations) | [`Agazzi.quasiconvex_integrandL`](Agazzi/Quasiconvex.lean#L69), [`Agazzi.quasiconvex_burkholderB`](Agazzi/Quasiconvex.lean#L75), [`Agazzi.quasiconvex_burkholder`](Agazzi/Quasiconvex.lean#L83) | `L`, and `B_p` for `1 < p < ∞`, are quasiconvex for Lipschitz test maps vanishing outside the unit cube; for `1 < p < 2`, so is `(\|a₊\| − (p − 1)\|a₋\|)(\|a₊\| + \|a₋\|)^{p−1}` |

The Challenge also states four compared theorems, all proved:
- `det A = |a₊|² − |a₋|²`;
- the operator norm is `|a₊| + |a₋|`;
- `|Q| = 1`;
- `𝒮 ∂_z̄ = ∂_z` on Schwartz functions.

It also states the two values of `p* − 1`.

**Comparison with the standard formulation.** Iwaniec's conjecture concerns the singular integral `𝒮 f (z) = −π⁻¹ p.v. ∫ f (w) (z − w)⁻² dA (w)`. This is the Fourier multiplier with symbol `ξ̄ / ξ`.
- The Challenge defines `𝒮` as that Fourier multiplier, using Mathlib's Fourier transform on `ℂ`. It proves `𝒮 ∂_z̄ = ∂_z`, the paper's characterization `(eq:BA-definition)`.
- It defines `‖𝒮‖_p` as the supremum of `‖𝒮 f‖_p / ‖f‖_p` over Schwartz functions, which are dense in `L^p`.
- The package HarmonicAnalysis proves that this supremum is the norm of the bounded extension (`HarmonicAnalysis.enorm_eq_multiplierNorm`). The Challenge does not restate that bridge.
- The torus `Q = ℝ² / ℤ²` is represented by `ℤ²`-periodic maps on `ℝ²`, with integrals over the open unit square.

**lean4-morrey.** [`Agazzi.quasiconvex_burkholder`](Agazzi/Quasiconvex.lean#L83) is, by definitional unfolding, the hypothesis `CalculusOfVariations.Quasiconvex (HomogeneousIsotropic.burkholder p)`, `1 < p < 2`, of the library `HomogeneousIsotropic` of [lean4-morrey](https://github.com/vltanh/lean4-morrey).
- lean4-morrey requires this project and uses that theorem.
- With it, a nonnegative, isotropic, positively `p`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is quasiconvex for every `p > 0` (`HomogeneousIsotropic.quasiconvex_of_rankOneConvex_of_pos`), with no hypothesis on the Burkholder function.

## What the audit found

| | Finding |
| --- | --- |
| E2 | Corollary 2 is not proved in the paper; the cited arguments work on the plane at `A = 0`, and the periodic case at every `A`, the case `p = 2` and the passage from the torus to `L^p (ℂ)` are left implicit |
| E3 | Lemma 4: the closedness in `L² (Q)` of the constraint class is asserted without argument |
| E1 | the attribution of the Hessian case to Guerra (arXiv:2608.23388): the theorem there is for compactly supported `u` on `ℝ²`, which is equivalent but not the periodic statement written |
| E4, E5 | Lemma 4: the sign change, and the ball that must embed in the torus, are left implicit |

The audit found no error and no missing hypothesis: six findings in all, the four rows above and the typos (E6). Each gap is filled in Lean; see the [report](docs/Agazzi/REPORT.md).

The proofs follow the paper's, except the passage from the torus to the plane in the upper bound for `‖𝒮‖_p`. That passage uses transference instead of the planar argument of the cited sources. It was chosen for economy, it is not forced, and it waits for the author's decision ([Section 7](docs/Agazzi/REPORT.md#7-departures-from-the-papers-proofs)).

## Trust

- `lake build` passes. No `sorry` remains outside the Challenge, where they are there by design, and there is no `axiom` and no `native_decide`.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of the library: each depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- The route check ([`scripts/route_check.py`](scripts/route_check.py)) compares the results that each formal proof uses with those that the paper's proof cites in the TeX source. It finds no difference.
- Comparator accepts the Solution under Lean's kernel and under NanoDa.
- AI agents reviewed the statements against the TeX source, and the proofs against the paper, independently of the provers. No person has reviewed the proofs.

## Dependencies

| Library | Pin | Used for |
| --- | --- | --- |
| Mathlib | `v4.36.0-rc2` | everything |
| [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations) | `b7a207a` | quasiconvexity, periodic and Dirichlet test maps, null Lagrangians, mollification, gradients of Lipschitz maps |
| [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis) | `90f1e01` | the Beurling–Ahlfors transform and its norm, `𝒮 ∂̄ = ∂`, torus multipliers, transference, duality, the density lemma |
| [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) | `dc3966c` | Burkholder's function and its majorization |

These are the pins of lean4-morrey, so that lean4-morrey can require this project.

## Palomar

The submission files are in [`palomar/Agazzi/`](palomar/Agazzi):
- [`Challenge.lean`](palomar/Agazzi/Challenge.lean);
- [`Solution.lean`](palomar/Agazzi/Solution.lean);
- [`comparator.json`](palomar/Agazzi/comparator.json);
- [`formalization.yaml`](palomar/Agazzi/formalization.yaml).

To run Comparator (it needs bubblewrap):

```sh
lake env lake comparator --config=palomar/Agazzi/comparator.json
```

Palomar's local metadata and source checks pass. Nothing has been submitted, and the preflight workflow has not been run.

## Building

Lean `leanprover/lean4:v4.36.0-rc2`:

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/Agazzi/paper_routes.tsv --accept docs/Agazzi/route_differences.tsv
```

## Layout

| Directory | Contents |
| --- | --- |
| [`Agazzi/`](Agazzi) | the Lean code: `Defs.lean` (the definitions of the Challenge), `Bridges.lean`, `Proof/` (§2: Lemma 3, Lemma 4), `Theorem1.lean`, `Corollary2/`, `Quasiconvex.lean`; `Basic/` (general lemmas, [README](Agazzi/Basic/README.md)); `External/` (the cited results, one directory per source, each with a README) |
| [`palomar/Agazzi/`](palomar/Agazzi) | the Palomar submission |
| [`docs/Agazzi/`](docs/Agazzi) | [`REPORT.md`](docs/Agazzi/REPORT.md), [`CREDITS.md`](docs/Agazzi/CREDITS.md), the routes of the paper's proofs |
| [`scripts/`](scripts) | the audit, the route check, the Challenge's copy of the definitions |
| `.github/workflows/` | CI and the Palomar preflight workflow |

## Related work and credits

- The integrand `L` is due to Burkholder (1989) and Šverák (1990).
- Baernstein and Montgomery-Smith (1999) showed that its quasiconvexity implies Iwaniec's conjecture.
- Guerra (arXiv:2608.23388, 2026, preprint) claims Theorem 1 for Hessians.
- No other formalization of the paper was found. Other formalizations of `𝒮` are listed in the [report, Section 10](docs/Agazzi/REPORT.md#10-the-paper-in-the-literature).
- The formalization was made by AI agents, at the request of the author and maintainer, The-Anh Vu-Le:
  - a main session (Claude Fable 5.2 in Claude Code) and a lead agent with sub-agents (Claude Opus 5.5);
  - following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill.

  No person has reviewed the proofs. See [`CREDITS.md`](docs/Agazzi/CREDITS.md).

License: Apache-2.0 ([LICENSE](LICENSE)).
