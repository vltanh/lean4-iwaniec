# Iwaniec's conjecture in Lean: the quasiconvexity of `L` and the `L^p` norm of the Beurling–Ahlfors transform

The paper formalized here is A. Agazzi, K. Astala, R. Bañuelos, G. Bruno, G. Cassese, D. Faraco, A. Guerra, M. Hormozi, B. Kirchheim, A. Koski, V. Kovač, J. Kristensen, F. Pasqualotto, I. Prause, E. Saksman, V. Šverák, L. Székelyhidi, R. Tione, A. Volberg and H. Yang, *Sharp higher integrability theory, Part I: the `L^p`-norm of the Beurling–Ahlfors transform*, [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311) (preprint, October 2026).
- It claims Iwaniec's conjecture of 1982: the Beurling–Ahlfors transform `𝒮` has norm `p* − 1` on `L^p (ℂ)`, where `p* = max (p, p / (p − 1))`.
- It deduces the conjecture from the quasiconvexity of an integrand `L` on `ℝ^{2×2}` (Theorem 1). Writing `A z = a₊ z + a₋ z̄`, `L (A) = |a₊|² − |a₋|²` if `|a₊| + |a₋| ≤ 1` and `2|a₊| − 1` otherwise.

Every result of the paper is formalized and proved, in Lean 4 with Mathlib. This includes the results the paper cites, and nothing is assumed.
- The proofs follow the paper's arguments or, where the paper only cites, the arguments of the cited sources ([report, Section 7](docs/Agazzi/REPORT.md#7-departures-from-the-papers-proofs)).
- Not formalized: the remarks of the introduction (Astala's area distortion as a consequence; the extensions to forms, to higher dimensions and to other integrands; the attribution of the Hessian case to Guerra), and the uniqueness of the projection, which no proof needs ([report, Section 9](docs/Agazzi/REPORT.md#9-not-formalized)).
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

Results marked (C) are stated in the Challenge, [`palomar/Agazzi/Challenge.lean`](palomar/Agazzi/Challenge.lean), as `AgazziChallenge.<name>`, and proved in [`Solution.lean`](palomar/Agazzi/Solution.lean) from the library theorem shown.

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1 (C) | [`Agazzi.theorem1`](Agazzi/Theorem1.lean#L401) | `∫_Q [L (A + Dφ) − L (A)] ≥ 0` for every `A ∈ ℝ^{2×2}` and every `C^∞` `ℤ²`-periodic `φ : ℝ² → ℝ²` |
| Theorem 1, Lipschitz form | [`Agazzi.theorem1_lipschitz`](Agazzi/Theorem1.lean#L250) | the same for Lipschitz periodic `φ` |
| Corollary 2 (a) (C) | [`Agazzi.corollary2`](Agazzi/Corollary2/Quasiconvexity.lean#L424) | `∫_Q [B_p (A + Dφ) − B_p (A)] ≥ 0` for `1 < p < ∞` |
| Corollary 2 (b) (C) | [`Agazzi.corollary2_norm`](Agazzi/Corollary2/Norm.lean#L378) | `‖𝒮‖_{L^p (ℂ) → L^p (ℂ)} = p* − 1` for `1 < p < ∞` |
| Lemma 3 | [`Agazzi.lemma3`](Agazzi/Proof/RowRepresentation.lean#L220) | `L (A) = sup_{z ∈ 𝒵 (A¹)} G_z (A¹, A²)` |
| Lemma 4 | [`Agazzi.lemma4_exists`](Agazzi/Proof/ScalarProjection/Existence.lean#L198), [`Agazzi.lemma4`](Agazzi/Proof/ScalarProjection/Main.lean#L748) | the `L² (Q)`-projection on a gradient-constrained class exists, and satisfies `Dw = Dv` or `Dw ∈ ∂K` a.e. and `∫_Q Dw · (Dv − Dw) ≥ 0` |
| (quasiconvexity in the sense of the package CalculusOfVariations) | [`Agazzi.quasiconvex_integrandL`](Agazzi/Quasiconvex.lean#L68), [`Agazzi.quasiconvex_burkholderB`](Agazzi/Quasiconvex.lean#L74), [`Agazzi.quasiconvex_burkholder`](Agazzi/Quasiconvex.lean#L82) | `L`, and `B_p` for `1 < p < ∞`, are quasiconvex for Lipschitz test maps vanishing outside the unit cube; for `1 < p < 2`, so is `(\|a₊\| − (p − 1)\|a₋\|)(\|a₊\| + \|a₋\|)^{p−1}` |

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

## What the audit found

| | Finding |
| --- | --- |
| E2 | Corollary 2 is proved by reference to arguments made on the plane; the periodic case at every `A`, the case `p = 2` and the passage from the torus to `L^p (ℂ)` are left implicit |
| E3 | Lemma 4: the closedness in `L² (Q)` of the constraint class is asserted without argument |
| E5 | Lemma 4: the ball of the construction must embed in the torus |
| E1 | a remark: the Hessian case is attributed to Guerra (arXiv:2608.23388), where it is stated for compactly supported `u` on `ℝ²`, an equivalent form |
| E4 | a remark: the sign change in Lemma 4 is left implicit |

The audit found no error and no missing hypothesis. Its findings are E1–E5 above and the typos (E6). E2, E3 and E5 are gaps, each filled in Lean; E1 concerns a remark of the introduction, which is not formalized. See the [report](docs/Agazzi/REPORT.md).

The proofs follow the paper's arguments, and those of the cited sources where the paper only cites them. The upper bound for `‖𝒮‖_p` follows the planar argument of Baernstein–Montgomery-Smith, from their Conjecture 2 to the norm, and Guerra's passage to `L^p (ℂ)` with cut-offs, in the gradient case ([Section 7](docs/Agazzi/REPORT.md#7-departures-from-the-papers-proofs)). A shorter proof of the upper bound, on the torus and by transference, is kept beside it and not used by the paper's results ([`Agazzi.beurlingNorm_le_of_torus`](Agazzi/Corollary2/NormTorus.lean); [report, Section 11](docs/Agazzi/REPORT.md#11-whats-next)).

## Trust

- `lake build` passes. No `sorry` remains outside the Challenge, where they are there by design, and there is no `axiom` and no `native_decide`.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of the library: each depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- The route check ([`scripts/route_check.py`](scripts/route_check.py)) compares, for each result, the paper's own numbered results that its formal proof uses with those that the paper's proof cites in the TeX source. It finds no difference. It does not compare results from the literature.
- Comparator accepts the Solution under Lean's kernel and under NanoDa.
- AI agents reviewed the statements against the TeX source, and the proofs against the paper, independently of the provers. No person has reviewed the proofs.

## Dependencies

| Library | Pin | Used for |
| --- | --- | --- |
| Mathlib | `v4.36.0-rc2` | everything |
| [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations) | `220f56c` | quasiconvexity, periodic and Dirichlet test maps, null Lagrangians, mollification, gradients of Lipschitz maps; the general toolkit of Lemma 4 and Theorem 1 (periodic integrals, derivatives of Lipschitz functions, gradient constraints, support functions, periodization) |
| [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis) | `495bafe` | the Beurling–Ahlfors transform and its norm, `𝒮 ∂̄ = ∂`, duality, the case `n = 1` of Dragičević's lower bound; the Cauchy transform of `C_c^∞` functions and the passage from `C_c^∞` to the norm by Guerra's cut-offs; torus multipliers and transference (for the shorter proof on the torus) |
| [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) | `dc3966c` | Burkholder's function and its majorization |

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
| [`Agazzi/`](Agazzi) | the Lean code: `Defs.lean` (the definitions of the Challenge), `Bridges.lean`, `Proof/` (§2: Lemma 3, Lemma 4), `Theorem1.lean`, `Corollary2/`, `Quasiconvex.lean`; `External/` (the cited results, one directory per source, each with a README). The general lemmas are in the packages (Dependencies) |
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
  - in a second round, a lead agent with six sub-agents (Claude Opus 5.5), for the planar proof of the upper bound and the move of general code into the packages;
  - following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill.

  No person has reviewed the proofs. See [`CREDITS.md`](docs/Agazzi/CREDITS.md).

License: Apache-2.0 ([LICENSE](LICENSE)).
