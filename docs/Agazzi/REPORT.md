# Audit of the paper and the formalization

Paper: A. Agazzi, K. Astala, R. Bañuelos, G. Bruno, G. Cassese, D. Faraco, A. Guerra, M. Hormozi, B. Kirchheim, A. Koski, V. Kovač, J. Kristensen, F. Pasqualotto, I. Prause, E. Saksman, V. Šverák, L. Székelyhidi, R. Tione, A. Volberg and H. Yang, *Sharp higher integrability theory, Part I: the `L^p`-norm of the Beurling–Ahlfors transform*, [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311).
- Version 2 is of 8 October 2026. Version 1, of 23 September 2026, differs only in its author list, according to the arXiv comment.
- The audit was made against the arXiv LaTeX source of v2 (`main.tex`). Line numbers are those of that file.
- Result numbers are the paper's: Theorem 1, Corollary 2, Lemma 3 and Lemma 4 share one counter.

Lean names are in the namespace [`Agazzi`](../../Agazzi) unless they begin with `External.`, `AgazziChallenge.` or a package's namespace.

Status of the formalization:
- Every result of the paper is proved: Lemma 3, Lemma 4, Theorem 1 and both assertions of Corollary 2.
- Theorem 1 and the first assertion of Corollary 2 are also proved for Lipschitz periodic test maps.
- Every cited result is proved, in [`Agazzi/External/`](../../Agazzi/External), by the arguments named in Section 2.
- Nothing is assumed: the formalization is unconditional.
- `lake build` passes. No `sorry` remains outside the Challenge, and there is no `axiom`.
- [`scripts/Audit.lean`](../../scripts/Audit.lean) checks that every declaration of the library depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- Comparator accepts the Solution against [`palomar/Agazzi/Challenge.lean`](../../palomar/Agazzi/Challenge.lean), under Lean's kernel and under NanoDa.
- No statement of the paper had to change.
- Every proof follows the paper's, except one step of the second assertion of Corollary 2. That step is a departure made for economy, waiting for the author's decision (Section 7).

## 1. Summary

| Kind | Findings |
| --- | --- |
| Errors | none |
| Gaps | E1: the Hessian case attributed to Guerra is the compactly supported statement of that preprint, not the periodic one written. E2: Corollary 2 is not proved; the cited arguments are planar, at `A = 0`. E3: the closedness of `𝒞` in `L² (Q)` is not argued. E4: the sign change in Lemma 4 is left implicit. E5: the ball of Lemma 4 must embed in the torus |
| Typos | E6 |
| Missing hypotheses | none |
| Redundant hypotheses | Lemma 4: `p ∈ K` is not used by the two assertions |
| Use of cited results | Kinderlehrer–Stampacchia: correct, once `𝒞` is closed (E3). Baernstein–Montgomery-Smith: correct; their arguments are applied in the periodic setting (E2). Lehto: the classical statement |

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Result | Where the paper uses it | Source | Theorem in `External/` | Argument |
| --- | --- | --- | --- | --- |
| The projection on a nonempty closed convex set of a Hilbert space exists and is unique | Lemma 4, l. 412: the `L² (Q)`-projection `ζ` | Kinderlehrer–Stampacchia, Ch. I, Lemma 2.1 | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50) | Mathlib's `exists_norm_eq_iInf_of_complete_convex`; uniqueness by adding the two variational inequalities |
| The projection is characterized by `⟪x − y, v − y⟫ ≤ 0` | Lemma 4, l. 412–415: `(eq:projection-variational-inequality)` | Kinderlehrer–Stampacchia, Ch. I, Thm 2.3 | [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) | Mathlib's `norm_eq_iInf_iff_real_inner_le_zero` |
| (1.2a): `∫_0^∞ t^{p−1} L (z/t, w/t) dt = β_p Φ_p (z, w)`, `1 < p < 2` | Corollary 2, l. 301 ("by the arguments in") | Baernstein–Montgomery-Smith, §1 | [`External.BaernsteinMontgomerySmith.equation1_2a`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L231) | direct integration (the source: "one calculates") |
| (1.2b): `∫_0^∞ t^{p−1} M (w/t, z/t) dt = γ_p Φ_p (z, w)`, `2 < p` | Corollary 2, l. 301 | Baernstein–Montgomery-Smith, §1 | [`External.BaernsteinMontgomerySmith.equation1_2b`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L288) | direct integration |
| `Φ_p (z, w) ≤ (p* − 1)^p \|z\|^p − \|w\|^p` | Corollary 2, l. 301 (the norm) | Baernstein–Montgomery-Smith, §1 ("From [Bu3, p. 77] follows the inequality") | [`External.BaernsteinMontgomerySmith.phi_le`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L332) | Burkholder's majorization (Burkholder 1988, (1.10)), as formalized in BanachProbability (`BanachProbability.Burkholder.burkholderU_ge`), with `Φ_p (z, w) = −U (\|w\|, \|z\|)` |
| `‖𝒮‖_p ≥ p* − 1` | Corollary 2, l. 320 ("classical [Lehto1965]") | Lehto 1965 | [`External.Lehto.lowerBound`](../../Agazzi/External/Lehto/LowerBound.lean#L82) | not Lehto's argument, which was not read: the extremals `f_α` of Baernstein–Montgomery-Smith, continued outside the disc by Dragičević's cut-off, with the density lemma of HarmonicAnalysis; duality for the half `1/(p − 1)` |

The paper uses the arguments of Baernstein and Montgomery-Smith, and not only their statements. Its Corollary 2 is proved "by the arguments in" their paper, and the formalization follows those arguments: the Mellin identities, Fubini's theorem and the null Lagrangian. The one exception is the passage from the torus to the plane (Section 7).

The source of Kinderlehrer–Stampacchia was not read. Its numbering is taken from the paper, and its statements are the standard ones.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| `\|A\| = \|a₊\| + \|a₋\|`, `det A = \|a₊\|² − \|a₋\|²` | l. 268 | [`opNorm_eq`](../../Agazzi/Bridges.lean#L139), [`det_eq`](../../Agazzi/Bridges.lean#L77) |
| `F (A) = \|A² + J A¹\| − 1 = 2\|a₊\| − 1`, `F` convex | l. 341, 344 | [`rowF_eq_norm`](../../Agazzi/Proof/RowRepresentation.lean#L148), [`rowF_eq`](../../Agazzi/Proof/RowRepresentation.lean#L155), [`convexOn_rowF`](../../Agazzi/Proof/RowRepresentation.lean#L167) |
| The determinant is a null Lagrangian for periodic Lipschitz perturbations | l. 386 | [`setIntegral_unitCube_det_add_grad`](../../Agazzi/Basic/Analysis/Calculus/Periodic.lean#L187), from the package's `setIntegral_minor_add_grad` and `quasiconvexAtOn_iff_periodic` |
| Jensen's inequality for `F` ("convexity gives") | l. 379 | `F` as a supremum of affine `G_z`, each with `∫_Q G_z (Du) = G_z (A)` ([`setIntegral_unitCube_grad_eq_zero`](../../Agazzi/Basic/Analysis/Calculus/Periodic.lean#L178)) |
| Rademacher's theorem | Lemma 4 | Mathlib's `LipschitzWith.ae_differentiableAt` |
| `H` Lipschitz, `DH ∈ K` | l. 421 | [`lipschitzWith_supportFun`](../../Agazzi/Basic/Analysis/Convex/SupportFunction.lean#L102), [`gradient_supportFun_mem`](../../Agazzi/Basic/Analysis/Convex/SupportFunction.lean#L143) |
| `Dw = Dv` a.e. on `{h = 0}`; `D max {w, c}` | l. 417, 434 | [`ae_fderiv_eq_zero_of_eq_zero`](../../Agazzi/Basic/Analysis/Calculus/LipschitzFDeriv.lean#L38), [`ae_fderiv_max_eq_or`](../../Agazzi/Basic/Analysis/Calculus/LipschitzFDeriv.lean#L56) |
| Translation invariance; difference quotients converge | l. 438–443 | [`setIntegral_unitCube_comp_add`](../../Agazzi/Basic/Analysis/Calculus/Periodic.lean#L58), [`tendsto_setIntegral_slope_mul`](../../Agazzi/Basic/Analysis/Calculus/LipschitzFDeriv.lean#L108) |
| `∫_Q Dh = 0` for periodic `h` | l. 443 | [`setIntegral_unitCube_fderiv_eq_zero`](../../Agazzi/Basic/Analysis/Calculus/Periodic.lean#L143) |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Kinderlehrer–Stampacchia, Ch. I, Lemma 2.1, Thm 2.3 | l. 412 | correct, once `𝒞` is shown closed (E3) |
| Baernstein–Montgomery-Smith, (1.2a), (1.2b), the inequality | l. 301 | correct: the identities and the inequality hold as stated (recomputed by hand, numerically, and proved in Lean); arguments made on the plane at `A = 0` are applied to periodic maps at every `A` (E2) |
| Lehto 1965 | l. 320 | the classical lower bound, stated as the paper uses it |
| Guerra 2026b | l. 285, 301 | the Hessian case: see E1 |

These citations only give context and are not used in proofs:
- Šverák 1990 and Burkholder 1984, 1989 (origin of `L` and `B_p`);
- Dacorogna 2007 (quasiconvexity);
- Astala–Iwaniec–Martin 2009 (`𝒮`);
- Astala et al. 2012, 2022, 2024 and Guerra–Kristensen 2021;
- the suboptimal upper bounds (Bañuelos–Wang, Nazarov–Volberg, Dragičević–Volberg, Bañuelos–Janakiraman, Borichev–Janakiraman–Volberg) and Bañuelos's survey;
- Iwaniec 1982, Astala 1994, Donaldson–Sullivan, Iwaniec–Martin, Iwaniec–Sbordone and Iwaniec 2002;
- Faraco–Székelyhidi, Kirchheim–Székelyhidi and Székelyhidi 2005;
- Ambrosio–De Philippis–Kirchheim, De Philippis–Figalli and De Philippis–Guerra–Tione;
- Bañuelos–Lindeman, Duse and Petermichl–Slavin–Wick.

## 3. Errors and gaps in the paper

### E1. The Hessian case (l. 285)

"In the case where $\varphi=\D u$ for some $u\in C^\infty_{\tp{per}}(Q)$ this result had been proved in \cite{Guerra2026b}."

Guerra's theorem (arXiv:2608.23388, theorem `thm:L` of its TeX) is stated differently: "For every $A\in\mathbb R^{2\times2}$ and every $u\in C_c^\infty(\mathbb R^2)$ we have $\int_{\mathbb R^2}\bigl[L(A+\D^2u)-L(A)\bigr]\d x\geq0$". That is, compactly supported potentials on `ℝ²`, not periodic ones.

The two forms are equivalent by the standard argument relating periodic and compactly supported test maps (Dacorogna, Prop. 5.13; here not checked for Hessians in Lean). So the claim holds, but it is not literally Guerra's statement. Not formalized: the sentence is context.

### E2. Corollary 2 has no proof (l. 301–316)

"By the arguments in \cite{Baernstein1997a} (see also \cite{Guerra2026b} for further details), Theorem~\ref{thm:L-quasiconvexity} implies:"

Baernstein and Montgomery-Smith argue on the plane, for `f ∈ Ẇ^{1,2} (ℂ)` and at `A = 0`: their (1.1), Conjecture 2, Conjecture 3 and remark (b). Corollary 2 is a periodic statement at every `A`. The same arguments work, with the following adjustments, which the paper does not mention:
- the Mellin identities are applied at `A / t` with the test maps `φ / t`;
- Fubini's theorem is used on `Q × (0, ∞)`, with an integrable majorant;
- for `p > 2`, the null Lagrangian `det`;
- for `p = 2`, `B_2 = −det` by the paper's definition (the branch `2 ≤ p`), a null Lagrangian.

For the norm, the paper does not say how its periodic inequality reaches `L^p (ℂ)`. Guerra's "further details" make this passage in the Hessian case, with a logarithmic potential and cut-offs `η_R` (proofs of the corollaries `cor:beurling` and `cor:beurling-lp` of that preprint).

The corollary holds. In Lean:
- [`corollary2_lipschitz`](../../Agazzi/Corollary2/Quasiconvexity.lean#L285) and [`corollary2`](../../Agazzi/Corollary2/Quasiconvexity.lean#L424) follow Baernstein–Montgomery-Smith, through [`burkholderB_eq_mellin_of_lt_two`](../../Agazzi/Corollary2/Quasiconvexity.lean#L136), [`burkholderB_eq_mellin_of_two_lt`](../../Agazzi/Corollary2/Quasiconvexity.lean#L153) and [`burkholderB_two`](../../Agazzi/Corollary2/Quasiconvexity.lean#L173);
- [`corollary2_norm`](../../Agazzi/Corollary2/Norm.lean#L262) follows them for the inequality on the torus. It departs from Guerra's planar passage (Section 7).

### E3. The closedness of `𝒞` (l. 412)

"The set $\mc C$ is nonempty, closed and convex in $L^2(Q)$."

Closedness is not argued, and it is what the existence of the projection rests on. It holds. The formalization proves it in [`Agazzi/Proof/ScalarProjection/Existence.lean`](../../Agazzi/Proof/ScalarProjection/Existence.lean) and [`Agazzi/Basic/Analysis/Calculus/GradientConstraint.lean`](../../Agazzi/Basic/Analysis/Calculus/GradientConstraint.lean):
- `p + Dξ ∈ K` a.e. is equivalent to the slope bound `ξ (y) − ξ (x) + p · (y − x) ≤ H_K (y − x)` for all `x`, `y`:
  - one direction by mollification and the mean value theorem ([`sub_add_dotProduct_le_supportFun_of_ae_mem`](../../Agazzi/Basic/Analysis/Calculus/GradientConstraint.lean#L105));
  - the other at points of differentiability ([`add_fderiv_mem_of_sub_add_dotProduct_le_supportFun`](../../Agazzi/Basic/Analysis/Calculus/GradientConstraint.lean#L131));
- the slope bound gives a Lipschitz constant that depends only on `K` and `p`;
- an `L²`-convergent sequence has an a.e.-convergent subsequence;
- being equi-Lipschitz and periodic, that subsequence converges everywhere ([`exists_tendsto_of_ae_restrict_unitCube_tendsto`](../../Agazzi/Basic/Analysis/Calculus/GradientConstraint.lean#L178)), to a limit that keeps the slope bound.

### E4. "By changing signs" (l. 422)

"By changing signs, we may assume $h(x_0)>0$."

The reduction replaces `(η, ζ, K, p)` by `(−η, −ζ, −K, −p)`. It is correct, but terse.

The formalization runs the mirror construction explicitly, with `s = ±1`:
- the cone `c (x) = w (x₀) − ε + H (x − x₀)`;
- the function `min {w, c}`;
- the competitor `ζ − (w − c)₊`.

The independent review checked that this is the image of the paper's construction under the sign change.

### E5. The ball in the torus (l. 434)

"Thus $(c-w)_+$ has compact support in $B_r(x_0)$ and, extending it by zero outside $B_r(x_0)$, we obtain $\zeta+(c-w)_+\in\mc C$".

On the torus, this needs `B_r (x₀)` to embed in `Q` (for instance `r < 1/2`) and a periodic extension. Since `r` can be shrunk, the step holds. The formalization takes `r ≤ 1/4` and periodizes with [`supPeriodize`](../../Agazzi/Basic/Topology/MetricSpace/Periodize.lean#L41) ([`Agazzi/Basic/Topology/MetricSpace/Periodize.lean`](../../Agazzi/Basic/Topology/MetricSpace/Periodize.lean)).

### E6. Typos

- l. 327: "implying a similar results".
- l. 345: Lemma 3 has no label; the formalization uses the label of its display, `eq:L-row-representation`.
- l. 377: "where $\varphi\in C^\infty_\tp{per}(Q)$" for $C^\infty_\tp{per}(Q;\R^2)$.
- l. 382: "to $u^1(x)=A^1\cdot x+\eta(x)$": `η` is not introduced; it is `φ¹`.
- l. 401: "take $p\in K$": the point of `K` has the name of the exponent `p` of Corollary 2.

## 4. Missing hypotheses

None: every statement of the paper is true as printed.

## 5. Redundant hypotheses

| Result | Hypothesis that is not needed | Lean |
| --- | --- | --- |
| Lemma 4, the two assertions | `p ∈ K`: `ζ ∈ 𝒞` implies it, since `p` is the mean of `p + Dζ` over `Q` and `K` is closed and convex; it is needed for `𝒞 ≠ ∅`, that is, for the existence of the projection | [`lemma4`](../../Agazzi/Proof/ScalarProjection/Main.lean#L748) keeps the paper's hypothesis, which its proof does not use; [`lemma4_exists`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L198) uses it |

## 6. How the formalization reads the paper

- `ℝ^{2×2}` is `Matrix (Fin 2) (Fin 2) ℝ` and `ℝ²` is `Fin 2 → ℝ`.
- `a₊`, `a₋` are `conformalPart A`, `anticonformalPart A`, with `A z = a₊ z + a₋ z̄` for `z` a column vector.
- `|A|` in the definition of `L` is `|a₊| + |a₋|`, the operator norm ([`opNorm_eq`](../../Agazzi/Bridges.lean#L139)).
- The torus `Q = ℝ² / ℤ²` is represented by `ℤ²`-periodic maps on `ℝ²` ([`IsPeriodic`](../../palomar/Agazzi/Challenge.lean#L103)), with integrals over the open unit square [`unitSquare`](../../palomar/Agazzi/Challenge.lean#L98), of measure `1` ([`volume_unitSquare`](../../Agazzi/Bridges.lean#L43)).
- `Dφ` is `jacobian φ x`, the matrix `(∂_j φ_i (x))`. Its rows are the gradients of the components, as in the paper's `D u = (D u¹, D u²)`. It equals the package's `grad`.
- `W^{1,∞}_per (Q)` is represented by Lipschitz periodic functions ([`LipPer`](../../Agazzi/Proof/ScalarProjection/Defs.lean#L42)), the Lipschitz representatives of its classes. `Dξ` is the a.e. derivative.
- The `L² (Q)`-projection of `η` on `𝒞` is a minimizer of `ξ ↦ ∫_Q (η − ξ)²` on `𝒞` ([`IsL2Projection`](../../Agazzi/Proof/ScalarProjection/Defs.lean#L51)).
  - Lemma 4 is proved for every minimizer, so the uniqueness that the paper states is not needed.
  - [`lemma4_exists`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L198) proves existence through `Lp ℝ 2`.
- `‖𝒮‖_{L^p (ℂ; ℂ) → L^p (ℂ; ℂ)}` is `beurlingNorm p`: the supremum of `‖𝒮 f‖_p / ‖f‖_p` over Schwartz functions, with `𝒮` the multiplier `ξ̄ / ξ` under Mathlib's Fourier transform. It equals the package's `beurlingPowNorm 1 p` ([`beurlingNorm_eq_beurlingPowNorm`](../../Agazzi/Bridges.lean#L53)), and `𝒮 ∂_z̄ = ∂_z` ([`beurling_dzbar`](../../Agazzi/Bridges.lean#L67)).
- `B_p` ([`burkholderB`](../../palomar/Agazzi/Challenge.lean#L88)) is defined for every real `p` and used for `p > 1`.
- Theorem 1 and the first assertion of Corollary 2 are proved for Lipschitz periodic test maps ([`theorem1_lipschitz`](../../Agazzi/Theorem1.lean#L250), [`corollary2_lipschitz`](../../Agazzi/Corollary2/Quasiconvexity.lean#L285)), by the paper's arguments, which use nothing more. The paper's statements for `C^∞` maps follow ([`theorem1`](../../Agazzi/Theorem1.lean#L401), [`corollary2`](../../Agazzi/Corollary2/Quasiconvexity.lean#L424)). This stronger form gives quasiconvexity in the sense of the package CalculusOfVariations, with Lipschitz test maps vanishing outside the unit cube ([`quasiconvex_integrandL`](../../Agazzi/Quasiconvex.lean#L69), [`quasiconvex_burkholderB`](../../Agazzi/Quasiconvex.lean#L75), [`quasiconvex_burkholder`](../../Agazzi/Quasiconvex.lean#L83)).

No statement of the paper was corrected.

## 7. Departures from the paper's proofs

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Corollary 2, second assertion: the upper bound `‖𝒮‖_p ≤ p* − 1` ([`beurlingNorm_le`](../../Agazzi/Corollary2/Norm.lean#L255)) | Not given; the cited arguments are planar. Baernstein and Montgomery-Smith derive the norm from the inequality on `Ẇ^{1,p} (ℂ)` (their remark (b)); Guerra passes from compactly supported test maps to `L^p (ℂ)` with a potential and cut-offs `η_R` (Hessian case) | Corollary 2 at `A = 0`, Burkholder's inequality and `u ↦ ū` give the bound on `L^p_0 (𝕋²)` ([`Corollary2Norm.torusBeurlingPowNorm_one_le`](../../Agazzi/Corollary2/Norm.lean#L239)); transference (Hytönen–van Neerven–Veraar–Weis, Cor. 5.7.6, in HarmonicAnalysis) gives `L^p (ℂ)` | It is not necessary. It was made for economy: the planar route needs the Cauchy transform of Schwartz functions and its cut-offs, which no Lean library has. It waits for the author's decision between keeping it and formalizing the planar route | E2 |

The departure is labelled "Departure from the paper:" in the docstrings of [`Agazzi/Corollary2/Norm.lean`](../../Agazzi/Corollary2/Norm.lean).

Every other proof follows the paper's, step by step. Only the following differ, and only in mechanics:
- In Lemma 4, the sup norm of `Fin 2 → ℝ` is used inside the proof (balls, `ρ`), in place of the Euclidean norm, with the constants adjusted.
- In Theorem 1, Jensen's inequality for `F` is proved through `F = sup_{|z| = 1} G_z`.
- In Lemma 4, the sign change and the periodization are made explicit (E4, E5).

## 8. What each result depends on

From the current output of [`scripts/Audit.lean`](../../scripts/Audit.lean). Every result depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and so do all 408 declarations of the library.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Theorem 1 | [`theorem1`](../../Agazzi/Theorem1.lean#L401) | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50), [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) |
| Theorem 1, Lipschitz form | [`theorem1_lipschitz`](../../Agazzi/Theorem1.lean#L250) | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50), [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) |
| Corollary 2 (a) | [`corollary2`](../../Agazzi/Corollary2/Quasiconvexity.lean#L424) | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50), [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39), [`External.BaernsteinMontgomerySmith.equation1_2a`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L231), [`External.BaernsteinMontgomerySmith.equation1_2b`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L288) |
| Corollary 2 (a), Lipschitz form | [`corollary2_lipschitz`](../../Agazzi/Corollary2/Quasiconvexity.lean#L285) | the same |
| Corollary 2 (b) | [`corollary2_norm`](../../Agazzi/Corollary2/Norm.lean#L262) | the same, and [`External.BaernsteinMontgomerySmith.phi_le`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L332), [`External.Lehto.lowerBound`](../../Agazzi/External/Lehto/LowerBound.lean#L82) |
| Lemma 3 | [`lemma3`](../../Agazzi/Proof/RowRepresentation.lean#L220) | none |
| Lemma 4 | [`lemma4`](../../Agazzi/Proof/ScalarProjection/Main.lean#L748) | [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) |

The route check finds that every proof uses the results that the paper's proof cites, and no other. [`docs/Agazzi/route_differences.tsv`](route_differences.tsv) records no difference.

## 9. Not formalized

- The uniqueness of the projection (l. 412): not needed.
- The remarks of the introduction:
  - Corollary 2 implies the sharp higher integrability of quasiconformal maps of Astala 1994 (l. 325);
  - the proof extends to higher dimensions and to the Beurling–Ahlfors transform on forms (l. 327);
  - it extends to the integrands of Faraco–Székelyhidi, Kirchheim–Székelyhidi and Székelyhidi (l. 327).
- The classical lower bound is proved, but by the argument named in Section 2, not by Lehto's.

## 10. The paper in the literature

Sources: the paper's own account (l. 276–327), and searches on 23 November 2026:
- arXiv, through its API, by title, author and keyword;
- GitHub code search, for `2609.28311`.

Bibliographic data not verified against the work itself are marked "as in the paper's bibliography".

### Before the paper

- D. L. Burkholder, *Differential subordination of harmonic functions and martingales*, in: Harmonic Analysis and PDE (El Escorial, 1987), Lecture Notes in Math. 1384, Springer, 1989, 1–23 (published; as in the paper's bibliography). V. Šverák, *Examples of rank-one convex functions*, Proc. Roy. Soc. Edinburgh 114A (1990), 237–242 (published; as in the paper's bibliography). These are the origin of `L`; not read here.
- A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and `∂̄f`* (published 1999; [arXiv:math/9709215v2](https://arxiv.org/abs/math/9709215), read). They show that the quasiconvexity of `L` implies that of `B_p` and Iwaniec's conjecture, and give the extremals `f_α` (Section 2).
- T. Iwaniec, *Extremal inequalities in Sobolev spaces and quasiconformal mappings*, Z. Anal. Anwend. 1 (1982) (published; as in the paper's bibliography; not read). This is the conjecture `‖𝒮‖_p = p* − 1`. O. Lehto (1965) proved the lower bound (not read).
- Upper bounds `C (p* − 1)`, as the paper lists them (published; not read here):
  - Bañuelos–Wang (Duke 1995);
  - Nazarov–Volberg (St. Petersburg Math. J. 2004);
  - Dragičević–Volberg (Indiana 2005);
  - Bañuelos–Janakiraman (Trans. AMS 2008);
  - Borichev–Janakiraman–Volberg (Duke 2013);
  - the survey of R. Bañuelos, [arXiv:1012.4850](https://arxiv.org/abs/1012.4850) (Illinois J. Math. 2010).
- Quasiconvexity of the Burkholder functional under sign restrictions, as the paper lists them:
  - Astala–Iwaniec–Prause–Saksman (J. AMS 2012);
  - Astala–Faraco–Guerra–Koski–Kristensen, [arXiv:2309.03495](https://arxiv.org/abs/2309.03495) (2023, preprint as cited) and Commun. Pure Appl. Anal. 2024;
  - Guerra–Kristensen, [arXiv:2112.10563](https://arxiv.org/abs/2112.10563) (Arch. Ration. Mech. Anal. 2022).

### Concurrent work

- A. Guerra, *Quasiconvexity of the Burkholder function on symmetric matrices*, [arXiv:2608.23388v1](https://arxiv.org/abs/2608.23388) (24 August 2026, preprint, read in part). It claims Theorem 1 for Hessians `D²u`, `u ∈ C_c^∞ (ℝ²)`, by Morse theory, with sharp weak-type and `L^p` bounds for `𝒮` on real-valued functions. The paper cites it (E1, E2).
- *The sharp `L^p` bound for the imaginary part of the Beurling–Ahlfors operator on the lattice*, [arXiv:2609.13573](https://arxiv.org/abs/2609.13573) (11 September 2026, preprint). Found by the search; its abstract and its relation to the paper were not checked.
- The README of the package lean4-harmonic-analysis records a bound `1.523958 (p* − 1)` as claimed in a 2026 manuscript of the repository Tencent-Hunyuan/Hyra-results. This was not checked here.

### Since the paper

- No later version, erratum or correction of the paper was found.
- The arXiv search returned later preprints on neighbouring questions. Whether they cite or build on the paper was not checked:
  - [arXiv:2610.19410](https://arxiv.org/abs/2610.19410) (October 2026, *Fractional elementary symmetric functions and Hessian estimates in the plane*);
  - [arXiv:2611.17088](https://arxiv.org/abs/2611.17088) (November 2026, *Mixed inner variation and global Hessian integrability for degenerate Monge–Ampère equations*).

### Formalizations

- This is, as far as the search found, the first formalization of the paper, of Theorem 1 and of Iwaniec's conjecture.
- The GitHub code search for `2609.28311` found no Lean formalization. It found only mentions in the READMEs of lean4-morrey and lean4-harmonic-analysis, and non-Lean listings (feeds, a problem catalogue).
- The README of lean4-harmonic-analysis lists other Lean formalizations about `𝒮`. None of them was opened or consulted here:
  - boundedness on `L^p` (will1491/no-wandering-domains, TauCetiProject/TauCeti);
  - the `L²` isometry (openai/math, Tencent-Hunyuan/Hyra-results);
  - statements without proof of Lehto's bound and of Iwaniec's conjecture (facebookresearch/atlas-lean).
- The cited results are proved here, with the help of three packages: lean4-calculus-of-variations, lean4-harmonic-analysis and lean4-banach-probability (see the README).

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **The series.** The paper announces later parts of the series:
  - the higher-dimensional theory: the Beurling–Ahlfors transform on forms, after Donaldson–Sullivan and Iwaniec–Martin, with the sharp higher integrability of quasiregular maps in even dimensions;
  - the separating functions of Faraco–Székelyhidi, Kirchheim–Székelyhidi and Székelyhidi.
- **Weak type.** Guerra's argument for the weak-type corollary of arXiv:2608.23388 (`L (A/λ) ≤ (2/λ) |a₊| − 1_{|a₋| > λ}`, applied to the Cauchy transform with cut-offs) is written for real-valued `h`. Combined with Theorem 1 for all matrices, and with `f ↦ f̄`, which exchanges `a₊` and `a₋`, it appears to give `λ |{|𝒮 h| > λ}| ≤ 2 ‖h‖₁` for complex-valued `h`. Guerra's laminates show that the constant `2` is sharp for real `h`. This was checked here only for the pointwise inequality, on paper; it has not been checked against the literature.
- **Higher powers.** The conjecture `‖𝒮^n‖_p = κ_n (p)` for `p ≥ 2` (Dragičević) remains open for `n ≥ 2`, as far as lean4-harmonic-analysis's README records. Corollary 2 gives `‖𝒮²‖_p ≤ (p* − 1)²`, but this does not improve on the known bounds for large `p`.
- **Morrey's problem.** [lean4-morrey](https://github.com/vltanh/lean4-morrey) requires this project and uses [`quasiconvex_burkholder`](../../Agazzi/Quasiconvex.lean#L83): with it, the theorem of its library `HomogeneousIsotropic` holds with no hypothesis for `1 < p < 2`. Nonnegative, isotropic, positively `p`-homogeneous, rank-one convex integrands on `ℝ^{2×2}` are quasiconvex for every `p > 0` (polyconvex for `p ≥ 2`). At the multiples of orthogonal matrices, and given the quasiconvexity of `B_p`, the case `1 < p < 2` is a theorem of Guerra and Kristensen (2022).

### Simpler proofs

Each was checked on paper only.
- **The variational inequality.** It follows from the minimality of `ζ` by a first variation: `ζ + t (ξ − ζ) ∈ 𝒞`, then `t → 0⁺`. This needs no Hilbert-space projection; existence still needs one, or another compactness argument.
- **The interior case split in Lemma 4 is redundant.** The pointwise conclusion `Dw (x₀) ∉ int K` holds trivially when `int K = ∅`, and `∂K = K ∖ int K` for closed `K`.
- **`∫_Q ∂_v f = 0`** follows from translation invariance and difference quotients. The formalization derives it from the package's null Lagrangians instead.
- **The convexity of `F`** is immediate from its definition as a supremum of the affine functions `G_z`.
- **Theorem 1 for `|A| > 1`.** The chain `L (A) = sup_z G_z (A) = sup_z ∫_Q G_z (Du) ≤ ∫_Q L (Du)` skips `F`.
- **Lehto's lower bound.** Duality, `‖𝒮‖_p = ‖𝒮‖_{p'}`, replaces the second family `f̄_α`. The formalization uses it.

### The formalization

- **The planar route for the norm** (Section 7), if the author prefers it to transference. It needs the Cauchy transform of Schwartz functions, its decay, and the cut-offs `η_R`.
- **[`Agazzi/Basic/`](../../Agazzi/Basic) holds the gradient-constrained `L²` projection on the torus,** with its tools. All of it is general, and its natural home is lean4-calculus-of-variations ([`Agazzi/Basic/README.md`](../../Agazzi/Basic/README.md)):
  - periodic integrals and the periodic null Lagrangian;
  - derivatives of Lipschitz functions;
  - the slope characterization of gradient constraints;
  - support functions;
  - periodization.
- **`External/` holds material other formalizations could reuse:**
  - the Mellin identities of Baernstein–Montgomery-Smith;
  - the `n = 1` case of Dragičević's lower bound ([`External.Lehto.sub_one_le_beurlingPowNorm_one`](../../Agazzi/External/Lehto/LowerBound.lean#L64)), a planned extension of lean4-harmonic-analysis.
- **Duplicates.** Three private copies of `volume unitSquare = 1` remain, and some public helpers are missing from their module docstrings.
