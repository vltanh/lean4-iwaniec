# Audit of the paper and the formalization

Paper: A. Agazzi, K. Astala, R. Bañuelos, G. Bruno, G. Cassese, D. Faraco, A. Guerra, M. Hormozi, B. Kirchheim, A. Koski, V. Kovač, J. Kristensen, F. Pasqualotto, I. Prause, E. Saksman, V. Šverák, L. Székelyhidi, R. Tione, A. Volberg and H. Yang, *Sharp higher integrability theory, Part I: the `L^p`-norm of the Beurling–Ahlfors transform*, [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311).
- Version 2 is of 8 October 2026, version 1 of 23 September 2026. The arXiv comment of v2 reads "updated list of authors", but the TeX sources also differ in content:
  - v1 states `(eq:BA-definition)` as `𝒮 ∘ ∂_z = ∂_z̄` (v1, l. 306), which is false for the symbol `ξ̄ / ξ`; v2 has `𝒮 ∘ ∂_z̄ = ∂_z` (l. 298);
  - v2 renames the `u` of Lemma 4 to `v`;
  - v1 carries a "preliminary version" notice, and v2 rewords the introduction;
  - the author list grows from 15 to 20 names (v1's "Hang Chang" is v2's "Hang Yang", with the same address).
- The audit was made against the arXiv LaTeX source of v2 (`main.tex`). Line numbers are those of that file.
- Result numbers are the paper's. Its four results share one counter:
  - Theorem 1;
  - Corollary 2;
  - Lemma 3;
  - Lemma 4.

Lean names are in the namespace [`Agazzi`](../../Agazzi) unless they begin with `External.`, `AgazziChallenge.` or a package's namespace.

Status of the formalization:
- Every result of the paper is proved:
  - Lemma 3;
  - Lemma 4;
  - Theorem 1;
  - both assertions of Corollary 2.
- Theorem 1 and the first assertion of Corollary 2 are also proved for Lipschitz periodic test maps.
- The claims of the introduction and of the proofs that have a precise statement are proved:
  - the Hessian case of Theorem 1 (l. 285), in the periodic form and in Guerra's compactly supported form, with the equivalence of the two forms (E1);
  - the uniqueness of the projection in Lemma 4 (l. 412);
  - Astala's sharp higher integrability of quasiconformal maps, as a consequence of Corollary 2 (l. 325), with the sharpness of the exponent.
- Not formalized (Section 9):
  - the extensions that the paper announces for later articles of the series, without precise statements;
  - the results that the paper cites only for context (end of Section 2).
- Every cited result that the paper uses is proved, by the arguments named in Section 2, some of them through the packages: in [`Agazzi/External/`](../../Agazzi/External), and Astala's theorem, as a consequence of Corollary 2, in [`Agazzi/Astala.lean`](../../Agazzi/Astala.lean).
- `lake build` passes. No `sorry` remains outside the Challenge, and there is no `axiom`.
- [`scripts/Audit.lean`](../../scripts/Audit.lean) checks that every declaration of the library depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- Comparator accepts the Solution against [`palomar/Agazzi/Challenge.lean`](../../palomar/Agazzi/Challenge.lean), under Lean's kernel and under NanoDa.
- No statement of the paper had to change.
- Every proof follows the paper's argument or, where the paper only cites, the argument of the cited sources (Section 7).

## 1. Summary

| Kind | Findings |
| --- | --- |
| Errors | none |
| Gaps | E2: Corollary 2 is proved by reference to planar arguments. E3: the closedness of `𝒞` in `L² (Q)` is not argued. E5: the ball of Lemma 4 must embed in the torus |
| Remarks | E1: the Hessian case attributed to Guerra is stated there for compactly supported potentials on `ℝ²`, an equivalent form (proved equivalent in Lean). E4: the sign change in Lemma 4 is left implicit |
| Typos | E6 |
| Missing hypotheses | none |
| Redundant hypotheses | none in the paper (Lemma 4's `p ∈ K` is used only for the existence and uniqueness of `ζ`; see Section 5) |
| Use of cited results | Kinderlehrer–Stampacchia: correct, once `𝒞` is closed (E3). Baernstein–Montgomery-Smith and Guerra: correct; their planar arguments are applied to periodic maps at every `A`, and the norm is brought back from the periodic statement to the plane (E2). Lehto: the classical statement. Astala: the classical statement, which follows from Corollary 2 by Iwaniec's derivation |

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Result | Where the paper uses it | Source | Theorem in `External/` | Argument |
| --- | --- | --- | --- | --- |
| The projection on a nonempty closed convex set of a Hilbert space exists and is unique | Lemma 4, l. 412: the `L² (Q)`-projection `ζ` "exists uniquely" ([`lemma4_exists`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L200), [`lemma4_unique`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L238)) | Kinderlehrer–Stampacchia, Ch. I, Lemma 2.1 | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50) | Mathlib's `exists_norm_eq_iInf_of_complete_convex`; uniqueness by adding the two variational inequalities |
| The projection is characterized by `⟪x − y, v − y⟫ ≤ 0` | Lemma 4, l. 412–415: `(eq:projection-variational-inequality)` | Kinderlehrer–Stampacchia, Ch. I, Thm 2.3 | [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) | Mathlib's `norm_eq_iInf_iff_real_inner_le_zero` |
| (1.2a): `∫_0^∞ t^{p−1} L (z/t, w/t) dt = β_p Φ_p (z, w)`, `1 < p < 2` | Corollary 2, l. 301 ("by the arguments in") | Baernstein–Montgomery-Smith, §1 | [`External.BaernsteinMontgomerySmith.equation1_2a`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L231) | direct integration (the source: "one calculates") |
| (1.2b): `∫_0^∞ t^{p−1} M (w/t, z/t) dt = γ_p Φ_p (z, w)`, `2 < p` | Corollary 2, l. 301 | Baernstein–Montgomery-Smith, §1 | [`External.BaernsteinMontgomerySmith.equation1_2b`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L288) | direct integration |
| `Φ_p (z, w) ≤ (p* − 1)^p \|z\|^p − \|w\|^p` | Corollary 2, l. 301 (the norm) | Baernstein–Montgomery-Smith, §1 ("From [Bu3, p. 77] follows the inequality") | [`External.BaernsteinMontgomerySmith.phi_le`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L332) | Burkholder's majorization (Burkholder 1988, (1.10)), as formalized in BanachProbability (`BanachProbability.Burkholder.burkholderU_ge`), with `Φ_p (z, w) = −U (\|w\|, \|z\|)` (the package's `U`, subordinate argument first; `Φ_p (z, w) = −u_p (z, w)` in Burkholder's notation) |
| `‖𝒮‖_p ≤ C` if `∫ \|∂f\|^p ≤ C^p ∫ \|∂̄f\|^p` for all `f ∈ C_c^∞ (ℂ)` (remark (b): Conjecture 3 gives the norm) | Corollary 2, l. 301 (the norm) | Baernstein–Montgomery-Smith, §1, remark (b), without proof; Guerra, arXiv:2608.23388, proof of `cor:beurling-lp`, for further details (l. 301) | [`External.BaernsteinMontgomerySmith.remark_b`](../../Agazzi/External/BaernsteinMontgomerySmith/RemarkB.lean#L116) | Guerra's passage to `L^p (ℂ)`, with Guerra's dense class `C_c^∞`: a potential (in the gradient case, the Cauchy transform `(1/π) ∫ g (w) / (z − w) dw`, with `∂̄f = g`, `∂f = 𝒮 g` and its decay), cut-offs `η_R`, limit, density; as formalized in HarmonicAnalysis (`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`; Section 7) |
| `∫_{ℝ²} [L (A + D²u) − L (A)] ≥ 0` for all `A` and `u ∈ C_c^∞ (ℝ²)` | the remark of l. 285: the Hessian case of Theorem 1 "had been proved in [Guerra2026b]" (E1) | Guerra, arXiv:2608.23388, Theorem 1.1 (`thm:L`) | [`External.Guerra.theorem1_1`](../../Agazzi/External/Guerra/TheoremL.lean#L43) | not Guerra's, which uses Morse theory: Theorem 1 for `φ = Du` ([`theorem1_hessian`](../../Agazzi/Hessian.lean#L66)) and the equivalence of the periodic and the compactly supported Hessian forms ([`theorem1_hessian_iff`](../../Agazzi/Hessian.lean#L78)) |
| `‖𝒮‖_p ≥ p* − 1` | Corollary 2, l. 320 ("classical [Lehto1965]") | Lehto 1965 | [`External.Lehto.lowerBound`](../../Agazzi/External/Lehto/LowerBound.lean#L68) | not Lehto's argument, which was not read: the case `n = 1` of Dragičević's lower bound, in HarmonicAnalysis (`HarmonicAnalysis.sub_one_le_beurlingPowNorm_one`), with Dragičević's test functions, which on the unit disc are the extremals `f_α` of Baernstein–Montgomery-Smith; duality for the half `1/(p − 1)` |

The paper uses the arguments of Baernstein and Montgomery-Smith, and not only their statements. Its Corollary 2 is proved "by the arguments in" their paper ("see also [Guerra2026b] for further details"), and the formalization follows those arguments:
- for the first assertion, the Mellin identities, with Fubini's theorem and the null Lagrangian `det`;
- for the norm, their passage from Conjecture 2 to Conjecture 3 and their remark (b), with Guerra's details for the remark.

The source of Kinderlehrer–Stampacchia was not read. Its numbering is taken from the paper, the assignment of the two statements to the two numbers is inferred from l. 412, and its statements are the standard ones.

### Proved from the paper's results

| Result | Where the paper states it | Source | Theorem | Argument |
| --- | --- | --- | --- | --- |
| For `0 ≤ k < 1` and `f ∈ W^{1,2}_loc (Ω)` with `\|∂̄f\| ≤ k \|∂f\|` a.e. (`K`-quasiregular, `K = (1 + k)/(1 − k)`), `Df ∈ L^p_loc (Ω)` for `2 ≤ p < 2K/(K − 1)`; the exponent is sharp | l. 325: "Corollary 2 implies the sharp higher integrability of derivatives of quasiconformal maps in the plane, originally obtained by complex-analytical methods in [Astala1994]" | K. Astala, *Area distortion of quasiconformal mappings*, Acta Math. 173 (1994), 37–60 (not read) | [`astala`](../../Agazzi/Astala.lean#L158), [`astala_sharp`](../../Agazzi/Astala.lean#L210) | Iwaniec's derivation from the norm of `𝒮` (T. Iwaniec, 1982; K. Astala, T. Iwaniec and G. Martin, *Elliptic partial differential equations and quasiconformal mappings in the plane*, Princeton, 2009, Chapters 13–14; neither was read), with `‖𝒮‖_p = p − 1` for `p ≥ 2` from Corollary 2 (b): in the package HarmonicAnalysis (`HarmonicAnalysis.memLpLoc_of_beltrami`), a cut-off `g = η f`, `∂g = 𝒮 ∂̄g` for compactly supported `g ∈ W^{1,2}` (`HarmonicAnalysis.beurlingL2_dzbar`), Sobolev's embedding in the plane for the right side `h` of `∂̄g − μ ∂g = h`, and a Neumann series for `I − μ𝒮` on `L²` whose partial sums are bounded in `L^p` since `k ‖𝒮‖_p = k (p − 1) < 1` (`HarmonicAnalysis.eLpNorm_beurlingL2_le`). The sharpness: the radial stretch `z \|z\|^{1/K − 1}` (`HarmonicAnalysis.Complex.RadialStretch`) |

### Standard facts used without citation

A selection: the facts whose proofs take more than a line in Lean. Names that begin with `CalculusOfVariations.` are in the package lean4-calculus-of-variations, which holds the general toolkit of Lemma 4 and Theorem 1; names that begin with `HarmonicAnalysis.` are in the package lean4-harmonic-analysis.

| Fact | Where | In the formalization |
| --- | --- | --- |
| `\|A\| = \|a₊\| + \|a₋\|`, `det A = \|a₊\|² − \|a₋\|²` | l. 268 | [`opNorm_eq`](../../Agazzi/Bridges.lean#L150), [`det_eq`](../../Agazzi/Bridges.lean#L88) |
| `F (A) = \|A² + J A¹\| − 1 = 2\|a₊\| − 1`, `F` convex | l. 341, 344 | [`rowF_eq_norm`](../../Agazzi/Proof/RowRepresentation.lean#L148), [`rowF_eq`](../../Agazzi/Proof/RowRepresentation.lean#L155), [`convexOn_rowF`](../../Agazzi/Proof/RowRepresentation.lean#L167) |
| The determinant is a null Lagrangian for periodic Lipschitz perturbations | l. 386 | `CalculusOfVariations.setIntegral_unitCube_det_add_grad`, from `CalculusOfVariations.setIntegral_minor_add_grad` and `CalculusOfVariations.quasiconvexAtOn_iff_periodic` |
| Jensen's inequality for `F` ("convexity gives") | l. 378 | `F` as a supremum of affine `G_z`, each with `∫_Q G_z (Du) = G_z (A)` (`CalculusOfVariations.setIntegral_unitCube_grad_eq_zero`) |
| Rademacher's theorem | Lemma 4 | Mathlib's `LipschitzWith.ae_differentiableAt` |
| `H` Lipschitz, `DH ∈ K` | l. 421 | `CalculusOfVariations.lipschitzWith_supportFun`, `CalculusOfVariations.gradient_supportFun_mem` |
| `Dw = Dv` a.e. on `{h = 0}`; `D max {w, c}` | l. 417, 434 | `CalculusOfVariations.ae_fderiv_eq_zero_of_eq_zero`, `CalculusOfVariations.ae_fderiv_max_eq_or` |
| Translation invariance; difference quotients converge | l. 438–443 | `CalculusOfVariations.setIntegral_unitCube_comp_add`, `CalculusOfVariations.tendsto_setIntegral_slope_mul` |
| `∫_Q Dh = 0` for periodic `h` | l. 443 | `CalculusOfVariations.setIntegral_unitCube_fderiv_eq_zero` |
| Periodic and compactly supported Hessian test functions give the same inequalities (the second-order form of Dacorogna, Prop. 5.13) | l. 285 (E1) | `CalculusOfVariations.hessian_periodic_iff_hasCompactSupport` |
| Weak derivatives: uniqueness, the Leibniz rule with a cut-off, mollification | l. 325 (Astala's theorem) | `HarmonicAnalysis.HasWeakLineDerivOn.ae_eq`, `HarmonicAnalysis.HasWeakFDerivOn.smul_of_tsupport_subset`, `HarmonicAnalysis.tendsto_eLpNorm_convolution_sub`, `HarmonicAnalysis.hasFDerivAt_convolution_of_hasWeakFDerivOn` |
| Sobolev's embedding `W^{1,2}_loc ⊂ L^q_loc`, `q < ∞`, in the plane | l. 325 | `HarmonicAnalysis.MemLpLoc.of_hasWeakFDerivOn`, from Mathlib's Gagliardo–Nirenberg–Sobolev inequality |
| `𝒮` on `L²` (norm `≤ 1`), its `L^p` bound on `L² ∩ L^p`, and `𝒮 ∂̄g = ∂g` for compactly supported `g ∈ W^{1,2}` | l. 325 | `HarmonicAnalysis.norm_beurlingL2_le`, `HarmonicAnalysis.eLpNorm_beurlingL2_le`, `HarmonicAnalysis.beurlingL2_dzbar` |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Kinderlehrer–Stampacchia, Ch. I, Lemma 2.1, Thm 2.3 | l. 412 | correct, once `𝒞` is shown closed (E3) |
| Baernstein–Montgomery-Smith, (1.2a), (1.2b), the inequality, remark (b) | l. 301 | correct: the identities and the inequality hold as stated (recomputed by hand, numerically, and proved in Lean), and so does remark (b), which the source states without proof; arguments made on the plane at `A = 0` are applied to periodic maps at every `A` (E2) |
| Lehto 1965 | l. 320 | the classical lower bound, stated as the paper uses it |
| Guerra 2026b | l. 285, 301 | the Hessian case: see E1. The "further details" (l. 301): the passage to `L^p (ℂ)` for Hessians, which carries over to gradients (E2, Section 7) |
| Astala 1994 | l. 325 | the classical higher integrability of quasiconformal maps, which Corollary 2 implies, as the paper says: proved in Lean from Corollary 2 (b), with its sharpness |

These citations only give context and are not used in proofs:
- Šverák 1990 and Burkholder 1984, 1989 (origin of `L` and `B_p`);
- Dacorogna 2007 (quasiconvexity);
- Astala–Iwaniec–Martin 2009 (`𝒮`);
- Astala et al. 2012, 2023, 2024 and Guerra–Kristensen 2021;
- the suboptimal upper bounds:
  - Bañuelos–Wang;
  - Nazarov–Volberg;
  - Dragičević–Volberg;
  - Bañuelos–Janakiraman;
  - Borichev–Janakiraman–Volberg;
  - Bañuelos's survey;
- the conjecture and its setting:
  - Iwaniec 1982;
  - Donaldson–Sullivan;
  - Iwaniec–Martin;
  - Iwaniec–Sbordone;
  - Iwaniec 2002;
- Faraco–Székelyhidi, Kirchheim–Székelyhidi and Székelyhidi 2005;
- Ambrosio–De Philippis–Kirchheim, De Philippis–Figalli and De Philippis–Guerra–Tione;
- Bañuelos–Lindeman, Duse and Petermichl–Slavin–Wick.

## 3. Errors and gaps in the paper

### E1. The Hessian case (l. 285): a remark on an attribution

"In the case where $\varphi=\D u$ for some $u\in C^\infty_{\tp{per}}(Q)$ this result had been proved in \cite{Guerra2026b}."

Guerra's theorem (arXiv:2608.23388, theorem `thm:L` of its TeX) is stated differently: "For every $A\in\mathbb R^{2\times2}$ and every $u\in C_c^\infty(\mathbb R^2)$ we have $\int_{\mathbb R^2}\bigl[L(A+\D^2u)-L(A)\bigr]\d x\geq0$". That is, compactly supported potentials on `ℝ²`, not periodic ones.

The two forms are equivalent, by the standard argument that relates periodic and compactly supported test maps (Dacorogna, Prop. 5.13), in its second-order form. So the claim holds, but it is not literally Guerra's statement. This is a remark, not a gap: no proof uses the sentence.

In Lean:
- the paper's form, [`theorem1_hessian`](../../Agazzi/Hessian.lean): Theorem 1 for `φ = Du`, which is smooth and periodic;
- the equivalence, for every Borel, locally bounded integrand at every `A`, `CalculusOfVariations.hessian_periodic_iff_hasCompactSupport` in lean4-calculus-of-variations, with the argument of Dacorogna's proof: rescaled periodic functions and cut-offs near the boundary of the cube for one direction, and a rescaled, translated and periodically extended test function for the other; for `L`, [`theorem1_hessian_iff`](../../Agazzi/Hessian.lean);
- Guerra's form, [`External.Guerra.theorem1_1`](../../Agazzi/External/Guerra/TheoremL.lean), from the two.

### E2. Corollary 2 is proved only by reference (l. 301–316)

"By the arguments in \cite{Baernstein1997a} (see also \cite{Guerra2026b} for further details), Theorem~\ref{thm:L-quasiconvexity} implies:"

Baernstein and Montgomery-Smith argue on the plane at `A = 0`, for `f ∈ Ẇ^{1,2} (ℂ)` in their (1.1) and `f ∈ Ẇ^{1,p} (ℂ)` in their Conjectures 2 and 3 and remark (b). Guerra's "further details" work at every `A`, for Hessians of compactly supported potentials. Corollary 2 is a periodic statement at every `A`, for all gradients. The same arguments work, with the following adjustments, which the paper does not mention:
- the Mellin identities are applied at `A / t` with the test maps `φ / t`;
- Fubini's theorem is used on `Q × (0, ∞)`, with an integrable majorant;
- for `p > 2`, the null Lagrangian `det`;
- for `p = 2`, `B_2 = −det` by the paper's definition (the branch `2 ≤ p`), a null Lagrangian.

For the norm, the paper does not say how its periodic inequality reaches `L^p (ℂ)`. Baernstein and Montgomery-Smith state the passage from Conjecture 3 to the norm (remark (b)) without proof. Guerra's "further details" make it in the Hessian case, with a logarithmic potential and cut-offs `η_R` (proofs of the corollaries `cor:beurling` and `cor:beurling-lp` of that preprint). Two more adjustments are needed:
- the periodic inequality at `A = 0` is first brought to compactly supported maps of the plane, the test maps of the planar arguments (the standard equivalences of Dacorogna, Props. 5.13 and 5.11, in lean4-calculus-of-variations; E1 rests on the same relation between periodic and compactly supported test maps);
- Guerra's passage is made for gradients, with the Cauchy transform in place of the logarithmic potential (Section 7).

The corollary holds. In Lean:
- [`corollary2_lipschitz`](../../Agazzi/Corollary2/Quasiconvexity.lean#L285) and [`corollary2`](../../Agazzi/Corollary2/Quasiconvexity.lean#L424) follow Baernstein–Montgomery-Smith, through [`burkholderB_eq_mellin_of_lt_two`](../../Agazzi/Corollary2/Quasiconvexity.lean#L136), [`burkholderB_eq_mellin_of_two_lt`](../../Agazzi/Corollary2/Quasiconvexity.lean#L153) and [`burkholderB_two`](../../Agazzi/Corollary2/Quasiconvexity.lean#L173);
- [`beurlingNorm_le`](../../Agazzi/Corollary2/Norm.lean#L371) and [`corollary2_norm`](../../Agazzi/Corollary2/Norm.lean#L378) follow them on the plane:
  - Corollary 2 at `A = 0` gives quasiconvexity on every ball ([`Corollary2Norm.integral_burkholderB_jacobian_nonneg`](../../Agazzi/Corollary2/Norm.lean#L246));
  - that gives Conjecture 2 for `u ∈ C_c^∞ (ℂ)` ([`Corollary2Norm.integral_phi_dz_dzbar_nonneg`](../../Agazzi/Corollary2/Norm.lean#L278), [`Corollary2Norm.integral_phi_dzbar_dz_nonneg`](../../Agazzi/Corollary2/Norm.lean#L293));
  - with Burkholder's inequality and `u ↦ ū`, Conjecture 3 ([`Corollary2Norm.integral_norm_dz_rpow_le`](../../Agazzi/Corollary2/Norm.lean#L341));
  - remark (b) ([`External.BaernsteinMontgomerySmith.remark_b`](../../Agazzi/External/BaernsteinMontgomerySmith/RemarkB.lean#L116)) concludes, by Guerra's argument, as formalized in HarmonicAnalysis.

### E3. The closedness of `𝒞` (l. 412)

"The set $\mc C$ is nonempty, closed and convex in $L^2(Q)$."

Closedness is not argued, and it is what the existence of the projection rests on. It holds. The formalization proves it in [`Agazzi/Proof/ScalarProjection/Existence.lean`](../../Agazzi/Proof/ScalarProjection/Existence.lean) and in the module `CalculusOfVariations.Lipschitz.GradientConstraint` of the package lean4-calculus-of-variations:
- `p + Dξ ∈ K` a.e. is equivalent to the slope bound `ξ (y) − ξ (x) + p · (y − x) ≤ H_K (y − x)` for all `x`, `y`:
  - one direction by mollification and the mean value theorem (`CalculusOfVariations.sub_add_dotProduct_le_supportFun_of_ae_mem`);
  - the other at points of differentiability (`CalculusOfVariations.add_fderiv_mem_of_sub_add_dotProduct_le_supportFun`);
- the slope bound gives a Lipschitz constant that depends only on `K` and `p`;
- an `L²`-convergent sequence has an a.e.-convergent subsequence;
- being equi-Lipschitz and periodic, that subsequence converges everywhere (`CalculusOfVariations.exists_tendsto_of_ae_restrict_unitCube_tendsto`), to a limit that keeps the slope bound.

### E4. "By changing signs" (l. 422): a remark

"By changing signs, we may assume $h(x_0)>0$."

The reduction replaces `(η, ζ, K, p)` by `(−η, −ζ, −K, −p)`. It is a standard reduction and it is correct; the paper states it in three words.

The formalization runs the mirror construction explicitly, with `s = ±1`:
- the cone `c (x) = w (x₀) − ε + H (x − x₀)`;
- the function `min {w, c}`;
- the competitor `ζ − (w − c)₊`.

The independent review checked that this is the image of the paper's construction under the sign change.

### E5. The ball in the torus (l. 434)

"Thus $(c-w)_+$ has compact support in $B_r(x_0)$ and, extending it by zero outside $B_r(x_0)$, we obtain $\zeta+(c-w)_+\in\mc C$".

On the torus, this needs `B_r (x₀)` to embed in `Q` (for instance `r < 1/2`) and a periodic extension. Since `r` can be shrunk, the step holds. The formalization takes `r ≤ 1/4` and periodizes with `CalculusOfVariations.supPeriodize` (module `CalculusOfVariations.Lipschitz.Periodize` of the package lean4-calculus-of-variations).

### E6. Typos and notation

- l. 321: "Previous, suboptimal bounds, had been obtained": stray commas.
- l. 327: "implying a similar results".
- l. 377: "where $\varphi\in C^\infty_\tp{per}(Q)$" for $C^\infty_\tp{per}(Q;\R^2)$.
- l. 382: "to $u^1(x)=A^1\cdot x+\eta(x)$": `η` is not introduced; it is `φ¹`.
- l. 401: "take $p\in K$": a clash of notation, not a typo: the point of `K` has the name of the exponent `p` of Corollary 2.

## 4. Missing hypotheses

None: every statement of the paper is true as printed.

## 5. Redundant hypotheses

None in the paper's statements.

- In Lemma 4, `p ∈ K` is equivalent to `𝒞 ≠ ∅`: if `ξ ∈ 𝒞`, then `p = ∫_Q (p + Dξ) ∈ K`, since `K` is closed and convex, `∫_Q Dξ = 0` and `|Q| = 1`.
- The paper uses it once, for the existence and uniqueness of `ζ` (l. 412).
- Lean's [`lemma4`](../../Agazzi/Proof/ScalarProjection/Main.lean#L748) takes a minimizer as a hypothesis, so there `p ∈ K` follows from the others and is unused; [`lemma4_exists`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L200) and [`lemma4_unique`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L238) use it: Kinderlehrer–Stampacchia's Lemma 2.1 needs `𝒞 ≠ ∅`. The uniqueness alone needs only the convexity of `𝒞` (Section 11).
- "`K` nonempty" follows from `p ∈ K`.

## 6. How the formalization reads the paper

- `ℝ^{2×2}` is `Matrix (Fin 2) (Fin 2) ℝ` and `ℝ²` is `Fin 2 → ℝ`.
- `a₊`, `a₋` are `conformalPart A`, `anticonformalPart A`, with `A z = a₊ z + a₋ z̄` for `z` a column vector.
- `|A|` in the definition of `L` is `|a₊| + |a₋|`, the operator norm ([`opNorm_eq`](../../Agazzi/Bridges.lean#L150)).
- The torus `Q = ℝ² / ℤ²` is represented by `ℤ²`-periodic maps on `ℝ²` ([`IsPeriodic`](../../palomar/Agazzi/Challenge.lean#L121)), with integrals over the open unit square [`unitSquare`](../../palomar/Agazzi/Challenge.lean#L116), of measure `1` ([`volume_unitSquare`](../../Agazzi/Bridges.lean#L46)).
- `Dφ` is `jacobian φ x`, the matrix `(∂_j φ_i (x))`. Its rows are the gradients of the components, as in the paper's `D u = (D u¹, D u²)`. It equals the package's `grad`.
- `W^{1,∞}_per (Q)` is represented by Lipschitz periodic functions ([`LipPer`](../../Agazzi/Proof/ScalarProjection/Defs.lean#L42)), the Lipschitz representatives of its classes. `Dξ` is the a.e. derivative.
- The `L² (Q)`-projection of `η` on `𝒞` is a minimizer of `ξ ↦ ∫_Q (η − ξ)²` on `𝒞` ([`IsL2Projection`](../../Agazzi/Proof/ScalarProjection/Defs.lean#L51)).
  - Lemma 4 is proved for every minimizer.
  - [`lemma4_exists`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L200) proves existence through `Lp ℝ 2`, and [`lemma4_unique`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L238) the uniqueness that the paper states: two minimizers are equal as Lipschitz periodic functions, hence in `W^{1,∞}_per (Q)` and in `L² (Q)`.
- `‖𝒮‖_{L^p (ℂ; ℂ) → L^p (ℂ; ℂ)}` is `beurlingNorm p`: the supremum of `‖𝒮 f‖_p / ‖f‖_p` over Schwartz functions, with `𝒮` the multiplier `ξ̄ / ξ` under Mathlib's Fourier transform. It equals the package's `beurlingPowNorm 1 p` ([`beurlingNorm_eq_beurlingPowNorm`](../../Agazzi/Bridges.lean#L56)), and `𝒮 ∂_z̄ = ∂_z` ([`beurling_dzbar`](../../Agazzi/Bridges.lean#L78)).
- `B_p` ([`burkholderB`](../../palomar/Agazzi/Challenge.lean#L106)) is defined for every real `p` and used for `p > 1`.
- The Hessian `D²u` of `u : ℝ² → ℝ` is the derivative matrix of the gradient, `jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x`; it is the package's `CalculusOfVariations.hessian` ([`jacobian_gradient_eq_hessian`](../../Agazzi/Hessian.lean#L43)).
- `W^{1,2}_loc (Ω)` is defined by weak partial derivatives ([`MemW12Loc`](../../palomar/Agazzi/Challenge.lean)): `f`, `fx`, `fy` are in `L²` of every compact subset of `Ω`, and `∫ f ∂_x φ = −∫ fx φ`, `∫ f ∂_y φ = −∫ fy φ` for every real `φ ∈ C_c^∞` with support in `Ω`. This is the standard definition; real test functions suffice for complex `f`, by linearity. The package HarmonicAnalysis uses the equivalent form with a weak derivative `Df : ℂ → (ℂ →L[ℝ] ℂ)`, `Df (z) v = v.re fx (z) + v.im fy (z)`.
- `|∂̄f| ≤ k |∂f|` is `|fx + i fy| ≤ k |fx − i fy|`, and `Df ∈ L^p_loc (Ω)` is `fx, fy ∈ L^p_loc (Ω)`. The range `2 ≤ p < 1 + 1/k = 2K/(K − 1)` is written `2 ≤ p`, `k (p − 1) < 1`, which gives every `p ≥ 2` for `k = 0`.
- The paper speaks of quasiconformal maps; [`astala`](../../Agazzi/Astala.lean) assumes no homeomorphism, so it covers the quasiregular maps. [`astala_sharp`](../../Agazzi/Astala.lean) shows that the radial stretch is quasiconformal: a homeomorphism of `ℂ`, in `W^{1,2}_loc (ℂ)` with its pointwise partial derivatives as weak ones, and `|∂̄f| = k |∂f|` off `0`. Its derivative is not in `L^{2K/(K−1)}` near `0`: `∂_x f` is not in `L^{2K/(K−1)}` of any disc around `0`.
- Lemma 3 has no `\label` in the TeX (l. 345). The formalization names it by its display, `eq:L-row-representation`.
- Theorem 1 and the first assertion of Corollary 2 are proved for Lipschitz periodic test maps ([`theorem1_lipschitz`](../../Agazzi/Theorem1.lean#L250), [`corollary2_lipschitz`](../../Agazzi/Corollary2/Quasiconvexity.lean#L285)), by the paper's arguments, which use nothing more. The paper's statements for `C^∞` maps follow ([`theorem1`](../../Agazzi/Theorem1.lean#L401), [`corollary2`](../../Agazzi/Corollary2/Quasiconvexity.lean#L424)). This stronger form gives quasiconvexity in the sense of the package CalculusOfVariations, with Lipschitz test maps vanishing outside the unit cube ([`quasiconvex_integrandL`](../../Agazzi/Quasiconvex.lean#L68), [`quasiconvex_burkholderB`](../../Agazzi/Quasiconvex.lean#L74), [`quasiconvex_burkholder`](../../Agazzi/Quasiconvex.lean#L82)).

No statement of the paper was corrected.

## 7. Departures from the paper's proofs

None. Every proof follows the paper's argument or, where the paper only cites, the argument of the cited sources. Two cited statements that no proof of the paper uses are proved by other arguments, as Section 2 says: Lehto's lower bound, whose source was not available, and Guerra's Theorem 1.1, from the paper's Theorem 1.

The statements of the introduction and of the proofs follow the paper:
- the Hessian case of Theorem 1 is Theorem 1 for `φ = Du`;
- the uniqueness of the projection is the uniqueness in Kinderlehrer–Stampacchia's Lemma 2.1, which the paper cites for it (l. 412);
- for Astala's theorem the paper says only that Corollary 2 implies it (l. 325); the formalization derives it from Corollary 2 (b) by Iwaniec's derivation, the standard one (Section 2).

The second assertion of Corollary 2 is proved "by the arguments in" Baernstein–Montgomery-Smith, with Guerra's "further details" (E2). Its upper bound, [`beurlingNorm_le`](../../Agazzi/Corollary2/Norm.lean#L371), follows those planar arguments:
- Corollary 2 at `A = 0` as quasiconvexity with compactly supported test maps;
- their Conjectures 2 and 3 for `u ∈ C_c^∞ (ℂ)`, with Burkholder's inequality and the interchange of `∂` and `∂̄`;
- their remark (b), by Guerra's passage to `L^p (ℂ)` with a potential and cut-offs `η_R`.

The remark is proved in the package HarmonicAnalysis (`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`) by Guerra's proof, with Guerra's dense class `C_c^∞`:
- for `g ∈ C_c^∞`, the potential is its Cauchy transform `f (z) = (1/π) ∫ g (w) / (z − w) dw`:
  - `∂̄f = g`, by the Cauchy–Pompeiu formula;
  - `∂f = 𝒮 g`;
  - `f = O (1/|z|)` and `∂f = O (1/|z|²)`;
- the inequality is applied to `η_R f`, with Guerra's cut-offs, and `R → ∞`: the cut-off error `‖f ∇η_R‖_p` is `O (R^{2/p − 2})`, which tends to `0` for every `p > 1`;
- density carries the bound from `C_c^∞` to the Schwartz functions over which the norm is a supremum.

One departure from Guerra's text is forced: Guerra proves a bound for Hessians of real potentials (a real `h`, its logarithmic potential), and the norm on complex `L^p` needs the gradient case (a complex `g`, its Cauchy transform). Guerra states the properties of the potential without proof:
- `Δu = 2h`;
- its decay;
- `𝒮h = 2u_{zz}`, which applies `𝒮 ∘ ∂_z̄ = ∂_z` to a function that is not a Schwartz function.

Their gradient analogues are proved in the package, the last one by Liouville's theorem. Guerra's "by density" presupposes that `𝒮` is bounded on `L^p`, which the package does not prove; its density step uses the convergence of the Fourier transforms in `L¹` and Fatou's lemma instead.

A shorter proof of the upper bound, on the torus and by transference (Hytönen–van Neerven–Veraar–Weis, Cor. 5.7.6), is [`beurlingNorm_le_of_torus`](../../Agazzi/Corollary2/NormTorus.lean#L355); [`corollary2_norm`](../../Agazzi/Corollary2/Norm.lean#L378) does not use it (Section 11).

Every proof follows its source step by step. Only the following differ, and only in mechanics:
- In Lemma 4, the sup norm of `Fin 2 → ℝ` is used inside the proof (balls, `ρ`), in place of the Euclidean norm, with the constants adjusted.
- In Theorem 1, Jensen's inequality for `F` is proved through `F = sup_{|z| = 1} G_z`.
- In Lemma 4, the sign change and the periodization are made explicit (E4, E5).
- In Corollary 2 (b), the test maps on the plane are `φ = (Re u, Im u)` for `u : ℂ → ℂ`, and the integrals over `ℝ²` and over `ℂ` are identified by `Complex.measurableEquivPi`.

## 8. What each result depends on

From the current output of [`scripts/Audit.lean`](../../scripts/Audit.lean). Every result depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and so do all 408 declarations of the library.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Theorem 1 | [`theorem1`](../../Agazzi/Theorem1.lean#L401) | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50), [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) |
| Theorem 1, Lipschitz form | [`theorem1_lipschitz`](../../Agazzi/Theorem1.lean#L250) | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50), [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) |
| Corollary 2 (a) | [`corollary2`](../../Agazzi/Corollary2/Quasiconvexity.lean#L424) | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50), [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39), [`External.BaernsteinMontgomerySmith.equation1_2a`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L231), [`External.BaernsteinMontgomerySmith.equation1_2b`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L288) |
| Corollary 2 (a), Lipschitz form | [`corollary2_lipschitz`](../../Agazzi/Corollary2/Quasiconvexity.lean#L285) | the same |
| Corollary 2 (b) | [`corollary2_norm`](../../Agazzi/Corollary2/Norm.lean#L378) | the same, and [`External.BaernsteinMontgomerySmith.phi_le`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L332), [`External.BaernsteinMontgomerySmith.remark_b`](../../Agazzi/External/BaernsteinMontgomerySmith/RemarkB.lean#L116), [`External.Lehto.lowerBound`](../../Agazzi/External/Lehto/LowerBound.lean#L68) |
| Corollary 2 (b), upper bound: the alternative proof on the torus (Section 11) | [`beurlingNorm_le_of_torus`](../../Agazzi/Corollary2/NormTorus.lean#L355) | the results of Corollary 2 (a), and [`External.BaernsteinMontgomerySmith.phi_le`](../../Agazzi/External/BaernsteinMontgomerySmith/Basic.lean#L332); transference from the package HarmonicAnalysis |
| Lemma 3 | [`lemma3`](../../Agazzi/Proof/RowRepresentation.lean#L220) | none |
| Lemma 4 | [`lemma4`](../../Agazzi/Proof/ScalarProjection/Main.lean#L748) | [`External.KinderlehrerStampacchia.theorem2_3`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L39) |
| Lemma 4, uniqueness of the projection | [`lemma4_unique`](../../Agazzi/Proof/ScalarProjection/Existence.lean#L238) | [`External.KinderlehrerStampacchia.lemma2_1`](../../Agazzi/External/KinderlehrerStampacchia/Projection.lean#L50) |
| Theorem 1, Hessian case | [`theorem1_hessian`](../../Agazzi/Hessian.lean#L66) | those of Theorem 1 |
| Theorem 1, Hessian case: the periodic and the compactly supported forms are equivalent | [`theorem1_hessian_iff`](../../Agazzi/Hessian.lean#L78) | none |
| Astala's theorem, from Corollary 2 (b) | [`astala`](../../Agazzi/Astala.lean#L158) | those of Corollary 2 (b) |
| Astala's theorem, sharpness | [`astala_sharp`](../../Agazzi/Astala.lean#L210) | none |

The route check compares, for each result, the paper's own numbered results that its formal proof uses with those that the paper's proof cites. It finds no difference, and [`docs/Agazzi/route_differences.tsv`](route_differences.tsv) records none. It does not compare results from the literature. It covers the results with a TeX label; the uniqueness of the projection, the Hessian case and Astala's theorem have none, and their proofs use Kinderlehrer–Stampacchia's Lemma 2.1, Theorem 1 and Corollary 2 (b) respectively, as the paper says (Section 7).

## 9. Not formalized

- The extensions that the paper announces for later articles of the series, without precise statements (l. 327): to higher dimensions and to the Beurling–Ahlfors transform on forms, to the integrands of Faraco–Székelyhidi, Kirchheim–Székelyhidi and Székelyhidi, and to the Monge–Ampère equation.
- The results that the paper cites only for context, listed at the end of Section 2, among them the earlier upper bounds for `‖𝒮‖_p` and the earlier quasiconvexity results under sign restrictions. The paper's proofs do not use them.
- The classical lower bound is proved, but by the argument named in Section 2, not by Lehto's, which was not available.

## 10. The paper in the literature

Sources: the paper's own account (l. 276–327), and searches on 23 November 2026:
- arXiv, through its API, by title, author and keyword, for work since August 2026;
- Semantic Scholar's list of the works that cite the paper, with the arXiv full texts of those works;
- the v1 source of the paper;
- GitHub code search, for `2609.28311`.

Bibliographic data not verified against the work itself are marked "as in the paper's bibliography". Not available, and not read:
- Kinderlehrer–Stampacchia's book;
- Lehto 1965;
- Iwaniec 1982;
- Astala 1994;
- the book of Astala, Iwaniec and Martin (2009);
- Burkholder 1988.

### Before the paper

- D. L. Burkholder, *Differential subordination of harmonic functions and martingales*, in: Harmonic Analysis and PDE (El Escorial, 1987), Lecture Notes in Math. 1384, Springer, 1989, 1–23 (published; the series and the conference are taken from other bibliographies). V. Šverák, *Examples of rank-one convex functions*, Proc. Roy. Soc. Edinburgh 114A (1990), 237–242 (published; as in the paper's bibliography). These are the origin of `L`; not read here.
- A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and `∂̄f`* (published 1999; first version 15 September 1997; [arXiv:math/9709215v2](https://arxiv.org/abs/math/9709215), read). They show that their Conjecture 1, the quasiconvexity of `L` at `0` on the plane, implies their Conjecture 2 (`∫ Φ_p (∂f, ∂̄f) ≥ 0`) and Iwaniec's conjecture, and they give the functions `f_α` that show that `p* − 1` cannot be lowered (see Section 2 of this report).
- T. Iwaniec, *Extremal inequalities in Sobolev spaces and quasiconformal mappings*, Z. Anal. Anwend. 1 (1982) (published; as in the paper's bibliography; not read). This is the conjecture `‖𝒮‖_p = p* − 1`. O. Lehto (1965) proved the lower bound (not read).
- Suboptimal upper bounds, as the paper lists them (l. 321; published; not read here):
  - Bañuelos–Wang (Duke 1995);
  - Nazarov–Volberg (St. Petersburg Math. J. 2004);
  - Dragičević–Volberg (Indiana 2005);
  - Bañuelos–Janakiraman (Trans. AMS 2008);
  - Borichev–Janakiraman–Volberg (Duke 2013);
  - the survey of R. Bañuelos, [arXiv:1012.4850](https://arxiv.org/abs/1012.4850) (Illinois J. Math. 2010).
- Quasiconvexity of the Burkholder functional under sign restrictions, as the paper lists them:
  - Astala–Iwaniec–Prause–Saksman (J. AMS 2012);
  - Astala–Faraco–Guerra–Koski–Kristensen, *The local Burkholder functional, quasiconvexity and geometric function theory*, [arXiv:2309.03495](https://arxiv.org/abs/2309.03495) (2023; no journal reference on arXiv);
  - the same authors, *Lower semicontinuity, Stoilow factorization and principal maps*, Commun. Pure Appl. Anal. 23 (2024) (as in the paper's bibliography);
  - Guerra–Kristensen, [arXiv:2112.10563](https://arxiv.org/abs/2112.10563) (Arch. Ration. Mech. Anal. 2022).

### Concurrent work

- A. Guerra, *Quasiconvexity of the Burkholder function on symmetric matrices*, [arXiv:2608.23388v1](https://arxiv.org/abs/2608.23388) (24 August 2026, preprint, read in part). It claims Theorem 1 for Hessians `D²u`, `u ∈ C_c^∞ (ℝ²)`, by Morse theory, with sharp weak-type and `L^p` bounds for `𝒮` on real-valued `h` (for `p > 2`: when `𝒮h` is real-valued). The paper cites it (E1, E2).
- K. Domelevo and S. Petermichl, *The sharp `L^p` bound for the imaginary part of the Beurling–Ahlfors operator on the lattice*, [arXiv:2609.13573](https://arxiv.org/abs/2609.13573) (v1 11 September, v2 15 September 2026, preprint). It claims the sharp `ℓ^p` bound `p* − 1` for a family of second-order discrete Riesz transforms on `ℤ^N`, which includes the imaginary part of the discrete Beurling–Ahlfors operator on `ℤ²`. It predates the paper, which does not cite it.
- The README of the package lean4-harmonic-analysis records a bound `1.523958 (p* − 1)` as claimed in a 2026 manuscript of the repository Tencent-Hunyuan/Hyra-results. This was not checked here.

### Since the paper

- No version later than v2, and no erratum, was found (arXiv API, 23 November 2026).
- Preprints that cite the paper, from Semantic Scholar's citation list and the arXiv full texts; their claims are as their authors state them:
  - G. N. Memana, N. S. Trudinger and P.-L. Yung, *Fractional elementary symmetric functions and Hessian estimates in the plane*, [arXiv:2610.19410](https://arxiv.org/abs/2610.19410) (14 October 2026). It cites v1 and builds a real-variable proof of the local Burkholder inequality of Astala–Faraco–Guerra–Koski–Kristensen on the paper's Lemma 3, Lemma 4 and Theorem 1, passing from the torus to the disc by zero extension.
  - A. Braides, J. Kristensen and S. Scalabrino, *Energies with values in networks and geometric quasiconvexity*, [arXiv:2610.32444](https://arxiv.org/abs/2610.32444) (23 October 2026). It uses the quasiconvexity of `B_p`, `1 < p < 2`, for a lower bound on a homogenized density.
  - D. Zhong, [arXiv:2608.16757v2](https://arxiv.org/abs/2608.16757) (28 September 2026). It discusses why the paper's row-wise projection does not preserve Hessian structure.
  - Three preprints cite only the value of the norm:
    - T. Sprekeler and H. V. Tran, [arXiv:2610.17142](https://arxiv.org/abs/2610.17142);
    - K. Moen and C. Pérez, [arXiv:2610.31888](https://arxiv.org/abs/2610.31888);
    - J. C. Cantero et al., [arXiv:2611.23073](https://arxiv.org/abs/2611.23073).
- [arXiv:2611.17088](https://arxiv.org/abs/2611.17088) (N. Q. Le, 12 November 2026), on degenerate Monge–Ampère equations, was returned by the search but does not cite the paper.
- No Part II of the series and no independent proof of the conjecture was found.

### Formalizations

- This is, as far as the search found, the first formalization of the paper, of Theorem 1 and of Iwaniec's conjecture. The independent review did not repeat the GitHub search.
- The GitHub code search for `2609.28311` found no Lean formalization. It found only mentions in the READMEs of Lean repositories, among them that of lean4-harmonic-analysis, and non-Lean listings (feeds, a problem catalogue).
- The README of lean4-harmonic-analysis lists other Lean formalizations about `𝒮`. None of them was opened or consulted here:
  - boundedness on `L^p` (will1491/no-wandering-domains, TauCetiProject/TauCeti);
  - the `L²` isometry (openai/math, Tencent-Hunyuan/Hyra-results);
  - statements without proof of Lehto's bound and of Iwaniec's conjecture (facebookresearch/atlas-lean).
- The cited results that the paper uses are proved here, with the help of three packages: lean4-calculus-of-variations, lean4-harmonic-analysis and lean4-banach-probability (see the README).

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **The series.** The paper announces later parts of the series:
  - the higher-dimensional theory: the Beurling–Ahlfors transform on forms, after Donaldson–Sullivan and Iwaniec–Martin, with the sharp higher integrability of quasiregular maps in even dimensions;
  - the separating functions of Faraco–Székelyhidi, Kirchheim–Székelyhidi and Székelyhidi.
- **Weak type.** Guerra's weak-type corollary (arXiv:2608.23388) applies `L (A/λ) ≤ (2/λ) |a₊| − 1_{|a₋| > λ}` to the Hessian of the logarithmic potential of a real-valued `h`, with cut-offs. With Theorem 1 for all matrices, the same bound applied to `f̄`, where `f` is the Cauchy transform of a complex-valued `h` (`∂̄f = h`, `∂f = 𝒮h`; conjugation exchanges `|a₊|` and `|a₋|`), appears to give `λ |{|𝒮 h| > λ}| ≤ 2 ‖h‖₁`. Guerra claims, by laminates, that `2` is sharp for real `h`, hence also for complex `h`. The pointwise bound was checked on paper, twice. The compactly supported form of Theorem 1 that the argument needs is in Lean ([`quasiconvex_integrandL`](../../Agazzi/Quasiconvex.lean#L68)). Neither the paper nor Guerra's preprint states the complex case, and an arXiv abstract search of 23 November 2026 found no work that does. The Cauchy transform of `g ∈ C_c^∞`, with its decay, and Guerra's cut-offs are in lean4-harmonic-analysis.
- **Astala's area distortion.** Astala's theorem in its full form is an area distortion estimate, `|f (E)| ≤ C |E|^{1/K}` for `K`-quasiconformal maps `f` of the disc. The paper claims only its consequence for the higher integrability of the derivatives, which is formalized ([`astala`](../../Agazzi/Astala.lean)); the area distortion estimate is not.
- **Higher powers.** The conjecture `‖𝒮^n‖_p = κ_n (p)` for `p ≥ 2` (Dragičević) remains open for `n ≥ 2`, as far as lean4-harmonic-analysis's README records. Corollary 2 gives `‖𝒮²‖_p ≤ (p* − 1)²`, but this does not improve on the known bounds for large `p`.

### Simpler proofs

Each was checked on paper only, except where noted.
- **The uniqueness of the projection** needs only the convexity of `𝒞`, not its closedness: adding the variational inequalities `∫_Q (η − ζ₁)(ζ₂ − ζ₁) ≤ 0` and `∫_Q (η − ζ₂)(ζ₁ − ζ₂) ≤ 0` of two minimizers gives `∫_Q (ζ₁ − ζ₂)² ≤ 0`. The formalization follows the paper and uses Kinderlehrer–Stampacchia's Lemma 2.1, under the hypotheses of Lemma 4.
- **The variational inequality.** It follows from the minimality of `ζ` by a first variation: `ζ + t (ξ − ζ) ∈ 𝒞`, then `t → 0⁺`. This needs no Hilbert-space projection; existence still needs one, or another compactness argument.
- **The interior case split in Lemma 4 is redundant.** The pointwise conclusion `Dw (x₀) ∉ int K` holds trivially when `int K = ∅`, and `∂K = K ∖ int K` for closed `K`.
- **`∫_Q ∂_v f = 0`** follows from translation invariance and difference quotients. The formalization derives it from the package's null Lagrangians instead. This one was checked in Lean, against lean4-calculus-of-variations, which holds the lemma; that package's README records it.
- **The convexity of `F`** is immediate from its definition as a supremum of the affine functions `G_z`.
- **Theorem 1 for `|A| > 1`.** The chain `L (A) = sup_z G_z (A) = sup_z ∫_Q G_z (Du) ≤ ∫_Q L (Du)` skips `F`.
- **Lehto's lower bound.** Duality, `‖𝒮‖_p = ‖𝒮‖_{p'}`, replaces the second family `f̄_α`. The formalization uses it.
- **The upper bound `‖𝒮‖_p ≤ p* − 1` on the torus.** The paper's Corollary 2 is periodic, so the bound can be proved on the torus and transferred to the plane. Corollary 2 at `A = 0` and Burkholder's inequality give `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂̄u‖_{L^p (Q)}` for smooth periodic `u`, hence the bound on `L^p_0 (𝕋²)`, and transference (Hytönen–van Neerven–Veraar–Weis, Cor. 5.7.6, in lean4-harmonic-analysis) gives `L^p (ℂ)`. It needs none of the planar tools: neither the Cauchy transform nor the cut-offs. This one is checked in Lean: [`beurlingNorm_le_of_torus`](../../Agazzi/Corollary2/NormTorus.lean#L355), in [`Agazzi/Corollary2/NormTorus.lean`](../../Agazzi/Corollary2/NormTorus.lean); [`corollary2_norm`](../../Agazzi/Corollary2/Norm.lean#L378) follows the paper's route instead.
- **Guerra's passage with another dense class.** The Schwartz functions whose Fourier transform is compactly supported off `0` (Hytönen–van Neerven–Veraar–Weis, Prop. 2.4.23 (ii)) have Schwartz Cauchy transforms, built on the Fourier side, so the cut-off step needs neither the kernel nor its estimates. This was checked in Lean; lean4-harmonic-analysis records it among its shorter proofs.

### The formalization

- **The gradient-constrained `L²` projection** (the closedness of `𝒞` and the existence of the projection) is stated for the paper's objects, in [`Agazzi/Proof/ScalarProjection/`](../../Agazzi/Proof/ScalarProjection), and stays here. Its general tools are in lean4-calculus-of-variations, and a general form on `(0, 1)^m` could join them.
- **`External/` holds material other formalizations could reuse:** the Mellin identities of Baernstein–Montgomery-Smith.
- **Duplicates.** Three private copies of `volume unitSquare = 1` remain, and some public helpers are missing from their module docstrings.
