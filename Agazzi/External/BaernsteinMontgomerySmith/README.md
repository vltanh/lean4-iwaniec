# Baernstein and Montgomery-Smith: the Mellin identities and Burkholder's inequality

## Source

A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
`∂̄f`*, in: Complex analysis and differential equations (Uppsala, 1997), Acta Univ. Upsaliensis
Skr. Uppsala Univ. C Organ. Hist. 64 (1999), 92–109. Read in its arXiv version,
[arXiv:math/9709215v2](https://arxiv.org/abs/math/9709215), §1 and §5.

The paper (arXiv:2609.28311, TeX line 301) proves its Corollary 2 "by the arguments in
[Baernstein1997a] (see also [Guerra2026b] for further details)". Those arguments are the content of
this directory and of `Agazzi/Corollary2/`. Guerra's "further details" are A. Guerra,
*Quasiconvexity of the Burkholder function on symmetric matrices*,
[arXiv:2608.23388v1](https://arxiv.org/abs/2608.23388) (2026, preprint), read: its proofs of the
corollaries labelled `cor:beurling` and `cor:beurling-lp` in its TeX.

## Statements (`Basic.lean`, in the source's terms)

- `L (z, w)`, `M (z, w) = L (z, w) − (|z|² − |w|²)`, `p*`, `α_p`, `Φ_p`, `β_p`, `γ_p`: the
  source's definitions (§1).
- `External.BaernsteinMontgomerySmith.equation1_2a`: (1.2a),
  `∫_0^∞ t^{p−1} L (z/t, w/t) dt = β_p Φ_p (z, w)` for `1 < p < 2`.
- `External.BaernsteinMontgomerySmith.equation1_2b`: (1.2b),
  `∫_0^∞ t^{p−1} M (w/t, z/t) dt = γ_p Φ_p (z, w)` for `2 < p < ∞` (with the arguments of `M`
  exchanged, as in the source).
- `External.BaernsteinMontgomerySmith.phi_le`: the inequality that "follows from [Bu3, p. 77]",
  `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p` for `1 < p < ∞`; [Bu3] is D. L. Burkholder, *Sharp
  inequalities for martingales and stochastic integrals*, Astérisque 157–158 (1988), 75–94.
- `integrableOn_equation1_2a`, `integrableOn_equation1_2b`, `alpha_pos`: the integrability of the
  two integrands and `α_p > 0`.

## Statement (`RemarkB.lean`)

- `External.BaernsteinMontgomerySmith.remark_b`: remark (b) at the end of §1, "Truth of
  Conjecture 3 would show that the norm of `S` on `L^p (ℂ, ℂ)` is precisely `p* − 1`", for the
  upper bound and any constant: if `∫ |∂f|^p ≤ C^p ∫ |∂̄f|^p` for every smooth compactly supported
  `f : ℂ → ℂ`, then `‖𝒮‖_p ≤ C` (`1 < p < ∞`, `0 ≤ C`). Conjecture 3 is stated with `∂f` and `∂̄f`
  in the other order; the source notes that it holds if and only if it holds with them
  interchanged. The source gives no proof of the remark.

## How the paper uses them

With `z = a₊`, `w = a₋` in (1.2a) and `z = a₋`, `w = a₊` in (1.2b), the identities give the Mellin
representations of the Burkholder integrand (`Agazzi.burkholderB_eq_mellin_of_lt_two`,
`Agazzi.burkholderB_eq_mellin_of_two_lt`), from which Corollary 2 follows by Theorem 1, the null
Lagrangian `det` and Fubini's theorem. For the norm (`Agazzi.beurlingNorm_le`):
- Corollary 2 at `A = 0` gives Conjecture 2 for compactly supported maps;
- the inequality gives Conjecture 3;
- remark (b) gives the upper bound for `‖𝒮‖_p`.

## Arguments used

- (1.2a), (1.2b): direct integration. With `s = |z|`, `r = |w|`, `S = s + r`, the integrand is
  `t^{p−1} (2s/t − 1)` (resp. `t^{p−1} (2r/t − 1 − (r² − s²)/t²)`) on `(0, S)` and
  `t^{p−3} (s² − r²)` (resp. `0`) on `(S, ∞)`; the integrals of powers give
  `(2 / (p (2 − p))) S^{p−1} (s/(p − 1) − r)` and `(2 / (p (p − 1)(p − 2))) S^{p−1} ((p − 1) s − r)`.
  The source states the identities without proof ("one calculates").
- The inequality: Burkholder's majorization `V ≤ U` (Burkholder 1988, (1.10)), as formalized in
  the package BanachProbability (`BanachProbability.Burkholder.burkholderU_ge`), with
  `Φ_p (z, w) = −U (|w|, |z|)`.
- Remark (b): Guerra's passage to `L^p (ℂ)` (proof of `cor:beurling-lp`), in the gradient case, as
  formalized in the package HarmonicAnalysis
  (`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`):
  - for `g` in a dense class, its Cauchy transform `f` has `∂̄f = g` and `∂f = 𝒮 g`;
  - the inequality is applied to `η_R f`, with Guerra's cut-offs `η_R`, and `R → ∞`;
  - density then reaches every Schwartz `g`.

  Two departures from Guerra's text, both along the lines of that argument:
  - the Cauchy transform in place of the logarithmic potential: Guerra treats Hessians of real
    potentials, while the norm on complex `L^p` needs the gradient case;
  - the dense class: the Schwartz functions whose Fourier transform is compactly supported in
    `ℂ ∖ {0}` (Hytönen–van Neerven–Veraar–Weis, Prop. 2.4.23 (ii)), in place of `C_c^∞`. Their
    Cauchy transforms are Schwartz functions, built on the Fourier side, so no Cauchy kernel and
    no decay estimate are needed. Guerra's class would also work, since the Cauchy transform of
    `g ∈ C_c^∞` is `O (1/|z|)` and the cut-off error `‖f ∇η_R‖_p` is then `O (R^{2/p − 2})`; the
    change is for economy.
