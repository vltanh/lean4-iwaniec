/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Baernstein and Montgomery-Smith: the Burkholder–Šverák function and its Mellin transforms

A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
`∂̄f`*, in: Complex analysis and differential equations (Uppsala, 1997), Acta Univ. Upsaliensis
Skr. Uppsala Univ. C Organ. Hist. 64 (1999), 92–109; arXiv:math/9709215v2 (the version read).

In the source's own terms, for `z, w ∈ ℂ` (TeX of arXiv:math/9709215v2, §1):

* `L (z, w) = |z|² − |w|²` if `|z| + |w| ≤ 1`, `2|z| − 1` if `|z| + |w| > 1`;
* `p* = max (p, p')`, `1/p + 1/p' = 1`, and
  `Φ_p (z, w) = α_p ((p* − 1)|z| − |w|)(|z| + |w|)^{p−1}`, `α_p = p (1 − 1/p*)^{p−1}`;
* (1.2a): `∫_0^∞ t^{p−1} L (z/t, w/t) dt = β_p Φ_p (z, w)` for `1 < p < 2`,
  `β_p = (½ p (2 − p) α_p)⁻¹`;
* (1.2b): with `M (z, w) = L (z, w) − (|z|² − |w|²)`,
  `∫_0^∞ t^{p−1} M (w/t, z/t) dt = γ_p Φ_p (z, w)` for `2 < p < ∞`,
  `γ_p = (½ p (p − 1)(p − 2) α_p)⁻¹`;
* "From [Bu3, p. 77] follows the inequality" `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p`
  (`1 < p < ∞`); [Bu3] is D. L. Burkholder, *Sharp inequalities for martingales and stochastic
  integrals*, Colloque Paul Lévy (Palaiseau, 1987), Astérisque 157–158 (1988), 75–94 (as listed in
  the source).

The paper (arXiv:2609.28311, TeX line 301) proves its Corollary 2 "by the arguments in
[Baernstein1997a]": these identities, the null Lagrangian `∫ |∂f|² − |∂̄f|² = 0`, and this
inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace External.BaernsteinMontgomerySmith

/-- The Burkholder–Šverák function `L : ℂ × ℂ → ℝ`. -/
def L (z w : ℂ) : ℝ :=
  if ‖z‖ + ‖w‖ ≤ 1 then ‖z‖ ^ 2 - ‖w‖ ^ 2 else 2 * ‖z‖ - 1

/-- `M (z, w) = L (z, w) − (|z|² − |w|²)`. -/
def M (z w : ℂ) : ℝ := L z w - (‖z‖ ^ 2 - ‖w‖ ^ 2)

/-- `p* = max (p, p')`, `p' = p / (p − 1)`. -/
def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- `α_p = p (1 − 1/p*)^{p−1}`. -/
def alpha (p : ℝ) : ℝ := p * (1 - 1 / pStar p) ^ (p - 1)

/-- `Φ_p (z, w) = α_p ((p* − 1)|z| − |w|)(|z| + |w|)^{p−1}`. -/
def Phi (p : ℝ) (z w : ℂ) : ℝ :=
  alpha p * ((pStar p - 1) * ‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) ^ (p - 1)

/-- `β_p = (½ p (2 − p) α_p)⁻¹`. -/
def beta (p : ℝ) : ℝ := (p * (2 - p) * alpha p / 2)⁻¹

/-- `γ_p = (½ p (p − 1)(p − 2) α_p)⁻¹`. -/
def gamma (p : ℝ) : ℝ := (p * (p - 1) * (p - 2) * alpha p / 2)⁻¹

/-- The integrand of (1.2a) is integrable on `(0, ∞)` for `1 < p < 2`. -/
theorem integrableOn_equation1_2a {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (z w : ℂ) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * L (z / t) (w / t)) (Set.Ioi 0) := by
  sorry

/-- **(1.2a)**: `∫_0^∞ t^{p−1} L (z/t, w/t) dt = β_p Φ_p (z, w)` for `1 < p < 2`. -/
theorem equation1_2a {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (z w : ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * L (z / t) (w / t) = beta p * Phi p z w := by
  sorry

/-- The integrand of (1.2b) is integrable on `(0, ∞)` for `2 < p`. -/
theorem integrableOn_equation1_2b {p : ℝ} (hp : 2 < p) (z w : ℂ) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * M (w / t) (z / t)) (Set.Ioi 0) := by
  sorry

/-- **(1.2b)**: `∫_0^∞ t^{p−1} M (w/t, z/t) dt = γ_p Φ_p (z, w)` for `2 < p < ∞`. -/
theorem equation1_2b {p : ℝ} (hp : 2 < p) (z w : ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * M (w / t) (z / t) = gamma p * Phi p z w := by
  sorry

/-- **Burkholder's inequality** as the source uses it ("From [Bu3, p. 77] follows the
inequality", §1): `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p` for `1 < p < ∞`. -/
theorem phi_le {p : ℝ} (hp : 1 < p) (z w : ℂ) :
    Phi p z w ≤ (pStar p - 1) ^ p * ‖z‖ ^ p - ‖w‖ ^ p := by
  sorry

end External.BaernsteinMontgomerySmith
