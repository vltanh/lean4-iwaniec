/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Bridges
public import Agazzi.Corollary2.Quasiconvexity
public import Agazzi.External.Lehto.LowerBound

/-!
# Corollary 2, second part: the norm of the Beurling–Ahlfors transform

**Corollary 2** (`cor:Bp-BA`), second assertion `(eq:BA-sharp-norm)`:
`‖𝒮‖_{L^p (ℂ; ℂ) → L^p (ℂ; ℂ)} = p* − 1`, which is `(p − 1)⁻¹` for `1 < p ≤ 2` and `p − 1` for
`2 ≤ p < ∞` (`pStar_sub_one_of_le_two`, `pStar_sub_one_of_two_le`).

The paper derives it from Theorem 1 "by the arguments in [Baernstein1997a]" (TeX line 301), with the
lower bound from [Lehto1965] (TeX line 320). The upper bound: the first assertion of Corollary 2 at
`A = 0`, Burkholder's inequality `α_p B_p ≤ (p* − 1)^p |a₋|^p − |a₊|^p` (for `p ≥ 2`; for `p < 2`
with `a₊`, `a₋` exchanged, through `u ↦ ū`), and `𝒮 ∂_z̄ = ∂_z`, give
`‖∂_z u‖_p ≤ (p* − 1) ‖∂_z̄ u‖_p` for smooth periodic `u`, that is, the bound on the torus; the
passage to the plane (transference, as in the package `HarmonicAnalysis`) gives it on `L^p (ℂ)`.
-/

@[expose] public section

noncomputable section

namespace Agazzi

/-- The upper bound in `(eq:BA-sharp-norm)`: `‖𝒮‖_p ≤ p* − 1` for `1 < p < ∞`. -/
theorem beurlingNorm_le {p : ℝ} (hp : 1 < p) : beurlingNorm p ≤ ENNReal.ofReal (pStar p - 1) := by
  sorry

/-- **Corollary 2** (`cor:Bp-BA`), second assertion `(eq:BA-sharp-norm)`: the norm of the
Beurling–Ahlfors transform on `L^p (ℂ; ℂ)` is `p* − 1`, for `1 < p < ∞`. -/
theorem corollary2_norm {p : ℝ} (hp : 1 < p) : beurlingNorm p = ENNReal.ofReal (pStar p - 1) := by
  refine le_antisymm (beurlingNorm_le hp) ?_
  rw [beurlingNorm_eq_beurlingPowNorm]
  exact External.Lehto.lowerBound hp

end Agazzi
