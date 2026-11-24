/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Defs

/-!
# Lehto: the lower bound `‖𝒮‖_p ≥ p* − 1`

O. Lehto, *Remarks on the integrability of the derivatives of quasiconformal mappings*, Ann. Acad.
Sci. Fenn. Ser. A I No. 371 (1965). The paper (arXiv:2609.28311, TeX line 320) cites it for the lower
bound in `(eq:BA-sharp-norm)`: "the lower bound in (eq:BA-sharp-norm) is classical [Lehto1965]".

Stated with the package `HarmonicAnalysis`'s Beurling–Ahlfors transform `𝓑` (symbol `ξ̄ / ξ`) and
its norm on `L^p (ℂ)`, the supremum over Schwartz functions (`HarmonicAnalysis.beurlingPowNorm 1 p`).
The source has not been read: its statement is the classical one, as the paper uses it.
-/

@[expose] public section

noncomputable section

namespace External.Lehto

/-- **Lehto's lower bound**: `‖𝒮‖_{L^p → L^p} ≥ p* − 1`, `p* = max (p, p / (p − 1))`, for
`1 < p < ∞`. -/
theorem lowerBound {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (max p (p / (p - 1)) - 1) ≤ HarmonicAnalysis.beurlingPowNorm 1 p := by
  sorry

end External.Lehto
