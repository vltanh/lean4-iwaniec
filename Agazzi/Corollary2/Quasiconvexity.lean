/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Theorem1
public import Agazzi.External.BaernsteinMontgomerySmith.Basic

/-!
# Corollary 2, first part: the quasiconvexity of the Burkholder integrand

**Corollary 2** (`cor:Bp-BA`), first assertion: for every `1 < p < ∞`, every `A ∈ ℝ^{2×2}` and every
`φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`.

The paper derives it from Theorem 1 "by the arguments in [Baernstein1997a] (see also [Guerra2026b])"
(TeX line 301). Those arguments: `B_p` is a positive multiple of the Mellin transform
`∫_0^∞ t^{p−1} L (A / t) dt` for `1 < p < 2` (Baernstein–Montgomery-Smith (1.2a)), and of
`∫_0^∞ t^{p−1} (L − det) (A / t) dt` for `2 < p < ∞` ((1.2b)); `B_2 = −det`. Each `A ↦ L (A / t)`
is quasiconvex (Theorem 1 applied to `A / t` and `φ / t`), `det` is a null Lagrangian, and Fubini's
theorem gives the inequality for `B_p`.

As for Theorem 1, `corollary2_lipschitz` states the inequality for Lipschitz periodic `φ`, by the
same argument from `theorem1_lipschitz`, and `corollary2` is the paper's statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Agazzi

/-- `L (A) = L_BMS (a₊, a₋)`: the paper's `L` is the function of Baernstein and Montgomery-Smith
in conformal coordinates. -/
theorem integrandL_eq_bms (A : Matrix (Fin 2) (Fin 2) ℝ) :
    integrandL A = External.BaernsteinMontgomerySmith.L (conformalPart A) (anticonformalPart A) :=
  rfl

/-- **Corollary 2**, first assertion, for Lipschitz periodic test maps: for `1 < p`,
`∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`. -/
theorem corollary2_lipschitz {p : ℝ} (hp : 1 < p) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} {C : NNReal} (hφ : LipschitzWith C φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (burkholderB p (A + jacobian φ x) - burkholderB p A) := by
  sorry

/-- **Corollary 2** (`cor:Bp-BA`), first assertion. For every `1 < p < ∞`, every `A ∈ ℝ^{2×2}` and
every `φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`. -/
theorem corollary2 {p : ℝ} (hp : 1 < p) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (burkholderB p (A + jacobian φ x) - burkholderB p A) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_of_contDiff_of_isPeriodic hφ hper
  exact corollary2_lipschitz hp A hC hper

end Agazzi
