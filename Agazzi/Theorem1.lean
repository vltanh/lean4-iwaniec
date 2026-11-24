/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Proof.RowRepresentation
public import Agazzi.Proof.ScalarProjection.Main
public import Agazzi.Basic.Analysis.Calculus.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Theorem 1: the quasiconvexity of `L`

**Theorem 1** (`thm:L-quasiconvexity`): for all `A ∈ ℝ^{2×2}` and all `φ ∈ C^∞_per (Q; ℝ²)`,
`∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`.

The paper's proof (TeX lines 376–396) uses only that `φ` is Lipschitz and periodic: Lemma 4 is
stated for `W^{1,∞}_per (Q)`. `theorem1_lipschitz` states the theorem for Lipschitz periodic `φ`
(`φ ∈ W^{1,∞}_per (Q; ℝ²)`), proved by the paper's argument, and `theorem1` is the paper's
statement, for `C^∞` periodic `φ`, which are Lipschitz.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Agazzi

/-- **Theorem 1** for Lipschitz periodic test maps (`φ ∈ W^{1,∞}_per (Q; ℝ²)`), by the paper's
proof: for all `A ∈ ℝ^{2×2}`, `∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`. -/
theorem theorem1_lipschitz (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {C : NNReal} (hφ : LipschitzWith C φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (integrandL (A + jacobian φ x) - integrandL A) := by
  sorry

/-- A `C^∞` `ℤ²`-periodic map `ℝ² → ℝ²` is Lipschitz. -/
theorem exists_lipschitzWith_of_contDiff_of_isPeriodic {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) : ∃ C : NNReal, LipschitzWith C φ := by
  sorry

/-- **Theorem 1** (`thm:L-quasiconvexity`). Let `Q = ℝ² / ℤ²`, with `|Q| = 1`. For all
`A ∈ ℝ^{2×2}` and all `φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`. -/
theorem theorem1 (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (integrandL (A + jacobian φ x) - integrandL A) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_of_contDiff_of_isPeriodic hφ hper
  exact theorem1_lipschitz A hC hper

end Agazzi
