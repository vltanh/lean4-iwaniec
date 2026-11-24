/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Defs
public import CalculusOfVariations.Basic
public import HarmonicAnalysis.BeurlingAhlfors.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Bridges: the definitions of `Agazzi.Defs` and the facts that the paper states about them

* The jacobian, the unit square and periodicity are those of the package `CalculusOfVariations`
  (`grad`, `unitCube 2`, the periodicity in `QuasiconvexAtPeriodic`); the Beurling–Ahlfors
  transform, its norm and the Wirtinger derivatives are those of the package `HarmonicAnalysis`
  (`beurlingPow 1`, `beurlingPowNorm 1`, `dz`, `dzbar`).
* The facts that the paper states in the introduction (TeX lines 264–268): with `A z = a₊ z + a₋ z̄`,
  the operator norm is `|A| = |a₊| + |a₋|` (`opNorm_eq`) and `det A = |a₊|² − |a₋|²` (`det_eq`).
* `p* − 1 = (p − 1)⁻¹` for `1 < p ≤ 2` and `p − 1` for `p ≥ 2` (the second equality of
  `(eq:BA-sharp-norm)`).
* The torus `Q` has measure `1` (`volume_unitSquare`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace Agazzi

theorem jacobian_eq_grad (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    jacobian φ x = CalculusOfVariations.grad φ x := rfl

theorem unitSquare_eq_unitCube : unitSquare = CalculusOfVariations.unitCube 2 := rfl

theorem volume_unitSquare : volume unitSquare = 1 := by
  sorry

theorem beurling_eq_beurlingPow (f : ℂ → ℂ) :
    beurling f = HarmonicAnalysis.beurlingPow 1 f := by
  sorry

theorem beurlingNorm_eq_beurlingPowNorm (p : ℝ) :
    beurlingNorm p = HarmonicAnalysis.beurlingPowNorm 1 p := by
  sorry

theorem dz_eq (g : ℂ → ℂ) : dz g = HarmonicAnalysis.dz g := rfl

theorem dzbar_eq (g : ℂ → ℂ) : dzbar g = HarmonicAnalysis.dzbar g := rfl

/-- `𝒮 ∘ ∂_z̄ = ∂_z` on Schwartz functions: the characterization `(eq:BA-definition)` of the
Beurling–Ahlfors transform (the package's `HarmonicAnalysis.beurlingPow_dzbar_iterate`). -/
theorem beurling_dzbar (F : 𝓢(ℂ, ℂ)) : beurling (dzbar F) = dz F := by
  sorry

/-- `det A = |a₊|² − |a₋|²` (TeX line 268). -/
theorem det_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 := by
  sorry

/-- The operator norm of `A` on Euclidean `ℝ²` is `|a₊| + |a₋|` (TeX line 268). -/
theorem opNorm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ =
      ‖conformalPart A‖ + ‖anticonformalPart A‖ := by
  sorry

/-- `p* − 1 = (p − 1)⁻¹` for `1 < p ≤ 2` (`(eq:BA-sharp-norm)`). -/
theorem pStar_sub_one_of_le_two {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    pStar p - 1 = (p - 1)⁻¹ := by
  sorry

/-- `p* − 1 = p − 1` for `p ≥ 2` (`(eq:BA-sharp-norm)`). -/
theorem pStar_sub_one_of_two_le {p : ℝ} (hp2 : 2 ≤ p) : pStar p - 1 = p - 1 := by
  sorry

/-- For `1 < p < 2`, `B_p = (p − 1)⁻¹ (|a₊| − (p − 1) |a₋|) (|a₊| + |a₋|)^{p−1}`: a positive multiple
of the form of the Burkholder function used for `1 < p ≤ 2`. -/
theorem burkholderB_of_lt_two {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderB p A = (p - 1)⁻¹ * ((‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
      (‖conformalPart A‖ - (p - 1) * ‖anticonformalPart A‖)) := by
  sorry

end Agazzi
