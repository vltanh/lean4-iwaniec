/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- The Challenge in `palomar/Agazzi/` imports exactly these modules.
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The definitions of the paper

The objects that the statements of the paper's main results use, for

A. Agazzi, K. Astala, R. Bañuelos, G. Bruno, G. Cassese, D. Faraco, A. Guerra, M. Hormozi,
B. Kirchheim, A. Koski, V. Kovač, J. Kristensen, F. Pasqualotto, I. Prause, E. Saksman, V. Šverák,
L. Székelyhidi, R. Tione, A. Volberg, H. Yang, *Sharp higher integrability theory, Part I: the
`L^p`-norm of the Beurling–Ahlfors transform*, arXiv:2609.28311v2 (2026).

Conventions.

* `ℝ^{2×2}` is `Matrix (Fin 2) (Fin 2) ℝ` and `ℝ²` is `Fin 2 → ℝ`. With `ℝ² = ℂ`
  (`(x, y) ↦ x + iy`), a matrix `A` acts as `A z = a₊ z + a₋ z̄`, with the conformal part
  `a₊ = conformalPart A = ((a₁₁ + a₂₂) + i (a₂₁ − a₁₂)) / 2` and the anticonformal part
  `a₋ = anticonformalPart A = ((a₁₁ − a₂₂) + i (a₂₁ + a₁₂)) / 2`. Then the operator norm of `A` is
  `|a₊| + |a₋|` and `det A = |a₊|² − |a₋|²` (`Agazzi.opNorm_eq`, `Agazzi.det_eq`).
* `integrandL A = L (A)` is the integrand `(eq:L-definition)`: `|a₊|² − |a₋|²` if `|A| ≤ 1`,
  `2 |a₊| − 1` if `|A| > 1`, with `|A| = |a₊| + |a₋|`.
* `pStar p = max (p, p / (p − 1))` and `burkholderB p A` is the Burkholder integrand
  `(eq:Bp-definition)`.
* The torus `Q = ℝ² / ℤ²` is represented by `ℤ²`-periodic maps on `ℝ²` (`IsPeriodic`), and
  integrals over `Q` by integrals over the open unit square `unitSquare = (0, 1)²`, of measure `1`.
  `C^∞_per (Q; ℝ²)` is the set of `C^∞` maps `ℝ² → ℝ²` that are `ℤ²`-periodic.
* `jacobian φ x` is the matrix `D φ (x)` with the entries `∂_j φ_i (x)`: its rows are the gradients
  of the components (the paper's `D u = (D u¹, D u²)`).
* The Fourier transform is Mathlib's, `𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv`, on `ℂ` as a real
  inner product space. `beurling f = 𝓕⁻¹ (ξ ↦ (ξ̄ / ξ) 𝓕 f (ξ))` is the Beurling–Ahlfors transform
  `𝒮`, the Fourier multiplier with `𝒮 ∘ ∂_z̄ = ∂_z` (`(eq:BA-definition)`), and `beurlingNorm p`
  its norm on `L^p (ℂ; ℂ)`, the supremum of `‖𝒮 f‖_p / ‖f‖_p` over the (dense) Schwartz functions.
  `dz`, `dzbar` are the Wirtinger derivatives.

The block between the markers is copied word for word into `palomar/Agazzi/Challenge.lean` by
`scripts/sync_challenge_defs.py`, and the imports are the Challenge's. The definitions of the
Beurling–Ahlfors transform repeat those of the package `HarmonicAnalysis` (`HarmonicAnalysis.Defs`),
specialized to `ℂ` and to the first power, and the jacobian is the package `CalculusOfVariations`'s
`grad`; the bridges are in `Agazzi.Bridges`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace Agazzi

-- BEGIN SHARED DEFINITIONS

/-- The conformal part `a₊ = ((a₁₁ + a₂₂) + i (a₂₁ − a₁₂)) / 2` of `A`: with `ℝ² = ℂ`,
`A z = a₊ z + a₋ z̄`. -/
def conformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 + A 1 1) / 2, (A 1 0 - A 0 1) / 2⟩

/-- The anticonformal part `a₋ = ((a₁₁ − a₂₂) + i (a₂₁ + a₁₂)) / 2` of `A`. -/
def anticonformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 - A 1 1) / 2, (A 1 0 + A 0 1) / 2⟩

/-- The integrand `L` of `(eq:L-definition)`: `L (A) = |a₊|² − |a₋|²` if `|A| ≤ 1`, and
`L (A) = 2 |a₊| − 1` if `|A| > 1`, where `|A| = |a₊| + |a₋|` is the operator norm. -/
def integrandL (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  if ‖conformalPart A‖ + ‖anticonformalPart A‖ ≤ 1 then
    ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2
  else 2 * ‖conformalPart A‖ - 1

/-- `p* = max (p, p / (p − 1))`. -/
def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- The Burkholder integrand `B_p` of `(eq:Bp-definition)`:
`B_p (A) = ((p* − 1) |a₊| − |a₋|) (|a₊| + |a₋|)^{p−1}` if `1 < p < 2`, and
`B_p (A) = ((p* − 1) |a₋| − |a₊|) (|a₊| + |a₋|)^{p−1}` if `2 ≤ p < ∞` (the real power `rpow`).
It is used for `1 < p` only. -/
def burkholderB (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  if p < 2 then
    ((pStar p - 1) * ‖conformalPart A‖ - ‖anticonformalPart A‖) *
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1)
  else
    ((pStar p - 1) * ‖anticonformalPart A‖ - ‖conformalPart A‖) *
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1)

/-- The open unit square `(0, 1)²`, a fundamental domain of `ℤ²` in `ℝ²`: integrals over the torus
`Q = ℝ² / ℤ²` are integrals over it. -/
def unitSquare : Set (Fin 2 → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- `φ` is `ℤ²`-periodic: `φ (x + k) = φ (x)` for all `x ∈ ℝ²`, `k ∈ ℤ²`; that is, `φ` is a
function on the torus `Q = ℝ² / ℤ²`. -/
def IsPeriodic {E : Type*} (φ : (Fin 2 → ℝ) → E) : Prop :=
  ∀ (x : Fin 2 → ℝ) (k : Fin 2 → ℤ), φ (x + fun i => (k i : ℝ)) = φ x

/-- The derivative matrix `D φ (x)` of `φ : ℝ² → ℝ²`: the entries `∂_j φ_i (x)` (rows are the
gradients of the components). An entry is `0` where `φ_i` is not differentiable. -/
def jacobian (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun y => φ y i) x (Pi.single j 1)

/-- The Beurling–Ahlfors transform `𝒮 f = 𝓕⁻¹ (ξ ↦ (ξ̄ / ξ) 𝓕 f (ξ))`, by Mathlib's integral
formulas for `𝓕` and `𝓕⁻¹` (the symbol is `0` at `ξ = 0`). -/
def beurling (f : ℂ → ℂ) : ℂ → ℂ :=
  𝓕⁻ (fun ξ : ℂ => (conj ξ / ξ) • 𝓕 f ξ)

/-- `‖𝒮‖_{L^p (ℂ; ℂ) → L^p (ℂ; ℂ)}`: the supremum, in `[0, ∞]`, of `‖𝒮 f‖_p / ‖f‖_p` over the
Schwartz functions `f` (`0 / 0 = 0`). -/
def beurlingNorm (p : ℝ) : ℝ≥0∞ :=
  ⨆ f : 𝓢(ℂ, ℂ), eLpNorm (beurling f) (ENNReal.ofReal p) volume /
    eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume

/-- The Wirtinger derivative `∂_z g = ½ (∂_x g − i ∂_y g)` of `g : ℂ → ℂ` (`0` where `g` is not
real-differentiable). -/
def dz (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 - Complex.I • fderiv ℝ g z Complex.I)

/-- The Wirtinger derivative `∂_z̄ g = ½ (∂_x g + i ∂_y g)` of `g : ℂ → ℂ` (`0` where `g` is not
real-differentiable). -/
def dzbar (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I)

-- END SHARED DEFINITIONS

end Agazzi
