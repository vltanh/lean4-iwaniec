/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# §2: the scalar projection lemma (Lemma 4)

For `K ⊂ ℝ²` nonempty, compact and convex, `p ∈ K` and `η ∈ W^{1,∞}_per (Q)`, let `v (x) = p · x + η (x)`
and let `ζ` be the `L² (Q)`-projection of `η` on
`𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`. Then `w (x) = p · x + ζ (x)` satisfies `Dw = Dv` or
`Dw ∈ ∂K` almost everywhere, and `∫_Q Dw · (Dv − Dw) ≥ 0` (`(eq:projection-integral-sign)`).

Representation (a choice of the formalization, see the report):

* `W^{1,∞}_per (Q)` is represented by the Lipschitz `ℤ²`-periodic functions `ℝ² → ℝ` (`LipPer`):
  every class of `W^{1,∞}_per (Q)` has exactly one Lipschitz representative, and the gradient of a
  Lipschitz function is its pointwise derivative almost everywhere (Rademacher).
* `Dξ (x)` is `sgrad ξ x = (∂₁ ξ (x), ∂₂ ξ (x))`, from the Fréchet derivative (`0` where `ξ` is not
  differentiable).
* "almost everywhere" is with respect to Lebesgue measure on the unit square, the torus `Q`.
* the `L² (Q)`-projection `ζ` of `η` on `𝒞` is a minimizer of `ξ ↦ ∫_Q (η − ξ)²` on `𝒞`
  (`IsL2Projection`): the point of `𝒞` nearest to `η` in `L² (Q)`.

Main statements:

* `lemma4_exists`: the projection exists (TeX line 412: `𝒞` is nonempty, closed and convex, and
  [Kinderlehrer–Stampacchia, Ch. I, Lemma 2.1]);
* `lemma4_variationalInequality`: `(eq:projection-variational-inequality)`,
  `∫_Q h (ξ − ζ) ≤ 0` for all `ξ ∈ 𝒞`, `h = η − ζ` ([Kinderlehrer–Stampacchia, Ch. I, Thm 2.3]);
* `lemma4`: **Lemma 4** (`lem:scalar-projection`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Agazzi

/-- The gradient `Dξ (x) = (∂₁ ξ (x), ∂₂ ξ (x))` of `ξ : ℝ² → ℝ` (`0` where `ξ` is not
differentiable). -/
def sgrad (ξ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun j => fderiv ℝ ξ x (Pi.single j 1)

/-- `W^{1,∞}_per (Q)`, by Lipschitz representatives: `ξ` is Lipschitz and `ℤ²`-periodic. -/
def LipPer (ξ : (Fin 2 → ℝ) → ℝ) : Prop :=
  (∃ C : NNReal, LipschitzWith C ξ) ∧ IsPeriodic ξ

/-- `𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`. -/
def constraintSet (K : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : Set ((Fin 2 → ℝ) → ℝ) :=
  {ξ | LipPer ξ ∧ ∀ᵐ x ∂(volume.restrict unitSquare), p + sgrad ξ x ∈ K}

/-- `ζ` is an `L² (Q)`-projection of `η` on `𝒞`: `ζ ∈ 𝒞` and
`∫_Q (η − ζ)² ≤ ∫_Q (η − ξ)²` for every `ξ ∈ 𝒞`. -/
def IsL2Projection (𝒞 : Set ((Fin 2 → ℝ) → ℝ)) (η ζ : (Fin 2 → ℝ) → ℝ) : Prop :=
  ζ ∈ 𝒞 ∧ ∀ ξ ∈ 𝒞, ∫ x in unitSquare, (η x - ζ x) ^ 2 ≤ ∫ x in unitSquare, (η x - ξ x) ^ 2

variable {K : Set (Fin 2 → ℝ)} {p : Fin 2 → ℝ}

/-- The `L² (Q)`-projection of `η` on `𝒞` exists (TeX line 412). -/
theorem lemma4_exists (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K) (hp : p ∈ K)
    {η : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) :
    ∃ ζ, IsL2Projection (constraintSet K p) η ζ := by
  sorry

/-- `(eq:projection-variational-inequality)`: with `h = η − ζ`, `∫_Q h (ξ − ζ) ≤ 0` for every
`ξ ∈ 𝒞` (TeX lines 412–415). -/
theorem lemma4_variationalInequality (hKcv : Convex ℝ K) {η ζ : (Fin 2 → ℝ) → ℝ}
    (hη : LipPer η) (hζ : IsL2Projection (constraintSet K p) η ζ) :
    ∀ ξ ∈ constraintSet K p, ∫ x in unitSquare, (η x - ζ x) * (ξ x - ζ x) ≤ 0 := by
  sorry

/-- **Lemma 4** (`lem:scalar-projection`). Let `K ⊂ ℝ²` be nonempty, compact and convex, `p ∈ K`,
`η ∈ W^{1,∞}_per (Q)`, `v (x) = p · x + η (x)`, and let `ζ` be the `L² (Q)`-projection of `η` on
`𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`. Then `w (x) = p · x + ζ (x)` satisfies `Dw = Dv` or
`Dw ∈ ∂K` almost everywhere, and `∫_Q Dw · (Dv − Dw) ≥ 0` (`(eq:projection-integral-sign)`). -/
theorem lemma4 (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K) (hp : p ∈ K)
    {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) (hζ : IsL2Projection (constraintSet K p) η ζ) :
    (∀ᵐ x ∂(volume.restrict unitSquare),
      sgrad (fun y => p ⬝ᵥ y + ζ y) x = sgrad (fun y => p ⬝ᵥ y + η y) x ∨
        sgrad (fun y => p ⬝ᵥ y + ζ y) x ∈ frontier K) ∧
    0 ≤ ∫ x in unitSquare, sgrad (fun y => p ⬝ᵥ y + ζ y) x ⬝ᵥ
      (sgrad (fun y => p ⬝ᵥ y + η y) x - sgrad (fun y => p ⬝ᵥ y + ζ y) x) := by
  sorry

end Agazzi
