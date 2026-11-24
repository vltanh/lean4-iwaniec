/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Proof.ScalarProjection.Existence

/-!
# §2: the scalar projection lemma (Lemma 4)

For `K ⊂ ℝ²` nonempty, compact and convex, `p ∈ K` and `η ∈ W^{1,∞}_per (Q)`, let
`v (x) = p · x + η (x)` and let `ζ` be the `L² (Q)`-projection of `η` on
`𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`. Then `w (x) = p · x + ζ (x)` satisfies `Dw = Dv` or
`Dw ∈ ∂K` almost everywhere, and `∫_Q Dw · (Dv − Dw) ≥ 0` (`(eq:projection-integral-sign)`).

The objects and the representation choices are in `Agazzi.Proof.ScalarProjection.Defs`; the
existence of the projection and the variational inequality in
`Agazzi.Proof.ScalarProjection.Existence`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Agazzi

variable {K : Set (Fin 2 → ℝ)} {p : Fin 2 → ℝ}

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
