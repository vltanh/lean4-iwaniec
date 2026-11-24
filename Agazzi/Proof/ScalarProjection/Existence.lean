/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Proof.ScalarProjection.Defs
public import Agazzi.External.KinderlehrerStampacchia.Projection

/-!
# §2, Lemma 4: the projection exists and satisfies the variational inequality

TeX lines 411–415: "The set `𝒞` is nonempty, closed and convex in `L² (Q)`. By
[Kinderlehrer–Stampacchia, Chapter I, Lemma 2.1 and Theorem 2.3], the projection `ζ` exists
uniquely and, with `h (x) = η (x) − ζ (x)`, satisfies `∫_Q h (ξ − ζ) dx ≤ 0` for all `ξ ∈ 𝒞`
(`(eq:projection-variational-inequality)`)."

* `lemma4_exists`: the projection exists;
* `lemma4_variationalInequality`: `(eq:projection-variational-inequality)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Agazzi

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

end Agazzi
