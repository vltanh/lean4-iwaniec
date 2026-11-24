/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Kinderlehrer and Stampacchia: the projection on a closed convex set

D. Kinderlehrer and G. Stampacchia, *An introduction to variational inequalities and their
applications*, SIAM Classics in Applied Mathematics 31, 2000 (reprint of the 1980 edition),
Chapter I, Lemma 2.1 and Theorem 2.3, as the paper (arXiv:2609.28311, TeX lines 412–415) uses them:
the projection of a point of a real Hilbert space on a nonempty closed convex set exists, is unique,
and is characterized by the variational inequality `⟪x − y, v − y⟫ ≤ 0` for all `v` in the set.

The source is not freely available and has not been read: the numbering is the paper's, and the
statements are the standard ones, as the paper uses them. Both are in Mathlib
(`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`).
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace External.KinderlehrerStampacchia

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Chapter I, Lemma 2.1** (as used by the paper): the projection of `x` on a nonempty closed
convex `K` exists and is unique: there is exactly one `y ∈ K` with `‖x − y‖ = inf_{v ∈ K} ‖x − v‖`. -/
theorem lemma2_1 {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K) (hcv : Convex ℝ K) (x : H) :
    ∃! y, y ∈ K ∧ ‖x - y‖ = ⨅ v : K, ‖x - v‖ := by
  sorry

/-- **Chapter I, Theorem 2.3** (as used by the paper): `y ∈ K` is the projection of `x` on the convex
`K` if and only if `⟪x − y, v − y⟫ ≤ 0` for every `v ∈ K`. -/
theorem theorem2_3 {K : Set H} (hcv : Convex ℝ K) {x y : H} (hy : y ∈ K) :
    ‖x - y‖ = ⨅ v : K, ‖x - v‖ ↔ ∀ v ∈ K, ⟪x - y, v - y⟫_ℝ ≤ 0 := by
  sorry

end External.KinderlehrerStampacchia
