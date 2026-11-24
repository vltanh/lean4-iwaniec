/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# The support function of a compact convex set in `ℝ^m`

For `K ⊂ ℝ^m = Fin m → ℝ`, the support function `H_K (y) = sup_{z ∈ K} z · y` (`supportFun`), with
the dot product `⬝ᵥ`. For `K` nonempty and compact:

* `dotProduct_le_supportFun`, `exists_dotProduct_eq_supportFun`: the supremum is attained;
* `supportFun_zero`, `supportFun_add_le`, `supportFun_smul`: `H_K` is sublinear;
* `lipschitzWith_supportFun`: `H_K` is Lipschitz;
* `mem_of_forall_dotProduct_le_supportFun`: for `K` also convex, `a ∈ K` if `a · y ≤ H_K (y)` for
  every `y`;
* `gradient_supportFun_mem`: the gradient of `H_K` lies in `K` wherever `H_K` is differentiable.
-/

@[expose] public section

noncomputable section

namespace Agazzi

variable {m : ℕ}

/-- The support function `H_K (y) = sup_{z ∈ K} z · y` of `K ⊂ ℝ^m`. -/
def supportFun (K : Set (Fin m → ℝ)) (y : Fin m → ℝ) : ℝ :=
  sSup ((fun z => z ⬝ᵥ y) '' K)

variable {K : Set (Fin m → ℝ)}

theorem dotProduct_le_supportFun (hK : IsCompact K) {z : Fin m → ℝ} (hz : z ∈ K)
    (y : Fin m → ℝ) : z ⬝ᵥ y ≤ supportFun K y := by
  sorry

theorem exists_dotProduct_eq_supportFun (hK : IsCompact K) (hne : K.Nonempty) (y : Fin m → ℝ) :
    ∃ z ∈ K, z ⬝ᵥ y = supportFun K y := by
  sorry

theorem supportFun_zero (hK : IsCompact K) (hne : K.Nonempty) : supportFun K 0 = 0 := by
  sorry

theorem supportFun_add_le (hK : IsCompact K) (hne : K.Nonempty) (y y' : Fin m → ℝ) :
    supportFun K (y + y') ≤ supportFun K y + supportFun K y' := by
  sorry

theorem supportFun_smul (hK : IsCompact K) (hne : K.Nonempty) {c : ℝ} (hc : 0 ≤ c)
    (y : Fin m → ℝ) : supportFun K (c • y) = c * supportFun K y := by
  sorry

theorem lipschitzWith_supportFun (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ C : NNReal, LipschitzWith C (supportFun K) := by
  sorry

theorem mem_of_forall_dotProduct_le_supportFun (hK : IsCompact K) (hcv : Convex ℝ K)
    {a : Fin m → ℝ} (h : ∀ y, a ⬝ᵥ y ≤ supportFun K y) : a ∈ K := by
  sorry

/-- Where `H_K` is differentiable, its gradient `(∂_j H_K (y))_j` lies in `K`. -/
theorem gradient_supportFun_mem (hK : IsCompact K) (hne : K.Nonempty) (hcv : Convex ℝ K)
    {y : Fin m → ℝ} (hy : DifferentiableAt ℝ (supportFun K) y) :
    (fun j => fderiv ℝ (supportFun K) y (Pi.single j 1)) ∈ K := by
  sorry

end Agazzi
