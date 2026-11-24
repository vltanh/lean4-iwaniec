/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Function

/-!
# §2: the row representation of `L` (Lemma 3)

The notation of §2 (TeX lines 332–344). For a matrix `A` with rows `A¹ = A 0`, `A² = A 1`:

* `rot a = J a`, `J = [[0, −1], [1, 0]]`, and `det2 a b = det (a, b) = J a · b`;
* `euclidNorm a = |a|`, the Euclidean norm of `a ∈ ℝ²`, and `unitCircle = 𝕊¹`;
* `rowG z a b = G_z (a, b) = det (z, b) + z · (a − z)`;
* `rowF A = F (A) = sup_{|z| = 1} G_z (A¹, A²)`, which is `|A² + J A¹| − 1 = 2 |a₊| − 1`
  (`rowF_eq_norm`, `rowF_eq`), a convex function (`convexOn_rowF`);
* `rowZ a = 𝒵 (a) = 𝕊¹ ∪ {a}` if `|a| ≤ 1`, `𝕊¹` if `|a| > 1`.

Lemma 3 (`lemma3`, the display `(eq:L-row-representation)`): `L (A) = sup_{z ∈ 𝒵 (A¹)} G_z (A¹, A²)`.
-/

@[expose] public section

noncomputable section

namespace Agazzi

/-- `J a = (−a₂, a₁)`, the rotation by `π/2`: `J = [[0, −1], [1, 0]]`. -/
def rot (a : Fin 2 → ℝ) : Fin 2 → ℝ := ![-a 1, a 0]

/-- `det (a, b) = a₁ b₂ − a₂ b₁`, the determinant of the matrix with rows `a`, `b`. -/
def det2 (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

/-- The Euclidean norm `|a|` of `a ∈ ℝ²`. -/
def euclidNorm (a : Fin 2 → ℝ) : ℝ := ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 2))‖

/-- The unit circle `𝕊¹ = {z : |z| = 1}`. -/
def unitCircle : Set (Fin 2 → ℝ) := {z | euclidNorm z = 1}

/-- `G_z (a, b) = det (z, b) + z · (a − z)`. -/
def rowG (z a b : Fin 2 → ℝ) : ℝ := det2 z b + z ⬝ᵥ (a - z)

/-- `F (A) = sup_{|z| = 1} G_z (A¹, A²)`. -/
def rowF (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  sSup ((fun z => rowG z (A 0) (A 1)) '' unitCircle)

open Classical in
/-- `𝒵 (a) = 𝕊¹ ∪ {a}` if `|a| ≤ 1`, and `𝒵 (a) = 𝕊¹` if `|a| > 1`. -/
def rowZ (a : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  unitCircle ∪ (if euclidNorm a ≤ 1 then {a} else ∅)

/-- `det A = det (A¹, A²) = J A¹ · A²` (TeX line 335). -/
theorem det_eq_det2 (A : Matrix (Fin 2) (Fin 2) ℝ) : A.det = det2 (A 0) (A 1) := by
  sorry

theorem det2_eq_rot_dotProduct (a b : Fin 2 → ℝ) : det2 a b = rot a ⬝ᵥ b := by
  sorry

/-- `F (A) = |A² + J A¹| − 1` (TeX line 341). -/
theorem rowF_eq_norm (A : Matrix (Fin 2) (Fin 2) ℝ) :
    rowF A = euclidNorm (A 1 + rot (A 0)) - 1 := by
  sorry

/-- `F (A) = 2 |a₊| − 1` (TeX line 341). -/
theorem rowF_eq (A : Matrix (Fin 2) (Fin 2) ℝ) : rowF A = 2 * ‖conformalPart A‖ - 1 := by
  sorry

/-- `F` is convex (TeX line 344). -/
theorem convexOn_rowF : ConvexOn ℝ Set.univ rowF := by
  sorry

/-- **Lemma 3** (`eq:L-row-representation`). `L (A) = sup_{z ∈ 𝒵 (A¹)} G_z (A¹, A²)`. -/
theorem lemma3 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    integrandL A = sSup ((fun z => rowG z (A 0) (A 1)) '' rowZ (A 0)) := by
  sorry

end Agazzi
