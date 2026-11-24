/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Basic

/-!
# Periodic Lipschitz functions on `ℝ^m`: integrals over the unit cube

General facts about `ℤ^m`-periodic functions on `ℝ^m = Fin m → ℝ`, integrated over the open unit
cube `(0, 1)^m` (`CalculusOfVariations.unitCube m`), a fundamental domain of `ℤ^m`, that is, over the
torus `ℝ^m / ℤ^m`. They are general and could join the package `CalculusOfVariations`; they are in
the namespace `Agazzi` so as not to clash with it.

* `setIntegral_unitCube_comp_add`: translation invariance, `∫_Q f (x + a) dx = ∫_Q f (x) dx` for a
  periodic `f` integrable on `Q`;
* `setIntegral_unitCube_fderiv_eq_zero`: `∫_Q ∂_v f = 0` for a periodic Lipschitz `f`;
* `setIntegral_unitCube_grad_eq_zero`: `∫_Q ∇φ = 0`, entrywise, for a periodic Lipschitz map `φ`;
* `setIntegral_unitCube_det_add_grad`: the determinant is a null Lagrangian for periodic Lipschitz
  perturbations: `∫_Q det (A + ∇ψ) = det A`.
-/

@[expose] public section

open MeasureTheory

namespace Agazzi

open CalculusOfVariations

variable {m : ℕ}

/-- Translation invariance of the integral over the torus: for a `ℤ^m`-periodic `f` integrable on
the unit cube, `∫_{(0,1)^m} f (x + a) dx = ∫_{(0,1)^m} f (x) dx`. -/
theorem setIntegral_unitCube_comp_add {f : (Fin m → ℝ) → ℝ}
    (hf : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), f (x + fun i => (z i : ℝ)) = f x)
    (hfi : IntegrableOn f (unitCube m)) (a : Fin m → ℝ) :
    ∫ x in unitCube m, f (x + a) = ∫ x in unitCube m, f x := by
  sorry

/-- `∫_{(0,1)^m} ∂_v f = 0` for a `ℤ^m`-periodic Lipschitz `f`. -/
theorem setIntegral_unitCube_fderiv_eq_zero {f : (Fin m → ℝ) → ℝ} {K : NNReal}
    (hf : LipschitzWith K f)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), f (x + fun i => (z i : ℝ)) = f x)
    (v : Fin m → ℝ) :
    ∫ x in unitCube m, fderiv ℝ f x v = 0 := by
  sorry

/-- `∫_{(0,1)^m} ∇φ = 0`, entrywise, for a `ℤ^m`-periodic Lipschitz `φ : ℝ^m → ℝ^d`. -/
theorem setIntegral_unitCube_grad_eq_zero {d : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (i : Fin d) (k : Fin m) :
    ∫ x in unitCube m, grad φ x i k = 0 := by
  sorry

/-- The determinant is a null Lagrangian for periodic perturbations:
`∫_{(0,1)²} det (A + ∇ψ) = det A` for a `ℤ²`-periodic Lipschitz `ψ : ℝ² → ℝ²`. -/
theorem setIntegral_unitCube_det_add_grad {ψ : (Fin 2 → ℝ) → Fin 2 → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ)
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ), ψ (x + fun i => (z i : ℝ)) = ψ x)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ x in unitCube 2, (A + grad ψ x).det = A.det := by
  sorry

end Agazzi
