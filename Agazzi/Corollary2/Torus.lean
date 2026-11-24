/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Defs
public import HarmonicAnalysis.BeurlingAhlfors.Periodic
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Corollary 2, second part: the periodic setting

The facts about smooth `ℤ²`-periodic functions `u : ℝ² → ℂ` and about the torus `𝕋² = ℝ² / ℤ²`
that the upper bound `‖𝒮‖_p ≤ p* − 1` (`Agazzi.beurlingNorm_le`) uses, between the objects of the
paper (`Agazzi.Defs`) and those of the package `HarmonicAnalysis`.

* The Wirtinger derivatives as the conformal and anticonformal parts of the jacobian
  (Baernstein–Montgomery-Smith, §5: `α (∇f) = (∂f, ∂̄f)` for `∇f` the matrix of the real and
  imaginary parts of `f`): for `φ = (Re u, Im u)` (`Agazzi.Corollary2Norm.toRealPair u`),
  `a₊ (D φ) = ∂u` and `a₋ (D φ) = ∂̄u`, with the package's `UnitAddTorus.dzPi`,
  `UnitAddTorus.dzbarPi` (`∂ = ½ (∂_x − i ∂_y)`, `∂̄ = ½ (∂_x + i ∂_y)`)
  (`Agazzi.Corollary2Norm.conformalPart_jacobian_toRealPair`,
  `Agazzi.Corollary2Norm.anticonformalPart_jacobian_toRealPair`).
* The interchangeability of `∂` and `∂̄` (Baernstein–Montgomery-Smith, §1): `∂ū = conj (∂̄u)` and
  `∂̄ū = conj (∂u)` (`Agazzi.Corollary2Norm.dzPi_conj`, `Agazzi.Corollary2Norm.dzbarPi_conj`).
* Integrals and `L^p` norms over `𝕋²`, with Mathlib's measure of total mass one, as integrals and
  `L^p` norms over the unit square (`Agazzi.Corollary2Norm.lintegral_torus_eq_cube`,
  `Agazzi.Corollary2Norm.eLpNorm_torus_eq_cube`).
* A trigonometric polynomial, as a function on `ℝ²`, is smooth and periodic, with mean `c₀`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set UnitAddTorus HarmonicAnalysis
open scoped ENNReal ComplexConjugate ContDiff Real

namespace Agazzi.Corollary2Norm

/-! ### The Wirtinger derivatives and the jacobian -/

/-- The map `φ = (Re u, Im u) : ℝ² → ℝ²` of `u : ℝ² → ℂ` (with `ℂ ≅ ℝ²`, `x + iy ↦ (x, y)`). -/
def toRealPair (u : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![(u y).re, (u y).im]

theorem contDiff_toRealPair {n : WithTop ℕ∞} {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (toRealPair u) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simp only [toRealPair, Fin.zero_eta, Matrix.cons_val_zero]
    exact Complex.reCLM.contDiff.comp hu
  · simp only [toRealPair, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Complex.imCLM.contDiff.comp hu

theorem isPeriodic_toRealPair {u : (Fin 2 → ℝ) → ℂ} (hu : UnitAddTorus.IsPeriodic u) :
    Agazzi.IsPeriodic (toRealPair u) := fun x k => by
  simp only [toRealPair, hu x k]

private lemma fderiv_re {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ} (hu : DifferentiableAt ℝ u x)
    (v : Fin 2 → ℝ) : fderiv ℝ (fun y => (u y).re) x v = (fderiv ℝ u x v).re := by
  have h := (Complex.reCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  have e : (fun y => (u y).re) = Complex.reCLM ∘ u := rfl
  rw [e, h]
  rfl

private lemma fderiv_im {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ} (hu : DifferentiableAt ℝ u x)
    (v : Fin 2 → ℝ) : fderiv ℝ (fun y => (u y).im) x v = (fderiv ℝ u x v).im := by
  have h := (Complex.imCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  have e : (fun y => (u y).im) = Complex.imCLM ∘ u := rfl
  rw [e, h]
  rfl

private lemma jacobian_toRealPair {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u x) (j : Fin 2) :
    jacobian (toRealPair u) x 0 j = (fderiv ℝ u x (Pi.single j 1)).re ∧
      jacobian (toRealPair u) x 1 j = (fderiv ℝ u x (Pi.single j 1)).im := by
  have h0 : (fun y => toRealPair u y 0) = fun y => (u y).re := by
    funext y; simp [toRealPair]
  have h1 : (fun y => toRealPair u y 1) = fun y => (u y).im := by
    funext y; simp [toRealPair]
  simp only [jacobian, Matrix.of_apply, h0, h1]
  exact ⟨fderiv_re hu _, fderiv_im hu _⟩

/-- `a₊ (D φ) = ∂u` for `φ = (Re u, Im u)`, at a point where `u` is differentiable. -/
theorem conformalPart_jacobian_toRealPair {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u x) :
    conformalPart (jacobian (toRealPair u) x) = dzPi u x := by
  obtain ⟨a0, b0⟩ := jacobian_toRealPair hu 0
  obtain ⟨a1, b1⟩ := jacobian_toRealPair hu 1
  apply Complex.ext <;>
    simp [conformalPart, dzPi, a0, b0, a1, b1, Complex.mul_re, Complex.mul_im] <;> ring

/-- `a₋ (D φ) = ∂̄u` for `φ = (Re u, Im u)`, at a point where `u` is differentiable. -/
theorem anticonformalPart_jacobian_toRealPair {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u x) :
    anticonformalPart (jacobian (toRealPair u) x) = dzbarPi u x := by
  obtain ⟨a0, b0⟩ := jacobian_toRealPair hu 0
  obtain ⟨a1, b1⟩ := jacobian_toRealPair hu 1
  apply Complex.ext <;>
    simp [anticonformalPart, dzbarPi, a0, b0, a1, b1, Complex.mul_re, Complex.mul_im] <;> ring

/-! ### The interchangeability of `∂` and `∂̄` -/

private lemma fderiv_conj (u : (Fin 2 → ℝ) → ℂ) (x v : Fin 2 → ℝ) :
    fderiv ℝ (fun y => conj (u y)) x v = conj (fderiv ℝ u x v) := by
  simp only [starRingEnd_apply, fderiv_star]
  rfl

/-- `∂ū = conj (∂̄u)`. -/
theorem dzPi_conj (u : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    dzPi (fun y => conj (u y)) x = conj (dzbarPi u x) := by
  simp only [dzPi, dzbarPi, fderiv_conj, map_mul, map_add, map_inv₀, map_ofNat, Complex.conj_I]
  ring

/-- `∂̄ū = conj (∂u)`. -/
theorem dzbarPi_conj (u : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    dzbarPi (fun y => conj (u y)) x = conj (dzPi u x) := by
  simp only [dzPi, dzbarPi, fderiv_conj, map_mul, map_sub, map_inv₀, map_ofNat, Complex.conj_I]
  ring

theorem contDiff_conj {n : WithTop ℕ∞} {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n fun y => conj (u y) :=
  Complex.conjCLE.contDiff.comp hu

theorem isPeriodic_conj {u : (Fin 2 → ℝ) → ℂ} (hu : UnitAddTorus.IsPeriodic u) :
    UnitAddTorus.IsPeriodic fun y => conj (u y) := fun x k => by
  simp only [hu x k]

/-! ### Integrals and `L^p` norms over the torus as over the unit square -/

/-- Integrals over `𝕋^ι` (with Mathlib's measure, of total mass one) are integrals over the open
unit cube `(0, 1)^ι`. -/
theorem lintegral_torus_eq_cube {ι : Type*} [Fintype ι] (f : UnitAddTorus ι → ℝ≥0∞) :
    ∫⁻ z, f z = ∫⁻ x in cube ι, f (ofPi x) := by
  have hvol : (volume : Measure (UnitAddTorus ι)) =
      @volume _ (@MeasureSpace.pi ι _ (fun _ => UnitAddCircle)
        (fun _ => instMeasureSpaceUnitAddCircle)) :=
    volume_eq_pi_haarAddCircle
  rw [hvol, UnitAddTorus.lintegral_preimage f 0]
  have h1 : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      univ.pi fun _ => Ioc (0 : ℝ) 1 := by
    ext x; simp
  rw [h1]
  exact setLIntegral_congr
    (Measure.univ_pi_Ioo_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm).symm

/-- `L^p` norms over `𝕋^ι` (with Mathlib's measure, of total mass one) are `L^p` norms over the open
unit cube `(0, 1)^ι`, for continuous functions and `0 < p < ∞`. -/
theorem eLpNorm_torus_eq_cube {ι : Type*} [Fintype ι] {F : UnitAddTorus ι → ℂ}
    (hF : Continuous F) {p : ℝ} (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) volume =
      eLpNorm (fun x => F (ofPi x)) (ENNReal.ofReal p) (volume.restrict (cube ι)) := by
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top hF.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top
      (f := fun x => F (ofPi x)) (hF.comp continuous_ofPi).aestronglyMeasurable,
    lintegral_torus_eq_cube (fun z => ‖F z‖ₑ ^ (ENNReal.ofReal p).toReal)]

/-! ### Trigonometric polynomials as functions on `ℝ^ι` -/

theorem trigPoly_ofPi_eq {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    (fun x => trigPoly c (ofPi x)) = fun x => ∑ n ∈ c.support, c n * mFourier n (ofPi x) := by
  funext x
  simp [trigPoly, Finsupp.sum]

theorem contDiff_mFourier_ofPi {ι : Type*} [Fintype ι] (n : ι → ℤ) :
    ContDiff ℝ ∞ fun x : ι → ℝ => mFourier n (ofPi x) := by
  simp_rw [mFourier_ofPi]
  refine Complex.contDiff_exp.comp (contDiff_const.mul (ContDiff.sum fun i _ => ?_))
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : ι => ℝ) i))

/-- A trigonometric polynomial, as a function on `ℝ^ι`, is smooth. -/
theorem contDiff_trigPoly_ofPi {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    ContDiff ℝ ∞ fun x => trigPoly c (ofPi x) := by
  rw [trigPoly_ofPi_eq]
  exact ContDiff.sum fun n _ => contDiff_const.mul (contDiff_mFourier_ofPi n)

/-- A trigonometric polynomial, as a function on `ℝ^ι`, is `ℤ^ι`-periodic. -/
theorem isPeriodic_trigPoly_ofPi {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    UnitAddTorus.IsPeriodic fun x => trigPoly c (ofPi x) := fun x k => by
  simp only [ofPi_add_int]

/-- The mean of a trigonometric polynomial over the cube is its coefficient `c₀`. -/
theorem cubeFourierCoeff_trigPoly_ofPi_zero {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    cubeFourierCoeff (fun x => trigPoly c (ofPi x)) 0 = c 0 := by
  rw [trigPoly_ofPi_eq, cubeFourierCoeff_trig]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

end Agazzi.Corollary2Norm
