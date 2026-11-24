/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.BeurlingAhlfors.TestFunctions
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Extremal functions for `‖𝓑‖_p ≥ p − 1`

The test functions are `f_α (z) = z |z|^{−2α} g₂ (|z|)`, `0 < α < 1/p`
(`External.Lehto.extremalFun`), with the cutoff `g₂ (x) = 1` for `x ≤ 1`, `exp (−(x − 1)²)` for
`x > 1`, of the package `HarmonicAnalysis` (`HarmonicAnalysis.BeurlingAhlfors.testCutoff 2`).

* On the unit disc they are the extremal functions `f_α (z) = z |z|^{−2α}` of
  Baernstein–Montgomery-Smith (1999, §1), also Guerra's `v_α` (2026).
* Outside the disc the source continues them by `1/z̄`. Here the continuation is the rapidly
  decaying one of Dragičević's test functions `f_{n,α} (z) = z^n |z|^{−2α} g_n (|z|)` (2011,
  p. 465), with `n = 1` and the cutoff `g₂` (`C¹` at `1`) in place of `g₁`. The smooth
  approximations of the package (`HarmonicAnalysis.BeurlingAhlfors.approxProfile`) then apply as
  they are, and the limit of the ratio is the same, since the integrals outside the disc stay
  bounded while those on the disc grow like `(1 − αp)⁻¹`.

With `t = |z|²` and `f (z) = z K (t)`, `∂f = K (t) + t K' (t)` and `∂̄f = z² K' (t)`
(`External.Lehto.dz_mul_ofReal_radial`, `External.Lehto.dzbar_mul_ofReal_radial`).

## Main results

* On the punctured unit disc, `∂f_α = (1 − α) |z|^{−2α}` and `|∂̄f_α| = α |z|^{−2α}`, so that
  `∫_Δ |∂f_α|^p = π / (1 − αp) (1 − α)^p` and `∫_Δ |∂̄f_α|^p = π / (1 − αp) α^p`
  (`External.Lehto.lintegral_dz_extremalFun_ball`,
  `External.Lehto.lintegral_dzbar_extremalFun_ball`); outside the disc, the integrals stay bounded
  for `α ∈ [0, 1]` (`External.Lehto.exists_bound_extremalFun_compl_ball`).
* `External.Lehto.tendsto_eLpNorm_div_extremalFun`: `‖∂f_α‖_p / ‖∂̄f_α‖_p → p − 1` as `α → 1/p`
  from below (Baernstein–Montgomery-Smith: `∫ |∂f_α|^p / ∫ |∂̄f_α|^p → (p − 1)^p`).
* `External.Lehto.exists_schwartz_tendsto_extremalFun`: `f_α ∈ W^{1,p}` for `1 ≤ p`,
  `0 < α < 1/p`, in the form used: Schwartz functions `φ_k` with `∂̄φ_k → ∂̄f_α` and
  `∂φ_k → ∂f_α` in `L^p`. The `φ_k (z) = z K_k (|z|²)` (`External.Lehto.extremalSchwartz`) have the
  profiles `K_k` of the package's approximations of `f_{2,α}`; dominated convergence, with the
  package's bounds on `K_k` and `K_k'`.

## References

* A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
  `∂̄f`*, in: Complex analysis and differential equations (Uppsala, 1997), Acta Univ. Upsaliensis
  Skr. Uppsala Univ. C Organ. Hist. 64 (1999), 92–109; arXiv:math/9709215v2, §1.
* O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471, p. 465.
* A. Guerra, *Quasiconvexity of the Burkholder function on symmetric matrices*, preprint (2026),
  arXiv:2608.23388: the functions `v_α`, in the proof of the sharpness of the bound on `‖𝒮‖_p`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped SchwartzMap ENNReal Real ComplexConjugate ContDiff

namespace External.Lehto

open HarmonicAnalysis HarmonicAnalysis.BeurlingAhlfors

/-! ### The first Wirtinger derivatives of `z k (|z|²)` -/

/-- `∂ (z k (|z|²)) = k (t) + t k' (t)`, `t = |z|²`, for a real profile `k` differentiable
at `t`. -/
theorem dz_mul_ofReal_radial {k : ℝ → ℝ} {z : ℂ} (hk : DifferentiableAt ℝ k (Complex.normSq z)) :
    dz (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z =
      ((k (Complex.normSq z) + Complex.normSq z * deriv k (Complex.normSq z) : ℝ) : ℂ) := by
  have hK : DifferentiableAt ℝ (fun s => (k s : ℂ)) (Complex.normSq z) :=
    hk.hasDerivAt.ofReal_comp.differentiableAt
  have h := dz_monomial_mul_radial 1 0 hK
  have hf : (fun w : ℂ => w ^ 1 * conj w ^ 0 * ((k (Complex.normSq w) : ℝ) : ℂ)) =
      fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ) := by
    funext w
    ring
  rw [hf, deriv_ofReal_comp] at h
  rw [h]
  simp only [Nat.cast_one, Nat.sub_self, pow_zero, pow_one, zero_add, one_mul, mul_one]
  push_cast
  rw [← Complex.mul_conj]

/-- `∂̄ (z k (|z|²)) = z² k' (|z|²)` for a real profile `k` differentiable at `|z|²`. -/
theorem dzbar_mul_ofReal_radial {k : ℝ → ℝ} {z : ℂ}
    (hk : DifferentiableAt ℝ k (Complex.normSq z)) :
    dzbar (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z =
      z ^ 2 * ((deriv k (Complex.normSq z) : ℝ) : ℂ) := by
  have hK : DifferentiableAt ℝ (fun s => (k s : ℂ)) (Complex.normSq z) :=
    hk.hasDerivAt.ofReal_comp.differentiableAt
  have h := dzbar_monomial_mul_radial 1 0 hK
  have hf : (fun w : ℂ => w ^ 1 * conj w ^ 0 * ((k (Complex.normSq w) : ℝ) : ℂ)) =
      fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ) := by
    funext w
    ring
  rw [hf, deriv_ofReal_comp] at h
  rw [h]
  push_cast
  ring

/-- `|∂ (z k (|z|²))|, |∂̄ (z k (|z|²))| ≤ 2 (1 + |z|²)² M` if `|k (|z|²)|, |k' (|z|²)| ≤ M`. -/
theorem norm_dz_mul_ofReal_radial_le {k : ℝ → ℝ} {z : ℂ} {M : ℝ}
    (hk : DifferentiableAt ℝ k (Complex.normSq z)) (h : DerivBoundTwo k (Complex.normSq z) M) :
    ‖dz (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z‖ ≤ 2 * (1 + ‖z‖ ^ 2) ^ 2 * M ∧
      ‖dzbar (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z‖ ≤
        2 * (1 + ‖z‖ ^ 2) ^ 2 * M := by
  rw [dz_mul_ofReal_radial hk, dzbar_mul_ofReal_radial hk, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← Complex.normSq_eq_norm_sq]
  obtain ⟨h0, h1, -⟩ := h
  set t := Complex.normSq z
  have hM : 0 ≤ M := (abs_nonneg _).trans h0
  have ht0 : 0 ≤ t := Complex.normSq_nonneg z
  have e1 : |k t + t * deriv k t| ≤ |k t| + t * |deriv k t| := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg ht0]
  have e2 := mul_le_mul_of_nonneg_left h1 ht0
  have e3 : (1 + t) * M ≤ 2 * (1 + t) ^ 2 * M := by
    have : 1 + t ≤ 2 * (1 + t) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hM
  constructor
  · nlinarith
  · nlinarith

/-- If `f_k → g` with one derivative at `t = |z|²`, then `∂ (z f_k (|z|²)) → ∂ (z g (|z|²))` and
`∂̄ (z f_k (|z|²)) → ∂̄ (z g (|z|²))` at `z`. -/
theorem tendsto_dz_mul_ofReal_radial {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {z : ℂ}
    (hf : ∀ k, DifferentiableAt ℝ (f k) (Complex.normSq z))
    (hg : DifferentiableAt ℝ g (Complex.normSq z)) (h : TendstoTwo f g (Complex.normSq z)) :
    Tendsto (fun k => dz (fun w => w * ((f k (Complex.normSq w) : ℝ) : ℂ)) z) atTop
        (𝓝 (dz (fun w => w * ((g (Complex.normSq w) : ℝ) : ℂ)) z)) ∧
      Tendsto (fun k => dzbar (fun w => w * ((f k (Complex.normSq w) : ℝ) : ℂ)) z) atTop
        (𝓝 (dzbar (fun w => w * ((g (Complex.normSq w) : ℝ) : ℂ)) z)) := by
  obtain ⟨h0, h1, -⟩ := h
  rw [dz_mul_ofReal_radial hg, dzbar_mul_ofReal_radial hg]
  constructor
  · refine ((Complex.continuous_ofReal.tendsto _).comp (h0.add (h1.const_mul _))).congr
      fun k => ?_
    rw [dz_mul_ofReal_radial (hf k)]
    rfl
  · refine (((Complex.continuous_ofReal.tendsto _).comp h1).const_mul _).congr fun k => ?_
    rw [dzbar_mul_ofReal_radial (hf k)]
    rfl

/-! ### The extremal functions -/

/-- The extremal functions `f_α (z) = z |z|^{−2α} g₂ (|z|)`: on the unit disc, those of
Baernstein–Montgomery-Smith (1999, §1); outside it, Dragičević's continuation (2011, p. 465), with
the cutoff `g₂`. -/
def extremalFun (α : ℝ) (z : ℂ) : ℂ :=
  z * ((‖z‖ ^ (-2 * α) * testCutoff 2 ‖z‖ : ℝ) : ℂ)

/-- On the unit disc, `f_α (w) = w K₀ (|w|²)`, `K₀ (t) = t^{−α}`. -/
theorem extremalFun_eventuallyEq_of_norm_lt_one (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    extremalFun α =ᶠ[𝓝 z] fun w => w * ((Complex.normSq w ^ (-α) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w
    (hw : ‖w‖ < 1)
  rw [extremalFun, testCutoff, ite_eq_left hw.le, mul_one, normSq_rpow_neg]

/-- Outside the closed unit disc, `f_α (w) = w K₁ (|w|²)`, `K₁ (t) = t^{−α} E (t)`,
`E (t) = exp (−(√t − 1)²)`. -/
theorem extremalFun_eventuallyEq_of_one_lt_norm (α : ℝ) {z : ℂ} (hz : 1 < ‖z‖) :
    extremalFun α =ᶠ[𝓝 z] fun w =>
      w * ((Complex.normSq w ^ (-α) * expCutoff (Complex.normSq w) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w
    (hw : 1 < ‖w‖)
  rw [extremalFun, testCutoff, ite_eq_right (not_le.2 hw), normSq_rpow_neg, expCutoff_normSq]

/-! ### The punctured unit disc -/

/-- On the punctured unit disc, `∂f_α (z) = (1 − α) |z|^{−2α}`. -/
theorem dz_extremalFun_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dz (extremalFun α) z = (((1 - α) * ‖z‖ ^ (-2 * α) : ℝ) : ℂ) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have h := dz_mul_ofReal_radial
    ((Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 1) ht.ne').differentiableAt one_ne_zero)
  beta_reduce at h
  rw [(extremalFun_eventuallyEq_of_norm_lt_one α hz).dz_eq, h, deriv_rpow_neg]
  beta_reduce
  rw [Real.rpow_sub_one ht.ne', normSq_rpow_neg]
  congr 1
  field_simp
  ring

/-- On the punctured unit disc, `∂̄f_α (z) = −α z² |z|^{−2α−2}`. -/
theorem dzbar_extremalFun_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dzbar (extremalFun α) z =
      z ^ 2 * ((-α * Complex.normSq z ^ (-α - 1) : ℝ) : ℂ) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have h := dzbar_mul_ofReal_radial
    ((Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 1) ht.ne').differentiableAt one_ne_zero)
  beta_reduce at h
  rw [(extremalFun_eventuallyEq_of_norm_lt_one α hz).dzbar_eq, h, deriv_rpow_neg]

/-- On the punctured unit disc, `|∂̄f_α (z)| = α |z|^{−2α}` for `α ≥ 0`. -/
theorem norm_dzbar_extremalFun_of_norm_lt_one {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz0 : z ≠ 0)
    (hz : ‖z‖ < 1) : ‖dzbar (extremalFun α) z‖ = α * ‖z‖ ^ (-2 * α) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  rw [dzbar_extremalFun_of_norm_lt_one α hz0 hz, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hα,
    abs_of_nonneg (Real.rpow_nonneg ht.le _), ← Complex.normSq_eq_norm_sq,
    Real.rpow_sub_one ht.ne', normSq_rpow_neg]
  field_simp

/-- `∫_Δ |∂f_α|^p = π / (1 − αp) (1 − α)^p` for `0 < α < 1/p`. -/
theorem lintegral_dz_extremalFun_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α) (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dz (extremalFun α) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * (1 - α) ^ p) := by
  have hp0 : 0 < p := by linarith
  have hα1 : α < 1 := by nlinarith
  have hc : 0 < 1 - α := by linarith
  have h : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Metric.ball (0 : ℂ) 1 →
      ‖dz (extremalFun α) z‖ₑ ^ p =
        ENNReal.ofReal ((1 - α) ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz0 hz
    rw [mem_ball_zero_iff] at hz
    rw [dz_extremalFun_of_norm_lt_one α hz0 hz, ← ofReal_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul (norm_nonneg z)]
    congr 3
    ring
  rw [setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet h,
    lintegral_const_mul _ (by fun_prop), lintegral_ball_norm_rpow (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : 1 - α * p ≠ 0 := by linarith
  have : 2 - 2 * α * p ≠ 0 := by linarith
  field_simp

/-- `∫_Δ |∂̄f_α|^p = π / (1 − αp) α^p` for `0 < α < 1/p`. -/
theorem lintegral_dzbar_extremalFun_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dzbar (extremalFun α) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * α ^ p) := by
  have hp0 : 0 < p := by linarith
  have h : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Metric.ball (0 : ℂ) 1 →
      ‖dzbar (extremalFun α) z‖ₑ ^ p =
        ENNReal.ofReal (α ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz0 hz
    rw [mem_ball_zero_iff] at hz
    rw [← ofReal_norm, norm_dzbar_extremalFun_of_norm_lt_one hα0.le hz0 hz,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow hα0.le (by positivity), ← Real.rpow_mul (norm_nonneg z)]
    congr 3
    ring
  rw [setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet h,
    lintegral_const_mul _ (by fun_prop), lintegral_ball_norm_rpow (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : 1 - α * p ≠ 0 := by linarith
  have : 2 - 2 * α * p ≠ 0 := by linarith
  field_simp

/-! ### Outside the unit disc -/

/-- For `|z| > 1` and `α ∈ [0, 1]`:
`|∂f_α (z)|, |∂̄f_α (z)| ≤ 32 (1 + |z|²)² e^{−(|z| − 1)²}`. -/
theorem norm_extremalFun_le_of_one_lt_norm {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : 1 < ‖z‖) :
    ‖dz (extremalFun α) z‖ ≤ 32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) ∧
      ‖dzbar (extremalFun α) z‖ ≤ 32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) := by
  have ht : 1 < Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := norm_dz_mul_ofReal_radial_le
    ((contDiffAt_rpow_neg_mul_expCutoff α (by linarith)).differentiableAt (by norm_num))
    (derivBoundTwo_rpow_neg_mul_expCutoff hα ht.le)
  beta_reduce at h
  rw [expCutoff_normSq] at h
  rw [(extremalFun_eventuallyEq_of_one_lt_norm α hz).dz_eq,
    (extremalFun_eventuallyEq_of_one_lt_norm α hz).dzbar_eq]
  exact ⟨h.1.trans_eq (by ring), h.2.trans_eq (by ring)⟩

/-- Outside the unit disc, `∫ |∂f_α|^p` and `∫ |∂̄f_α|^p` are bounded uniformly in
`α ∈ [0, 1]`. -/
theorem exists_bound_extremalFun_compl_ball {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dz (extremalFun α) z‖ₑ ^ p ≤ ENNReal.ofReal C ∧
        ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dzbar (extremalFun α) z‖ₑ ^ p ≤ ENNReal.ofReal C := by
  set I := ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ,
    ENNReal.ofReal (32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2))) ^ p with hI_def
  have hI : I < ⊤ := lintegral_compl_ball_majorant_lt_top hp (by norm_num)
  refine ⟨I.toReal, fun α hα => ?_⟩
  rw [ENNReal.ofReal_toReal hI.ne]
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) 1)ᶜ), 1 < ‖z‖ := by
    filter_upwards [ae_restrict_of_ae ae_norm_ne_one,
      ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with z hz1 hz2
    rw [mem_compl_iff, mem_ball_zero_iff, not_lt] at hz2
    exact lt_of_le_of_ne hz2 (Ne.symm hz1)
  constructor
  · refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    rw [← ofReal_norm]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (norm_extremalFun_le_of_one_lt_norm hα hz).1) hp.le
  · refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    rw [← ofReal_norm]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (norm_extremalFun_le_of_one_lt_norm hα hz).2) hp.le

/-! ### The limit of the ratio -/

/-- Baernstein–Montgomery-Smith's limit (1999, §1): `‖∂f_α‖_p / ‖∂̄f_α‖_p → p − 1` as `α → 1/p`
from below, for `1 < p < ∞`. -/
theorem tendsto_eLpNorm_div_extremalFun {p : ℝ} (hp : 1 < p) :
    Tendsto (fun α : ℝ =>
        eLpNorm (dz (extremalFun α)) (ENNReal.ofReal p) volume /
          eLpNorm (dzbar (extremalFun α)) (ENNReal.ofReal p) volume)
      (𝓝[<] p⁻¹) (𝓝 (ENNReal.ofReal (p - 1))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpi : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hB : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  have hIoo : ∀ α ∈ Set.Ioo 0 p⁻¹, 0 < α ∧ α * p < 1 ∧ α ∈ Set.Icc (0 : ℝ) 1 := fun α hα =>
    ⟨hα.1, by
      calc α * p < p⁻¹ * p := mul_lt_mul_of_pos_right hα.2 hp0
        _ = 1 := inv_mul_cancel₀ hp0.ne', hα.1.le, (hα.2.trans hpi).le⟩
  -- the integrals over `Δᶜ`, bounded uniformly in `α`
  obtain ⟨C, hC⟩ := exists_bound_extremalFun_compl_ball hp0
  obtain ⟨iOut, hiOut⟩ : ∃ g : ℝ → ℝ, ∀ α, g α =
      (∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dz (extremalFun α) z‖ₑ ^ p).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jOut, hjOut⟩ : ∃ g : ℝ → ℝ, ∀ α, g α =
      (∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dzbar (extremalFun α) z‖ₑ ^ p).toReal :=
    ⟨_, fun _ => rfl⟩
  -- the ratio of the `p`-th powers of the norms, with numerator and denominator multiplied by
  -- `1 − αp`
  have heq : ∀ α ∈ Set.Ioo 0 p⁻¹,
      eLpNorm (dz (extremalFun α)) (ENNReal.ofReal p) volume /
          eLpNorm (dzbar (extremalFun α)) (ENNReal.ofReal p) volume =
        ENNReal.ofReal (((Real.pi * (1 - α) ^ p + (1 - α * p) * iOut α) /
          (Real.pi * α ^ p + (1 - α * p) * jOut α)) ^ (1 / p)) := by
    intro α hα
    obtain ⟨hα0, hαp, hα1⟩ := hIoo α hα
    obtain ⟨hI, hJ⟩ := hC α hα1
    have hε : 0 < 1 - α * p := by linarith
    have hα1' : α < 1 := hα.2.trans hpi
    have ha : 0 < Real.pi / (1 - α * p) * (1 - α) ^ p :=
      mul_pos (div_pos Real.pi_pos hε) (Real.rpow_pos_of_pos (by linarith) _)
    have hb : 0 < Real.pi / (1 - α * p) * α ^ p :=
      mul_pos (div_pos Real.pi_pos hε) (Real.rpow_pos_of_pos hα0 _)
    have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top
        (measurable_dz _).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top
        (measurable_dzbar _).aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le, ← lintegral_add_compl (μ := volume) _ hB,
      ← lintegral_add_compl (μ := volume) _ hB, lintegral_dz_extremalFun_ball hp hα0 hαp,
      lintegral_dzbar_extremalFun_ball hp hα0 hαp,
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI),
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJ),
      ← ENNReal.ofReal_add ha.le ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_add hb.le ENNReal.toReal_nonneg,
      ← ENNReal.div_rpow_of_nonneg _ _ (one_div_nonneg.2 hp0.le),
      ← ENNReal.ofReal_div_of_pos (add_pos_of_pos_of_nonneg hb ENNReal.toReal_nonneg),
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (add_nonneg ha.le ENNReal.toReal_nonneg)
        (add_nonneg hb.le ENNReal.toReal_nonneg)) (one_div_nonneg.2 hp0.le)]
    congr 2
    rw [hiOut, hjOut]
    field_simp
  -- as `α → 1/p`, `1 − αp → 0`, and the integrals over `Δᶜ` disappear
  have hev : ∀ᶠ α in 𝓝[<] p⁻¹, α ∈ Set.Ioo 0 p⁻¹ := Ioo_mem_nhdsLT (inv_pos.2 hp0)
  have hε : Tendsto (fun α : ℝ => 1 - α * p) (𝓝[<] p⁻¹) (𝓝 0) := by
    have h : Tendsto (fun α : ℝ => 1 - α * p) (𝓝 p⁻¹) (𝓝 (1 - p⁻¹ * p)) :=
      (continuous_const.sub (continuous_id.mul continuous_const)).tendsto p⁻¹
    rw [inv_mul_cancel₀ hp0.ne', sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hvanish : ∀ g : ℝ → ℝ,
      (∀ α ∈ Set.Ioo 0 p⁻¹, 0 ≤ g α ∧ g α ≤ (ENNReal.ofReal C).toReal) →
        Tendsto (fun α => (1 - α * p) * g α) (𝓝[<] p⁻¹) (𝓝 0) := by
    intro g hg
    have h0 := hε.mul_const (ENNReal.ofReal C).toReal
    rw [zero_mul] at h0
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [hev] with α hα
      exact mul_nonneg (by linarith [(hIoo α hα).2.1]) (hg α hα).1
    · filter_upwards [hev] with α hα
      exact mul_le_mul_of_nonneg_left (hg α hα).2 (by linarith [(hIoo α hα).2.1])
  have hi := hvanish iOut fun α hα => ⟨(hiOut α).symm ▸ ENNReal.toReal_nonneg,
    (hiOut α).symm ▸ ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC α (hIoo α hα).2.2).1⟩
  have hj := hvanish jOut fun α hα => ⟨(hjOut α).symm ▸ ENNReal.toReal_nonneg,
    (hjOut α).symm ▸ ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC α (hIoo α hα).2.2).2⟩
  have hcont : ∀ g : ℝ → ℝ, Continuous g →
      Tendsto (fun α => Real.pi * g α ^ p) (𝓝[<] p⁻¹) (𝓝 (Real.pi * g p⁻¹ ^ p)) := fun g hg =>
    ((continuous_const.mul (hg.rpow_const fun _ => Or.inr hp0.le)).tendsto p⁻¹).mono_left
      nhdsWithin_le_nhds
  have hnum : Tendsto (fun α => Real.pi * (1 - α) ^ p + (1 - α * p) * iOut α)
      (𝓝[<] p⁻¹) (𝓝 (Real.pi * (1 - p⁻¹) ^ p + 0)) :=
    (hcont (fun α => 1 - α) (by fun_prop)).add hi
  have hden : Tendsto (fun α => Real.pi * α ^ p + (1 - α * p) * jOut α)
      (𝓝[<] p⁻¹) (𝓝 (Real.pi * p⁻¹ ^ p + 0)) :=
    (hcont (fun α => α) (by fun_prop)).add hj
  have ha : 0 < 1 - p⁻¹ := by linarith
  have hb : 0 < p⁻¹ := inv_pos.2 hp0
  have hlim := (hnum.div hden (by
    rw [add_zero]
    exact (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hb p)).ne')).rpow_const
    (Or.inr (one_div_nonneg.2 hp0.le))
  -- the limit is `p − 1`
  have hval : ((Real.pi * (1 - p⁻¹) ^ p + 0) / (Real.pi * p⁻¹ ^ p + 0)) ^ (1 / p) = p - 1 := by
    rw [add_zero, add_zero, mul_div_mul_left _ _ Real.pi_ne_zero, ← Real.div_rpow ha.le hb.le,
      ← Real.rpow_mul (div_pos ha hb).le, mul_one_div_cancel hp0.ne', Real.rpow_one]
    field_simp
  rw [hval] at hlim
  refine (ENNReal.tendsto_ofReal hlim).congr' ?_
  filter_upwards [hev] with α hα
  exact (heq α hα).symm

/-! ### Approximation in `W^{1,p}` -/

/-- The approximants `φ_k (z) = z K_k (|z|²)`, with the profiles `K_k` of the package
(`HarmonicAnalysis.BeurlingAhlfors.approxProfile`). -/
def extremalApprox (α : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  z * ((approxProfile α k (Complex.normSq z) : ℝ) : ℂ)

theorem contDiff_extremalApprox (α : ℝ) (k : ℕ) : ContDiff ℝ ∞ (extremalApprox α k) := by
  have hN : ContDiff ℝ ∞ Complex.normSq := by
    rw [show Complex.normSq = fun z : ℂ => ‖z‖ ^ 2 from funext Complex.normSq_eq_norm_sq]
    exact contDiff_norm_sq ℝ
  rw [contDiff_iff_contDiffAt]
  intro z
  have h1 : ContDiffAt ℝ ∞ (approxProfile α k) (Complex.normSq z) :=
    contDiffAt_approxProfile α k (by linarith [Complex.normSq_nonneg z, approxEps_pos k])
  have h2 : ContDiffAt ℝ ∞ (fun w => ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (h1.comp z hN.contDiffAt)
  exact contDiffAt_id.mul h2

/-- `φ_k (z) = 0` for `|z|² ≥ 2 R_k`. -/
theorem extremalApprox_eq_zero (α : ℝ) (k : ℕ) {z : ℂ}
    (hz : 2 * approxRadius k ≤ Complex.normSq z) : extremalApprox α k z = 0 := by
  rw [extremalApprox, approxProfile, approxTrunc_eq_zero k hz]
  simp

theorem hasCompactSupport_extremalApprox (α : ℝ) (k : ℕ) :
    HasCompactSupport (extremalApprox α k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * approxRadius k))
    fun z hz => extremalApprox_eq_zero α k ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  rw [Complex.normSq_eq_norm_sq]
  have := two_le_approxRadius k
  nlinarith

/-- `φ_k` as a Schwartz function. -/
def extremalSchwartz (α : ℝ) (k : ℕ) : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_extremalApprox α k).toSchwartzMap (contDiff_extremalApprox α k)

/-- `∂φ_k` is the pointwise `∂` of `z K_k (|z|²)`. -/
theorem dzCLM_pow_one_extremalSchwartz (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzCLM ^ 1) (extremalSchwartz α k) z =
      dz (fun w => w * ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ)) z := by
  rw [pow_one, dzCLM_apply]
  rfl

/-- `∂̄φ_k` is the pointwise `∂̄` of `z K_k (|z|²)`. -/
theorem dzbarCLM_pow_one_extremalSchwartz (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzbarCLM ^ 1) (extremalSchwartz α k) z =
      dzbar (fun w => w * ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ)) z := by
  rw [pow_one, dzbarCLM_apply]
  rfl

/-- On `(0, 1)`: `|K_k + t K_k'| ≤ t^{−α}` and `t |K_k'| ≤ t^{−α}`, since `t / (t + ε_k) ≤ 1` and
`(t + ε_k)^{−α} ≤ t^{−α}`. -/
theorem abs_approxProfile_add_le_of_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    |approxProfile α k t + t * deriv (approxProfile α k) t| ≤ t ^ (-α) ∧
      t * |deriv (approxProfile α k) t| ≤ t ^ (-α) := by
  obtain ⟨h0, h1, -⟩ := approxProfile_jet_of_lt_one α k ht1
  rw [h0, h1]
  have hε := approxEps_pos k
  obtain ⟨s, hs_def⟩ : ∃ s, s = t + approxEps k := ⟨_, rfl⟩
  rw [← hs_def]
  have hs : 0 < s := by linarith
  have hts : t ≤ s := by linarith
  have hX0 : 0 < s ^ (-α) := Real.rpow_pos_of_pos hs _
  have hXt : s ^ (-α) ≤ t ^ (-α) := Real.rpow_le_rpow_of_nonpos ht0 hts (by linarith)
  have e1 : s ^ (-α - 1) = s ^ (-α) / s := Real.rpow_sub_one hs.ne' _
  rw [e1]
  obtain ⟨r, hr_def⟩ : ∃ r, r = t / s := ⟨_, rfl⟩
  have hr0 : 0 < r := hr_def ▸ div_pos ht0 hs
  have hr1 : r ≤ 1 := hr_def ▸ (div_le_one hs).2 hts
  have eq1 : s ^ (-α) + t * (-α * (s ^ (-α) / s)) = s ^ (-α) * (1 - α * r) := by
    rw [hr_def]; field_simp; ring
  have eq2 : t * |-α * (s ^ (-α) / s)| = s ^ (-α) * (α * r) := by
    rw [abs_mul, abs_neg, abs_of_pos hα0, abs_of_pos (div_pos hX0 hs), hr_def]
    field_simp
  rw [eq1, eq2, abs_mul, abs_of_pos hX0]
  have har : α * r ≤ 1 := by nlinarith
  have har0 : 0 ≤ α * r := by positivity
  constructor
  · rw [abs_of_nonneg (by linarith)]; nlinarith
  · nlinarith

/-- Domination on the punctured unit disc: `|∂φ_k (z)|, |∂̄φ_k (z)| ≤ |z|^{−2α}`. -/
theorem norm_extremalSchwartz_le_of_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ‖(dzCLM ^ 1) (extremalSchwartz α k) z‖ ≤ ‖z‖ ^ (-2 * α) ∧
      ‖(dzbarCLM ^ 1) (extremalSchwartz α k) z‖ ≤ ‖z‖ ^ (-2 * α) := by
  have ht0 : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have ht1 : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hk := (contDiffAt_two_approxProfile α k z).differentiableAt (by norm_num)
  obtain ⟨h1, h2⟩ := abs_approxProfile_add_le_of_lt_one hα0 hα1 k ht0 ht1
  rw [dzCLM_pow_one_extremalSchwartz, dzbarCLM_pow_one_extremalSchwartz, dz_mul_ofReal_radial hk,
    dzbar_mul_ofReal_radial hk, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, ← Complex.normSq_eq_norm_sq, ← normSq_rpow_neg]
  exact ⟨h1, h2⟩

/-- Domination outside the unit disc, for `α ∈ [0, 1]`:
`|∂φ_k (z)|, |∂̄φ_k (z)| ≤ C (1 + |z|²)² e^{−(|z| − 1)²}`, uniformly in `k`. -/
theorem exists_norm_extremalSchwartz_le_of_one_lt {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C, ∀ k z, 1 < ‖z‖ →
      ‖(dzCLM ^ 1) (extremalSchwartz α k) z‖ ≤
          C * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) ∧
        ‖(dzbarCLM ^ 1) (extremalSchwartz α k) z‖ ≤
          C * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) := by
  obtain ⟨B, hB⟩ := exists_derivBoundTwo_approxProfile hα0 hα1
  refine ⟨2 * B, fun k z hz => ?_⟩
  have ht : 1 < Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := norm_dz_mul_ofReal_radial_le
    ((contDiffAt_two_approxProfile α k z).differentiableAt (by norm_num)) (hB k _ ht)
  rw [expCutoff_normSq] at h
  rw [dzCLM_pow_one_extremalSchwartz, dzbarCLM_pow_one_extremalSchwartz]
  exact ⟨h.1.trans_eq (by ring), h.2.trans_eq (by ring)⟩

/-- `f_α ∈ W^{1,p}` for `1 ≤ p < ∞`, `0 < α < 1/p`, in the form used: there are Schwartz functions
`φ_k` with `∂̄φ_k → ∂̄f_α` and `∂φ_k → ∂f_α` in `L^p`. The `φ_k (z) = z K_k (|z|²)`
(`External.Lehto.extremalSchwartz`) regularise the singularity at `0`, smooth the cutoff at
`|z| = 1` and truncate at infinity. Off `0` and the unit circle, `∂φ_k → ∂f_α` and `∂̄φ_k → ∂̄f_α`
pointwise, with a domination uniform in `k`, by `|z|^{−2α}` on the disc and by
`C (1 + |z|²)² e^{−(|z| − 1)²}` outside it, whose `p`-th power is integrable; dominated convergence
concludes. -/
theorem exists_schwartz_tendsto_extremalFun {p α : ℝ} (hp : 1 ≤ p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    ∃ φ : ℕ → 𝓢(ℂ, ℂ),
      Tendsto (fun k => eLpNorm (fun z => (dzbarCLM ^ 1) (φ k) z - dzbar (extremalFun α) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (fun z => (dzCLM ^ 1) (φ k) z - dz (extremalFun α) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hα1 : α < 1 := by nlinarith
  obtain ⟨C, hC⟩ := exists_norm_extremalSchwartz_le_of_one_lt hα0.le hα1.le
  set c := max C 0 with hc_def
  have hc : 0 ≤ c := le_max_right _ _
  set D : ℂ → ℝ := fun z => if ‖z‖ < 1 then ‖z‖ ^ (-2 * α) else
    c * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) with hD_def
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 ∧ ‖z‖ ≠ 1 :=
    (Measure.ae_ne volume 0).and ae_norm_ne_one
  -- the domination, uniform in `k`
  have hdom : ∀ k z, z ≠ 0 → ‖z‖ ≠ 1 → ‖(dzbarCLM ^ 1) (extremalSchwartz α k) z‖ ≤ D z ∧
      ‖(dzCLM ^ 1) (extremalSchwartz α k) z‖ ≤ D z := by
    intro k z hz0 hz1
    rcases lt_or_gt_of_ne hz1 with h | h
    · rw [hD_def]
      simp only [ite_eq_left h]
      obtain ⟨h1, h2⟩ := norm_extremalSchwartz_le_of_lt_one hα0 hα1 k hz0 h
      exact ⟨h2, h1⟩
    · rw [hD_def]
      simp only [ite_eq_right (not_lt.2 h.le)]
      obtain ⟨h1, h2⟩ := hC k z h
      have hm : 0 ≤ (1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2) := by positivity
      exact ⟨h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm),
        h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm)⟩
  -- the pointwise limits
  have hlim : ∀ z, z ≠ 0 → ‖z‖ ≠ 1 →
      Tendsto (fun k => (dzCLM ^ 1) (extremalSchwartz α k) z) atTop
          (𝓝 (dz (extremalFun α) z)) ∧
        Tendsto (fun k => (dzbarCLM ^ 1) (extremalSchwartz α k) z) atTop
          (𝓝 (dzbar (extremalFun α) z)) := by
    intro z hz0 hz1
    simp only [dzCLM_pow_one_extremalSchwartz, dzbarCLM_pow_one_extremalSchwartz]
    have ht0 : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
    have hk : ∀ k, DifferentiableAt ℝ (approxProfile α k) (Complex.normSq z) := fun k =>
      (contDiffAt_two_approxProfile α k z).differentiableAt (by norm_num)
    rcases lt_or_gt_of_ne hz1 with h | h
    · have ht1 : Complex.normSq z < 1 := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
      have := tendsto_dz_mul_ofReal_radial hk
        ((Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 1) ht0.ne').differentiableAt
          one_ne_zero)
        (tendstoTwo_approxProfile_of_lt_one α ht0 ht1)
      beta_reduce at this
      rwa [(extremalFun_eventuallyEq_of_norm_lt_one α h).dz_eq,
        (extremalFun_eventuallyEq_of_norm_lt_one α h).dzbar_eq]
    · have ht1 : 1 < Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith
      have := tendsto_dz_mul_ofReal_radial hk
        ((contDiffAt_rpow_neg_mul_expCutoff α ht0).differentiableAt (by norm_num))
        (tendstoTwo_approxProfile_of_one_lt α ht1)
      beta_reduce at this
      rwa [(extremalFun_eventuallyEq_of_one_lt_norm α h).dz_eq,
        (extremalFun_eventuallyEq_of_one_lt_norm α h).dzbar_eq]
  -- the integrability of the majorant
  have hfin : ∫⁻ z, ENNReal.ofReal (2 * D z) ^ p ≠ ⊤ := by
    rw [← lintegral_add_compl _ (Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1)).measurableSet]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
        (g := fun z => ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))))
        (fun z hz => ?_)]
      · rw [lintegral_const_mul _ (by fun_prop), lintegral_ball_norm_rpow (by linarith)]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      · rw [mem_ball_zero_iff] at hz
        rw [hD_def]
        simp only [ite_eq_left hz]
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
          Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (norm_nonneg _),
          ENNReal.ofReal_mul (by positivity)]
        congr 3
        ring
    · refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono'
        Metric.isOpen_ball.measurableSet.compl fun z hz => ?_)
        (lintegral_compl_ball_majorant_lt_top hp0 (c := 2 * c) (by positivity)))
      rw [mem_compl_iff, mem_ball_zero_iff, not_lt] at hz
      rw [hD_def]
      simp only [ite_eq_right (not_lt.2 hz)]
      rw [← mul_assoc]
  refine ⟨extremalSchwartz α, ?_, ?_⟩
  · exact tendsto_eLpNorm_sub_of_dominated hp0 (fun k => (SchwartzMap.continuous _).measurable)
      (measurable_dzbar _) (fun k => hae.mono fun z hz => (hdom k z hz.1 hz.2).1) hfin
      (hae.mono fun z hz => (hlim z hz.1 hz.2).2)
  · exact tendsto_eLpNorm_sub_of_dominated hp0 (fun k => (SchwartzMap.continuous _).measurable)
      (measurable_dz _) (fun k => hae.mono fun z hz => (hdom k z hz.1 hz.2).2) hfin
      (hae.mono fun z hz => (hlim z hz.1 hz.2).1)

end External.Lehto
