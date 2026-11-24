/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Bridges
public import Agazzi.Corollary2.Quasiconvexity
public import Agazzi.Corollary2.Torus
public import Agazzi.External.Lehto.LowerBound

/-!
# Corollary 2, second part: the norm of the Beurling–Ahlfors transform

**Corollary 2** (`cor:Bp-BA`), second assertion `(eq:BA-sharp-norm)`:
`‖𝒮‖_{L^p (ℂ; ℂ) → L^p (ℂ; ℂ)} = p* − 1`, which is `(p − 1)⁻¹` for `1 < p ≤ 2` and `p − 1` for
`2 ≤ p < ∞` (`pStar_sub_one_of_le_two`, `pStar_sub_one_of_two_le`).

The paper derives it from Theorem 1 "by the arguments in [Baernstein1997a]" (TeX line 301), with the
lower bound from [Lehto1965] (TeX line 320). The upper bound `beurlingNorm_le` follows the argument
of Baernstein–Montgomery-Smith (§1, "Conjecture 2 ⇒ Conjecture 3", and remark (b)), in the periodic
setting of the paper, in four steps.

1. For smooth `ℤ²`-periodic `u : ℝ² → ℂ` and `φ = (Re u, Im u)`, `a₊ (D φ) = ∂u` and
   `a₋ (D φ) = ∂̄u` (`Agazzi.Corollary2Norm.conformalPart_jacobian_toRealPair`,
   `Agazzi.Corollary2Norm.anticonformalPart_jacobian_toRealPair`, in `Agazzi.Corollary2.Torus`).
2. The first assertion of Corollary 2 at `A = 0` (`corollary2`; `B_p (0) = 0`) gives
   `∫_Q B_p (D φ) ≥ 0`. With `α_p B_p (A) = Φ_p (a₊, a₋)` for `p < 2` and `Φ_p (a₋, a₊)` for
   `p ≥ 2` (`α_p > 0`), and Burkholder's inequality `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p`
   (`External.BaernsteinMontgomerySmith.phi_le`):
   * for `p ≥ 2`, `∫_Q |∂u|^p ≤ (p* − 1)^p ∫_Q |∂̄u|^p`;
   * for `p < 2`, `∫_Q |∂̄u|^p ≤ (p* − 1)^p ∫_Q |∂u|^p`, and, applied to `ū`
     (`∂ū = conj (∂̄u)`, `∂̄ū = conj (∂u)`: the interchangeability of `∂f` and `∂̄f` of
     Baernstein–Montgomery-Smith), `∫_Q |∂u|^p ≤ (p* − 1)^p ∫_Q |∂̄u|^p`.

   Hence `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂̄u‖_{L^p (Q)}` for every `1 < p < ∞`
   (`Agazzi.Corollary2Norm.eLpNorm_dzPi_le`).
3. On the torus: every mean-zero trigonometric polynomial `h` is `∂̄u` for a smooth periodic `u`
   (`UnitAddTorus.exists_dzbarPi_eq`), and then `𝓑 h = ∂u`
   (`HarmonicAnalysis.periodicMultiplier_beurlingSymbol_dzbarPi`); hence the norm of the
   Beurling–Ahlfors multiplier on `L^p_0 (𝕋²)` is at most `p* − 1`
   (`Agazzi.Corollary2Norm.torusBeurlingPowNorm_one_le`).
4. Transference from `𝕋²` to `ℂ` (`HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm`).

The paper does not say how it passes from the periodic inequality to `L^p (ℂ)`: Baernstein and
Montgomery-Smith work on the plane, with compactly supported `f`. Step 4, transference
(Hytönen–van Neerven–Veraar–Weis, Corollary 5.7.6, as in the package `HarmonicAnalysis`), is the
formalization's route for this step, the cheapest sound one given the package.
-/

@[expose] public section

noncomputable section

open MeasureTheory UnitAddTorus
open scoped ENNReal ComplexConjugate ContDiff

namespace Agazzi

namespace Corollary2Norm

open External.BaernsteinMontgomerySmith (Phi alpha phi_le)

/-! ### The Burkholder integrand and the function `Φ_p` of Baernstein–Montgomery-Smith -/

theorem bms_pStar_eq (p : ℝ) : External.BaernsteinMontgomerySmith.pStar p = pStar p := rfl

theorem le_pStar (p : ℝ) : p ≤ pStar p := le_max_left _ _

/-- `α_p = p (1 − 1/p*)^{p−1} > 0` for `1 < p`. -/
theorem alpha_pos {p : ℝ} (hp : 1 < p) : 0 < alpha p := by
  have h1 : 1 < pStar p := lt_of_lt_of_le hp (le_pStar p)
  have h2 : 0 < 1 - 1 / pStar p := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact h1
  rw [alpha, bms_pStar_eq]
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos h2 _)

/-- `B_p (0) = 0`. -/
theorem burkholderB_zero (p : ℝ) : burkholderB p 0 = 0 := by
  have h1 : conformalPart 0 = 0 := by apply Complex.ext <;> simp [conformalPart]
  have h2 : anticonformalPart 0 = 0 := by apply Complex.ext <;> simp [anticonformalPart]
  simp [burkholderB, h1, h2]

/-- `α_p B_p (A) = Φ_p (a₊, a₋)` for `p < 2`. -/
theorem alpha_mul_burkholderB_of_lt_two {p : ℝ} (hp2 : p < 2) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    alpha p * burkholderB p A = Phi p (conformalPart A) (anticonformalPart A) := by
  rw [burkholderB, ite_eq_left hp2, Phi, bms_pStar_eq, mul_assoc]

/-- `α_p B_p (A) = Φ_p (a₋, a₊)` for `p ≥ 2`. -/
theorem alpha_mul_burkholderB_of_two_le {p : ℝ} (hp2 : 2 ≤ p) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    alpha p * burkholderB p A = Phi p (anticonformalPart A) (conformalPart A) := by
  rw [burkholderB, ite_eq_right (not_lt.2 hp2), Phi, bms_pStar_eq, mul_assoc,
    add_comm ‖anticonformalPart A‖]

/-! ### Step 2: `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂̄u‖_{L^p (Q)}` -/

/-- From `0 ≤ ∫_Q Φ_p (f, g)` and Burkholder's inequality `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p`:
`∫_Q |g|^p ≤ (p* − 1)^p ∫_Q |f|^p`, for continuous `f`, `g`. -/
theorem integral_rpow_le_of_integral_phi_nonneg {p : ℝ} (hp : 1 < p)
    {f g : (Fin 2 → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : 0 ≤ ∫ x in unitSquare, Phi p (f x) (g x)) :
    ∫ x in unitSquare, ‖g x‖ ^ p ≤ (pStar p - 1) ^ p * ∫ x in unitSquare, ‖f x‖ ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hF : IntegrableOn (fun x => ‖f x‖ ^ p) unitSquare :=
    integrableOn_cube_of_continuous (hf.norm.rpow_const fun _ => Or.inr hp0)
  have hG : IntegrableOn (fun x => ‖g x‖ ^ p) unitSquare :=
    integrableOn_cube_of_continuous (hg.norm.rpow_const fun _ => Or.inr hp0)
  have hPhi : IntegrableOn (fun x => Phi p (f x) (g x)) unitSquare := by
    refine integrableOn_cube_of_continuous ?_
    unfold Phi
    exact (continuous_const.mul ((continuous_const.mul hf.norm).sub hg.norm)).mul
      ((hf.norm.add hg.norm).rpow_const fun _ => Or.inr (by linarith))
  have hR : IntegrableOn (fun x => (pStar p - 1) ^ p * ‖f x‖ ^ p - ‖g x‖ ^ p) unitSquare :=
    (hF.const_mul _).sub hG
  have hmono := setIntegral_mono hPhi hR fun x => by
    simpa only [bms_pStar_eq] using phi_le hp (f x) (g x)
  rw [integral_sub (hF.const_mul _) hG, integral_const_mul] at hmono
  linarith

/-- `0 ≤ ∫_Q α_p B_p (D φ)` for `φ = (Re u, Im u)`: Corollary 2 at `A = 0`. -/
theorem integral_alpha_mul_burkholderB_nonneg {p : ℝ} (hp : 1 < p) {u : (Fin 2 → ℝ) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    0 ≤ ∫ x in unitSquare, alpha p * burkholderB p (jacobian (toRealPair u) x) := by
  have h := corollary2 hp 0 (contDiff_toRealPair hu) (isPeriodic_toRealPair hper)
  simp only [zero_add, burkholderB_zero, sub_zero] at h
  rw [integral_const_mul]
  exact mul_nonneg (alpha_pos hp).le h

/-- Step 2 for `1 < p < 2`: `∫_Q |∂̄u|^p ≤ (p* − 1)^p ∫_Q |∂u|^p` for smooth periodic `u`. -/
theorem integral_norm_dzbarPi_rpow_le_of_lt_two {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    ∫ x in unitSquare, ‖dzbarPi u x‖ ^ p ≤
      (pStar p - 1) ^ p * ∫ x in unitSquare, ‖dzPi u x‖ ^ p := by
  refine integral_rpow_le_of_integral_phi_nonneg hp (contDiff_dzPi hu).continuous
    (contDiff_dzbarPi hu).continuous ?_
  have hd : ∀ x, DifferentiableAt ℝ u x := hu.differentiable (by simp)
  have e : (fun x => Phi p (dzPi u x) (dzbarPi u x)) =
      fun x => alpha p * burkholderB p (jacobian (toRealPair u) x) := by
    funext x
    rw [alpha_mul_burkholderB_of_lt_two hp2, conformalPart_jacobian_toRealPair (hd x),
      anticonformalPart_jacobian_toRealPair (hd x)]
  rw [e]
  exact integral_alpha_mul_burkholderB_nonneg hp hu hper

/-- Step 2 for `2 ≤ p`: `∫_Q |∂u|^p ≤ (p* − 1)^p ∫_Q |∂̄u|^p` for smooth periodic `u`. -/
theorem integral_norm_dzPi_rpow_le_of_two_le {p : ℝ} (hp2 : 2 ≤ p)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    ∫ x in unitSquare, ‖dzPi u x‖ ^ p ≤
      (pStar p - 1) ^ p * ∫ x in unitSquare, ‖dzbarPi u x‖ ^ p := by
  have hp : 1 < p := by linarith
  refine integral_rpow_le_of_integral_phi_nonneg hp (contDiff_dzbarPi hu).continuous
    (contDiff_dzPi hu).continuous ?_
  have hd : ∀ x, DifferentiableAt ℝ u x := hu.differentiable (by simp)
  have e : (fun x => Phi p (dzbarPi u x) (dzPi u x)) =
      fun x => alpha p * burkholderB p (jacobian (toRealPair u) x) := by
    funext x
    rw [alpha_mul_burkholderB_of_two_le hp2, conformalPart_jacobian_toRealPair (hd x),
      anticonformalPart_jacobian_toRealPair (hd x)]
  rw [e]
  exact integral_alpha_mul_burkholderB_nonneg hp hu hper

/-- Step 2: `∫_Q |∂u|^p ≤ (p* − 1)^p ∫_Q |∂̄u|^p` for smooth periodic `u` and `1 < p`. For `p < 2`,
the inequality for `p < 2` applied to `ū`, by the interchangeability of `∂` and `∂̄`
(Baernstein–Montgomery-Smith, §1: `∂ū = conj (∂̄u)`, `∂̄ū = conj (∂u)`). This is the source's
argument; duality (`HarmonicAnalysis.beurlingPowNorm_conjExponent`, `‖𝒮‖_p = ‖𝒮‖_{p'}`) would
also reduce `p < 2` to `p' > 2`, at the level of the norm on `L^p (ℂ)`. -/
theorem integral_norm_dzPi_rpow_le {p : ℝ} (hp : 1 < p)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    ∫ x in unitSquare, ‖dzPi u x‖ ^ p ≤
      (pStar p - 1) ^ p * ∫ x in unitSquare, ‖dzbarPi u x‖ ^ p := by
  rcases lt_or_ge p 2 with hp2 | hp2
  · have h := integral_norm_dzbarPi_rpow_le_of_lt_two hp hp2 (contDiff_conj hu)
      (isPeriodic_conj hper)
    simpa only [dzPi_conj, dzbarPi_conj, Complex.norm_conj] using h
  · exact integral_norm_dzPi_rpow_le_of_two_le hp2 hu hper

/-- Step 2, in `L^p` norms: `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂̄u‖_{L^p (Q)}` for smooth periodic `u` and
`1 < p`. -/
theorem eLpNorm_dzPi_le {p : ℝ} (hp : 1 < p)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    eLpNorm (dzPi u) (ENNReal.ofReal p) (volume.restrict (cube (Fin 2))) ≤
      ENNReal.ofReal (pStar p - 1) *
        eLpNorm (dzbarPi u) (ENNReal.ofReal p) (volume.restrict (cube (Fin 2))) := by
  have hp0 : 0 < p := by linarith
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hc : 0 ≤ pStar p - 1 := by linarith [le_pStar p]
  have hmem : ∀ g : (Fin 2 → ℝ) → ℂ, Continuous g → UnitAddTorus.IsPeriodic g →
      MemLp g (ENNReal.ofReal p) (volume.restrict (cube (Fin 2))) := by
    intro g hg hgp
    obtain ⟨C, hC⟩ := hgp.exists_bound hg
    exact MemLp.of_bound hg.aestronglyMeasurable C (ae_of_all _ hC)
  rw [(hmem _ (contDiff_dzPi hu).continuous (isPeriodic_dzPi hper)).eLpNorm_eq_integral_rpow_norm
      h0 ENNReal.ofReal_ne_top,
    (hmem _ (contDiff_dzbarPi hu).continuous
      (isPeriodic_dzbarPi hper)).eLpNorm_eq_integral_rpow_norm h0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have hI2 : 0 ≤ ∫ x in cube (Fin 2), ‖dzbarPi u x‖ ^ p :=
    integral_nonneg fun x => by positivity
  calc (∫ x in cube (Fin 2), ‖dzPi u x‖ ^ p) ^ p⁻¹
      ≤ ((pStar p - 1) ^ p * ∫ x in cube (Fin 2), ‖dzbarPi u x‖ ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x => by positivity)
          (integral_norm_dzPi_rpow_le hp hu hper) (inv_nonneg.2 hp0.le)
    _ = (pStar p - 1) * (∫ x in cube (Fin 2), ‖dzbarPi u x‖ ^ p) ^ p⁻¹ := by
        rw [Real.mul_rpow (by positivity) hI2, Real.rpow_rpow_inv hc hp0.ne']

/-! ### Step 3: the bound on the torus -/

/-- `‖𝓑 h‖_{L^p (𝕋²)} ≤ (p* − 1) ‖h‖_{L^p (𝕋²)}` for every mean-zero trigonometric polynomial `h`
(coefficients `c`, `c₀ = 0`): `h = ∂̄u` for a smooth periodic `u`, and `𝓑 h = ∂u`. -/
theorem eLpNorm_torusBeurlingPow_le {p : ℝ} (hp : 1 < p) (c : (Fin 2 → ℤ) →₀ ℂ) (hc : c 0 = 0) :
    eLpNorm (HarmonicAnalysis.torusBeurlingPow 1 c) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (pStar p - 1) *
        eLpNorm (HarmonicAnalysis.trigPoly c) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  obtain ⟨u, hu, hup, -, hdu⟩ := exists_dzbarPi_eq (contDiff_trigPoly_ofPi c)
    (isPeriodic_trigPoly_ofPi c) (by rw [cubeFourierCoeff_trigPoly_ofPi_zero, hc])
  have key : (fun x => HarmonicAnalysis.torusBeurlingPow 1 c (ofPi x)) = dzPi u := by
    rw [← HarmonicAnalysis.periodicMultiplier_beurlingSymbol_dzbarPi hu hup, hdu,
      ← HarmonicAnalysis.periodicMultiplier_trigPoly 1 c]
    simp only [pow_one]
  have hcont : Continuous (HarmonicAnalysis.torusBeurlingPow 1 c) :=
    HarmonicAnalysis.continuous_torusMultiplier _ c
  rw [eLpNorm_torus_eq_cube hcont hp0,
    eLpNorm_torus_eq_cube (HarmonicAnalysis.continuous_trigPoly c) hp0, key, ← hdu]
  exact eLpNorm_dzPi_le hp hu hup

/-- Step 3: the norm of the Beurling–Ahlfors multiplier on `L^p_0 (𝕋²)` is at most `p* − 1`. -/
theorem torusBeurlingPowNorm_one_le {p : ℝ} (hp : 1 < p) :
    HarmonicAnalysis.torusBeurlingPowNorm 1 p ≤ ENNReal.ofReal (pStar p - 1) :=
  iSup₂_le fun c hc => ENNReal.div_le_of_le_mul (eLpNorm_torusBeurlingPow_le hp c hc)

end Corollary2Norm

/-- The upper bound in `(eq:BA-sharp-norm)`: `‖𝒮‖_p ≤ p* − 1` for `1 < p < ∞`.

The argument of Baernstein–Montgomery-Smith (§1) in the periodic setting: Corollary 2 at `A = 0`
and Burkholder's inequality give `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂̄u‖_{L^p (Q)}` for smooth periodic
`u` (for `p < 2` through `u ↦ ū`, the interchangeability of `∂` and `∂̄`), that is, the bound on
`L^p_0 (𝕋²)` (`Corollary2Norm.torusBeurlingPowNorm_one_le`). The passage to `L^p (ℂ)`, which the
paper leaves implicit, is here transference
(`HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm`). -/
theorem beurlingNorm_le {p : ℝ} (hp : 1 < p) : beurlingNorm p ≤ ENNReal.ofReal (pStar p - 1) := by
  rw [beurlingNorm_eq_beurlingPowNorm]
  exact (HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm 1 hp).trans
    (Corollary2Norm.torusBeurlingPowNorm_one_le hp)

/-- **Corollary 2** (`cor:Bp-BA`), second assertion `(eq:BA-sharp-norm)`: the norm of the
Beurling–Ahlfors transform on `L^p (ℂ; ℂ)` is `p* − 1`, for `1 < p < ∞`. -/
theorem corollary2_norm {p : ℝ} (hp : 1 < p) : beurlingNorm p = ENNReal.ofReal (pStar p - 1) := by
  refine le_antisymm (beurlingNorm_le hp) ?_
  rw [beurlingNorm_eq_beurlingPowNorm]
  exact External.Lehto.lowerBound hp

end Agazzi
