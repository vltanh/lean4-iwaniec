/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Defs
import Agazzi.External.Lehto.TestFunctions
import HarmonicAnalysis.BeurlingAhlfors.Duality

/-!
# Lehto: the lower bound `‖𝒮‖_p ≥ p* − 1`

O. Lehto, *Remarks on the integrability of the derivatives of quasiconformal mappings*, Ann. Acad.
Sci. Fenn. Ser. A I No. 371 (1965). The paper (arXiv:2609.28311, TeX line 320) cites it for the
lower bound in `(eq:BA-sharp-norm)`: "the lower bound in (eq:BA-sharp-norm) is classical
[Lehto1965]".

Stated (`lowerBound`) with the package `HarmonicAnalysis`'s Beurling–Ahlfors transform `𝓑`
(symbol `ξ̄ / ξ`) and its norm on `L^p (ℂ)`, the supremum over Schwartz functions
(`HarmonicAnalysis.beurlingPowNorm 1 p`).
The source has not been read: its statement is the classical one, as the paper uses it.

## Proof

Not Lehto's, which was not read. First `‖𝓑‖_p ≥ p − 1`
(`External.Lehto.sub_one_le_beurlingPowNorm_one`), with the extremal functions of
Baernstein–Montgomery-Smith (1999, §1), `f_α (z) = z |z|^{−2α}` on the unit disc, `0 < α < 1/p`,
continued outside the disc by a rapidly decaying cutoff (`External.Lehto.extremalFun`, in
`Agazzi.External.Lehto.TestFunctions`):

* `‖∂f_α‖_p ≤ ‖𝓑‖_p ‖∂̄f_α‖_p`, by `𝓑 (∂̄φ) = ∂φ` for Schwartz functions `φ` and the density lemma
  `HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto`, applied to Schwartz approximations of
  `f_α` in `W^{1,p}` (`External.Lehto.exists_schwartz_tendsto_extremalFun`);
* `‖∂f_α‖_p / ‖∂̄f_α‖_p → p − 1` as `α → 1/p` (`External.Lehto.tendsto_eLpNorm_div_extremalFun`).

Then `‖𝓑‖_p = ‖𝓑‖_q`, `q = p / (p − 1)` (`HarmonicAnalysis.beurlingPowNorm_conjExponent`), gives
`‖𝓑‖_p ≥ q − 1`; Baernstein and Montgomery-Smith take the
conjugates `f̄_α` instead.

## References

* A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
  `∂̄f`*, in: Complex analysis and differential equations (Uppsala, 1997), Acta Univ. Upsaliensis
  Skr. Uppsala Univ. C Organ. Hist. 64 (1999), 92–109; arXiv:math/9709215v2, §1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace External.Lehto

open HarmonicAnalysis

/-- `‖𝒮‖_{L^p → L^p} ≥ p − 1` for `1 < p < ∞`.

Proof: the extremal functions `f_α` of Baernstein–Montgomery-Smith (1999, §1), with
`‖∂f_α‖_p / ‖∂̄f_α‖_p → p − 1` as `α → 1/p`, and the density lemma of `HarmonicAnalysis`
(`HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto`). -/
theorem sub_one_le_beurlingPowNorm_one {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (p - 1) ≤ beurlingPowNorm 1 p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  refine le_of_tendsto (tendsto_eLpNorm_div_extremalFun hp) ?_
  filter_upwards [Ioo_mem_nhdsLT (inv_pos.mpr hp0)] with α hα
  have hαp : α * p < 1 :=
    calc α * p < p⁻¹ * p := mul_lt_mul_of_pos_right hα.2 hp0
      _ = 1 := inv_mul_cancel₀ hp0.ne'
  obtain ⟨φ, hu, hv⟩ := exists_schwartz_tendsto_extremalFun hp.le hα.1 hαp
  exact div_le_beurlingPowNorm_of_tendsto 1 hp.le hu hv

/-- **Lehto's lower bound**: `‖𝒮‖_{L^p → L^p} ≥ p* − 1`, `p* = max (p, p / (p − 1))`, for
`1 < p < ∞`.

Proof: the extremal functions `f_α` of Baernstein–Montgomery-Smith (1999, §1) and the density
lemma of `HarmonicAnalysis` give `‖𝒮‖_p ≥ p − 1` (`External.Lehto.sub_one_le_beurlingPowNorm_one`);
duality, `‖𝒮‖_p = ‖𝒮‖_{p'}` (`HarmonicAnalysis.beurlingPowNorm_conjExponent`), gives
`‖𝒮‖_p ≥ p' − 1`. Lehto's own argument was not read. -/
theorem lowerBound {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (max p (p / (p - 1)) - 1) ≤ HarmonicAnalysis.beurlingPowNorm 1 p := by
  have hq : 1 < p / (p - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
  rw [← max_sub_sub_right, ENNReal.ofReal_max]
  refine max_le (sub_one_le_beurlingPowNorm_one hp) ?_
  rw [beurlingPowNorm_conjExponent 1 hp]
  exact sub_one_le_beurlingPowNorm_one hq

end External.Lehto
