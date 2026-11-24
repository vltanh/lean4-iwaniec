module

public import Agazzi.Bridges
public import Agazzi.Corollary2.Norm
public import Agazzi.Quasiconvex

/-!
# Solution: the Challenge's theorems, proved from the library

Each theorem restates the Challenge's word for word and proves it from the library: Theorem 1 is
`Agazzi.theorem1`, Corollary 2 is `Agazzi.corollary2` and `Agazzi.corollary2_norm`, and the compared
theorems are in `Agazzi.Bridges`. The module is also the entry point of the library: it imports
every module that the main results use, and `Agazzi.Quasiconvex`, Theorem 1 and Corollary 2 as
quasiconvexity in the sense of `CalculusOfVariations`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate ContDiff

namespace AgazziChallenge

open Agazzi

/-- `det A = |a₊|² − |a₋|²`. -/
theorem det_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 :=
  Agazzi.det_eq A

/-- The operator norm of `A` on Euclidean `ℝ²` is `|a₊| + |a₋|`. -/
theorem opNorm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ =
      ‖conformalPart A‖ + ‖anticonformalPart A‖ :=
  Agazzi.opNorm_eq A

/-- The unit square, the torus `Q`, has measure `1`. -/
theorem volume_unitSquare : volume unitSquare = 1 :=
  Agazzi.volume_unitSquare

/-- `𝒮 ∘ ∂_z̄ = ∂_z` on Schwartz functions (`(eq:BA-definition)`). -/
theorem beurling_dzbar (F : 𝓢(ℂ, ℂ)) : beurling (dzbar F) = dz F :=
  Agazzi.beurling_dzbar F

/-- **Theorem 1.** For all `A ∈ ℝ^{2×2}` and all `φ ∈ C^∞_per (Q; ℝ²)`,
`∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`. -/
theorem theorem1 (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (integrandL (A + jacobian φ x) - integrandL A) :=
  Agazzi.theorem1 A hφ hper

/-- **Corollary 2**, first assertion. For every `1 < p < ∞`, every `A ∈ ℝ^{2×2}` and every
`φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`. -/
theorem corollary2 {p : ℝ} (hp : 1 < p) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (burkholderB p (A + jacobian φ x) - burkholderB p A) :=
  Agazzi.corollary2 hp A hφ hper

/-- **Corollary 2**, second assertion. The norm of the Beurling–Ahlfors transform on
`L^p (ℂ; ℂ)` is `p* − 1`, for `1 < p < ∞`. -/
theorem corollary2_norm {p : ℝ} (hp : 1 < p) : beurlingNorm p = ENNReal.ofReal (pStar p - 1) :=
  Agazzi.corollary2_norm hp

/-- `p* − 1 = (p − 1)⁻¹` for `1 < p ≤ 2`. -/
theorem pStar_sub_one_of_le_two {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    pStar p - 1 = (p - 1)⁻¹ :=
  Agazzi.pStar_sub_one_of_le_two hp hp2

/-- `p* − 1 = p − 1` for `p ≥ 2`. -/
theorem pStar_sub_one_of_two_le {p : ℝ} (hp2 : 2 ≤ p) : pStar p - 1 = p - 1 :=
  Agazzi.pStar_sub_one_of_two_le hp2

end AgazziChallenge
