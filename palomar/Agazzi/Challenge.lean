module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Challenge: the main results of arXiv:2609.28311

A. Agazzi, K. Astala, R. Bañuelos, G. Bruno, G. Cassese, D. Faraco, A. Guerra, M. Hormozi,
B. Kirchheim, A. Koski, V. Kovač, J. Kristensen, F. Pasqualotto, I. Prause, E. Saksman, V. Šverák,
L. Székelyhidi, R. Tione, A. Volberg, H. Yang, *Sharp higher integrability theory, Part I: the
`L^p`-norm of the Beurling–Ahlfors transform*, arXiv:2609.28311v2 (2026).

Conventions (the definitions are below, between the markers).

* A real `2 × 2` matrix `A` (`Matrix (Fin 2) (Fin 2) ℝ`) acts on `ℝ² = ℂ` as `A z = a₊ z + a₋ z̄`,
  with `a₊ = conformalPart A = ((a₁₁ + a₂₂) + i (a₂₁ − a₁₂)) / 2` and
  `a₋ = anticonformalPart A = ((a₁₁ − a₂₂) + i (a₂₁ + a₁₂)) / 2`. Its operator norm is
  `|a₊| + |a₋|` and its determinant `|a₊|² − |a₋|²` (`opNorm_eq`, `det_eq` below).
* `integrandL A` is the paper's `L (A)`: `|a₊|² − |a₋|²` if `|a₊| + |a₋| ≤ 1`, and `2 |a₊| − 1`
  otherwise.
* `pStar p = max (p, p / (p − 1))`; `burkholderB p A` is the paper's `B_p (A)`:
  `((p* − 1) |a₊| − |a₋|) (|a₊| + |a₋|)^{p−1}` if `p < 2`, and
  `((p* − 1) |a₋| − |a₊|) (|a₊| + |a₋|)^{p−1}` if `p ≥ 2`.
* The torus `Q = ℝ² / ℤ²` is represented by `ℤ²`-periodic maps on `ℝ² = Fin 2 → ℝ` (`IsPeriodic`),
  and `∫_Q` by the integral over the open unit square `unitSquare = (0, 1)²`, which has measure `1`.
  A map `φ ∈ C^∞_per (Q; ℝ²)` is a `C^∞` (`ContDiff ℝ ∞`) periodic map `ℝ² → ℝ²`, and
  `jacobian φ x` is its derivative matrix `(∂_j φ_i (x))_{i j}`.
* `beurling f = 𝓕⁻¹ (ξ ↦ (ξ̄ / ξ) 𝓕 f (ξ))` is the Beurling–Ahlfors transform `𝒮`, with Mathlib's
  Fourier transform on `ℂ`; it satisfies `𝒮 (∂_z̄ F) = ∂_z F` for Schwartz `F` (`beurling_dzbar`
  below), the paper's characterization `(eq:BA-definition)`. `beurlingNorm p` is its norm on
  `L^p (ℂ; ℂ)`, the supremum of `‖𝒮 f‖_p / ‖f‖_p` over Schwartz functions `f` (a dense class), in
  `[0, ∞]`.
* Sobolev functions on an open `Ω ⊆ ℂ`: `MemLpLoc f p Ω` is `f ∈ L^p_loc (Ω)` (`f ∈ L^p (K)` for
  every compact `K ⊆ Ω`); `HasWeakLineDerivOn Ω f g v` says that `g` is the weak derivative of `f`
  in the direction `v` on `Ω` (`∫ (∂_v φ) f = −∫ φ g` for every real `φ ∈ C_c^∞ (ℂ)` with support
  in `Ω`); `MemW12Loc Ω f fx fy` is `f ∈ W^{1,2}_loc (Ω)` with the weak partial derivatives
  `fx = ∂_x f`, `fy = ∂_y f`. Then `∂f = (fx − i fy) / 2`, `∂̄f = (fx + i fy) / 2`, and
  `Df ∈ L^p_loc (Ω)` means `fx, fy ∈ L^p_loc (Ω)`. `radialStretch α z = |z|^{α − 1} z`.

Statements.

* `theorem1` (Theorem 1): for all `A` and all `φ ∈ C^∞_per (Q; ℝ²)`,
  `∫_Q [L (A + Dφ) − L (A)] ≥ 0`.
* `corollary2` (Corollary 2, first assertion): for every `1 < p < ∞`, every `A` and every
  `φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [B_p (A + Dφ) − B_p (A)] ≥ 0`.
* `corollary2_norm` (Corollary 2, second assertion): `‖𝒮‖_{L^p → L^p} = p* − 1` for `1 < p < ∞`,
  and `p* − 1` is `(p − 1)⁻¹` for `1 < p ≤ 2` and `p − 1` for `p ≥ 2`
  (`pStar_sub_one_of_le_two`, `pStar_sub_one_of_two_le`).
* `theorem1_hessian` (the Hessian case of Theorem 1, TeX line 285): for all `A` and all
  `u ∈ C^∞_per (Q)`, `∫_Q [L (A + D²u) − L (A)] ≥ 0`, with `D²u` the derivative matrix of the
  gradient `(∂₁u, ∂₂u)`.
* `astala` (the consequence of Corollary 2 stated at TeX lines 323–324: Astala's sharp higher
  integrability of quasiregular maps): for `0 ≤ k < 1` and `f ∈ W^{1,2}_loc (Ω)` with
  `|∂̄f| ≤ k |∂f|` a.e. in the open `Ω`, `Df ∈ L^p_loc (Ω)` for `2 ≤ p` with `k (p − 1) < 1`,
  that is `p < 1 + 1/k = 2K/(K − 1)`, `K = (1 + k)/(1 − k)`.
* `astala_sharp`: for `K > 1`, `f (z) = z |z|^{1/K − 1}` is a homeomorphism in `W^{1,2}_loc (ℂ)`
  with `|∂̄f| = k |∂f|` off `0`, `k = (K − 1)/(K + 1)`, `k (2K/(K − 1) − 1) = 1`, and `∂_x f` is not
  in `L^{2K/(K−1)}` of any disc around `0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace Agazzi

-- BEGIN SHARED DEFINITIONS

/-- The conformal part `a₊ = ((a₁₁ + a₂₂) + i (a₂₁ − a₁₂)) / 2` of `A`: with `ℝ² = ℂ`,
`A z = a₊ z + a₋ z̄`. -/
def conformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 + A 1 1) / 2, (A 1 0 - A 0 1) / 2⟩

/-- The anticonformal part `a₋ = ((a₁₁ − a₂₂) + i (a₂₁ + a₁₂)) / 2` of `A`. -/
def anticonformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 - A 1 1) / 2, (A 1 0 + A 0 1) / 2⟩

/-- The integrand `L` of `(eq:L-definition)`: `L (A) = |a₊|² − |a₋|²` if `|A| ≤ 1`, and
`L (A) = 2 |a₊| − 1` if `|A| > 1`, where `|A| = |a₊| + |a₋|` is the operator norm. -/
def integrandL (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  if ‖conformalPart A‖ + ‖anticonformalPart A‖ ≤ 1 then
    ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2
  else 2 * ‖conformalPart A‖ - 1

/-- `p* = max (p, p / (p − 1))`. -/
def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- The Burkholder integrand `B_p` of `(eq:Bp-definition)`:
`B_p (A) = ((p* − 1) |a₊| − |a₋|) (|a₊| + |a₋|)^{p−1}` if `1 < p < 2`, and
`B_p (A) = ((p* − 1) |a₋| − |a₊|) (|a₊| + |a₋|)^{p−1}` if `2 ≤ p < ∞` (the real power `rpow`).
It is used for `1 < p` only. -/
def burkholderB (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  if p < 2 then
    ((pStar p - 1) * ‖conformalPart A‖ - ‖anticonformalPart A‖) *
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1)
  else
    ((pStar p - 1) * ‖anticonformalPart A‖ - ‖conformalPart A‖) *
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1)

/-- The open unit square `(0, 1)²`, a fundamental domain of `ℤ²` in `ℝ²`: integrals over the torus
`Q = ℝ² / ℤ²` are integrals over it. -/
def unitSquare : Set (Fin 2 → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- `φ` is `ℤ²`-periodic: `φ (x + k) = φ (x)` for all `x ∈ ℝ²`, `k ∈ ℤ²`; that is, `φ` is a
function on the torus `Q = ℝ² / ℤ²`. -/
def IsPeriodic {E : Type*} (φ : (Fin 2 → ℝ) → E) : Prop :=
  ∀ (x : Fin 2 → ℝ) (k : Fin 2 → ℤ), φ (x + fun i => (k i : ℝ)) = φ x

/-- The derivative matrix `D φ (x)` of `φ : ℝ² → ℝ²`: the entries `∂_j φ_i (x)` (rows are the
gradients of the components). An entry is `0` where `φ_i` is not differentiable. -/
def jacobian (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun y => φ y i) x (Pi.single j 1)

/-- The Beurling–Ahlfors transform `𝒮 f = 𝓕⁻¹ (ξ ↦ (ξ̄ / ξ) 𝓕 f (ξ))`, by Mathlib's integral
formulas for `𝓕` and `𝓕⁻¹` (the symbol is `0` at `ξ = 0`). -/
def beurling (f : ℂ → ℂ) : ℂ → ℂ :=
  𝓕⁻ (fun ξ : ℂ => (conj ξ / ξ) • 𝓕 f ξ)

/-- `‖𝒮‖_{L^p (ℂ; ℂ) → L^p (ℂ; ℂ)}`: the supremum, in `[0, ∞]`, of `‖𝒮 f‖_p / ‖f‖_p` over the
Schwartz functions `f` (`0 / 0 = 0`). -/
def beurlingNorm (p : ℝ) : ℝ≥0∞ :=
  ⨆ f : 𝓢(ℂ, ℂ), eLpNorm (beurling f) (ENNReal.ofReal p) volume /
    eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume

/-- The Wirtinger derivative `∂_z g = ½ (∂_x g − i ∂_y g)` of `g : ℂ → ℂ` (`0` where `g` is not
real-differentiable). -/
def dz (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 - Complex.I • fderiv ℝ g z Complex.I)

/-- The Wirtinger derivative `∂_z̄ g = ½ (∂_x g + i ∂_y g)` of `g : ℂ → ℂ` (`0` where `g` is not
real-differentiable). -/
def dzbar (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I)

/-- `f ∈ L^p_loc (Ω)`: `f ∈ L^p (K)` for every compact `K ⊆ Ω`. -/
def MemLpLoc (f : ℂ → ℂ) (p : ℝ≥0∞) (Ω : Set ℂ) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → MemLp f p (volume.restrict K)

open scoped ContDiff in
/-- `g` is the weak derivative of `f` in the direction `v` on `Ω`: `∫ (∂_v φ) f = −∫ φ g` for every
real `φ ∈ C_c^∞ (ℂ)` with `tsupport φ ⊆ Ω`. -/
def HasWeakLineDerivOn (Ω : Set ℂ) (f g : ℂ → ℂ) (v : ℂ) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ z, fderiv ℝ φ z v • f z = -∫ z, φ z • g z

/-- `f ∈ W^{1,2}_loc (Ω)`, with the weak partial derivatives `fx = ∂_x f` and `fy = ∂_y f`: `f`,
`fx` and `fy` are in `L²_loc (Ω)`, and `fx`, `fy` are the weak derivatives of `f` on `Ω` in the
directions `1` and `i`. -/
def MemW12Loc (Ω : Set ℂ) (f fx fy : ℂ → ℂ) : Prop :=
  MemLpLoc f 2 Ω ∧ MemLpLoc fx 2 Ω ∧ MemLpLoc fy 2 Ω ∧
    HasWeakLineDerivOn Ω f fx 1 ∧ HasWeakLineDerivOn Ω f fy Complex.I

/-- The radial stretch `z ↦ |z|^{α − 1} z` (`0` at `z = 0`), `r e^{iθ} ↦ r^α e^{iθ}` for `α > 0`. -/
def radialStretch (α : ℝ) (z : ℂ) : ℂ := (‖z‖ ^ (α - 1) : ℝ) • z

-- END SHARED DEFINITIONS

end Agazzi

open scoped ContDiff

namespace AgazziChallenge

open Agazzi

/-- `det A = |a₊|² − |a₋|²`. -/
theorem det_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 := by
  sorry

/-- The operator norm of `A` on Euclidean `ℝ²` is `|a₊| + |a₋|`. -/
theorem opNorm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ =
      ‖conformalPart A‖ + ‖anticonformalPart A‖ := by
  sorry

/-- The unit square, the torus `Q`, has measure `1`. -/
theorem volume_unitSquare : volume unitSquare = 1 := by
  sorry

/-- `𝒮 ∘ ∂_z̄ = ∂_z` on Schwartz functions (`(eq:BA-definition)`). -/
theorem beurling_dzbar (F : 𝓢(ℂ, ℂ)) : beurling (dzbar F) = dz F := by
  sorry

/-- **Theorem 1.** For all `A ∈ ℝ^{2×2}` and all `φ ∈ C^∞_per (Q; ℝ²)`,
`∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`. -/
theorem theorem1 (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (integrandL (A + jacobian φ x) - integrandL A) := by
  sorry

/-- **Corollary 2**, first assertion. For every `1 < p < ∞`, every `A ∈ ℝ^{2×2}` and every
`φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`. -/
theorem corollary2 {p : ℝ} (hp : 1 < p) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (burkholderB p (A + jacobian φ x) - burkholderB p A) := by
  sorry

/-- **Corollary 2**, second assertion. The norm of the Beurling–Ahlfors transform on
`L^p (ℂ; ℂ)` is `p* − 1`, for `1 < p < ∞`. -/
theorem corollary2_norm {p : ℝ} (hp : 1 < p) : beurlingNorm p = ENNReal.ofReal (pStar p - 1) := by
  sorry

/-- `p* − 1 = (p − 1)⁻¹` for `1 < p ≤ 2`. -/
theorem pStar_sub_one_of_le_two {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    pStar p - 1 = (p - 1)⁻¹ := by
  sorry

/-- `p* − 1 = p − 1` for `p ≥ 2`. -/
theorem pStar_sub_one_of_two_le {p : ℝ} (hp2 : 2 ≤ p) : pStar p - 1 = p - 1 := by
  sorry

/-- **Theorem 1 for Hessians** (TeX line 285): for all `A ∈ ℝ^{2×2}` and all `u ∈ C^∞_per (Q)`,
`∫_Q [L (A + D²u) − L (A)] dx ≥ 0`. -/
theorem theorem1_hessian (A : Matrix (Fin 2) (Fin 2) ℝ) {u : (Fin 2 → ℝ) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hper : IsPeriodic u) :
    0 ≤ ∫ x in unitSquare,
      (integrandL (A + jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x) - integrandL A) := by
  sorry

/-- **Astala's theorem, from Corollary 2** (TeX lines 323–324): for `0 ≤ k < 1`, an open `Ω ⊆ ℂ`
and `f ∈ W^{1,2}_loc (Ω)` with weak partial derivatives `fx`, `fy` and `|∂̄f| ≤ k |∂f|` almost
everywhere in `Ω`, `Df ∈ L^p_loc (Ω)` for every `p ≥ 2` with `k (p − 1) < 1`. -/
theorem astala {Ω : Set ℂ} (hΩ : IsOpen Ω) {k p : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hp : 2 ≤ p)
    (hpk : k * (p - 1) < 1) {f fx fy : ℂ → ℂ} (hf : MemW12Loc Ω f fx fy)
    (hbel : ∀ᵐ z ∂(volume.restrict Ω),
      ‖fx z + Complex.I * fy z‖ ≤ k * ‖fx z - Complex.I * fy z‖) :
    MemLpLoc fx (ENNReal.ofReal p) Ω ∧ MemLpLoc fy (ENNReal.ofReal p) Ω := by
  sorry

/-- **Sharpness of Astala's theorem**: for `K > 1`, `f (z) = z |z|^{1/K − 1}` is a homeomorphism
of `ℂ` in `W^{1,2}_loc (ℂ)` with `|∂̄f| = k |∂f|` off `0`, `k = (K − 1)/(K + 1)`; for
`p = 2K/(K − 1)`, `k (p − 1) = 1` and `∂_x f ∉ L^p` on every disc around `0`. -/
theorem astala_sharp {K : ℝ} (hK : 1 < K) :
    (∃ e : ℂ ≃ₜ ℂ, ⇑e = radialStretch K⁻¹) ∧
    MemW12Loc Set.univ (radialStretch K⁻¹) (fun z => fderiv ℝ (radialStretch K⁻¹) z 1)
      (fun z => fderiv ℝ (radialStretch K⁻¹) z Complex.I) ∧
    (∀ z, z ≠ 0 →
      ‖fderiv ℝ (radialStretch K⁻¹) z 1 + Complex.I * fderiv ℝ (radialStretch K⁻¹) z Complex.I‖ =
        (K - 1) / (K + 1) * ‖fderiv ℝ (radialStretch K⁻¹) z 1 -
          Complex.I * fderiv ℝ (radialStretch K⁻¹) z Complex.I‖) ∧
    (K - 1) / (K + 1) * (2 * K / (K - 1) - 1) = 1 ∧
    ∀ r, 0 < r → ¬ MemLp (fun z => fderiv ℝ (radialStretch K⁻¹) z 1)
      (ENNReal.ofReal (2 * K / (K - 1))) (volume.restrict (Metric.ball 0 r)) := by
  sorry

end AgazziChallenge
