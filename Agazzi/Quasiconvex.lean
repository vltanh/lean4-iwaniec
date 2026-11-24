/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Agazzi.Corollary2.Quasiconvexity
public import CalculusOfVariations.Quasiconvex.Periodic

/-!
# Theorem 1 and Corollary 2 as quasiconvexity in the sense of `CalculusOfVariations`

The paper's Theorem 1 and Corollary 2 test quasiconvexity with `C^∞` periodic maps on the torus.
The package `CalculusOfVariations` defines quasiconvexity (`CalculusOfVariations.Quasiconvex`) with
Lipschitz test maps vanishing outside the unit cube. The two notions agree for Borel, locally
bounded integrands (`CalculusOfVariations.quasiconvexAtOn_iff_periodic`, Dacorogna, Prop. 5.13), and
the paper's proofs give the periodic inequalities for Lipschitz periodic maps
(`theorem1_lipschitz`, `corollary2_lipschitz`). Hence:

* `quasiconvex_integrandL`: `L` is quasiconvex;
* `quasiconvex_burkholderB`: `B_p` is quasiconvex for every `1 < p < ∞`;
* `quasiconvex_burkholder`: for `1 < p < 2`, the Burkholder function
  `(|a₊| − (p − 1)|a₋|)(|a₊| + |a₋|)^{p−1}` (a positive multiple of `B_p`) is quasiconvex. This is
  the form in which lean4-morrey (`Isotropic.burkholder p`) uses it.
-/

@[expose] public section

noncomputable section

namespace Agazzi

/-- `L` is quasiconvex, in the sense of `CalculusOfVariations` (Lipschitz test maps vanishing
outside the unit cube). -/
theorem quasiconvex_integrandL : CalculusOfVariations.Quasiconvex integrandL := by
  sorry

/-- `B_p` is quasiconvex for every `1 < p < ∞`, in the sense of `CalculusOfVariations`. -/
theorem quasiconvex_burkholderB {p : ℝ} (hp : 1 < p) :
    CalculusOfVariations.Quasiconvex (burkholderB p) := by
  sorry

/-- For `1 < p < 2`, the Burkholder function `(|a₊| − (p − 1)|a₋|)(|a₊| + |a₋|)^{p−1}` is quasiconvex,
in the sense of `CalculusOfVariations`. -/
theorem quasiconvex_burkholder (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    CalculusOfVariations.Quasiconvex fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
        (‖conformalPart A‖ - (p - 1) * ‖anticonformalPart A‖) := by
  sorry

end Agazzi
