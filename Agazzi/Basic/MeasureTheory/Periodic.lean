/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import CalculusOfVariations.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Periodic properties: almost everywhere on the unit cube and on `ℝ^m`

`ae_of_ae_restrict_unitCube_of_periodic`: a property `P` on `ℝ^m = Fin m → ℝ` that holds almost
everywhere on the open unit cube `(0, 1)^m` (`CalculusOfVariations.unitCube m`) and passes from
`x + k` to `x` for every `k ∈ ℤ^m` (in particular, a `ℤ^m`-periodic property) holds almost
everywhere on `ℝ^m`. It is general and could join the package `CalculusOfVariations`; it is in the
namespace `Agazzi` so as not to clash with it. Used in the proof of Lemma 4 (`Agazzi.lemma4`),
where "almost everywhere on the torus" is "almost everywhere on the unit square", and for the
gradient constraint of `Agazzi.Basic.Analysis.Calculus.GradientConstraint`.
-/

@[expose] public section

open MeasureTheory Filter

namespace Agazzi

variable {m : ℕ}

/-- A property that holds almost everywhere on the unit cube `(0, 1)^m` and passes from `x + k` to
`x` for every `k ∈ ℤ^m` holds almost everywhere on `ℝ^m`: every `x` has a translate `x − ⌊x⌋` in
`[0, 1)^m`, which differs from the open cube by a null set, and the translations by `ℤ^m` preserve
the Lebesgue measure. -/
theorem ae_of_ae_restrict_unitCube_of_periodic {P : (Fin m → ℝ) → Prop}
    (hP : ∀ (x : Fin m → ℝ) (k : Fin m → ℤ), P (x + fun i => (k i : ℝ)) → P x)
    (h : ∀ᵐ x ∂(volume.restrict (CalculusOfVariations.unitCube m)), P x) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), P x := by
  have hIco : (CalculusOfVariations.unitCube m : Set (Fin m → ℝ))
      =ᵐ[(volume : Measure (Fin m → ℝ))] (Set.pi Set.univ fun _ : Fin m => Set.Ico (0 : ℝ) 1) :=
    (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => 1)).trans
      (Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => 1)).symm
  rw [Measure.restrict_congr_set hIco,
    ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ico)] at h
  have hk : ∀ k : Fin m → ℤ, ∀ᵐ x : Fin m → ℝ,
      (x + fun i => (k i : ℝ)) ∈ (Set.pi Set.univ fun _ : Fin m => Set.Ico (0 : ℝ) 1) →
        P (x + fun i => (k i : ℝ)) := fun k =>
    (measurePreserving_add_right volume (fun i => (k i : ℝ))).quasiMeasurePreserving.ae h
  filter_upwards [ae_all_iff.2 hk] with x hx
  refine hP x (fun i => -⌊x i⌋) (hx _ fun i _ => ?_)
  simp only [Int.cast_neg, Set.mem_Ico, Pi.add_apply]
  constructor <;> linarith [Int.floor_le (x i), Int.lt_floor_add_one (x i)]

end Agazzi
