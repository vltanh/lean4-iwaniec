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

`lem4_ae_of_ae_unitCube`: a `ℤ^m`-periodic property that holds almost everywhere on the open unit
cube `(0, 1)^m` holds almost everywhere on `ℝ^m`. The translates `k + (0, 1)^m`, `k ∈ ℤ^m`, cover
`ℝ^m` up to the null set of points with an integer coordinate. Used in the proof of Lemma 4
(`Agazzi.lemma4`), where "almost everywhere on the torus" is "almost everywhere on the unit
square".
-/

@[expose] public section

open MeasureTheory Filter

namespace Agazzi

variable {m : ℕ}

/-- A `ℤ^m`-periodic property that holds almost everywhere on the open unit cube holds almost
everywhere on `ℝ^m`. -/
theorem lem4_ae_of_ae_unitCube {P : (Fin m → ℝ) → Prop}
    (hP : ∀ (x : Fin m → ℝ) (k : Fin m → ℤ), P (x + fun i => (k i : ℝ)) ↔ P x)
    (h : ∀ᵐ x ∂(volume.restrict (CalculusOfVariations.unitCube m)), P x) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), P x := by
  have hmeas : MeasurableSet (CalculusOfVariations.unitCube m) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  rw [ae_restrict_iff' hmeas] at h
  have h1 : ∀ k : Fin m → ℤ, ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      (x - fun i => (k i : ℝ)) ∈ CalculusOfVariations.unitCube m → P x := by
    intro k
    filter_upwards [QuasiMeasurePreserving.ae
      (measurePreserving_sub_right volume (fun i => (k i : ℝ))).quasiMeasurePreserving h]
      with x hx hmem
    have := hx hmem
    rwa [← hP _ k, sub_add_cancel] at this
  have h2 : ∀ i : Fin m, ∀ n : ℤ, ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), x i ≠ (n : ℝ) := by
    intro i n
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [volume_pi]
    exact Measure.pi_hyperplane (α := fun _ : Fin m => ℝ) (fun _ => volume) i (n : ℝ)
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 fun i => ae_all_iff.2 (h2 i)] with x hx hx'
  refine hx (fun i => ⌊x i⌋) fun i _ => ?_
  simp only [Pi.sub_apply]
  refine ⟨sub_pos.2 (lt_of_le_of_ne (Int.floor_le (x i)) fun h => hx' i ⌊x i⌋ h.symm), ?_⟩
  linarith [Int.lt_floor_add_one (x i)]

end Agazzi
