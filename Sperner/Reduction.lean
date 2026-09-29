/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Reduction to a single positivity component

Let `u ≥ 0` be Lipschitz and one-homogeneous, and let `U` be the connected component of
`{u > 0}` through `y₀`. Then `U` is an open cone, and the truncation `v = 𝟙_U u` is again
nonnegative, one-homogeneous and Lipschitz (with the same constant), with `{v > 0} = U`; if `u`
is harmonic on `U` then `v` is harmonic on its positivity set.
-/

open MeasureTheory Metric Set InnerProductSpace Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {y₀ : EuclideanSpace ℝ (Fin n)}

lemma isOpen_connectedComponentIn_pos (hu : Continuous u) :
    IsOpen (connectedComponentIn {y | 0 < u y} y₀) :=
  (isOpen_lt continuous_const hu).connectedComponentIn

lemma isCone_connectedComponentIn_pos (hhom : IsOneHomogeneous u) :
    IsCone (connectedComponentIn {y | 0 < u y} y₀) := by
  intro x hx t ht
  have hxpos : 0 < u x := (connectedComponentIn_subset {y | 0 < u y} y₀ hx : _)
  set T := (fun s : ℝ => s • x) '' Ioi 0 with hT
  have hTconn : IsPreconnected T :=
    isPreconnected_Ioi.image _ (by fun_prop : Continuous fun s : ℝ => s • x).continuousOn
  have hxT : x ∈ T := ⟨1, by norm_num, one_smul _ _⟩
  have hTsub : T ⊆ {y | 0 < u y} := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [mem_setOf_eq, hhom x s hs]
    exact mul_pos hs hxpos
  have := hTconn.subset_connectedComponentIn hxT hTsub
  rw [← connectedComponentIn_eq hx] at this
  exact this ⟨t, ht, rfl⟩

/-- The truncation of `u` to the component `U` is Lipschitz with the same constant. -/
lemma lipschitzWith_indicator_connectedComponentIn {L : ℝ≥0} (hu : LipschitzWith L u)
    (hnn : ∀ y, 0 ≤ u y) :
    LipschitzWith L ((connectedComponentIn {y | 0 < u y} y₀).indicator u) := by
  set U := connectedComponentIn {y | 0 < u y} y₀
  -- If `x ∈ U` and `y ∉ U`, the segment `[x, y]` leaves `{u > 0}`.
  have key : ∀ x ∈ U, ∀ y ∉ U, u x ≤ L * dist x y := by
    intro x hx y hy
    have hseg : ¬ segment ℝ x y ⊆ {y | 0 < u y} := by
      intro hsub
      have := (convex_segment x y).isPreconnected.subset_connectedComponentIn
        (left_mem_segment ℝ x y) hsub
      rw [← connectedComponentIn_eq hx] at this
      exact hy (this (right_mem_segment ℝ x y))
    obtain ⟨z, hz, hz0⟩ := not_subset.1 hseg
    have hz0 : u z = 0 := le_antisymm (not_lt.1 hz0) (hnn z)
    have hdist : dist x z ≤ dist x y := by
      simpa [mem_closedBall, dist_comm] using segment_subset_closedBall_left x y hz
    calc u x = u x - u z := by rw [hz0, sub_zero]
      _ ≤ dist (u x) (u z) := by rw [Real.dist_eq]; exact le_abs_self _
      _ ≤ L * dist x z := hu.dist_le_mul x z
      _ ≤ L * dist x y := by gcongr
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
  · simpa [indicator_of_mem hx, indicator_of_mem hy] using hu.dist_le_mul x y
  · rw [indicator_of_mem hx, indicator_of_notMem hy, Real.dist_eq, sub_zero,
      abs_of_nonneg (hnn x)]
    exact key x hx y hy
  · rw [indicator_of_notMem hx, indicator_of_mem hy, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg (hnn y), dist_comm]
    exact key y hy x hx
  · simp only [indicator_of_notMem hx, indicator_of_notMem hy, dist_self]
    positivity

lemma setOf_indicator_pos :
    {x | 0 < (connectedComponentIn {y | 0 < u y} y₀).indicator u x} =
      connectedComponentIn {y | 0 < u y} y₀ := by
  ext x
  by_cases hx : x ∈ connectedComponentIn {y | 0 < u y} y₀
  · simp only [mem_setOf_eq, indicator_of_mem hx, hx, iff_true]
    exact (connectedComponentIn_subset {y | 0 < u y} y₀ hx : _)
  · simp [hx]

lemma isOneHomogeneous_indicator (hhom : IsOneHomogeneous u) :
    IsOneHomogeneous ((connectedComponentIn {y | 0 < u y} y₀).indicator u) := by
  have hcone := isCone_connectedComponentIn_pos (y₀ := y₀) hhom
  intro x t ht
  by_cases hx : x ∈ connectedComponentIn {y | 0 < u y} y₀
  · rw [indicator_of_mem hx, indicator_of_mem (hcone x hx t ht), hhom x t ht]
  · have htx : t • x ∉ connectedComponentIn {y | 0 < u y} y₀ := by
      intro h
      apply hx
      have := hcone _ h t⁻¹ (inv_pos.2 ht)
      rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
    rw [indicator_of_notMem hx, indicator_of_notMem htx, mul_zero]

lemma harmonicAt_indicator (hu : Continuous u) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ connectedComponentIn {y | 0 < u y} y₀) (hharm : HarmonicAt u x) :
    HarmonicAt ((connectedComponentIn {y | 0 < u y} y₀).indicator u) x := by
  refine (harmonicAt_congr_nhds ?_).2 hharm
  filter_upwards [(isOpen_connectedComponentIn_pos hu).mem_nhds hx] with y hy
  rw [indicator_of_mem hy]

end Sperner
