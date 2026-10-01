/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Gaussian measure of cones

For a measurable cone `s ⊆ ℝⁿ`, the Gaussian measure and the Lebesgue measure of `s ∩ B₁`
are proportional with a universal constant:
`γ(s) · |B₁| = γ(ℝⁿ) · |s ∩ B₁|`. (Layer-cake: `γ(s) = ∫₀¹ |s ∩ B_{r(t)}| dt` with
`r(t) = √(-2 log t)`, and `|s ∩ B_r| = rⁿ |s ∩ B₁|` by scaling.)
-/

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- The trace of a cone on the ball of radius `r > 0` is the `r`-dilate of its trace on the unit
ball, so its volume scales like `rⁿ`. -/
lemma volume_inter_ball_of_isCone {s : Set (EuclideanSpace ℝ (Fin n))} (hcone : IsCone s)
    {r : ℝ} (hr : 0 < r) :
    volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) r) =
      ENNReal.ofReal (r ^ n) * volume (s ∩ ball 0 1) := by
  have hs : r • s = s := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
    constructor
    · intro h
      have := hcone _ h r hr
      rwa [smul_inv_smul₀ hr.ne'] at this
    · intro h
      exact hcone x h r⁻¹ (inv_pos.2 hr)
  have hball : r • ball (0 : EuclideanSpace ℝ (Fin n)) 1 = ball 0 r := by
    rw [_root_.smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hset : s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) r = r • (s ∩ ball 0 1) := by
    rw [Set.smul_set_inter₀ hr.ne', hs, hball]
  rw [hset, Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hr n)]

/-- The superlevel sets of the Gaussian weight are empty or balls centred at `0`; hence the
volume of their trace on a cone is a fixed multiple of the volume of its trace on `B₁`. -/
lemma exists_volume_inter_setOf_lt_gaussWeight {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ≥0∞, ∀ s : Set (EuclideanSpace ℝ (Fin n)), IsCone s →
      volume (s ∩ {x | t < gaussWeight x}) = c * volume (s ∩ ball 0 1) := by
  rcases le_or_gt 1 t with h1 | h1
  · refine ⟨0, fun s _ => ?_⟩
    have : {x : EuclideanSpace ℝ (Fin n) | t < gaussWeight x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      refine le_trans ?_ h1
      unfold gaussWeight
      rw [Real.exp_le_one_iff]
      have := sq_nonneg ‖x‖
      linarith
    simp [this]
  · have hlog : Real.log t < 0 := Real.log_neg ht h1
    set r := Real.sqrt (-2 * Real.log t) with hrdef
    have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
    have hset : {x : EuclideanSpace ℝ (Fin n) | t < gaussWeight x} = ball 0 r := by
      ext x
      simp only [mem_ofPred_eq, mem_ball, dist_zero_right, gaussWeight]
      rw [← Real.log_lt_iff_lt_exp ht, hrdef, Real.lt_sqrt (norm_nonneg _)]
      constructor <;> intro h <;> linarith
    exact ⟨ENNReal.ofReal (r ^ n), fun s hs => by rw [hset, volume_inter_ball_of_isCone hs hr]⟩

/-- The Gaussian measure of a cone is proportional to the volume of its trace on the unit
ball, with the same constant as for the whole space. -/
theorem gaussMeasure_mul_volume_ball {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hcone : IsCone s) :
    gaussMeasure n s * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) =
      gaussMeasure n univ * volume (s ∩ ball 0 1) := by
  choose! c hc using fun t (ht : 0 < t) => exists_volume_inter_setOf_lt_gaussWeight (n := n) ht
  have hγ : ∀ s' : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s' → IsCone s' →
      gaussMeasure n s' = (∫⁻ t in Ioi 0, c t) * volume (s' ∩ ball 0 1) := by
    intro s' hs' hcone'
    have hfin : volume (s' ∩ ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
    rw [gaussMeasure, withDensity_apply _ hs',
      lintegral_eq_lintegral_meas_lt _ (ae_of_all _ fun x => (gaussWeight_pos x).le)
        continuous_gaussWeight.aemeasurable, ← lintegral_mul_const' _ _ hfin]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Measure.restrict_apply
        (measurableSet_lt measurable_const continuous_gaussWeight.measurable), inter_comm,
      hc t ht s' hcone']
  have huniv : IsCone (univ : Set (EuclideanSpace ℝ (Fin n))) := fun _ _ _ _ => mem_univ _
  rw [hγ s hs hcone, hγ univ MeasurableSet.univ huniv, univ_inter]
  ring

end Sperner
