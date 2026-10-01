/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Semicontinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compactness of the admissible class and existence of a maximizer

A sequence of `L`-Lipschitz one-homogeneous functions has a pointwise convergent subsequence
(Arzelà–Ascoli on the closed unit ball, then extension by homogeneity). The class
`AdmissibleClass L D M m` is closed under such limits: Lipschitz bound, sign and homogeneity pass
to pointwise limits, `∫ w² dγ` by dominated convergence, the Dirichlet energy by lower
semicontinuity (`Sperner.dirichletEnergy_le_of_tendsto`), and `γ{w > 0}` by Fatou's lemma. Hence
the Gaussian moment `J_e(w) = ∫ w ⟪x, e⟫ dγ` attains its maximum on a nonempty admissible class.
-/

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal RealInnerProductSpace BoundedContinuousFunction

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

lemma abs_le_mul_norm_of_lipschitz_of_map_zero {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (h0 : w 0 = 0) (x : EuclideanSpace ℝ (Fin n)) :
    |w x| ≤ L * ‖x‖ := by
  have := hw.dist_le_mul x 0
  rwa [Real.dist_eq, h0, sub_zero, dist_zero_right] at this

/-- **Sequential compactness**: a sequence of `L`-Lipschitz one-homogeneous functions has a
pointwise convergent subsequence. -/
theorem exists_subseq_tendsto_of_lipschitzWith {L : ℝ≥0} {w : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : ∀ k, LipschitzWith L (w k)) (hhom : ∀ k, IsOneHomogeneous (w k)) :
    ∃ (φ : ℕ → ℕ) (w₀ : EuclideanSpace ℝ (Fin n) → ℝ), StrictMono φ ∧
      ∀ x, Tendsto (fun k => w (φ k) x) atTop (𝓝 (w₀ x)) := by
  let B := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  let u : ℕ → (↥B →ᵇ ℝ) := fun k => BoundedContinuousFunction.mkOfCompact
    ⟨fun y => w k y, (hw k).continuous.comp continuous_subtype_val⟩
  have hu : ∀ k (y : B), u k y = w k y := fun _ _ => rfl
  have hLip : ∀ k, LipschitzWith L (fun y : B => w k y) := fun k => by
    have h := (hw k).comp (LipschitzWith.subtype_val B)
    rw [mul_one] at h
    exact h
  have hA : IsCompact (closure (range u)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℝ) L)
      (isCompact_closedBall 0 L) (range u) ?_ ?_
    · rintro f y ⟨k, rfl⟩
      rw [mem_closedBall, dist_zero_right, hu, Real.norm_eq_abs]
      refine (abs_le_mul_norm_of_lipschitz_of_map_zero (hw k) (hhom k).map_zero y).trans ?_
      have : ‖(y : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
        have hy := mem_closedBall.1 y.2
        rwa [dist_zero_right] at hy
      nlinarith [L.coe_nonneg]
    · refine (LipschitzWith.uniformEquicontinuous _ L fun f => ?_).equicontinuous
      obtain ⟨k, hk⟩ := f.2
      have : ((f : ↥B →ᵇ ℝ) : ↥B → ℝ) = fun y : ↥B => w k y := by rw [← hk]; rfl
      rw [this]; exact hLip k
  obtain ⟨g, -, φ, hφ, hlim⟩ := hA.tendsto_subseq fun k => subset_closure (mem_range_self k)
  have hball : ∀ y : B, Tendsto (fun k => w (φ k) y) atTop (𝓝 (g y)) := fun y =>
    ((continuous_eval_const y).tendsto g).comp hlim
  have hmem : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖⁻¹ • x ∈ B := fun x => by
    simp only [B, mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  refine ⟨φ, fun x => ‖x‖ * g ⟨‖x‖⁻¹ • x, hmem x⟩, hφ, fun x => ?_⟩
  have hk : ∀ k, w (φ k) x = ‖x‖ * w (φ k) (‖x‖⁻¹ • x) := fun k => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [(hhom _).map_zero]
    · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      rw [← hhom (φ k) _ _ hpos, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  simp_rw [hk]
  exact (hball ⟨_, hmem x⟩).const_mul _

/-- **Existence of a maximizer** of the Gaussian moment `J_e` on a nonempty admissible class. -/
theorem exists_isMaxOn_gaussMoment {L : ℝ≥0} {D M : ℝ} {m : ℝ≥0∞}
    (e : EuclideanSpace ℝ (Fin n)) {w₀ : EuclideanSpace ℝ (Fin n) → ℝ}
    (h₀ : AdmissibleClass L D M m w₀) :
    ∃ w, AdmissibleClass L D M m w ∧
      ∀ w', AdmissibleClass L D M m w' → gaussMoment e w' ≤ gaussMoment e w := by
  set S := {w : EuclideanSpace ℝ (Fin n) → ℝ | AdmissibleClass L D M m w}
  have i2 := integrable_norm_pow_gaussMeasure (n := n) 2
  set K := (L : ℝ) * ‖e‖ * ∫ x, ‖x‖ ^ 2 ∂gaussMeasure n
  -- pointwise bounds on the class
  have hbd : ∀ w ∈ S, ∀ x, |w x| ≤ L * ‖x‖ := fun w hw x =>
    abs_le_mul_norm_of_lipschitz_of_map_zero hw.1 hw.2.2.1.map_zero x
  have hJint : ∀ w ∈ S, Integrable (fun x => w x * ⟪x, e⟫) (gaussMeasure n) := fun w hw =>
    (i2.const_mul (L * ‖e‖)).mono'
      ((hw.1.continuous.mul (continuous_id.inner continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |w x| * |⟪x, e⟫| ≤ (L * ‖x‖) * (‖x‖ * ‖e‖) :=
              mul_le_mul (hbd w hw x) (abs_real_inner_le_norm x e) (abs_nonneg _) (by positivity)
          _ = L * ‖e‖ * ‖x‖ ^ 2 := by ring)
  have hJbd : ∀ w ∈ S, gaussMoment e w ≤ K := fun w hw => by
    refine (integral_mono (hJint w hw) (i2.const_mul ((L : ℝ) * ‖e‖)) fun x => ?_).trans_eq
      (integral_const_mul _ _)
    calc w x * ⟪x, e⟫ ≤ |w x * ⟪x, e⟫| := le_abs_self _
      _ = |w x| * |⟪x, e⟫| := abs_mul _ _
      _ ≤ (L * ‖x‖) * (‖x‖ * ‖e‖) :=
          mul_le_mul (hbd w hw x) (abs_real_inner_le_norm x e) (abs_nonneg _) (by positivity)
      _ = L * ‖e‖ * ‖x‖ ^ 2 := by ring
  have hne : (gaussMoment e '' S).Nonempty := ⟨_, w₀, h₀, rfl⟩
  have hbdd : BddAbove (gaussMoment e '' S) := ⟨K, by rintro _ ⟨w, hw, rfl⟩; exact hJbd w hw⟩
  set s := sSup (gaussMoment e '' S)
  -- a maximizing sequence
  have hseq : ∀ k : ℕ, ∃ w ∈ S, s - 1 / ((k : ℝ) + 1) < gaussMoment e w := fun k => by
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne
      (sub_lt_self s (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    exact ⟨w, hw, hlt⟩
  choose wk hwkS hwk using hseq
  obtain ⟨φ, w, hφ, hconv⟩ := exists_subseq_tendsto_of_lipschitzWith (fun k => (hwkS k).1)
    (fun k => (hwkS k).2.2.1)
  -- properties of the limit
  have hwL : LipschitzWith L w := LipschitzWith.of_dist_le_mul fun x y =>
    le_of_tendsto' ((hconv x).dist (hconv y)) fun k => (hwkS (φ k)).1.dist_le_mul x y
  have hwnn : ∀ x, 0 ≤ w x := fun x =>
    ge_of_tendsto' (hconv x) fun k => (hwkS (φ k)).2.1 x
  have hwhom : IsOneHomogeneous w := fun x t ht =>
    tendsto_nhds_unique (hconv (t • x))
      (((hconv x).const_mul t).congr fun k => ((hwkS (φ k)).2.2.1 x t ht).symm)
  have h0 : ∀ k, wk (φ k) 0 = 0 := fun k => (hwkS (φ k)).2.2.1.map_zero
  have hcont : ∀ k, Continuous (wk (φ k)) := fun k => (hwkS (φ k)).1.continuous
  have hL2 : gaussL2 w = M := by
    have : Tendsto (fun k => gaussL2 (wk (φ k))) atTop (𝓝 (gaussL2 w)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => (L : ℝ) ^ 2 * ‖x‖ ^ 2)
        (fun k => ((hcont k).pow 2).aestronglyMeasurable) (i2.const_mul _)
        (fun k => Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x => (hconv x).pow 2)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      change |wk (φ k) x| ^ 2 ≤ (L : ℝ) ^ 2 * ‖x‖ ^ 2
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbd _ (hwkS (φ k)) x) 2
    exact tendsto_nhds_unique this (tendsto_const_nhds.congr fun k => ((hwkS (φ k)).2.2.2.1).symm)
  have hD : dirichletEnergy w ≤ D :=
    dirichletEnergy_le_of_tendsto (fun k => (hwkS (φ k)).1) hwL h0 hconv
      fun k => (hwkS (φ k)).2.2.2.2.1
  have hm : gaussMeasure n {x | 0 < w x} ≤ m := by
    have hmeas : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), Continuous f →
        Measurable fun x => {x | 0 < f x}.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) x :=
      fun f hf => measurable_const.indicator (measurableSet_lt measurable_const hf.measurable)
    rw [← lintegral_indicator_one (measurableSet_lt measurable_const hwL.continuous.measurable)]
    calc ∫⁻ x, {x | 0 < w x}.indicator 1 x ∂gaussMeasure n
        ≤ ∫⁻ x, liminf (fun k => {x | 0 < wk (φ k) x}.indicator
            (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) x) atTop ∂gaussMeasure n := by
          refine lintegral_mono fun x => ?_
          by_cases hx : 0 < w x
          · rw [indicator_of_mem (show x ∈ {x | 0 < w x} from hx)]
            refine le_liminf_of_le (by isBoundedDefault) ?_
            filter_upwards [(hconv x).eventually (lt_mem_nhds hx)] with k hk
            rw [indicator_of_mem (show x ∈ {x | 0 < wk (φ k) x} from hk)]
          · rw [indicator_of_notMem (show x ∉ {x | 0 < w x} from hx)]
            exact bot_le
      _ ≤ liminf (fun k => ∫⁻ x, {x | 0 < wk (φ k) x}.indicator 1 x ∂gaussMeasure n) atTop :=
          lintegral_liminf_le fun k => hmeas _ (hcont k)
      _ ≤ m := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
          rw [lintegral_indicator_one (measurableSet_lt measurable_const (hcont k).measurable)]
          exact (hwkS (φ k)).2.2.2.2.2
  have hwS : AdmissibleClass L D M m w := ⟨hwL, hwnn, hwhom, hL2, hD, hm⟩
  -- the limit attains the supremum
  have hJlim : Tendsto (fun k => gaussMoment e (wk (φ k))) atTop (𝓝 (gaussMoment e w)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => L * ‖e‖ * ‖x‖ ^ 2)
      (fun k => ((hcont k).mul (continuous_id.inner continuous_const)).aestronglyMeasurable)
      (i2.const_mul _) (fun k => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => (hconv x).mul_const _)
    rw [Real.norm_eq_abs, abs_mul]
    calc |wk (φ k) x| * |⟪x, e⟫| ≤ (L * ‖x‖) * (‖x‖ * ‖e‖) :=
          mul_le_mul (hbd _ (hwkS (φ k)) x) (abs_real_inner_le_norm x e) (abs_nonneg _)
            (by positivity)
      _ = L * ‖e‖ * ‖x‖ ^ 2 := by ring
  have hJs : Tendsto (fun k => gaussMoment e (wk (φ k))) atTop (𝓝 s) := by
    have hlow : Tendsto (fun k => s - 1 / ((φ k : ℝ) + 1)) atTop (𝓝 s) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_sub s
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun k => (hwk (φ k)).le) fun k => le_csSup hbdd ⟨_, hwkS (φ k), rfl⟩
  have hJw : gaussMoment e w = s := tendsto_nhds_unique hJlim hJs
  exact ⟨w, hwS, fun w' hw' => hJw ▸ le_csSup hbdd ⟨w', hw', rfl⟩⟩

end Sperner
