/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.Harmonic
public import InnerVariational.Basic.SphereIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Kernel.IBP

/-!
# The energy identity on spheres, (3.8)

Identity (3.8) of Kriventsov–Weiss (in the proof of Proposition 3.4; full reference below): for a
nonnegative Lipschitz `u` harmonic on `{u > 0}` and a.e. `s`,
`∫_{B_s(x)} |∇u|² = ∫_{∂B_s(x)} u ∇u · ν`, with `ν = (y − x) / |y − x|`.

## Main definitions

* `Kernel.radialCutoff x s δ`: the piecewise linear radial cutoff, `1` on `B̄_s(x)`, `0` off
  `B_{s+δ}(x)`, and linear in `|y − x|` in between. The paper uses it with `δ = 1/k`
  (proof of Proposition 3.4).

## Main results

* `Kernel.hasFDerivAt_radialCutoff`: on the open annulus, `∇η = −δ⁻¹ (y − x) / |y − x|`.
* `Kernel.fderiv_radialCutoff_of_lt`, `Kernel.fderiv_radialCutoff_of_gt`: `∇η = 0` inside and
  outside.
* `IsLipHarmonicPos.energy_eq_sphere_ae`: identity (3.8) for a.e. `s ∈ (0, R)` with
  `B_R(x) ⊆ U`.

## Proof

We follow the paper's approach for the Rellich–Pohozaev identity (3.7), which is simpler than its
route to (3.8). The energy identity with a cutoff (`IsLipHarmonicPos.integral_norm_gradient_sq_mul`)
with `η_k = radialCutoff x s (1/k)` gives
`∫ |∇u|² η_k = k ∫_{B_{s+1/k} ∖ B_s} u ∇u · ν`. The left side tends to `∫_{B_s} |∇u|²` by
dominated convergence. The right side tends to the sphere integral at every Lebesgue point of
the sphere integral (`ae_tendsto_average_annulus`). The paper's own route to (3.8) uses the
smoothness of `∂{u > ε}` for a.e. `ε`. We avoid it.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Kernel

/-! ### The radial cutoff -/

/-- The radial cutoff `η(y) = min(1, max(0, (s + δ − |y − x|) / δ))`. It equals `1` on
`B̄_s(x)`, `0` off `B_{s+δ}(x)`, and is linear in `|y − x|` in between (as in the proof of
Proposition 3.4). -/
def radialCutoff (x : Rn n) (s δ : ℝ) (y : Rn n) : ℝ :=
  min 1 (max 0 ((s + δ - ‖y - x‖) / δ))

variable {x : Rn n} {s δ : ℝ}

theorem radialCutoff_nonneg (y : Rn n) : 0 ≤ radialCutoff x s δ y :=
  le_min zero_le_one (le_max_left _ _)

theorem radialCutoff_le_one (y : Rn n) : radialCutoff x s δ y ≤ 1 := min_le_left _ _

theorem abs_radialCutoff_le_one (y : Rn n) : |radialCutoff x s δ y| ≤ 1 := by
  rw [abs_of_nonneg (radialCutoff_nonneg y)]; exact radialCutoff_le_one y

theorem radialCutoff_eq_one (hδ : 0 < δ) {y : Rn n} (hy : ‖y - x‖ ≤ s) :
    radialCutoff x s δ y = 1 := by
  have : 1 ≤ (s + δ - ‖y - x‖) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [radialCutoff, max_eq_right (zero_le_one.trans this), min_eq_left this]

theorem radialCutoff_eq_zero (hδ : 0 < δ) {y : Rn n} (hy : s + δ ≤ ‖y - x‖) :
    radialCutoff x s δ y = 0 := by
  have : (s + δ - ‖y - x‖) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [radialCutoff, max_eq_left this, min_eq_right zero_le_one]

theorem radialCutoff_eq_of_mem (hδ : 0 < δ) {y : Rn n} (h1 : s ≤ ‖y - x‖)
    (h2 : ‖y - x‖ ≤ s + δ) : radialCutoff x s δ y = (s + δ - ‖y - x‖) / δ := by
  have a : 0 ≤ (s + δ - ‖y - x‖) / δ := div_nonneg (by linarith) hδ.le
  have b : (s + δ - ‖y - x‖) / δ ≤ 1 := by rw [div_le_iff₀ hδ]; linarith
  rw [radialCutoff, max_eq_right a, min_eq_right b]

theorem lipschitzWith_radialCutoff (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal δ⁻¹) (radialCutoff x s δ) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, radialCutoff, radialCutoff, Real.coe_toNNReal _ (inv_nonneg.2 hδ.le)]
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), ← sub_div, abs_div, abs_of_pos hδ,
    div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hδ.le)
  have := abs_norm_sub_norm_le (b - x) (a - x)
  rw [sub_sub_sub_cancel_right] at this
  calc |s + δ - ‖a - x‖ - (s + δ - ‖b - x‖)| = |‖b - x‖ - ‖a - x‖| := by congr 1; ring
    _ ≤ ‖b - a‖ := this
    _ = dist a b := by rw [dist_comm, dist_eq_norm]

theorem continuous_radialCutoff : Continuous (radialCutoff x s δ) := by
  unfold radialCutoff
  fun_prop

theorem tsupport_radialCutoff_subset (hδ : 0 < δ) :
    tsupport (radialCutoff x s δ) ⊆ closedBall x (s + δ) := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_eq_norm]
  by_contra h
  exact hy (radialCutoff_eq_zero hδ (not_le.1 h).le)

theorem hasCompactSupport_radialCutoff (hδ : 0 < δ) : HasCompactSupport (radialCutoff x s δ) :=
  (isCompact_closedBall x (s + δ)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_radialCutoff_subset hδ)

/-- The derivative of `y ↦ |y − x|` away from `x`. -/
theorem hasFDerivAt_norm_sub {y : Rn n} (hy : y ≠ x) :
    HasFDerivAt (fun z => ‖z - x‖) (‖y - x‖⁻¹ • innerSL ℝ (y - x)) y := by
  have h0 : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hy)
  have h1 := ((hasFDerivAt_id y).sub_const x).norm_sq
  have h2 := h1.sqrt (by simpa using h0)
  have e : (fun z => √(‖id z - x‖ ^ 2)) = fun z => ‖z - x‖ := by
    ext z; simp [Real.sqrt_sq (norm_nonneg _)]
  rw [e] at h2
  convert h2 using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, id, ContinuousLinearMap.id_apply,
    Real.sqrt_sq (norm_nonneg _)]
  field_simp
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- On the open annulus `s < |y − x| < s + δ`, `Dη(y) = −δ⁻¹ |y − x|⁻¹ ⟪y − x, ·⟫`. -/
theorem hasFDerivAt_radialCutoff (hδ : 0 < δ) (hs0 : 0 ≤ s) {y : Rn n} (h1 : s < ‖y - x‖)
    (h2 : ‖y - x‖ < s + δ) :
    HasFDerivAt (radialCutoff x s δ) (-(δ⁻¹ * ‖y - x‖⁻¹) • innerSL ℝ (y - x)) y := by
  have hy : y ≠ x := by
    intro h; rw [h, sub_self, norm_zero] at h1
    linarith
  have hN := hasFDerivAt_norm_sub hy
  have hg : HasFDerivAt (fun z => (s + δ - ‖z - x‖) / δ)
      (-(δ⁻¹ * ‖y - x‖⁻¹) • innerSL ℝ (y - x)) y := by
    have := HasFDerivAt.const_mul (HasFDerivAt.const_sub hN (s + δ)) δ⁻¹
    have e : (fun z => (s + δ - ‖z - x‖) / δ) = fun z => δ⁻¹ * (s + δ - ‖z - x‖) := by
      ext z; rw [div_eq_inv_mul]
    rw [e]
    convert this using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
      ContinuousLinearMap.neg_apply]
    ring
  refine hg.congr_of_eventuallyEq ?_
  have hU : IsOpen {z : Rn n | s < ‖z - x‖ ∧ ‖z - x‖ < s + δ} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  filter_upwards [hU.mem_nhds ⟨h1, h2⟩] with z hz
  exact radialCutoff_eq_of_mem hδ hz.1.le hz.2.le

theorem radialCutoff_eventuallyEq_one (hδ : 0 < δ) {y : Rn n} (hy : ‖y - x‖ < s) :
    radialCutoff x s δ =ᶠ[𝓝 y] fun _ => 1 := by
  have hU : IsOpen {z : Rn n | ‖z - x‖ < s} :=
    isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  filter_upwards [hU.mem_nhds hy] with z hz
  exact radialCutoff_eq_one hδ (le_of_lt hz)

theorem radialCutoff_eventuallyEq_zero (hδ : 0 < δ) {y : Rn n} (hy : s + δ < ‖y - x‖) :
    radialCutoff x s δ =ᶠ[𝓝 y] fun _ => 0 := by
  have hU : IsOpen {z : Rn n | s + δ < ‖z - x‖} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  filter_upwards [hU.mem_nhds hy] with z hz
  exact radialCutoff_eq_zero hδ (le_of_lt hz)

theorem fderiv_radialCutoff_of_lt (hδ : 0 < δ) {y : Rn n} (hy : ‖y - x‖ < s) :
    fderiv ℝ (radialCutoff x s δ) y = 0 := by
  rw [(radialCutoff_eventuallyEq_one hδ hy).fderiv_eq, fderiv_const_apply]

theorem fderiv_radialCutoff_of_gt (hδ : 0 < δ) {y : Rn n} (hy : s + δ < ‖y - x‖) :
    fderiv ℝ (radialCutoff x s δ) y = 0 := by
  rw [(radialCutoff_eventuallyEq_zero hδ hy).fderiv_eq, fderiv_const_apply]

/-- Off the two spheres, `η` is differentiable, with derivative
`−δ⁻¹ |y − x|⁻¹ ⟪y − x, ·⟫` on the annulus `B_{s+δ} ∖ B_s` and `0` elsewhere. -/
theorem hasFDerivAt_radialCutoff_indicator (hδ : 0 < δ) (hs0 : 0 ≤ s) {y : Rn n}
    (hs : ‖y - x‖ ≠ s)
    (hsδ : ‖y - x‖ ≠ s + δ) :
    HasFDerivAt (radialCutoff x s δ) ((ball x (s + δ) \ ball x s).indicator
      (fun z => -(δ⁻¹ * ‖z - x‖⁻¹) • innerSL ℝ (z - x)) y) y := by
  rcases lt_or_gt_of_ne hs with h1 | h1
  · have : y ∉ ball x (s + δ) \ ball x s := fun h => h.2 (by rw [mem_ball, dist_eq_norm]; exact h1)
    rw [indicator_of_notMem this]
    exact (hasFDerivAt_const 1 y).congr_of_eventuallyEq (radialCutoff_eventuallyEq_one hδ h1)
  rcases lt_or_gt_of_ne hsδ with h2 | h2
  · have hmem : y ∈ ball x (s + δ) \ ball x s := by
      refine ⟨by rw [mem_ball, dist_eq_norm]; exact h2, ?_⟩
      rw [mem_ball, dist_eq_norm, not_lt]; exact h1.le
    rw [indicator_of_mem hmem]
    exact hasFDerivAt_radialCutoff hδ hs0 h1 h2
  · have : y ∉ ball x (s + δ) \ ball x s := fun h => by
      have := h.1; rw [mem_ball, dist_eq_norm] at this; linarith
    rw [indicator_of_notMem this]
    exact (hasFDerivAt_const 0 y).congr_of_eventuallyEq (radialCutoff_eventuallyEq_zero hδ h2)

/-- For `y` off the two spheres, `⟪v, ∇η(y)⟫ = −δ⁻¹ 1_{B_{s+δ} ∖ B_s}(y) ⟪v, ν(y)⟫`, with
`ν(y) = (y − x) / |y − x|`. -/
theorem inner_gradient_radialCutoff (hδ : 0 < δ) (hs0 : 0 ≤ s) {y : Rn n}
    (hs : ‖y - x‖ ≠ s)
    (hsδ : ‖y - x‖ ≠ s + δ) (v : Rn n) :
    ⟪v, gradient (radialCutoff x s δ) y⟫ = -δ⁻¹ *
      (ball x (s + δ) \ ball x s).indicator (fun z => ⟪v, ‖z - x‖⁻¹ • (z - x)⟫) y := by
  rw [inner_gradient_right]
  rcases lt_or_gt_of_ne hs with h1 | h1
  · have : y ∉ ball x (s + δ) \ ball x s := fun h => h.2 (by rw [mem_ball, dist_eq_norm]; exact h1)
    rw [fderiv_radialCutoff_of_lt hδ h1, indicator_of_notMem this]
    simp
  rcases lt_or_gt_of_ne hsδ with h2 | h2
  · have hmem : y ∈ ball x (s + δ) \ ball x s := by
      refine ⟨by rw [mem_ball, dist_eq_norm]; exact h2, ?_⟩
      rw [mem_ball, dist_eq_norm, not_lt]; exact h1.le
    rw [(hasFDerivAt_radialCutoff hδ hs0 h1 h2).fderiv, indicator_of_mem hmem]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, inner_smul_right]
    rw [real_inner_comm]
    ring
  · have : y ∉ ball x (s + δ) \ ball x s := fun h => by
      have := h.1; rw [mem_ball, dist_eq_norm] at this; linarith
    rw [fderiv_radialCutoff_of_gt hδ h2, indicator_of_notMem this]
    simp

theorem eventually_one_div_lt {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop, 0 < (1 : ℝ) / k ∧ (1 : ℝ) / k < a := by
  filter_upwards [tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds ha),
    eventually_ge_atTop 1] with k hk hk1
  exact ⟨by simp only [one_div, inv_pos, Nat.cast_pos]; omega, hk⟩

/-- If `F` is bounded and measurable on `B̄_ρ(x)` and `s < ρ`, then
`∫ F η_k → ∫_{B_s(x)} F`, with `η_k = radialCutoff x s (1/k)`. -/
theorem tendsto_integral_mul_radialCutoff [NeZero n] {F : Rn n → ℝ} {ρ : ℝ} (hsρ : s < ρ)
    (hFm : AEStronglyMeasurable F (volume.restrict (closedBall x ρ))) {M : ℝ}
    (hM : ∀ y ∈ closedBall x ρ, |F y| ≤ M) :
    Tendsto (fun k : ℕ => ∫ y, F y * radialCutoff x s (1 / k) y) atTop
      (𝓝 (∫ y in ball x s, F y)) := by
  have hev := eventually_one_div_lt (sub_pos.2 hsρ)
  have e1 : (fun k : ℕ => ∫ y in closedBall x ρ, F y * radialCutoff x s (1 / k) y) =ᶠ[atTop]
      fun k : ℕ => ∫ y, F y * radialCutoff x s (1 / k) y := by
    filter_upwards [hev] with k ⟨hk0, hkρ⟩
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    rw [radialCutoff_eq_zero hk0 (by linarith), mul_zero]
  have e2 : ∫ y in ball x s, F y = ∫ y in closedBall x ρ, (ball x s).indicator F y := by
    rw [setIntegral_indicator measurableSet_ball,
      inter_eq_right.2 (ball_subset_closedBall.trans (closedBall_subset_closedBall hsρ.le))]
  rw [e2]
  refine Tendsto.congr' e1 ?_
  have hMi : Integrable (fun _ : Rn n => M) (volume.restrict (closedBall x ρ)) :=
    integrableOn_const (isCompact_closedBall x ρ).measure_lt_top.ne
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    (.of_forall fun k => hFm.mul continuous_radialCutoff.aestronglyMeasurable)
    (.of_forall fun k => ?_) hMi ?_
  · refine (ae_restrict_iff' measurableSet_closedBall).2 (.of_forall fun y hy => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |F y| * |radialCutoff x s (1 / k) y| ≤ M * 1 :=
          mul_le_mul (hM y hy) (abs_radialCutoff_le_one y) (abs_nonneg _)
            ((abs_nonneg _).trans (hM y hy))
      _ = M := mul_one M
  · have h1 := Measure.addHaar_sphere (volume : Measure (Rn n)) x s
    refine ae_restrict_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with y hy
    rw [mem_sphere, dist_eq_norm] at hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · have hyb : y ∈ ball x s := by rw [mem_ball, dist_eq_norm]; exact hlt
      rw [indicator_of_mem hyb]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with k ⟨hk0, _⟩
      rw [radialCutoff_eq_one hk0 hlt.le, mul_one]
    · have hyb : y ∉ ball x s := by rw [mem_ball, dist_eq_norm, not_lt]; exact hgt.le
      rw [indicator_of_notMem hyb]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_one_div_lt (sub_pos.2 hgt)] with k ⟨hk0, hk⟩
      rw [radialCutoff_eq_zero hk0 (by linarith), mul_zero]

end Kernel

namespace IsLipHarmonicPos

open Kernel

variable {U : Set (Rn n)} {u : Rn n → ℝ}

/-- **Identity (3.8)** (proof of Proposition 3.4). If `B_R(x) ⊆ U`, then for a.e. `s ∈ (0, R)`,
`∫_{B_s(x)} |∇u|² = ∫_{∂B_s(x)} u ∇u · ν`, with `ν(y) = (y − x) / |y − x|`. -/
theorem energy_eq_sphere_ae [NeZero n] (h : IsLipHarmonicPos U u) {x : Rn n} {R : ℝ}
    (hR : ball x R ⊆ U) :
    ∀ᵐ s, s ∈ Ioo 0 R → ∫ y in ball x s, ‖gradient u y‖ ^ 2 =
      sphereIntegral (fun y => u y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫) x s := by
  rcases le_or_gt R 0 with hR0 | hR0
  · exact .of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.2 hR0)
  set f : Rn n → ℝ := fun y => u y * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ with hfdef
  obtain ⟨C, hC⟩ := h.lipschitzOnWith
  have hCR := hC x R hR
  obtain ⟨Cg, hCg⟩ := h.exists_norm_gradient_le
  -- `f` is bounded and measurable on `B_R(x)`
  have hub : ∀ y ∈ ball x R, |u y| ≤ |u x| + C * R := by
    intro y hy
    have := hCR.dist_le_mul y hy x (mem_ball_self hR0)
    rw [Real.dist_eq] at this
    have hd : dist y x ≤ R := (mem_ball.1 hy).le
    have := abs_sub_abs_le_abs_sub (u y) (u x)
    nlinarith [C.coe_nonneg]
  have hνb : ∀ y : Rn n, ‖‖y - x‖⁻¹ • (y - x)‖ ≤ 1 := by
    intro y
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖y - x‖ 0 with h0 | h0
    · rw [h0]; simp
    · rw [inv_mul_cancel₀ h0]
  have hfm : AEStronglyMeasurable f (volume.restrict (ball x R)) :=
    ((h.continuousOn.mono hR).aestronglyMeasurable measurableSet_ball).mul
      ((measurable_gradient u).inner ((measurable_id.sub_const x).norm.inv.smul
        (measurable_id.sub_const x))).aestronglyMeasurable
  have hf : IntegrableOn f (ball x R) := by
    refine IntegrableOn.of_bound measure_ball_lt_top hfm ((|u x| + C * R) * Cg)
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hub y hy) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hub y hy))
    rw [← Real.norm_eq_abs]
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖gradient u y‖ * ‖‖y - x‖⁻¹ • (y - x)‖ ≤ Cg * 1 :=
          mul_le_mul (hCg y (hR hy)) (hνb y) (norm_nonneg _) Cg.2
      _ = Cg := mul_one _
  filter_upwards [ae_tendsto_average_annulus hf] with s hs hsR
  have hlim := hs hsR
  set ρ := (s + R) / 2 with hρ
  have hsρ : s < ρ := by rw [hρ]; linarith [hsR.2]
  have hρR : ρ < R := by rw [hρ]; linarith [hsR.2]
  -- eventually `1/k < ρ - s`
  have hev := eventually_one_div_lt (sub_pos.2 hsρ)
  -- the energy identity with `η_k`
  have hid : ∀ᶠ k : ℕ in atTop, ∫ y, ‖gradient u y‖ ^ 2 * radialCutoff x s (1 / k) y =
      (k : ℝ) * ∫ y in ball x (s + 1 / k) \ ball x s, f y := by
    filter_upwards [hev] with k ⟨hk0, hkρ⟩
    have hsub : tsupport (radialCutoff x s (1 / k)) ⊆ U := (tsupport_radialCutoff_subset hk0).trans
      ((closedBall_subset_ball (by linarith)).trans hR)
    rw [h.integral_norm_gradient_sq_mul ⟨_, lipschitzWith_radialCutoff hk0⟩
      (hasCompactSupport_radialCutoff hk0) hsub]
    have hae : ∀ᵐ y, u y * ⟪gradient u y, gradient (radialCutoff x s (1 / k)) y⟫ =
        -(k : ℝ) * (ball x (s + 1 / k) \ ball x s).indicator f y := by
      have h1 := Measure.addHaar_sphere (volume : Measure (Rn n)) x s
      have h2 := Measure.addHaar_sphere (volume : Measure (Rn n)) x (s + 1 / k)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
        with y hy1 hy2
      rw [mem_sphere, dist_eq_norm] at hy1 hy2
      rw [inner_gradient_radialCutoff hk0 hsR.1.le hy1 hy2, one_div, inv_inv]
      by_cases hy : y ∈ ball x (s + (↑k)⁻¹) \ ball x s
      · rw [indicator_of_mem hy, indicator_of_mem hy]
        simp only [hfdef]
        ring
      · rw [indicator_of_notMem hy, indicator_of_notMem hy]
        ring
    rw [integral_congr_ae hae, integral_const_mul, integral_indicator
      (measurableSet_ball.diff measurableSet_ball)]
    ring
  -- the left side converges to `∫_{B_s} |∇u|²`
  have hL : Tendsto (fun k : ℕ => ∫ y, ‖gradient u y‖ ^ 2 * radialCutoff x s (1 / k) y) atTop
      (𝓝 (∫ y in ball x s, ‖gradient u y‖ ^ 2)) := by
    refine tendsto_integral_mul_radialCutoff hsρ
      ((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable (M := (Cg : ℝ) ^ 2)
      fun y hy => ?_
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCg y (hR (closedBall_subset_ball hρR hy))) 2
  exact tendsto_nhds_unique (hL.congr' hid) hlim

/-- **Identity (3.8)** with the normal written as `(y − x) / s`. -/
theorem energy_eq_sphere_ae' [NeZero n] (h : IsLipHarmonicPos U u) {x : Rn n} {R : ℝ}
    (hR : ball x R ⊆ U) :
    ∀ᵐ s, s ∈ Ioo 0 R → ∫ y in ball x s, ‖gradient u y‖ ^ 2 =
      sphereIntegral (fun y => u y * ⟪gradient u y, s⁻¹ • (y - x)⟫) x s := by
  filter_upwards [h.energy_eq_sphere_ae hR] with s hs hsR
  rw [hs hsR]
  refine sphereIntegral_congr hsR.1.le fun y hy => ?_
  rw [mem_sphere, dist_eq_norm] at hy
  rw [hy]

end IsLipHarmonicPos

end InnerVariational
