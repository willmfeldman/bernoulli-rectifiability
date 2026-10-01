/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.Energy
public import InnerVariational.Kernel.Subharmonic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Kernel.VariationalQ
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral

/-!
# The Rellich–Pohozaev identity (3.7)

Identity (3.7) of Kriventsov–Weiss (in the proof of Proposition 3.4; full reference below): for a
variational solution `(u, χ)` on `Ω`, `B_R(x) ⊆ Ω`, and a.e. `s ∈ (0, R)`,
`(n − 2) ∫_{B_s(x)} |∇u|² + n ∫_{B_s(x)} χ = s ∫_{∂B_s(x)} (|∇u|² + χ − 2 (∇u · ν)²)`,
with `ν(y) = (y − x) / |y − x|`.

We prove it for a Lipschitz coefficient `Q` with `0 < c ≤ Q ≤ C'` (`QBounds`), where it reads
`(n − 2) ∫_{B_s} |∇u|² + n ∫_{B_s} Q² χ + ∫_{B_s} χ ∇(Q²) · (y − x)
  = s ∫_{∂B_s} (|∇u|² + Q² χ − 2 (∇u · ν)²)`
(`IsVariationalSolutionQ.rellich_pohozaev_ae`). The same argument applied to
`∫ div (Q² ξ) = 0` gives `n ∫_{B_s} Q² + ∫_{B_s} ∇(Q²) · (y − x) = s ∫_{∂B_s} Q²`
(`QBounds.rellich_pohozaev_ae`), and the difference of the two is the weighted form
`s ∫_{∂B_s} (|∇u|² − 2 (∇u · ν)² − Q² (1 − χ))
  = (n − 2) ∫_{B_s} |∇u|² − n ∫_{B_s} Q² (1 − χ) − ∫_{B_s} (1 − χ) ∇(Q²) · (y − x)`
(`IsVariationalSolutionQ.rellich_pohozaev_weighted_ae`), in which every coefficient term lives on
`{χ = 0}`. For `Q ≡ 1` the first identity is (3.7) (`IsVariationalSolution.rellich_pohozaev_ae`).

## Proof

We follow the paper. Test the inner variation with `ξ(y) = η_k(y) (y − x)`, where
`η_k = radialCutoff x s (1/k)`. Off the two spheres bounding the annulus
`A_k = B_{s+1/k} ∖ B_s`, `Dξ = η_k I + (y − x) ⊗ ∇η_k`. The inner variation then reads
`∫ ((n − 2)|∇u|² + nQ²χ + χ ∇(Q²) · (y − x)) η_k
  = k ∫_{A_k} |y − x| (|∇u|² + Q²χ − 2 (∇u · ν)²)`.
The left side tends to `∫_{B_s} ((n − 2)|∇u|² + nQ²χ + χ ∇(Q²) · (y − x))` by dominated
convergence, and the right side to the sphere integral at a.e. `s` (`ae_tendsto_average_annulus`).
This limit argument is `Kernel.ae_setIntegral_ball_eq_of_radialCutoff`.

The paper's intermediate display just before (3.7) has `∫_{B_s} (n − 2)(|∇u|² + χ)` on the
left; the correct left side is
`∫_{B_s} ((n − 2)|∇u|² + nχ)`: `div ξ` multiplies `|∇u|² + χ`, while `−2 ∇u·Dξ∇u` contributes
`−2η|∇u|²` only to the gradient part. The identity (3.7) itself is correct, and it is what we
formalize.

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

variable {x : Rn n} {s δ : ℝ}

/-- The radial field `ξ(y) = η(y) (y − x)`, `η = radialCutoff x s δ`, is a Lipschitz test field
on any `Ω ⊇ B̄_{s+δ}(x)`. -/
theorem isLipTestField_radialField {Ω : Set (Rn n)} (hδ : 0 < δ)
    (hK : closedBall x (s + δ) ⊆ Ω) :
    IsLipTestField Ω fun z => radialCutoff x s δ z • (z - x) := by
  refine ⟨⟨_, lipschitzWith_smul_of_support (lipschitzWith_radialCutoff hδ)
    abs_radialCutoff_le_one (K := closedBall x (s + δ)) (fun y hy => ?_) (Lg := 1)
    (LipschitzOnWith.of_dist_le_mul fun a _ b _ => by rw [dist_sub_right]; simp)
    (M := s + δ) (fun y hy => by rw [← dist_eq_norm]; exact hy)⟩,
    (hasCompactSupport_radialCutoff hδ).smul_right,
    (tsupport_smul_subset_left _ _).trans ((tsupport_radialCutoff_subset hδ).trans hK)⟩
  rw [mem_closedBall, dist_eq_norm, not_le] at hy
  exact radialCutoff_eq_zero hδ hy.le

/-- The derivative of the radial field `ξ(y) = η(y) (y − x)`, `η = radialCutoff x s δ`, off the
two spheres: `div ξ = n η − δ⁻¹ 1_A |y − x|` and
`w · Dξ w = η |w|² − δ⁻¹ 1_A |y − x|⁻¹ (w · (y − x))²`, with `A = B_{s+δ}(x) ∖ B_s(x)`. -/
theorem ae_radialField [NeZero n] (hδ : 0 < δ) (hs : 0 < s) :
    ∀ᵐ y, divergence (fun z => radialCutoff x s δ z • (z - x)) y =
        n * radialCutoff x s δ y -
          δ⁻¹ * (ball x (s + δ) \ ball x s).indicator (fun z => ‖z - x‖) y ∧
      ∀ w : Rn n, ⟪w, fderiv ℝ (fun z => radialCutoff x s δ z • (z - x)) y w⟫ =
        radialCutoff x s δ y * ‖w‖ ^ 2 -
          δ⁻¹ * (ball x (s + δ) \ ball x s).indicator
            (fun z => ‖z - x‖⁻¹ * ⟪w, z - x⟫ ^ 2) y := by
  have h1 := Measure.addHaar_sphere (volume : Measure (Rn n)) x s
  have h2 := Measure.addHaar_sphere (volume : Measure (Rn n)) x (s + δ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
    with y hy1 hy2
  rw [mem_sphere, dist_eq_norm] at hy1 hy2
  set A := ball x (s + δ) \ ball x s with hAdef
  have hη := hasFDerivAt_radialCutoff_indicator hδ hs.le hy1 hy2
  set η' := A.indicator (fun z => -(δ⁻¹ * ‖z - x‖⁻¹) • innerSL ℝ (z - x)) y with hη'def
  have hid' : HasFDerivAt (fun z : Rn n => z - x) (ContinuousLinearMap.id ℝ (Rn n)) y :=
    (hasFDerivAt_id y).sub_const x
  have hD : fderiv ℝ (fun z => radialCutoff x s δ z • (z - x)) y =
      radialCutoff x s δ y • ContinuousLinearMap.id ℝ (Rn n) + η'.smulRight (y - x) :=
    (hη.smul hid').fderiv
  have hdiv : divergence (fun z => radialCutoff x s δ z • (z - x)) y =
      radialCutoff x s δ y * n + η' (y - x) := by
    rw [divergence, hD]
    simp [LinearMap.trace_smulRight, mul_comm]
  have hquad : ∀ w : Rn n, ⟪w, fderiv ℝ (fun z => radialCutoff x s δ z • (z - x)) y w⟫ =
      radialCutoff x s δ y * ‖w‖ ^ 2 + η' w * ⟪w, y - x⟫ := by
    intro w
    rw [hD]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq]
  refine ⟨?_, fun w => ?_⟩
  · rw [hdiv]
    by_cases hyA : y ∈ A
    · have ha : ‖y - x‖ ≠ 0 := by
        have := hyA.2; rw [mem_ball, dist_eq_norm, not_lt] at this
        exact (lt_of_lt_of_le hs this).ne'
      rw [hη'def, indicator_of_mem hyA, indicator_of_mem hyA]
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
        real_inner_self_eq_norm_sq]
      field_simp
      ring
    · rw [hη'def, indicator_of_notMem hyA, indicator_of_notMem hyA]
      simp only [zero_apply]
      ring
  · rw [hquad]
    by_cases hyA : y ∈ A
    · rw [hη'def, indicator_of_mem hyA, indicator_of_mem hyA]
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
        real_inner_comm (y - x) w]
      ring
    · rw [hη'def, indicator_of_notMem hyA, indicator_of_notMem hyA]
      simp only [zero_apply]
      ring

/-- `G η` is integrable for `G` bounded and measurable on `B̄_{s+δ}(x)`, with
`η = radialCutoff x s δ`. -/
theorem integrable_mul_radialCutoff {G : Rn n → ℝ} (hδ : 0 < δ)
    (hGm : AEStronglyMeasurable G (volume.restrict (closedBall x (s + δ)))) {B : ℝ}
    (hGb : ∀ y ∈ closedBall x (s + δ), |G y| ≤ B) :
    Integrable fun y => G y * radialCutoff x s δ y := by
  refine integrable_mul_of_isCompact (isCompact_closedBall x (s + δ))
    (hGm.mul continuous_radialCutoff.aestronglyMeasurable) (A := B) (B := 1)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hGb y hy)
    (fun y _ => by rw [Real.norm_eq_abs]; exact abs_radialCutoff_le_one y) (fun y hy => ?_)
  rw [mem_closedBall, dist_eq_norm, not_le] at hy
  exact radialCutoff_eq_zero hδ hy.le

/-- `|y − x| f` is integrable on `B_R(x)` for `f` bounded and measurable there. -/
theorem integrableOn_norm_sub_mul {f : Rn n → ℝ} {R : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (ball x R))) {B : ℝ}
    (hfb : ∀ y ∈ ball x R, |f y| ≤ B) : IntegrableOn (fun y => ‖y - x‖ * f y) (ball x R) := by
  refine IntegrableOn.of_bound measure_ball_lt_top
    ((measurable_id.sub_const x).norm.aestronglyMeasurable.mul hfm) (R * B)
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_norm]
  have h1 : ‖y - x‖ ≤ R := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
  exact mul_le_mul h1 (hfb y hy) (abs_nonneg _) ((norm_nonneg _).trans h1)

/-- **The limit `δ → 0` in a radial cutoff identity.** Let `G`, `f` be bounded and measurable on
`B_R(x)`, and suppose that for all `0 < s`, `0 < δ` with `s + δ < R`,
`∫ G η = δ⁻¹ ∫_{B_{s+δ}(x) ∖ B_s(x)} |y − x| f`, where `η = radialCutoff x s δ`. Then for a.e.
`s ∈ (0, R)`, `∫_{B_s(x)} G = s ∫_{∂B_s(x)} f`. -/
theorem ae_setIntegral_ball_eq_of_radialCutoff [NeZero n] {R : ℝ} {G f : Rn n → ℝ}
    (hGm : AEStronglyMeasurable G (volume.restrict (ball x R))) {B : ℝ}
    (hGb : ∀ y ∈ ball x R, |G y| ≤ B)
    (hfm : AEStronglyMeasurable f (volume.restrict (ball x R))) {B' : ℝ}
    (hfb : ∀ y ∈ ball x R, |f y| ≤ B')
    (hid : ∀ s δ, 0 < s → 0 < δ → s + δ < R →
      ∫ y, G y * radialCutoff x s δ y =
        δ⁻¹ * ∫ y in ball x (s + δ) \ ball x s, ‖y - x‖ * f y) :
    ∀ᵐ s, s ∈ Ioo 0 R → ∫ y in ball x s, G y = s * sphereIntegral f x s := by
  have hg := integrableOn_norm_sub_mul hfm hfb
  filter_upwards [ae_tendsto_average_annulus hg] with s hs hsR
  have hlim := hs hsR
  set ρ := (s + R) / 2 with hρ
  have hsρ : s < ρ := by rw [hρ]; linarith [hsR.2]
  have hρR : ρ < R := by rw [hρ]; linarith [hsR.2]
  have hρsub : closedBall x ρ ⊆ ball x R := closedBall_subset_ball hρR
  have hL := tendsto_integral_mul_radialCutoff hsρ
    (hGm.mono_measure (Measure.restrict_mono hρsub le_rfl)) (fun y hy => hGb y (hρsub hy))
  have hid' : ∀ᶠ k : ℕ in atTop, ∫ y, G y * radialCutoff x s (1 / k) y =
      (k : ℝ) * ∫ y in ball x (s + 1 / k) \ ball x s, ‖y - x‖ * f y := by
    filter_upwards [eventually_one_div_lt (sub_pos.2 hsρ)] with k ⟨hk0, hkρ⟩
    rw [hid s (1 / k) hsR.1 hk0 (by linarith), one_div, inv_inv]
  rw [tendsto_nhds_unique (hL.congr' hid') hlim, ← sphereIntegral_const_mul]
  refine sphereIntegral_congr hsR.1.le fun y hy => ?_
  rw [mem_sphere, dist_eq_norm] at hy
  simp only [hy]

end Kernel

open Kernel

namespace QBounds

variable {Ω : Set (Rn n)} {Q : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ} {x : Rn n}

theorem aestronglyMeasurable_rellich (hQ : QBounds Ω Q L c C') {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
    AEStronglyMeasurable (fun y => n * Q y ^ 2 + fderiv ℝ (fun z => Q z ^ 2) y (y - x))
      (volume.restrict S) :=
  ((((hQ.continuousOn.mono hSΩ).pow 2).aestronglyMeasurable hS).const_mul _).add
    (measurable_fderiv_apply _ (measurable_id.sub_const x)).aestronglyMeasurable

theorem abs_rellich_le (hQ : QBounds Ω Q L c C') (hΩ : IsOpen Ω) {y : Rn n} (hy : y ∈ Ω) :
    |n * Q y ^ 2 + fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤
      n * C' ^ 2 + 2 * C' * L * ‖y - x‖ := by
  refine (abs_add_le _ _).trans (add_le_add ?_ (hQ.abs_fderiv_sq_apply_le hΩ hy _))
  rw [abs_mul, Nat.abs_cast, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hQ.sq_le hy) (Nat.cast_nonneg n)

/-- The cutoff form of the ball identity for `Q²`: with `η = radialCutoff x s δ` and
`B̄_{s+δ}(x) ⊆ Ω`, `∫ (n Q² + ∇(Q²) · (y − x)) η = δ⁻¹ ∫_{B_{s+δ} ∖ B_s} |y − x| Q²`. -/
theorem integral_rellich_mul_radialCutoff [NeZero n] (hQ : QBounds Ω Q L c C') (hΩ : IsOpen Ω)
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hK : closedBall x (s + δ) ⊆ Ω) :
    ∫ y, (n * Q y ^ 2 + fderiv ℝ (fun z => Q z ^ 2) y (y - x)) * radialCutoff x s δ y =
      δ⁻¹ * ∫ y in ball x (s + δ) \ ball x s, ‖y - x‖ * Q y ^ 2 := by
  set η := radialCutoff x s δ with hηdef
  set A := ball x (s + δ) \ ball x s with hAdef
  have hξ := isLipTestField_radialField hδ hK
  have h0 := hQ.integral_sq_mul_divergence_add_eq_zero hΩ hξ
  have hAK : A ⊆ closedBall x (s + δ) := sdiff_subset.trans ball_subset_closedBall
  have hpt : ∀ᵐ y, Q y ^ 2 * divergence (fun z => η z • (z - x)) y +
      fderiv ℝ (fun z => Q z ^ 2) y (η y • (y - x)) =
      (n * Q y ^ 2 + fderiv ℝ (fun z => Q z ^ 2) y (y - x)) * η y -
        δ⁻¹ * A.indicator (fun z => ‖z - x‖ * Q z ^ 2) y := by
    filter_upwards [ae_radialField (x := x) hδ hs] with y hy
    rw [hy.1, map_smul, smul_eq_mul]
    by_cases hyA : y ∈ A
    · rw [indicator_of_mem hyA, indicator_of_mem hyA]; ring
    · rw [indicator_of_notMem hyA, indicator_of_notMem hyA]; ring
  have hI1 := integrable_mul_radialCutoff (s := s) hδ
    (hQ.aestronglyMeasurable_rellich (x := x) measurableSet_closedBall hK)
    (B := n * C' ^ 2 + 2 * C' * L * (s + δ)) fun y hy => by
      refine (hQ.abs_rellich_le hΩ (hK hy)).trans ?_
      have := hQ.nonneg_of_mem (hK hy)
      rw [mem_closedBall, dist_eq_norm] at hy
      gcongr
  have hI2 : Integrable (A.indicator fun z => ‖z - x‖ * Q z ^ 2) := by
    refine (IntegrableOn.integrable_indicator ?_ (measurableSet_ball.diff measurableSet_ball))
    refine IntegrableOn.of_bound (measure_ball_lt_top.trans_le' (measure_mono sdiff_subset))
      ((measurable_id.sub_const x).norm.aestronglyMeasurable.mul
        (((hQ.continuousOn.mono (hAK.trans hK)).pow 2).aestronglyMeasurable
          (measurableSet_ball.diff measurableSet_ball))) ((s + δ) * C' ^ 2)
      ((ae_restrict_iff' (measurableSet_ball.diff measurableSet_ball)).2
        (.of_forall fun y hy => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖y - x‖ ≤ s + δ := by
      have := hy.1; rw [mem_ball, dist_eq_norm] at this; exact this.le
    exact mul_le_mul h1 (hQ.sq_le (hK (hAK hy))) (sq_nonneg _) (by linarith)
  rw [integral_congr_ae hpt, integral_sub hI1 (hI2.const_mul _), integral_const_mul,
    integral_indicator (measurableSet_ball.diff measurableSet_ball)] at h0
  linarith

/-- **The ball identity for `Q²`.** If `Q` is Lipschitz with `0 < c ≤ Q ≤ C'` on the open set
`Ω` and `B_R(x) ⊆ Ω`, then for a.e. `s ∈ (0, R)`,
`n ∫_{B_s(x)} Q² + ∫_{B_s(x)} ∇(Q²) · (y − x) = s ∫_{∂B_s(x)} Q²`. This is the divergence
theorem for the field `Q² (y − x)`. -/
theorem rellich_pohozaev_ae [NeZero n] (hQ : QBounds Ω Q L c C') (hΩ : IsOpen Ω) {R : ℝ}
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      n * (∫ y in ball x s, Q y ^ 2) + ∫ y in ball x s, fderiv ℝ (fun z => Q z ^ 2) y (y - x) =
        s * sphereIntegral (fun y => Q y ^ 2) x s := by
  have hGb : ∀ y ∈ ball x R, |n * Q y ^ 2 + fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤
      n * C' ^ 2 + 2 * C' * L * R := fun y hy => by
    refine (hQ.abs_rellich_le hΩ (hR hy)).trans ?_
    have := hQ.nonneg_of_mem (hR hy)
    rw [mem_ball, dist_eq_norm] at hy
    gcongr
  have hae := ae_setIntegral_ball_eq_of_radialCutoff
    (hQ.aestronglyMeasurable_rellich (x := x) measurableSet_ball hR) hGb
    ((show ContinuousOn (fun y => Q y ^ 2) _ from
      (hQ.continuousOn.mono hR).pow 2).aestronglyMeasurable
      measurableSet_ball)
    (B' := C' ^ 2) (fun y hy => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact hQ.sq_le (hR hy))
    fun s δ hs hδ hsδ => hQ.integral_rellich_mul_radialCutoff hΩ hs hδ
      ((closedBall_subset_ball hsδ).trans hR)
  filter_upwards [hae] with s hs hsR
  rw [← hs hsR]
  have hsub : ball x s ⊆ ball x R := ball_subset_ball hsR.2.le
  have hi1 : IntegrableOn (fun y => Q y ^ 2) (ball x s) :=
    IntegrableOn.of_bound measure_ball_lt_top
      (((hQ.continuousOn.mono (hsub.trans hR)).pow 2).aestronglyMeasurable measurableSet_ball)
      (C' ^ 2) ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hQ.sq_le (hR (hsub hy))))
  have hi2 : IntegrableOn (fun y => fderiv ℝ (fun z => Q z ^ 2) y (y - x)) (ball x s) :=
    IntegrableOn.of_bound measure_ball_lt_top
      (measurable_fderiv_apply _ (measurable_id.sub_const x)).aestronglyMeasurable
      (2 * C' * L * R) ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]
        refine (hQ.abs_fderiv_sq_apply_le hΩ (hR (hsub hy)) _).trans ?_
        have := hQ.nonneg_of_mem (hR (hsub hy))
        have h1 : ‖y - x‖ ≤ R := by
          rw [← dist_eq_norm]; exact (mem_ball.1 (hsub hy)).le
        gcongr))
  rw [integral_add (hi1.const_mul _) hi2, integral_const_mul]

end QBounds

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ} {x : Rn n}

theorem aestronglyMeasurable_rellich (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {S : Set (Rn n)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
    AEStronglyMeasurable (fun y => ((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 + n * (Q y ^ 2 * χ y) +
      χ y * fderiv ℝ (fun z => Q z ^ 2) y (y - x)) (volume.restrict S) := by
  have hχ := h.aestronglyMeasurable_chi hS hSΩ
  have hQ2 := ((hQ.continuousOn.mono hSΩ).pow 2).aestronglyMeasurable (μ := volume) hS
  exact ((((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable.const_mul _).add
    ((hQ2.mul hχ).const_mul _)).add
    (hχ.mul (measurable_fderiv_apply _ (measurable_id.sub_const x)).aestronglyMeasurable)

theorem abs_rellich_le (h : IsVariationalSolutionQ Ω C Q u χ) (hQ : QBounds Ω Q L c C')
    {y : Rn n} (hy : y ∈ Ω) :
    |((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 + n * (Q y ^ 2 * χ y) +
      χ y * fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤
      |(n : ℝ) - 2| * C ^ 2 + n * C' ^ 2 + 2 * C' * L * ‖y - x‖ := by
  have hχ := h.abs_chi_le_one hy
  have hsq : ‖gradient u y‖ ^ 2 ≤ (C : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (h.norm_gradient_le hy) 2
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul, abs_of_nonneg (sq_nonneg ‖gradient u y‖)]
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  · rw [abs_mul, Nat.abs_cast, abs_mul, abs_of_nonneg (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    calc Q y ^ 2 * |χ y| ≤ C' ^ 2 * 1 :=
          mul_le_mul (hQ.sq_le hy) hχ (abs_nonneg _) (sq_nonneg _)
      _ = C' ^ 2 := mul_one _
  · rw [abs_mul]
    calc |χ y| * |fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤ 1 * (2 * C' * L * ‖y - x‖) :=
          mul_le_mul hχ (hQ.abs_fderiv_sq_apply_le h.isOpen hy _) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem aestronglyMeasurable_rellich_sphere (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {S : Set (Rn n)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :
    AEStronglyMeasurable (fun y => ‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y -
      2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) (volume.restrict S) := by
  have hνm : Measurable fun y : Rn n => ‖y - x‖⁻¹ • (y - x) :=
    (measurable_id.sub_const x).norm.inv.smul (measurable_id.sub_const x)
  exact ((((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable).add
    ((((hQ.continuousOn.mono hSΩ).pow 2).aestronglyMeasurable hS).mul
      (h.aestronglyMeasurable_chi hS hSΩ))).sub
    ((((measurable_gradient u).inner hνm).pow_const 2).const_mul 2).aestronglyMeasurable

theorem abs_rellich_sphere_le (h : IsVariationalSolutionQ Ω C Q u χ) (hQ : QBounds Ω Q L c C')
    {y : Rn n} (hy : y ∈ Ω) :
    |‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y - 2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2| ≤
      3 * C ^ 2 + C' ^ 2 := by
  have hν : ‖‖y - x‖⁻¹ • (y - x)‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖y - x‖ 0 with h0 | h0
    · rw [h0]; simp
    · rw [inv_mul_cancel₀ h0]
  have hCg := h.norm_gradient_le hy
  have a1 : ‖gradient u y‖ ^ 2 ≤ (C : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hCg 2
  have a2 := h.abs_chi_le_one hy
  have a3 : ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2 ≤ (C : ℝ) ^ 2 := by
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [← Real.norm_eq_abs]
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖gradient u y‖ * ‖‖y - x‖⁻¹ • (y - x)‖ ≤ C * 1 :=
          mul_le_mul hCg hν (norm_nonneg _) C.2
      _ = C := mul_one _
  have a4 : 0 ≤ ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2 := sq_nonneg _
  have a5 : 0 ≤ ‖gradient u y‖ ^ 2 := sq_nonneg _
  have a6 := hQ.sq_le hy
  have a7 : 0 ≤ Q y ^ 2 := sq_nonneg _
  have a8 : |Q y ^ 2 * χ y| ≤ C' ^ 2 := by
    rw [abs_mul, abs_of_nonneg a7]
    calc Q y ^ 2 * |χ y| ≤ C' ^ 2 * 1 := mul_le_mul a6 a2 (abs_nonneg _) (sq_nonneg _)
      _ = C' ^ 2 := mul_one _
  rw [abs_le] at a8 ⊢
  constructor <;> nlinarith

/-- The cutoff form of the Rellich–Pohozaev identity: with `η = radialCutoff x s δ` and
`B̄_{s+δ}(x) ⊆ Ω`,
`∫ ((n − 2)|∇u|² + n Q² χ + χ ∇(Q²) · (y − x)) η
  = δ⁻¹ ∫_{B_{s+δ} ∖ B_s} |y − x| (|∇u|² + Q² χ − 2 (∇u · ν)²)`. This is the inner variation
along `ξ = η (y − x)`. -/
theorem integral_rellich_mul_radialCutoff [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hK : closedBall x (s + δ) ⊆ Ω) :
    ∫ y, (((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 + n * (Q y ^ 2 * χ y) +
        χ y * fderiv ℝ (fun z => Q z ^ 2) y (y - x)) * radialCutoff x s δ y =
      δ⁻¹ * ∫ y in ball x (s + δ) \ ball x s, ‖y - x‖ * (‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y -
        2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) := by
  set η := radialCutoff x s δ with hηdef
  set A := ball x (s + δ) \ ball x s with hAdef
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hAK : A ⊆ closedBall x (s + δ) := sdiff_subset.trans ball_subset_closedBall
  have hIV := h.innerVariationQ_eq_zero _ (isLipTestField_radialField hδ hK)
  have hpt : ∀ᵐ y, ((‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y) *
      divergence (fun z => η z • (z - x)) y -
      2 * ⟪gradient u y, fderiv ℝ (fun z => η z • (z - x)) y (gradient u y)⟫ +
      fderiv ℝ (fun z => Q z ^ 2) y (η y • (y - x)) * χ y) =
      (((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 + n * (Q y ^ 2 * χ y) +
        χ y * fderiv ℝ (fun z => Q z ^ 2) y (y - x)) * η y -
      δ⁻¹ * A.indicator (fun y => ‖y - x‖ * (‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y -
        2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2)) y := by
    filter_upwards [ae_radialField (x := x) hδ hs] with y hy
    rw [hy.1, hy.2, map_smul, smul_eq_mul]
    by_cases hyA : y ∈ A
    · have ha : ‖y - x‖ ≠ 0 := by
        have := hyA.2; rw [mem_ball, dist_eq_norm, not_lt] at this
        exact (lt_of_lt_of_le hs this).ne'
      rw [indicator_of_mem hyA, indicator_of_mem hyA, indicator_of_mem hyA]
      simp only [inner_smul_right, real_inner_comm (y - x)]
      field_simp
      ring
    · rw [indicator_of_notMem hyA, indicator_of_notMem hyA, indicator_of_notMem hyA]
      ring
  have hI1 := integrable_mul_radialCutoff (s := s) hδ
    (h.aestronglyMeasurable_rellich (x := x) hQ measurableSet_closedBall hK)
    (B := |(n : ℝ) - 2| * C ^ 2 + n * C' ^ 2 + 2 * C' * L * (s + δ)) fun y hy => by
      refine (h.abs_rellich_le hQ (hK hy)).trans ?_
      have := hQ.nonneg_of_mem (hK hy)
      rw [mem_closedBall, dist_eq_norm] at hy
      gcongr
  have hI2 : Integrable (A.indicator fun y => ‖y - x‖ * (‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y -
      2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2)) := ((integrableOn_norm_sub_mul (x := x)
    (R := s + δ)
    (h.aestronglyMeasurable_rellich_sphere (x := x) hQ measurableSet_ball
      (ball_subset_closedBall.trans hK))
    (B := 3 * C ^ 2 + C' ^ 2) fun y hy =>
      h.abs_rellich_sphere_le (x := x) hQ (hK (ball_subset_closedBall hy))).mono_set
    sdiff_subset).integrable_indicator hA
  rw [innerVariationQ, integral_congr_ae hpt, integral_sub hI1 (hI2.const_mul _),
    integral_const_mul, integral_indicator hA] at hIV
  linarith

theorem abs_one_sub_chi_le_one (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    |1 - χ y| ≤ 1 := by
  rcases h.chi_mem y hy with h0 | h1 <;> simp [*]

/-- The three volume terms of the Rellich–Pohozaev identity are integrable on `S ⊆ Ω` of finite
measure. -/
theorem integrableOn_rellich_terms (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {s : ℝ} (hsub : ball x s ⊆ Ω) :
    IntegrableOn (fun y => ‖gradient u y‖ ^ 2) (ball x s) ∧
      IntegrableOn (fun y => Q y ^ 2 * χ y) (ball x s) ∧
      IntegrableOn (fun y => χ y * fderiv ℝ (fun z => Q z ^ 2) y (y - x)) (ball x s) := by
  have hχ := h.aestronglyMeasurable_chi measurableSet_ball hsub
  have hQ2 := ((hQ.continuousOn.mono hsub).pow 2).aestronglyMeasurable (μ := volume)
    measurableSet_ball
  refine ⟨?_, ?_, ?_⟩
  · refine IntegrableOn.of_bound measure_ball_lt_top
      ((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable ((C : ℝ) ^ 2)
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h.norm_gradient_le (hsub hy)) 2
  · refine IntegrableOn.of_bound measure_ball_lt_top (hQ2.mul hχ) (C' ^ 2)
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc Q y ^ 2 * |χ y| ≤ C' ^ 2 * 1 :=
          mul_le_mul (hQ.sq_le (hsub hy)) (h.abs_chi_le_one (hsub hy)) (abs_nonneg _)
            (sq_nonneg _)
      _ = C' ^ 2 := mul_one _
  · refine IntegrableOn.of_bound measure_ball_lt_top
      (hχ.mul (measurable_fderiv_apply _ (measurable_id.sub_const x)).aestronglyMeasurable)
      (2 * C' * L * s) ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
    have hC' := hQ.nonneg_of_mem (hsub hy)
    have h1 : ‖y - x‖ ≤ s := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
    rw [Real.norm_eq_abs, abs_mul]
    calc |χ y| * |fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤ 1 * (2 * C' * L * ‖y - x‖) :=
          mul_le_mul (h.abs_chi_le_one (hsub hy)) (hQ.abs_fderiv_sq_apply_le h.isOpen (hsub hy) _)
            (abs_nonneg _) zero_le_one
      _ ≤ 2 * C' * L * s := by rw [one_mul]; gcongr

/-- The three volume terms of the weighted Rellich–Pohozaev identity are integrable on balls in
`Ω`. -/
theorem integrableOn_rellich_weighted_terms (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {s : ℝ} (hsub : ball x s ⊆ Ω) :
    IntegrableOn (fun y => ‖gradient u y‖ ^ 2) (ball x s) ∧
      IntegrableOn (fun y => Q y ^ 2 * (1 - χ y)) (ball x s) ∧
      IntegrableOn (fun y => (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x)) (ball x s) := by
  have hχ := (aestronglyMeasurable_const (b := (1 : ℝ))).sub
    (h.aestronglyMeasurable_chi measurableSet_ball hsub)
  have hQ2 := ((hQ.continuousOn.mono hsub).pow 2).aestronglyMeasurable (μ := volume)
    measurableSet_ball
  refine ⟨(h.integrableOn_rellich_terms (x := x) hQ hsub).1, ?_, ?_⟩
  · refine IntegrableOn.of_bound measure_ball_lt_top (hQ2.mul hχ) (C' ^ 2)
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc Q y ^ 2 * |1 - χ y| ≤ C' ^ 2 * 1 :=
          mul_le_mul (hQ.sq_le (hsub hy)) (h.abs_one_sub_chi_le_one (hsub hy)) (abs_nonneg _)
            (sq_nonneg _)
      _ = C' ^ 2 := mul_one _
  · refine IntegrableOn.of_bound measure_ball_lt_top
      (hχ.mul (measurable_fderiv_apply _ (measurable_id.sub_const x)).aestronglyMeasurable)
      (2 * C' * L * s) ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
    have hC' := hQ.nonneg_of_mem (hsub hy)
    have h1 : ‖y - x‖ ≤ s := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
    rw [Real.norm_eq_abs, abs_mul]
    calc |1 - χ y| * |fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤ 1 * (2 * C' * L * ‖y - x‖) :=
          mul_le_mul (h.abs_one_sub_chi_le_one (hsub hy))
            (hQ.abs_fderiv_sq_apply_le h.isOpen (hsub hy) _) (abs_nonneg _) zero_le_one
      _ ≤ 2 * C' * L * s := by rw [one_mul]; gcongr

/-- **The Rellich–Pohozaev identity (3.7)** with a Lipschitz coefficient. If `B_R(x) ⊆ Ω`, then
for a.e. `s ∈ (0, R)`,
`(n − 2) ∫_{B_s(x)} |∇u|² + n ∫_{B_s(x)} Q² χ + ∫_{B_s(x)} χ ∇(Q²) · (y − x)
  = s ∫_{∂B_s(x)} (|∇u|² + Q² χ − 2 (∇u · ν)²)`,
with `ν(y) = (y − x) / |y − x|`. -/
theorem rellich_pohozaev_ae [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {R : ℝ} (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      ((n : ℝ) - 2) * (∫ y in ball x s, ‖gradient u y‖ ^ 2) +
          n * (∫ y in ball x s, Q y ^ 2 * χ y) +
          ∫ y in ball x s, χ y * fderiv ℝ (fun z => Q z ^ 2) y (y - x) =
        s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y -
          2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s := by
  have hae := ae_setIntegral_ball_eq_of_radialCutoff
    (h.aestronglyMeasurable_rellich (x := x) hQ measurableSet_ball hR)
    (B := |(n : ℝ) - 2| * C ^ 2 + n * C' ^ 2 + 2 * C' * L * R) (fun y hy => by
      refine (h.abs_rellich_le hQ (hR hy)).trans ?_
      have := hQ.nonneg_of_mem (hR hy)
      rw [mem_ball, dist_eq_norm] at hy
      gcongr)
    (h.aestronglyMeasurable_rellich_sphere (x := x) hQ measurableSet_ball hR)
    (fun y hy => h.abs_rellich_sphere_le (x := x) hQ (hR hy))
    fun s δ hs hδ hsδ => h.integral_rellich_mul_radialCutoff hQ hs hδ
      ((closedBall_subset_ball hsδ).trans hR)
  filter_upwards [hae] with s hs hsR
  rw [← hs hsR]
  have hsub : ball x s ⊆ Ω := (ball_subset_ball hsR.2.le).trans hR
  obtain ⟨hi1, hi2, hi3⟩ := h.integrableOn_rellich_terms (x := x) hQ hsub
  have h12 : IntegrableOn (fun y => ((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 + n * (Q y ^ 2 * χ y))
      (ball x s) := (hi1.const_mul _).add (hi2.const_mul _)
  rw [integral_add h12 hi3, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
    integral_const_mul]

/-- **The weighted Rellich–Pohozaev identity.** If `B_R(x) ⊆ Ω`, then for a.e. `s ∈ (0, R)`,
`s ∫_{∂B_s(x)} (|∇u|² − 2 (∇u · ν)² − Q² (1 − χ))
  = (n − 2) ∫_{B_s(x)} |∇u|² − n ∫_{B_s(x)} Q² (1 − χ) − ∫_{B_s(x)} (1 − χ) ∇(Q²) · (y − x)`,
with `ν(y) = (y − x) / |y − x|`. This is `rellich_pohozaev_ae` minus the ball identity for `Q²`
(`QBounds.rellich_pohozaev_ae`); every coefficient term is supported on `{χ = 0}`, and for
`Q ≡ 1` the last term vanishes. -/
theorem rellich_pohozaev_weighted_ae [NeZero n] {L : ℝ≥0} {c C' : ℝ}
    (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ) {x : Rn n} {R : ℝ}
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      ((n : ℝ) - 2) * (∫ y in ball x s, ‖gradient u y‖ ^ 2)
          - n * (∫ y in ball x s, Q y ^ 2 * (1 - χ y))
          - (∫ y in ball x s, (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x)) =
        s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y) -
          2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s := by
  set Ga : Rn n → ℝ := fun y => ((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 + n * (Q y ^ 2 * χ y) +
    χ y * fderiv ℝ (fun z => Q z ^ 2) y (y - x) with hGa
  set Gb : Rn n → ℝ := fun y => n * Q y ^ 2 + fderiv ℝ (fun z => Q z ^ 2) y (y - x) with hGb
  set fa : Rn n → ℝ := fun y => ‖gradient u y‖ ^ 2 + Q y ^ 2 * χ y -
    2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2 with hfa
  have hC' : ∀ y ∈ ball x R, 0 ≤ C' := fun y hy => hQ.nonneg_of_mem (hR hy)
  have hbA : ∀ y ∈ ball x R, |Ga y| ≤ |(n : ℝ) - 2| * C ^ 2 + n * C' ^ 2 + 2 * C' * L * R :=
    fun y hy => by
      refine (h.abs_rellich_le hQ (hR hy)).trans ?_
      have := hC' y hy
      rw [mem_ball, dist_eq_norm] at hy
      gcongr
  have hbB : ∀ y ∈ ball x R, |Gb y| ≤ n * C' ^ 2 + 2 * C' * L * R := fun y hy => by
    refine (hQ.abs_rellich_le h.isOpen (hR hy)).trans ?_
    have := hC' y hy
    rw [mem_ball, dist_eq_norm] at hy
    gcongr
  have hae := ae_setIntegral_ball_eq_of_radialCutoff (G := fun y => Ga y - Gb y)
    (f := fun y => fa y - Q y ^ 2)
    ((h.aestronglyMeasurable_rellich (x := x) hQ measurableSet_ball hR).sub
      (hQ.aestronglyMeasurable_rellich (x := x) measurableSet_ball hR))
    (B := (|(n : ℝ) - 2| * C ^ 2 + n * C' ^ 2 + 2 * C' * L * R) +
      (n * C' ^ 2 + 2 * C' * L * R))
    (fun y hy => (abs_sub _ _).trans (add_le_add (hbA y hy) (hbB y hy)))
    ((h.aestronglyMeasurable_rellich_sphere (x := x) hQ measurableSet_ball hR).sub
      ((show ContinuousOn (fun y => Q y ^ 2) _ from
      (hQ.continuousOn.mono hR).pow 2).aestronglyMeasurable
      measurableSet_ball))
    (B' := (3 * C ^ 2 + C' ^ 2) + C' ^ 2)
    (fun y hy => (abs_sub _ _).trans (add_le_add (h.abs_rellich_sphere_le (x := x) hQ (hR hy))
      (by rw [abs_of_nonneg (sq_nonneg _)]; exact hQ.sq_le (hR hy))))
    fun s δ hs hδ hsδ => by
      have hK : closedBall x (s + δ) ⊆ Ω := (closedBall_subset_ball hsδ).trans hR
      have hKR : closedBall x (s + δ) ⊆ ball x R := closedBall_subset_ball hsδ
      have hIa := integrable_mul_radialCutoff (s := s) hδ
        (h.aestronglyMeasurable_rellich (x := x) hQ measurableSet_closedBall hK)
        fun y hy => hbA y (hKR hy)
      have hIb := integrable_mul_radialCutoff (s := s) hδ
        (hQ.aestronglyMeasurable_rellich (x := x) measurableSet_closedBall hK)
        fun y hy => hbB y (hKR hy)
      have hAR : ball x (s + δ) \ ball x s ⊆ ball x R :=
        sdiff_subset.trans (ball_subset_ball hsδ.le)
      have hJa := (integrableOn_norm_sub_mul (x := x)
        (h.aestronglyMeasurable_rellich_sphere (x := x) hQ measurableSet_ball hR)
        fun y hy => h.abs_rellich_sphere_le (x := x) hQ (hR hy)).mono_set hAR
      have hJb := (integrableOn_norm_sub_mul (x := x) (B := C' ^ 2)
        ((show ContinuousOn (fun y => Q y ^ 2) _ from
      (hQ.continuousOn.mono hR).pow 2).aestronglyMeasurable
      measurableSet_ball)
        fun y hy => by
          rw [abs_of_nonneg (sq_nonneg _)]; exact hQ.sq_le (hR hy)).mono_set hAR
      simp_rw [sub_mul, mul_sub]
      rw [integral_sub hIa hIb, integral_sub hJa hJb,
        h.integral_rellich_mul_radialCutoff hQ hs hδ hK,
        hQ.integral_rellich_mul_radialCutoff h.isOpen hs hδ hK]
      ring
  filter_upwards [hae] with s hs hsR
  have hs' := hs hsR
  have e1 : sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y) -
      2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s =
      sphereIntegral (fun y => fa y - Q y ^ 2) x s :=
    sphereIntegral_congr hsR.1.le fun y _ => by rw [hfa]; ring
  rw [e1, ← hs']
  have hsub : ball x s ⊆ Ω := (ball_subset_ball hsR.2.le).trans hR
  have e2 : (fun y => Ga y - Gb y) = fun y => ((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 -
      n * (Q y ^ 2 * (1 - χ y)) - (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x) := by
    funext y; rw [hGa, hGb]; ring
  rw [e2]
  obtain ⟨hi1, hi2, hi3⟩ := h.integrableOn_rellich_weighted_terms (x := x) hQ hsub
  have h12 : IntegrableOn (fun y => ((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 -
      n * (Q y ^ 2 * (1 - χ y))) (ball x s) := (hi1.const_mul _).sub (hi2.const_mul _)
  rw [integral_sub h12 hi3, integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
    integral_const_mul]

end IsVariationalSolutionQ

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

theorem aestronglyMeasurable_chi (h : IsVariationalSolution Ω C u χ) {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) : AEStronglyMeasurable χ (volume.restrict S) :=
  h.toQ.aestronglyMeasurable_chi hS hSΩ

theorem abs_chi_le_one (h : IsVariationalSolution Ω C u χ) {y : Rn n} (hy : y ∈ Ω) :
    |χ y| ≤ 1 :=
  h.toQ.abs_chi_le_one hy

/-- **The Rellich–Pohozaev identity (3.7)** (proof of Proposition 3.4). If `B_R(x) ⊆ Ω`, then
for a.e. `s ∈ (0, R)`,
`(n − 2) ∫_{B_s(x)} |∇u|² + n ∫_{B_s(x)} χ = s ∫_{∂B_s(x)} (|∇u|² + χ − 2 (∇u · ν)²)`,
with `ν(y) = (y − x) / |y − x|`. -/
theorem rellich_pohozaev_ae [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n} {R : ℝ}
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      ((n : ℝ) - 2) * (∫ y in ball x s, ‖gradient u y‖ ^ 2) + n * ∫ y in ball x s, χ y =
        s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y -
          2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s := by
  simpa using h.toQ.rellich_pohozaev_ae (QBounds.one Ω) hR

end IsVariationalSolution

end InnerVariational
