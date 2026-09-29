/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.LimitsQ
public import InnerVariational.Monotonicity.Limits
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Monotonicity.Homogeneity
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Kernel.Rescale
import InnerVariational.Basic.Polar

/-!
# Blow-ups and the density formula with a Lipschitz coefficient

Let `(u, χ)` be a variational solution on `Ω` for a coefficient `Q` with `QBounds Ω Q L c C'`,
and `x ∈ Ω`. This file proves the analogues of the last claim of Proposition 3.4 and of
formula (3.10) of Kriventsov–Weiss.

## Main results

* `IsVariationalSolutionQ.integral_annulus_sub_inner_sq_le`: the annulus bound
  `∫_{B_t(x) ∖ B_s(x)} (u − ∇u·(y−x))² ≤ (t^{n+2}/2) (M^w_x(t) − M^w_x(s) + A (t − s))` from
  the almost-monotonicity of `M^w`.
* `IsVariationalSolutionQ.blowup_homogeneous'`: blow-up limits `u_{x,r_k} → u₀` are homogeneous
  of degree one.
* `IsVariationalSolutionQ.tendsto_monotonicityMq_zero` (formula (3.10) with a coefficient): if
  `u(x) = 0`, then `M^{Q(x)}_x(0+)` is a real number `m`, and
  `Q(x)² r^{-n} ∫_{B_r(x)} χ → m`, that is, `M(0+) = Q(x)² · (density of {χ = 1} at x)`.
* `IsVariationalSolutionQ.MzeroQ_le_sq_mul_unitBallVolume`: `M^{Q(x)}_x(0+) ≤ Q(x)² |B_1|`.

## Proof

Under the rescaling `u_{x,r}(y) = u(x + r y)/r`, `χ_{x,r}(y) = χ(x + r y)`, the pair
`(u_{x,r}, χ_{x,r})` is a variational solution for the coefficient `Q(x + r ·)`, which is
`r L`-Lipschitz. Its constants in the almost-monotonicity and in the comparison of `M^w` with
`M^{Q(x)}` are therefore `r A` and `r B`, and they tend to `0` along a blow-up sequence: the
blow-up sees the constant coefficient `Q(x)`. The frozen quantity `M^{Q(x)}` is exactly
invariant under the rescaling (`monotonicityMq_rescale`). The rest follows the proof of
Proposition 3.5 for `Q ≡ 1` (`Monotonicity/Density.lean`): the annulus integrals of
`(u_{x,r_k} − ∇u_{x,r_k}·y)²` tend to `0`, which gives Euler's identity and homogeneity for the
blow-up (`inner_gradient_eq_of_tendsto_integral_annulus`), and then
`Q(x)² ∫_{B_1} χ_{x,r_k} = M^{Q(x)}_0(u_{x,r_k}; 1) − ∫_{B_1} |∇u_{x,r_k}|² + ∫_{∂B_1} u_{x,r_k}²
→ m − ∫_{B_1} |∇u₀|² + ∫_{∂B_1} u₀² = m`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Two convergence lemmas -/

/-- `|‖a‖² − ‖b‖²| ≤ 2 L ‖a − b‖` when `‖a‖, ‖b‖ ≤ L`. -/
theorem abs_sq_norm_sub_sq_norm_le {a b : Rn n} {L : ℝ} (ha : ‖a‖ ≤ L) (hb : ‖b‖ ≤ L) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * L * ‖a - b‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (by linarith) (abs_norm_sub_norm_le a b) (abs_nonneg _)
    (by linarith [norm_nonneg a])

/-- `L²` convergence of uniformly bounded vector fields on a set of finite measure implies
convergence of `∫ ‖g_k‖²`. -/
theorem tendsto_setIntegral_norm_sq_of_tendsto_sub {S : Set (Rn n)} (hS : MeasurableSet S)
    (hSf : volume S < ⊤) {g : ℕ → Rn n → Rn n} {g₀ : Rn n → Rn n} {L : ℝ}
    (hgm : ∀ k, Measurable (g k)) (hg0m : Measurable g₀) (hgb : ∀ k, ∀ y ∈ S, ‖g k y‖ ≤ L)
    (hg0b : ∀ y ∈ S, ‖g₀ y‖ ≤ L)
    (hlim : Tendsto (fun k => ∫ y in S, ‖g k y - g₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y in S, ‖g k y‖ ^ 2) atTop (𝓝 (∫ y in S, ‖g₀ y‖ ^ 2)) := by
  have hint : ∀ f : Rn n → ℝ, Measurable f → ∀ M, (∀ y ∈ S, |f y| ≤ M) → IntegrableOn f S :=
    fun f hf M hM => IntegrableOn.of_bound hSf hf.aestronglyMeasurable M
      ((ae_restrict_iff' hS).2 (.of_forall fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy))
  have hL0 : ∀ y ∈ S, 0 ≤ L := fun y hy => (norm_nonneg _).trans (hg0b y hy)
  have hsq : ∀ k, IntegrableOn (fun y => ‖g k y - g₀ y‖ ^ 2) S := fun k =>
    hint _ (((hgm k).sub hg0m).norm.pow_const 2) ((2 * L) ^ 2) fun y hy => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by
        linarith [hgb k y hy, hg0b y hy])) 2
  have hlin : ∀ k, IntegrableOn (fun y => ‖g k y - g₀ y‖) S := fun k =>
    hint _ ((hgm k).sub hg0m).norm (2 * L) fun y hy => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by linarith [hgb k y hy, hg0b y hy])
  have hone : IntegrableOn (fun _ : Rn n => (1 : ℝ)) S := integrableOn_const hSf.ne
  -- Cauchy–Schwarz: `(∫_S ‖g_k − g₀‖)² ≤ |S| ∫_S ‖g_k − g₀‖²`.
  have hCS : ∀ k, (∫ y in S, ‖g k y - g₀ y‖) ^ 2 ≤
      (∫ y in S, ‖g k y - g₀ y‖ ^ 2) * volume.real S := by
    intro k
    have := sq_integral_mul_le (μ := volume.restrict S) (F := fun y => ‖g k y - g₀ y‖)
      (G := fun _ => (1 : ℝ)) (hsq k) (by simp only [one_pow]; exact hone)
      (by simp only [mul_one]; exact hlin k)
    simpa [Measure.real, Measure.restrict_apply MeasurableSet.univ] using this
  have hD : Tendsto (fun k => ∫ y in S, ‖g k y - g₀ y‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => √((∫ y in S, ‖g k y - g₀ y‖ ^ 2) * volume.real S)) atTop
        (𝓝 0) := by
      simpa using (hlim.mul_const (volume.real S)).sqrt
    refine squeeze_zero (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) h1
    exact (le_abs_self _).trans (Real.abs_le_sqrt (hCS k))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ k, ‖(∫ y in S, ‖g k y‖ ^ 2) - ∫ y in S, ‖g₀ y‖ ^ 2‖ ≤
      2 * L * ∫ y in S, ‖g k y - g₀ y‖ := by
    intro k
    by_cases hSe : S.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hSe
      have hLn : 0 ≤ L := hL0 y₀ hy₀
      rw [← integral_sub (hint _ ((hgm k).norm.pow_const 2) (L ^ 2) fun y hy => by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hgb k y hy) 2)
        (hint _ (hg0m.norm.pow_const 2) (L ^ 2) fun y hy => by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hg0b y hy) 2),
        ← integral_const_mul]
      refine norm_integral_le_of_norm_le ((hlin k).const_mul _)
        ((ae_restrict_iff' hS).2 (.of_forall fun y hy => ?_))
      rw [Real.norm_eq_abs]
      exact abs_sq_norm_sub_sq_norm_le (hgb k y hy) (hg0b y hy)
    · rw [not_nonempty_iff_eq_empty] at hSe
      simp [hSe]
  refine squeeze_zero (fun _ => norm_nonneg _) hbd ?_
  simpa using hD.const_mul (2 * L)

namespace IsVariationalSolution

variable {u : Rn n → ℝ} {x : Rn n}

/-- A blow-up limit at `x` forces `u(x) = 0`. -/
theorem eq_zero_of_tendstoLocallyUniformly_rescale {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    u x = 0 := by
  have e : ∀ k, r k * oneHomRescale u x (r k) 0 = u x := fun k => by
    rw [oneHomRescale_apply, smul_zero, add_zero]
    field_simp [(hr k).ne']
  have := hr0.mul ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ 0))
  rw [zero_mul] at this
  exact tendsto_nhds_unique tendsto_const_nhds (this.congr e)

/-- `u₀(0) = 0`. -/
theorem blowup_apply_zero {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    u₀ 0 = 0 := by
  have hux := eq_zero_of_tendstoLocallyUniformly_rescale hr hr0 hconv
  refine tendsto_nhds_unique ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ 0)) ?_
  simp [hux]

end IsVariationalSolution

/-! ### Scaling -/

section Scaling

variable (u χ : Rn n → ℝ) (x : Rn n) {r : ℝ}

/-- `D^q_0(u_{x,r}, χ_{x,r}; t) = D^q_x(u, χ; r t)`. -/
theorem energyDq_rescale (q : ℝ) (hr : 0 < r) (t : ℝ) :
    energyDq q (oneHomRescale u x r) (chiRescale χ x r) 0 t = energyDq q u χ x (r * t) := by
  have hg : ∀ y, ‖gradient (oneHomRescale u x r) y‖ ^ 2 + q ^ 2 * chiRescale χ x r y =
      (fun z => ‖gradient u z‖ ^ 2 + q ^ 2 * χ z) (x + r • y) := by
    intro y
    have : oneHomRescale u x r = fun z => u (x + r • z) / r := rfl
    rw [this, gradient_comp_add_smul_div u x hr.ne' y]
    rfl
  rw [energyDq, energyDq, integral_congr_ae (.of_forall hg),
    setIntegral_ball_comp_add_smul (fun z => ‖gradient u z‖ ^ 2 + q ^ 2 * χ z) x 0 hr, smul_zero,
    add_zero, mul_pow, mul_inv]
  ring

/-- `M^q_0(u_{x,r}, χ_{x,r}; t) = M^q_x(u, χ; r t)`. -/
theorem monotonicityMq_rescale [NeZero n] (q : ℝ) (hr : 0 < r) (t : ℝ) :
    monotonicityMq q (oneHomRescale u x r) (chiRescale χ x r) 0 t =
      monotonicityMq q u χ x (r * t) := by
  rw [monotonicityMq, monotonicityMq, energyDq_rescale u χ x q hr, heightH_rescale u x hr]

/-- `M^q_0(u_{x,r_k}, χ_{x,r_k}; t) → m` when `M^q_x(r) → m` as `r → 0+` and `r_k → 0+`. -/
theorem tendsto_monotonicityMq_rescale [NeZero n] {q m : ℝ}
    (hm : Tendsto (monotonicityMq q u χ x) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => monotonicityMq q (oneHomRescale u x (r k)) (chiRescale χ x (r k)) 0 t)
      atTop (𝓝 m) := by
  have e : ∀ k, monotonicityMq q u χ x (r k * t) =
      monotonicityMq q (oneHomRescale u x (r k)) (chiRescale χ x (r k)) 0 t := fun k =>
    (monotonicityMq_rescale u χ x q (hr k) t).symm
  refine (hm.comp (tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall fun k => mul_pos (hr k) ht⟩)).congr e
  simpa using hr0.mul_const t

end Scaling

/-- The constant `A` scales linearly with the Lipschitz constant of the coefficient. -/
theorem weissConst_toNNReal_mul {r : ℝ} (hr : 0 ≤ r) (L : ℝ≥0) (c C' : ℝ) :
    weissConst n (Real.toNNReal r * L) c C' = r * weissConst n L c C' := by
  simp only [weissConst, weissKappa, NNReal.coe_mul, Real.coe_toNNReal _ hr]
  ring

/-- The constant `B` scales linearly with the Lipschitz constant of the coefficient. -/
theorem weissCompConst_toNNReal_mul {r : ℝ} (hr : 0 ≤ r) (L : ℝ≥0) (C' : ℝ) :
    weissCompConst n (Real.toNNReal r * L) C' = r * weissCompConst n L C' := by
  simp only [weissCompConst, NNReal.coe_mul, Real.coe_toNNReal _ hr]
  ring

namespace IsVariationalSolutionQ

open Kernel

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {R : ℝ} {L : ℝ≥0}
  {c C' : ℝ}

/-! ### The annulus bound -/

/-- **Integrated almost-monotonicity**: for `0 < s ≤ t < R`, `B_R(x) ⊆ Ω`,
`∫_{B_t(x) ∖ B_s(x)} (u − ∇u·(y−x))² ≤ (t^{n+2} / 2) (M^w_x(t) − M^w_x(s) + A (t − s))`. -/
theorem integral_annulus_sub_inner_sq_le [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (htR : t < R) :
    ∫ y in ball x t \ ball x s, (u y - ⟪gradient u y, y - x⟫) ^ 2 ≤
      t ^ (n + 2) / 2 * (weightedMonotonicityM Q u χ x t - weightedMonotonicityM Q u χ x s +
        weissConst n L c C' * (t - s)) := by
  set F : Rn n → ℝ := fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2 with hFdef
  have ht : 0 < t := hs.trans_le hst
  have hK : closedBall x t ⊆ Ω := (closedBall_subset_ball htR).trans hR
  have hFint : IntegrableOn F (ball x t) :=
    (integrableOn_sub_inner_sq (isCompact_closedBall x t) (h.continuousOn.mono hK)
      (fun y hy => h.norm_gradient_le (hK hy)) x).mono_set ball_subset_closedBall
  rw [integral_ball_diff_ball hs.le hst hFint]
  set d := h.radialDataErr hQ hR hs hst htR
  set A := weissConst n L c C'
  have hΛ := h.volume_term_le hQ hR hs hst htR
  have hSI0 : ∀ σ, 0 < σ → 0 ≤ sphereIntegral F x σ := fun σ hσ =>
    sphereIntegral_nonneg hσ.le fun _ _ => sq_nonneg _
  have hAC : AbsolutelyContinuousOnInterval (fun σ => weissKappa L c C' *
      (C' ^ 2 * unitBallVolume n) * σ) s t :=
    ContDiffOn.absolutelyContinuousOnInterval
      (by fun_prop : ContDiff ℝ 1 fun σ : ℝ => weissKappa L c C' *
        (C' ^ 2 * unitBallVolume n) * σ).contDiffOn
  have key := AbsolutelyContinuousOnInterval.integral_le_sub_of_ae_le
    (f := fun σ => d.monotonicityM σ + weissKappa L c C' * (C' ^ 2 * unitBallVolume n) * σ)
    (f' := fun σ => 2 / σ ^ (n + 2) * (d.sphRad σ - 2 * d.sphMix σ + d.sphSq σ) + d.err σ +
      weissKappa L c C' * (C' ^ 2 * unitBallVolume n))
    (g := fun σ => 2 / t ^ (n + 2) * sphereIntegral F x σ) hst
    (d.absolutelyContinuousOnInterval_monotonicityM.fun_add hAC)
    (by
      filter_upwards [d.hasDerivAt_monotonicityM] with σ hσ hσ'
      exact (hσ hσ').add (((hasDerivAt_id σ).const_mul _).congr_deriv (mul_one _)))
    (.of_forall fun σ hσ => mul_nonneg (by positivity) (hSI0 σ (hs.trans hσ.1)))
    (by
      filter_upwards [d.ae_monotonicityM_deriv_add_nonneg hΛ] with σ hσ hσ'
      have hσ0 : 0 < σ := hs.trans hσ'.1
      have e : sphereIntegral F x σ = d.sphRad σ - 2 * d.sphMix σ + d.sphSq σ :=
        h.sphereIntegral_sub_inner_sq hR hσ0.le (hσ'.2.trans htR)
      calc 2 / t ^ (n + 2) * sphereIntegral F x σ ≤ 2 / σ ^ (n + 2) * sphereIntegral F x σ :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_left zero_le_two (by positivity)
                (pow_le_pow_left₀ hσ0.le hσ'.2.le _)) (hSI0 σ hσ0)
        _ = 2 / σ ^ (n + 2) * (d.sphRad σ - 2 * d.sphMix σ + d.sphSq σ) := by rw [e]
        _ ≤ _ := hσ hσ')
  rw [intervalIntegral.integral_const_mul] at key
  have htp : 0 < t ^ (n + 2) := by positivity
  simp only [radialDataErr_monotonicityM, d] at key
  rw [div_mul_eq_mul_div, div_le_iff₀ htp] at key
  have e2 : A = weissKappa L c C' * (C' ^ 2 * unitBallVolume n) := rfl
  rw [e2]
  nlinarith

/-! ### Blow-ups -/

/-- For `r_k → 0+`, the rescalings `(u_{x,r_k}, χ_{x,r_k})` are eventually variational solutions
on `B_ρ` for the coefficient `Q(x + r_k ·)`, which satisfies the bounds with Lipschitz constant
`r_k L`. -/
theorem eventually_rescale_ball (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR0 : 0 < R) (hR : ball x R ⊆ Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {ρ : ℝ} (hρ : 0 < ρ) : ∀ᶠ k in atTop,
      IsVariationalSolutionQ (ball 0 ρ) C (fun y => Q (x + r k • y)) (oneHomRescale u x (r k))
        (chiRescale χ x (r k)) ∧
      QBounds (ball 0 ρ) (fun y => Q (x + r k • y)) (Real.toNNReal (r k) * L) c C' := by
  filter_upwards [hr0.eventually (gt_mem_nhds (div_pos hR0 hρ))] with k hk
  have hsub : ball (0 : Rn n) ρ ⊆ (fun y => x + r k • y) ⁻¹' Ω := by
    refine (ball_subset_ball ?_).trans (ball_div_subset_preimage (hr k) hR)
    rw [le_div_iff₀ (hr k)]
    rw [lt_div_iff₀ hρ] at hk
    linarith
  exact ⟨(h.rescale x (hr k)).mono isOpen_ball hsub, (hQ.rescale x (hr k)).mono hsub⟩

/-- On the window `B_ρ`, a blow-up is Lipschitz, harmonic on its positivity set, and satisfies
Euler's identity away from `0`. -/
theorem blowup_ball [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR0 : 0 < R) (hR : ball x R ⊆ Ω) {m : ℝ}
    (hm : Tendsto (monotonicityMq (Q x) u χ x) (𝓝[>] 0) (𝓝 m))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsLipHarmonicPos (ball 0 ρ) u₀ ∧ LipschitzOnWith C u₀ (ball 0 ρ) ∧
      ∀ y ∈ ball (0 : Rn n) ρ, y ≠ 0 → 0 < u₀ y → ⟪gradient u₀ y, y⟫ = u₀ y := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (h.eventually_rescale_ball hQ hR0 hR hr hr0 hρ)
  have hw := fun j => (hk₀ (j + k₀) (Nat.le_add_left _ _)).1
  have hQw := fun j => (hk₀ (j + k₀) (Nat.le_add_left _ _)).2
  have hwL := fun j => (hw j).isLipHarmonicPos (hQw j)
  have hL := fun j => (hw j).lipschitzOnWith
  have hconv' : TendstoLocallyUniformlyOn (fun j => oneHomRescale u x (r (j + k₀))) u₀ atTop
      (ball 0 ρ) :=
    tendstoLocallyUniformlyOn_comp_add_nat
      ((tendstoLocallyUniformlyOn_univ.2 hconv).mono (subset_univ _)) k₀
  refine ⟨IsLipHarmonicPos.of_tendstoLocallyUniformlyOn hwL hL hconv',
    lipschitzOnWith_of_tendstoLocallyUniformlyOn hL hconv' (subset_refl _), ?_⟩
  intro y hy hy0 hpos
  refine inner_gradient_eq_of_tendsto_integral_annulus hwL hL hconv'
    (fun s t hs hst htρ => ?_) hy hy0 hpos
  -- The annulus integrals of the rescalings tend to `0`.
  have hrk : ∀ j, 0 < r (j + k₀) := fun j => hr _
  have hrk0 : Tendsto (fun j => r (j + k₀)) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat k₀).2 hr0
  have ht : 0 < t := hs.trans_le hst
  have hbound : ∀ j, ∫ z in ball (0 : Rn n) t \ ball 0 s,
      (oneHomRescale u x (r (j + k₀)) z - ⟪gradient (oneHomRescale u x (r (j + k₀))) z, z⟫) ^ 2 ≤
      t ^ (n + 2) / 2 * (monotonicityMq (Q x) u χ x (r (j + k₀) * t) -
        monotonicityMq (Q x) u χ x (r (j + k₀) * s) + r (j + k₀) * (weissConst n L c C' * (t - s) +
          weissCompConst n L C' * (t + s))) := by
    intro j
    have hA := (hw j).integral_annulus_sub_inner_sq_le (hQw j) (subset_refl _) hs hst htρ
    simp only [sub_zero] at hA
    have hsΩ : ball (0 : Rn n) s ⊆ ball 0 ρ := ball_subset_ball (hst.trans htρ.le)
    have htΩ : ball (0 : Rn n) t ⊆ ball 0 ρ := ball_subset_ball htρ.le
    have h1 := (abs_le.1 ((hw j).abs_monotonicityMq_sub_le (hQw j) ht htΩ)).1
    have h2 := (abs_le.1 ((hw j).abs_monotonicityMq_sub_le (hQw j) hs hsΩ)).2
    rw [smul_zero, add_zero, monotonicityMq_rescale u χ x (Q x) (hr (j + k₀))] at h1 h2
    rw [weissConst_toNNReal_mul (hr (j + k₀)).le] at hA
    rw [weissCompConst_toNNReal_mul (hr (j + k₀)).le] at h1 h2
    have htn : 0 ≤ t ^ (n + 2) / 2 := by positivity
    refine hA.trans (mul_le_mul_of_nonneg_left ?_ htn)
    nlinarith
  have hlim : Tendsto (fun j => t ^ (n + 2) / 2 * (monotonicityMq (Q x) u χ x (r (j + k₀) * t) -
      monotonicityMq (Q x) u χ x (r (j + k₀) * s) + r (j + k₀) * (weissConst n L c C' * (t - s) +
        weissCompConst n L C' * (t + s)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => monotonicityMq (Q x) u χ x (r (j + k₀) * t)) atTop (𝓝 m) :=
      hm.comp (tendsto_nhdsWithin_iff.2 ⟨by simpa using hrk0.mul_const t,
        .of_forall fun j => mul_pos (hr (j + k₀)) ht⟩)
    have h2 : Tendsto (fun j => monotonicityMq (Q x) u χ x (r (j + k₀) * s)) atTop (𝓝 m) :=
      hm.comp (tendsto_nhdsWithin_iff.2 ⟨by simpa using hrk0.mul_const s,
        .of_forall fun j => mul_pos (hr (j + k₀)) hs⟩)
    have := ((h1.sub h2).add (hrk0.mul_const (weissConst n L c C' * (t - s) +
      weissCompConst n L C' * (t + s)))).const_mul (t ^ (n + 2) / 2)
    simpa using this
  exact squeeze_zero (fun j => setIntegral_nonneg (measurableSet_ball.diff measurableSet_ball)
    fun _ _ => sq_nonneg _) hbound hlim

section Blowup

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω)
  {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
  (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop)
include hQ h hx hr hr0 hconv

/-- `blowup_ball` for any window, with the hypotheses of the section. -/
theorem blowup_ball' {ρ : ℝ} (hρ : 0 < ρ) :
    IsLipHarmonicPos (ball 0 ρ) u₀ ∧ LipschitzOnWith C u₀ (ball 0 ρ) ∧
      ∀ y ∈ ball (0 : Rn n) ρ, y ≠ 0 → 0 < u₀ y → ⟪gradient u₀ y, y⟫ = u₀ y := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  have hux := IsVariationalSolution.eq_zero_of_tendstoLocallyUniformly_rescale hr hr0 hconv
  obtain ⟨m, -, hm⟩ := h.exists_tendsto_monotonicityMq_of_eq_zero hQ hx hux
  exact h.blowup_ball hQ hR0 hR hm hr hr0 hconv hρ

/-- Blow-ups are Lipschitz: `u₀` is `C_V`-Lipschitz on `ℝⁿ`. -/
theorem blowup_lipschitzWith : LipschitzWith C u₀ := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have hρ : 0 < ‖y‖ + ‖z‖ + 1 := by positivity
  have hy : y ∈ ball (0 : Rn n) (‖y‖ + ‖z‖ + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg z]
  have hz : z ∈ ball (0 : Rn n) (‖y‖ + ‖z‖ + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg y]
  exact (blowup_ball' hQ h hx hr hr0 hconv hρ).2.1.dist_le_mul y hy z hz

/-- Blow-ups are harmonic on their positivity set. -/
theorem blowup_isLipHarmonicPos : IsLipHarmonicPos univ u₀ where
  isOpen := isOpen_univ
  nonneg y _ :=
    (blowup_ball' hQ h hx hr hr0 hconv (ρ := ‖y‖ + 1) (by positivity)).1.nonneg y
      (by rw [mem_ball_zero_iff]; linarith)
  lipschitzOnWith :=
    ⟨C, fun _ _ _ => (blowup_lipschitzWith hQ h hx hr hr0 hconv).lipschitzOnWith⟩
  harmonicAt y _ hpos :=
    (blowup_ball' hQ h hx hr hr0 hconv (ρ := ‖y‖ + 1) (by positivity)).1.harmonicAt y
      (by rw [mem_ball_zero_iff]; linarith) hpos

/-- **Euler's identity for blow-ups**: `∇u₀(y)·y = u₀(y)` for every `y`. -/
theorem blowup_inner_gradient_eq (y : Rn n) : ⟪gradient u₀ y, y⟫ = u₀ y := by
  have h0 := blowup_isLipHarmonicPos hQ h hx hr hr0 hconv
  rcases (h0.nonneg y trivial).lt_or_eq with hpos | hzero
  · have hy0 : y ≠ 0 := by
      rintro rfl
      rw [IsVariationalSolution.blowup_apply_zero hr hr0 hconv] at hpos
      exact lt_irrefl _ hpos
    exact (blowup_ball' hQ h hx hr hr0 hconv (ρ := ‖y‖ + 1) (by positivity)).2.2 y
      (by rw [mem_ball_zero_iff]; linarith) hy0 hpos
  · rw [h0.gradient_eq_zero_of_eq_zero trivial hzero.symm, inner_zero_left, ← hzero]

/-- **Blow-up limits are homogeneous** of degree one (the last claim of Proposition 3.4, for a
Lipschitz coefficient): `u₀(t y) = t u₀(y)` for `t > 0`. -/
theorem blowup_homogeneous' : ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y := by
  have h0 := blowup_isLipHarmonicPos hQ h hx hr hr0 hconv
  exact homogeneous_of_inner_gradient_eq (blowup_lipschitzWith hQ h hx hr hr0 hconv).continuous
    (fun y => h0.nonneg y trivial)
    (fun y hpos => (h0.harmonicAt y trivial hpos).1.differentiableAt two_ne_zero)
    (fun y _ => blowup_inner_gradient_eq hQ h hx hr hr0 hconv y)

end Blowup

/-! ### The density formula (3.10) -/

theorem integrableOn_chi (h : IsVariationalSolutionQ Ω C Q u χ) {s : ℝ} (hs : ball x s ⊆ Ω) :
    IntegrableOn χ (ball x s) :=
  IntegrableOn.of_bound measure_ball_lt_top (h.aestronglyMeasurable_chi measurableSet_ball hs) 1
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hs hy)))

/-- **Formula (3.10) along a blow-up sequence**: if `u(x) = 0`, `M^{Q(x)}_x(r) → m`, and
`u_{x,r_k} → u₀` locally uniformly, then `Q(x)² r_k^{-n} ∫_{B_{r_k}(x)} χ → m`. -/
theorem tendsto_density_of_tendstoLocallyUniformly [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR0 : 0 < R) (hR : ball x R ⊆ Ω) (hux : u x = 0)
    {m : ℝ} (hm : Tendsto (monotonicityMq (Q x) u χ x) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    Tendsto (fun k => Q x ^ 2 * ((r k ^ n)⁻¹ * ∫ y in ball x (r k), χ y)) atTop (𝓝 m) := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (h.eventually_rescale_ball hQ hR0 hR hr hr0 two_pos)
  obtain ⟨h0, -, heuler⟩ := h.blowup_ball hQ hR0 hR hm hr hr0 hconv two_pos
  set w : ℕ → Rn n → ℝ := fun j => oneHomRescale u x (r (j + k₀)) with hwdef
  set χw : ℕ → Rn n → ℝ := fun j => chiRescale χ x (r (j + k₀)) with hχwdef
  have hw := fun j => (hk₀ (j + k₀) (Nat.le_add_left _ _)).1
  have hQw := fun j => (hk₀ (j + k₀) (Nat.le_add_left _ _)).2
  have hconv' : TendstoLocallyUniformlyOn w u₀ atTop (ball 0 2) :=
    tendstoLocallyUniformlyOn_comp_add_nat
      ((tendstoLocallyUniformlyOn_univ.2 hconv).mono (subset_univ _)) k₀
  have hM' : Tendsto (fun j => monotonicityMq (Q x) (w j) (χw j) 0 1) atTop (𝓝 m) :=
    (tendsto_add_atTop_iff_nat k₀).2 (tendsto_monotonicityMq_rescale u χ x hm hr hr0 one_pos)
  refine (tendsto_add_atTop_iff_nat k₀).1 ?_
  have hwL : ∀ j, IsLipHarmonicPos (ball 0 2) (w j) := fun j => (hw j).isLipHarmonicPos (hQw j)
  have hL : ∀ j y s, ball y s ⊆ ball (0 : Rn n) 2 → LipschitzOnWith C (w j) (ball y s) :=
    fun j => (hw j).lipschitzOnWith
  have hE := integral_norm_gradient_sq_eq_of_inner_gradient_eq h0 heuler one_pos one_lt_two
  rw [one_mul] at hE
  have hB1 : ball (0 : Rn n) 1 ⊆ ball 0 2 := ball_subset_ball one_le_two
  -- `∫_{B_1} |∇w_j|² → ∫_{B_1} |∇u₀|²`.
  have hG : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, ‖gradient (w j) y‖ ^ 2) atTop
      (𝓝 (∫ y in ball (0 : Rn n) 1, ‖gradient u₀ y‖ ^ 2)) := by
    have hK := tendsto_setIntegral_norm_gradient_sub_sq hwL hL hconv'
      (isCompact_closedBall (0 : Rn n) 1) (closedBall_subset_ball one_lt_two)
    refine tendsto_setIntegral_norm_sq_of_tendsto_sub measurableSet_ball measure_ball_lt_top
      (fun _ => measurable_gradient _) (measurable_gradient _) (L := C)
      (fun j y hy => (hw j).norm_gradient_le (hB1 hy))
      (fun y hy => norm_gradient_le_of_tendstoLocallyUniformlyOn hwL hL hconv' (hB1 hy)) ?_
    refine squeeze_zero (fun j => setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _)
      (fun j => ?_) hK
    refine setIntegral_mono_set ?_ (.of_forall fun _ => sq_nonneg _)
      (.of_forall ball_subset_closedBall)
    refine integrableOn_of_abs_le (isCompact_closedBall _ _)
      (((measurable_gradient _).sub (measurable_gradient _)).norm.pow_const 2).aestronglyMeasurable
      (M := (2 * C) ^ 2) fun y hy => ?_
    have hy2 := closedBall_subset_ball one_lt_two hy
    rw [abs_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
    linarith [(hw j).norm_gradient_le hy2,
      norm_gradient_le_of_tendstoLocallyUniformlyOn hwL hL hconv' hy2]
  -- `∫_{∂B_1} w_j² → ∫_{∂B_1} u₀²`.
  have hsph : ∀ ω : sphere (0 : Rn n) 1, (0 : Rn n) + (1 : ℝ) • (ω : Rn n) ∈ ball (0 : Rn n) 2 :=
    fun ω => sphere_subset_closedBall.trans (closedBall_subset_ball one_lt_two)
      (add_smul_mem_sphere zero_le_one ω)
  have hS : Tendsto (fun j => sphereIntegral (fun y => w j y ^ 2) 0 1) atTop
      (𝓝 (sphereIntegral (fun y => u₀ y ^ 2) 0 1)) := by
    simp only [sphereIntegral]
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_of_dominated_convergence (fun _ => (C : ℝ) ^ 2) (fun j => ?_)
      (integrable_const _) (fun j => .of_forall fun ω => ?_) (.of_forall fun ω => ?_)
    · exact (((hw j).continuousOn.pow 2).mono (sphere_subset_closedBall.trans
        (closedBall_subset_ball one_lt_two))).sphereIntegrable zero_le_one |>.aestronglyMeasurable
    · have h1 := (hw j).lipschitzOnWith 0 2 (subset_refl _) |>.dist_le_mul _ (hsph ω) 0
        (mem_ball_self two_pos)
      have hw0 : oneHomRescale u x (r (j + k₀)) 0 = 0 := by simp [hux]
      have hnorm : dist ((0 : Rn n) + (1 : ℝ) • (ω : Rn n)) 0 = 1 := by
        rw [dist_zero_right, zero_add, one_smul]; exact norm_eq_of_mem_sphere ω
      rw [hw0, hnorm, mul_one, Real.dist_eq, sub_zero] at h1
      change ‖oneHomRescale u x (r (j + k₀)) ((0 : Rn n) + (1 : ℝ) • (ω : Rn n)) ^ 2‖ ≤
        (C : ℝ) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    · exact (hconv'.tendsto_at (hsph ω)).pow 2
  -- The identity `Q(x)² r^{-n} ∫_{B_r(x)} χ = M^{Q(x)}_0(w; 1) − ∫_{B_1} |∇w|² + ∫_{∂B_1} w²`.
  have hid : ∀ j, Q x ^ 2 * ((r (j + k₀) ^ n)⁻¹ * ∫ y in ball x (r (j + k₀)), χ y) =
      monotonicityMq (Q x) (w j) (χw j) 0 1 -
        (∫ y in ball (0 : Rn n) 1, ‖gradient (w j) y‖ ^ 2) +
        sphereIntegral (fun y => w j y ^ 2) 0 1 := by
    intro j
    have e1 := setIntegral_chiRescale χ x (hr (j + k₀)) 1
    rw [mul_one] at e1
    have hI1 := (hw j).integrableOn_norm_gradient_sq (hQw j) hB1
    have hI2 := ((hw j).integrableOn_chi hB1).const_mul (Q x ^ 2)
    rw [← e1, monotonicityMq, energyDq, heightH, integral_add hI1 hI2, integral_const_mul]
    simp only [one_pow, inv_one, one_mul]
    ring
  have := ((hM'.sub hG).add hS)
  rw [hE, sub_add_cancel] at this
  exact this.congr fun j => (hid j).symm

/-- **Formula (3.10) with a Lipschitz coefficient**: if `u(x) = 0`, then `M^{Q(x)}_x(u; 0+)` is a
real number `m`, `M^{Q(x)}_x(r) → m`, and `Q(x)² r^{-n} ∫_{B_r(x)} χ → m` as `r → 0+`. Thus
`M(0+) = Q(x)² · (density of {χ = 1} at x)`. -/
theorem tendsto_monotonicityMq_zero [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hux : u x = 0) :
    ∃ m : ℝ, MzeroQ (Q x) u χ x = m ∧
      Tendsto (monotonicityMq (Q x) u χ x) (𝓝[>] 0) (𝓝 m) ∧
      Tendsto (fun r => Q x ^ 2 * ((r ^ n)⁻¹ * ∫ y in ball x r, χ y)) (𝓝[>] 0) (𝓝 m) := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  obtain ⟨m, hm, hMlim⟩ := h.exists_tendsto_monotonicityMq_of_eq_zero hQ hx hux
  refine ⟨m, hm, hMlim, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 (hns.eventually self_mem_nhdsWithin)
  set r : ℕ → ℝ := fun k => ns (k + k₁) with hrdef
  have hr : ∀ k, 0 < r k := fun k => hk₁ _ (Nat.le_add_left _ _)
  have hr0 : Tendsto r atTop (𝓝 0) :=
    (tendsto_nhds_of_tendsto_nhdsWithin hns).comp (tendsto_add_atTop_nat k₁)
  have hρ : Tendsto (fun k => R / r k) atTop atTop := by
    have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
    simpa [div_eq_mul_inv] using (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hR0
  have hLip : ∀ k, LipschitzOnWith C (oneHomRescale u x (r k)) (ball 0 (R / r k)) := fun k =>
    (h.rescale x (hr k)).lipschitzOnWith 0 _ (ball_div_subset_preimage (hr k) hR)
  have hM0 : ∀ k, |oneHomRescale u x (r k) 0| ≤ 0 := fun k => by simp [hux]
  obtain ⟨φ, hφ, u₀, -, hconv⟩ :=
    exists_blowup_subseq hρ (fun k => div_pos hR0 (hr k)) hLip hM0
  exact ⟨fun k => φ k + k₁, h.tendsto_density_of_tendstoLocallyUniformly hQ hR0 hR hux hMlim
    (fun k => hr (φ k)) (hr0.comp hφ.tendsto_atTop) hconv⟩

/-! ### Bounds on `M(0+)` -/

/-- `0 ≤ r^{-n} ∫_{B_r(x)} χ ≤ |B_1|` when `B_r(x) ⊆ Ω`. -/
theorem density_mem_Icc (h : IsVariationalSolutionQ Ω C Q u χ) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ Ω) :
    (r ^ n)⁻¹ * ∫ y in ball x r, χ y ∈ Icc 0 (unitBallVolume n) := by
  have h1 : IntegrableOn (fun _ : Rn n => (1 : ℝ)) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have hle : ∫ y in ball x r, χ y ≤ ∫ y in ball x r, (1 : ℝ) :=
    setIntegral_mono_on (h.integrableOn_chi hball) h1 measurableSet_ball fun y hy =>
      h.chi_le_one (hball hy)
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, volume_ball_toReal x hr] at hle
  have hrn : 0 < r ^ n := pow_pos hr n
  refine ⟨mul_nonneg (inv_nonneg.2 hrn.le)
    (setIntegral_nonneg measurableSet_ball fun y hy => h.chi_nonneg (hball hy)), ?_⟩
  rw [inv_mul_le_iff₀ hrn]
  linarith

/-- `M^{Q(x)}_x(0+) ≤ Q(x)² |B_1|`. -/
theorem MzeroQ_le_sq_mul_unitBallVolume [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) :
    MzeroQ (Q x) u χ x ≤ ((Q x ^ 2 * unitBallVolume n : ℝ) : EReal) := by
  rcases (h.nonneg x hx).lt_or_eq with hpos | hux
  · rw [h.MzeroQ_eq_bot_of_pos hQ hx hpos]; exact bot_le
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  obtain ⟨m, hm, -, hlim⟩ := h.tendsto_monotonicityMq_zero hQ hx hux.symm
  rw [hm, EReal.coe_le_coe_iff]
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hR0] with r hr
  exact mul_le_mul_of_nonneg_left
    (h.density_mem_Icc hr.1 ((ball_subset_ball hr.2.le).trans hR)).2 (sq_nonneg _)

end IsVariationalSolutionQ

end InnerVariational
