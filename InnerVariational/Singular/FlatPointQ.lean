/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Singular.FlatPoint
public import InnerVariational.Blowup.Approx1DQ
public import InnerVariational.Estimates.DichotomyQ.Setup
public import InnerVariational.NaberValtorta.MainFrequencyQ
public import InnerVariational.Frequency.ConcreteQ
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Estimates.Dichotomy.Rescale
import InnerVariational.Homogeneity.RayCalculus
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.RadialQ

/-!
# Lemma 8.5 (1) at a flat point, with a Lipschitz coefficient

The proof of Lemma 8.5 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for a variational
solution with a Lipschitz coefficient `Q` (`QBounds Ω Q L c C'`, `κ = weissKappa L c C'`). We fix
`x ∈ Σ^H_Q` with
* `Ñ_x(u; r) → 1` as `r → 0+`, where `Ñ = N + κ² r²/2` is the modified frequency
  (`modFrequencyN`);
* `Σ^H_Q` *flat at `x` in direction `ν`* (`IsFlatAtQ`),

and show that `v_{x,r} → α(n)|y·ν|` in `W^{1,2}(B_R)` for every `R`
(`tendsto_profile_of_isFlatAtQ`), in the integral form of `Singular.renormalized_tendsto_alpha_ae`.

The steps are those of the constant-coefficient proof (`Singular/FlatPoint.lean`), with the
frequency `N` replaced by `Ñ`:
1. `exists_modFrequencyN_le`: `Ñ_y(u; s) ≤ 1 + η` for `y ∈ Σ^H_Q` near `x` and small `s`.
2. `exists_integral_norm_gradient_sq_leQ`: `∫_{B_s(x)} |∇u|² ≤ K₀ s^n H_x(s)`.
3. `tendsto_heightH_mul_divQ`: `H_x(c r)/H_x(r) → 1`. Here `H_x` is only almost monotone:
   `H_x(s) ≤ e^{κ² r²/8} H_x(r)` for `s ≤ r` (`heightH_le_exp_mul_of_mem_sigmaHQ`), and the factor
   `e^{κ² r²/8}` tends to `1`.
4. `tendsto_tangentialQ`: the tangential energy tends to `0`, with the pinching `IsPinchedQ` in `Ñ`.
5. `tendsto_annulus_profileQ`: Theorem 5.3 with a Lipschitz coefficient
   (`approx1DQ_limit_tendsto_profile`) for the rescalings `u_{x,ρ}` with coefficients
   `Q(x + ρ ·)`, whose constant `κ_ρ = ρ κ` tends to `0`.
6. `tendsto_profile_of_isFlatAtQ`: the assembly of the annuli, with `H_x(s) ≤ 2 H_x(r)` for
   `s ≤ r` in place of monotonicity (`tendsto_ball_of_tendsto_annulus'`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

namespace Singular

variable {n : ℕ} {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-- `Σ^H_Q` is *flat at `x` in direction `ν`*: for every `p ⊥ ν` and `τ > 0`, `B_{τr}(x + r p)`
meets `Σ^H_Q` for all small `r > 0`. -/
def IsFlatAtQ (Ω : Set (Rn n)) (Q u χ : Rn n → ℝ) (x ν : Rn n) : Prop :=
  ∀ p : Rn n, ⟪p, ν⟫ = 0 → ∀ τ : ℝ, 0 < τ → ∀ᶠ r in 𝓝[>] (0 : ℝ),
    (sigmaHQ Ω Q u χ ∩ ball (x + r • p) (τ * r)).Nonempty

/-- A point of `Σ^H_Q` has a radius `R > 0` with `B̄_R(x) ⊆ Ω` and `κ R ≤ 1/2`. -/
theorem exists_radius_of_mem_sigmaHQ (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ sigmaHQ Ω Q u χ) :
    ∃ R, 0 < R ∧ closedBall x R ⊆ Ω ∧ weissKappa L c C' * R ≤ 1 / 2 :=
  NaberValtorta.exists_radius_of_mem h.isOpen hx.1 (hQ.weissKappa_nonneg hx.1)

/-- `e^{κ² r²/8} → 1` as `r → 0+`. -/
theorem tendsto_exp_sq_mul_sq (κ : ℝ) :
    Tendsto (fun r : ℝ => Real.exp (κ ^ 2 * r ^ 2 / 8)) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous fun r : ℝ => Real.exp (κ ^ 2 * r ^ 2 / 8) := by fun_prop
  simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- **Almost monotonicity of `H` on `Σ^H_Q`**: for `0 < s ≤ r ≤ t ≤ R` with `B̄_R(x) ⊆ Ω` and
`κ R ≤ 1/2`, `H_x(s) ≤ e^{κ² t²/8} H_x(r)` (the lower half of Lemma 4.3). -/
theorem heightH_le_exp_mul_of_mem_sigmaHQ [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ sigmaHQ Ω Q u χ) {R : ℝ}
    (hΩ : closedBall x R ⊆ Ω) (hκ : weissKappa L c C' * R ≤ 1 / 2) {s r t : ℝ} (hs : 0 < s)
    (hsr : s ≤ r) (hrt : r ≤ t) (htR : t ≤ R) :
    heightH u x s ≤ Real.exp (weissKappa L c C' ^ 2 * t ^ 2 / 8) * heightH u x r := by
  set κ := weissKappa L c C' with hκdef
  have hk : 0 ≤ κ := hQ.weissKappa_nonneg hx.1
  have hrR : r ≤ R := hrt.trans htR
  have hκs : κ * s ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (hsr.trans hrR) hk).trans hκ
  have hZ := h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hx hs hκs
    ((closedBall_subset_closedBall (hsr.trans hrR)).trans hΩ)
  refine (h.heightH_le_exp_mul hQ hx.2.1 hs hZ hκ hΩ ⟨le_rfl, hsr.trans hrR⟩ ⟨hsr, hrR⟩
    hsr).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (heightH_nonneg u x (hs.le.trans hsr)))
  have h1 : κ ^ 2 * r ^ 2 ≤ κ ^ 2 * t ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs.le.trans hsr) hrt 2) (sq_nonneg κ)
  have h2 : 0 ≤ κ ^ 2 * s ^ 2 := by positivity
  have e : κ ^ 2 * (r ^ 2 - s ^ 2) / 8 = κ ^ 2 * r ^ 2 / 8 - κ ^ 2 * s ^ 2 / 8 := by ring
  rw [e]
  linarith

section Frequency

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
  (hx : x ∈ sigmaHQ Ω Q u χ)
  (hN : Tendsto (modFrequencyN (weissKappa L c C') Q u χ x) (𝓝[>] 0) (𝓝 1))
include hQ h hx hN

/-- **Step 1**. For every `η > 0` there is `δ > 0` with `Ñ_y(u; s) ≤ 1 + η`
for all `y ∈ Σ^H_Q ∩ B_δ(x)` and `s ∈ (0, δ]`. -/
theorem exists_modFrequencyN_le {η : ℝ} (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ y ∈ sigmaHQ Ω Q u χ, dist y x < δ → ∀ s, 0 < s → s ≤ δ →
      modFrequencyN (weissKappa L c C') Q u χ y s ≤ 1 + η := by
  obtain ⟨R, hR, hRΩ, hκR⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  have hk := hQ.weissKappa_nonneg hx.1
  obtain ⟨s₀, hs₀N, hs₀⟩ := ((hN.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + η))).and
    (Ioo_mem_nhdsGT (half_pos hR))).exists
  have hs₀Ω : closedBall x s₀ ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith [hs₀.2])).trans hRΩ
  have hH := h.heightH_pos hQ hx.2.1 hs₀.1 hs₀Ω
  have hc := h.continuousAt_modFrequencyN hQ (weissKappa L c C') hs₀.1 hs₀Ω hH.ne'
  obtain ⟨δ', hδ', hδ'N⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hs₀N))
  refine ⟨min δ' s₀, lt_min hδ' hs₀.1, fun y hy hyx s hs hsδ => ?_⟩
  have hyΩ : closedBall y s₀ ⊆ Ω := by
    refine (closedBall_subset_closedBall' ?_).trans hRΩ
    have := hyx.trans_le (min_le_right _ _)
    linarith [hs₀.2]
  have hκs₀ : weissKappa L c C' * s₀ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by linarith [hs₀.2]) hk).trans hκR
  have h1 : modFrequencyN (weissKappa L c C') Q u χ y s₀ < 1 + η :=
    hδ'N (hyx.trans_le (min_le_left _ _))
  have hss₀ : s ≤ s₀ := hsδ.trans (min_le_right _ _)
  exact ((h.monotoneOn_modFrequencyN_of_mem_sigmaHQ hQ hy hκs₀ hyΩ) ⟨hs, hss₀⟩ ⟨hs₀.1, le_rfl⟩
    hss₀).trans h1.le

/-- **Step 2**: the energy bound `∫_{B_s(x)} |∇u|² ≤ K₀ s^n H_x(u; s)` for small `s`, from
`N + V = s^{-n} ∫_{B_s} |∇u|² / H` (identity (4.11)), `N ≤ Ñ < 2` and Lemma 4.5. -/
theorem exists_integral_norm_gradient_sq_leQ :
    ∃ K₀, 0 ≤ K₀ ∧ ∃ r₀, 0 < r₀ ∧ ∀ s ∈ Ioo 0 r₀,
      ∫ y in ball x s, ‖gradient u y‖ ^ 2 ≤ K₀ * (s ^ n * heightH u x s) := by
  obtain ⟨R, hR, hRΩ, hκR⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  have hk := hQ.weissKappa_nonneg hx.1
  set κ := weissKappa L c C' with hκdef
  have h2 : Tendsto (fun s => modFrequencyN κ Q u χ x (2 * s)) (𝓝[>] 0) (𝓝 1) :=
    hN.comp (tendsto_const_mul_nhdsGT_zero two_pos)
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), modFrequencyN κ Q u χ x (2 * s) < 2 ∧
      modFrequencyN κ Q u χ x (2 * s) - modFrequencyN κ Q u χ x s < 1 / 3 ∧ s < R / 2 := by
    have hd : Tendsto (fun s => modFrequencyN κ Q u χ x (2 * s) - modFrequencyN κ Q u χ x s)
        (𝓝[>] 0) (𝓝 (1 - 1)) := h2.sub hN
    rw [sub_self] at hd
    filter_upwards [h2.eventually (gt_mem_nhds one_lt_two),
      hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)),
      Ioo_mem_nhdsGT (half_pos hR)] with s h1 h2 h3
    exact ⟨h1, h2, h3.2⟩
  obtain ⟨r₀, hr₀, hr₀P⟩ := exists_Ioo_of_eventually hev
  set K₀ := 2 + 2 ^ n * Abstract.RadialData.doublingConst 2 with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have := Abstract.RadialData.doublingConst_pos 2
    positivity
  refine ⟨K₀, hK₀0, r₀, hr₀, fun s hs => ?_⟩
  obtain ⟨hN2, hδ, hsR⟩ := hr₀P s hs
  have hs0 := hs.1
  have h2sΩ : closedBall x (2 * s) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hRΩ
  have hsΩ : closedBall x s ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans h2sΩ
  have hκ2s : κ * (2 * s) ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (by linarith) hk).trans hκR
  have hκs : κ * s ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (by linarith) hk).trans hκR
  have hZ := h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hx hs0 hκs hsΩ
  have hV := h.weightedVolumeV_le_sqrt hQ hx.2.1 hs0 le_rfl hZ hκ2s h2sΩ hN2 hδ
  rw [show (3 : ℝ) * (1 / 3) = 1 by norm_num, Real.sqrt_one, mul_one] at hV
  have hNs : modFrequencyN κ Q u χ x s ≤ modFrequencyN κ Q u χ x (2 * s) :=
    (h.monotoneOn_modFrequencyN_of_mem_sigmaHQ hQ hx hκ2s h2sΩ) ⟨hs0, by linarith⟩
      ⟨by linarith, le_rfl⟩ (by linarith)
  have hNle := weightedFrequencyN_le_modFrequencyN κ Q u χ x s
  have hid := h.weightedFrequencyN_add_weightedVolumeV hQ (ball_subset_closedBall.trans hsΩ)
  have hH := h.heightH_pos hQ hx.2.1 hs0 hsΩ
  have hsn : 0 < s ^ n := pow_pos hs0 n
  have hle : (s ^ n)⁻¹ * (∫ y in ball x s, ‖gradient u y‖ ^ 2) / heightH u x s ≤ K₀ := by
    rw [← hid, hK₀]
    linarith
  rw [div_le_iff₀ hH, inv_mul_le_iff₀ hsn] at hle
  linarith

/-- Lemma 4.3 with `N₊ ↓ 1`: `H_x(r/2) / H_x(r) → 1`. -/
theorem tendsto_heightH_half_divQ :
    Tendsto (fun r => heightH u x (r / 2) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨R, hR, hRΩ, hκR⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  have hk := hQ.weissKappa_nonneg hx.1
  have hC : Tendsto (fun θ => Abstract.RadialData.doublingConst (1 + θ)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun θ : ℝ => Real.exp (2 * (1 + θ - 1) + 4 * √(1 + θ - 1)) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Abstract.RadialData.doublingConst] using this
  rw [tendsto_order]
  constructor
  · intro a ha
    have hCa : Tendsto (fun θ => a * Abstract.RadialData.doublingConst (1 + θ)) (𝓝[>] 0)
        (𝓝 (a * 1)) := hC.const_mul a
    rw [mul_one] at hCa
    obtain ⟨θ, hθa, hθ⟩ := ((hCa.eventually (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have hθ0 : (0 : ℝ) < θ := hθ
    filter_upwards [hN.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + θ)),
      Ioo_mem_nhdsGT hR] with r hr hrR
    have hr0 := hrR.1
    have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
    have hκr : weissKappa L c C' * r ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hrR.2.le hk).trans hκR
    have hκr2 : weissKappa L c C' * (r / 2) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (by linarith) hk).trans hκr
    have hr2Ω : closedBall x (r / 2) ⊆ Ω :=
      (closedBall_subset_closedBall (by linarith)).trans hrΩ
    have hH2 := h.heightH_pos hQ hx.2.1 (half_pos hr0) hr2Ω
    obtain ⟨-, hd⟩ := h.heightH_doubling hQ hx.2.1 (half_pos hr0) (by linarith) (by linarith)
      (h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hx (half_pos hr0) hκr2 hr2Ω) hκr hrΩ
      (by linarith : (1 : ℝ) < 1 + θ) hr.le ⟨le_rfl, by linarith⟩
    have hH := h.heightH_pos hQ hx.2.1 hr0 hrΩ
    rw [lt_div_iff₀ hH]
    rcases le_or_gt a 0 with ha0 | ha0
    · have : a * heightH u x r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hH.le
      linarith
    · calc a * heightH u x r ≤ a * (Abstract.RadialData.doublingConst (1 + θ) *
            heightH u x (r / 2)) := mul_le_mul_of_nonneg_left hd ha0.le
        _ = (a * Abstract.RadialData.doublingConst (1 + θ)) * heightH u x (r / 2) := by ring
        _ < 1 * heightH u x (r / 2) := mul_lt_mul_of_pos_right hθa hH2
        _ = heightH u x (r / 2) := one_mul _
  · intro b hb
    filter_upwards [Ioo_mem_nhdsGT hR,
      (tendsto_exp_sq_mul_sq (weissKappa L c C')).eventually (gt_mem_nhds hb)] with r hrR hE
    have hr0 := hrR.1
    have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
    have hH := h.heightH_pos hQ hx.2.1 hr0 hrΩ
    have hle := heightH_le_exp_mul_of_mem_sigmaHQ hQ h hx hRΩ hκR (half_pos hr0)
      (by linarith : r / 2 ≤ r) le_rfl hrR.2.le
    rw [div_lt_iff₀ hH]
    exact hle.trans_lt (mul_lt_mul_of_pos_right hE hH)

/-- `H_x(r/2^j) / H_x(r) → 1`. -/
theorem tendsto_heightH_div_pow_divQ (j : ℕ) :
    Tendsto (fun r => heightH u x (r / 2 ^ j) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨R, hR, hRΩ, -⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  induction j with
  | zero => exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
      have hH := h.heightH_pos hQ hx.2.1 hrR.1
        ((closedBall_subset_closedBall hrR.2.le).trans hRΩ)
      simp [div_self hH.ne'])
  | succ j ih =>
    have hj : Tendsto (fun r : ℝ => r / 2 ^ j) (𝓝[>] 0) (𝓝[>] 0) := by
      simpa [div_eq_inv_mul] using tendsto_const_mul_nhdsGT_zero (c := (2 ^ j)⁻¹) (by positivity)
    have h2 := (tendsto_heightH_half_divQ hQ h hx hN).comp hj
    have := ih.mul h2
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
    have hH := h.heightH_pos hQ hx.2.1 (div_pos hrR.1 (by positivity) : 0 < r / 2 ^ j)
      ((closedBall_subset_closedBall (by
        have : r / 2 ^ j ≤ r := div_le_self hrR.1.le (one_le_pow₀ one_le_two)
        linarith [hrR.2])).trans hRΩ)
    simp only [Function.comp_apply, pow_succ]
    rw [div_div]
    field_simp

/-- **Step 3**: `H_x(c r) / H_x(r) → 1` for every `c > 0`. -/
theorem tendsto_heightH_mul_divQ {c₀ : ℝ} (hc : 0 < c₀) :
    Tendsto (fun r => heightH u x (c₀ * r) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨R, hR, hRΩ, hκR⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  have hE := tendsto_exp_sq_mul_sq (weissKappa L c C')
  have hle : ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 →
      Tendsto (fun r => heightH u x (c₀ * r) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
    intro c₀ hc hc1
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt c₀⁻¹ one_lt_two
    have hj' : 1 / 2 ^ j ≤ c₀ := by
      rw [div_le_iff₀ (by positivity)]
      have := (inv_lt_iff_one_lt_mul₀' hc).1 hj
      linarith
    have hlow := (tendsto_heightH_div_pow_divQ hQ h hx hN j).div hE one_ne_zero
    rw [div_one] at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hE ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
      have hr0 := hrR.1
      have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
      have hH := h.heightH_pos hQ hx.2.1 hr0 hrΩ
      have hEpos := Real.exp_pos (weissKappa L c C' ^ 2 * r ^ 2 / 8)
      have hj2 : r / 2 ^ j ≤ c₀ * r := by
        calc r / 2 ^ j = 1 / 2 ^ j * r := by ring
          _ ≤ c₀ * r := mul_le_mul_of_nonneg_right hj' hr0.le
      have h1 := heightH_le_exp_mul_of_mem_sigmaHQ hQ h hx hRΩ hκR (by positivity) hj2
        (by nlinarith) hrR.2.le
      rw [Pi.div_apply, div_div, div_le_div_iff₀ (by positivity) hH]
      nlinarith
    · filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
      have hr0 := hrR.1
      have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
      have hH := h.heightH_pos hQ hx.2.1 hr0 hrΩ
      rw [div_le_iff₀ hH]
      exact heightH_le_exp_mul_of_mem_sigmaHQ hQ h hx hRΩ hκR (by positivity) (by nlinarith)
        le_rfl hrR.2.le
  rcases le_or_gt c₀ 1 with hc1 | hc1
  · exact hle c₀ hc hc1
  · have h1 := (hle c₀⁻¹ (inv_pos.2 hc) (inv_le_one_of_one_le₀ hc1.le)).comp
      (tendsto_const_mul_nhdsGT_zero hc)
    have h2 := h1.inv₀ one_ne_zero
    rw [inv_one] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [Function.comp_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, inv_div]

/-- **Step 4**: the renormalized tangential energy on `B_ρ(x) \ B_{ρ/2}(x)`
tends to `0` at a flat point. -/
theorem tendsto_tangentialQ {ν : Rn n} (hν : ‖ν‖ = 1) (hflat : IsFlatAtQ Ω Q u χ x ν) :
    Tendsto (fun ρ => (ρ ^ n)⁻¹ * (∫ y in ball x ρ \ ball x (ρ / 2),
      ‖gradient u y - ⟪gradient u y, ν⟫ • ν‖ ^ 2) / heightH u x ρ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Kc, hKc, hcomp⟩ := Dichotomy.exists_heightH_comparisonQ n 2
  obtain ⟨K₀, hK₀, r₁, hr₁, hen⟩ := exists_integral_norm_gradient_sq_leQ hQ h hx hN
  obtain ⟨R, hR, hRΩ, hκR⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  have hk := hQ.weissKappa_nonneg hx.1
  set G : ℝ → ℝ := fun t => 3200 * n * (2 ^ (n + 2) * Kc * (4 * (2 * t) + 144 * (2 * t) ^ 2)) +
    800 * n * t ^ 2 * K₀ with hGdef
  have hG : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous G := by rw [hGdef]; fun_prop
    simpa [hGdef] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, htG, ht⟩ := ((hG.eventually (gt_mem_nhds hε)).and
    (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 20))).exists
  have ht0 : 0 < t := ht.1
  obtain ⟨δ, hδ, hδN⟩ := exists_modFrequencyN_le hQ h hx hN ht0
  have hflat' : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ i,
      (sigmaHQ Ω Q u χ ∩ ball (x + ρ • tangentDir ν i) (t * ρ)).Nonempty :=
    eventually_all.2 fun i => hflat _ (inner_tangentDir hν i) t ht0
  have hρ₀ : 0 < min (min r₁ (R / 5)) (δ / 2) := lt_min (lt_min hr₁ (by positivity)) (by positivity)
  filter_upwards [hflat', Ioo_mem_nhdsGT hρ₀] with ρ hfl hρ
  have hρ0 : 0 < ρ := hρ.1
  have hρ1 : ρ < r₁ := hρ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hρR : ρ < R / 5 := hρ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hρδ : ρ < δ / 2 := hρ.2.trans_le (min_le_right _ _)
  choose a ha using hfl
  -- the scale `r' = ρ/10` of the pinching
  set r' := ρ / 10 with hr'
  have hr'0 : 0 < r' := by positivity
  have e10 : 10 * r' = ρ := by rw [hr']; ring
  have e20 : 20 * r' = 2 * ρ := by rw [hr']; ring
  have hΩ50 : ball x (50 * r') ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by rw [hr']; linarith)).trans hRΩ)
  have hκ50 : weissKappa L c C' * (50 * r') ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by rw [hr']; linarith) hk).trans hκR
  have hκr' : weissKappa L c C' * r' ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by rw [hr']; linarith) hk).trans hκR
  set l := 1 + t with hl
  set εp := 2 * t with hεp
  have hpin : ∀ y ∈ sigmaHQ Ω Q u χ, dist y x ≤ r' →
      Dichotomy.IsPinchedQ (weissKappa L c C') Q u χ x r' l εp y := by
    intro y hy hyx
    have hyΩ : closedBall y r' ⊆ Ω := by
      refine (closedBall_subset_closedBall' ?_).trans hRΩ
      rw [hr'] at hyx ⊢
      linarith
    refine ⟨mem_closedBall.2 hyx, hy.2.1,
      ⟨r', hr'0, le_rfl, h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hy hr'0 hκr' hyΩ⟩, ?_, ?_⟩
    · exact hδN y hy (by rw [hr'] at hyx; linarith) (20 * r') (by positivity)
        (by rw [e20]; linarith)
    · have := (h.frequency_bounds_of_mem_sigmaHQ hQ hy hr'0 hκr' hyΩ).2
      rw [hl, hεp]
      linarith
  have hdist : ∀ i, ‖(a i - x) - ρ • tangentDir ν i‖ ≤ t * ρ := by
    intro i
    have := (ha i).2
    rw [mem_ball, dist_eq_norm] at this
    rw [sub_sub]
    exact this.le
  have hax : ∀ i, dist (a i) x ≤ r' := by
    intro i
    have h1 := hdist i
    have h2 : ‖ρ • tangentDir ν i‖ ≤ ρ / 20 := by
      rw [norm_smul, Real.norm_of_nonneg hρ0.le]
      have := norm_tangentDir_le hν i
      nlinarith
    rw [dist_eq_norm]
    calc ‖a i - x‖ = ‖((a i - x) - ρ • tangentDir ν i) + ρ • tangentDir ν i‖ := by
          rw [sub_add_cancel]
      _ ≤ t * ρ + ρ / 20 := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ r' := by rw [hr']; nlinarith [ht.2]
  have hpx := hpin x hx (by rw [dist_self]; exact hr'0.le)
  have hpa : ∀ i, Dichotomy.IsPinchedQ (weissKappa L c C') Q u χ x r' l εp (a i) :=
    fun i => hpin _ (ha i).1 (hax i)
  -- the homogeneity defects on `A = B_ρ(x) \ B_{ρ/2}(x)`
  set A : Set (Rn n) := ball x ρ \ ball x (ρ / 2) with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  set F : Rn n → Rn n → ℝ := fun y z => (⟪gradient u z, z - y⟫ - l * u z) ^ 2 with hF
  have hlip := h.lipschitzOnWith x (50 * r') hΩ50
  have hA50 : A ⊆ ball x (50 * r') := sdiff_subset.trans (ball_subset_ball (by rw [hr']; linarith))
  have hFint : ∀ y, IntegrableOn (F y) A := fun y =>
    Dichotomy.integrableOn_sq_inner_gradient_sub_mul_of_lipschitzOnWith hlip hAm hA50 y l
  have hFbound : ∀ y, Dichotomy.IsPinchedQ (weissKappa L c C') Q u χ x r' l εp y →
      ∫ z in A, F y z ≤
        (2 * ρ) ^ (n + 2) * (Kc * heightH u x ρ) * (4 * εp + 144 * εp ^ 2) := by
    intro y hy
    have hyx := mem_closedBall.1 hy.mem_closedBall
    have hAy : A ⊆ ball y (20 * r') \ ball y r' := by
      intro z hz
      have hz1 : dist z x < ρ := hz.1
      have hz2 : ¬ dist z x < ρ / 2 := hz.2
      have t1 := dist_triangle z x y
      have t2 := dist_triangle z y x
      rw [dist_comm x y] at t1
      refine ⟨mem_ball.2 (by rw [hr'] at hyx ⊢; linarith), fun hzy => hz2 ?_⟩
      have : dist z y < r' := hzy
      rw [hr'] at hyx this
      linarith
    have hann : ball y (20 * r') \ ball y r' ⊆ ball x (50 * r') := by
      intro z hz
      have hz1 : dist z y < 20 * r' := hz.1
      have := dist_triangle z y x
      exact mem_ball.2 (by linarith)
    have h1 : ∫ z in A, F y z ≤ ∫ z in ball y (20 * r') \ ball y r', F y z :=
      setIntegral_mono_set
        (Dichotomy.integrableOn_sq_inner_gradient_sub_mul_of_lipschitzOnWith hlip
          (measurableSet_ball.diff measurableSet_ball) hann _ l)
        (Eventually.of_forall fun z => sq_nonneg _) hAy.eventuallyLE
    have h2 := hy.setIntegral_homogeneity_le hQ h hr'0 hκ50 hΩ50
    have hH20 : heightH u y (20 * r') ≤ Kc * heightH u x ρ := by
      have hc := hcomp Ω C Q u χ L c C' x x y r' l εp hQ h hr'0 hκ50 hΩ50
        (by rw [hl]; linarith [ht.2]) hpx hy
      rw [e10] at hc
      exact hc.2
    have hε0 : 0 ≤ 4 * εp + 144 * εp ^ 2 := by positivity
    calc ∫ z in A, F y z ≤ _ := h1
      _ ≤ (20 * r') ^ (n + 2) * heightH u y (20 * r') * (4 * εp + 144 * εp ^ 2) := h2
      _ ≤ (2 * ρ) ^ (n + 2) * (Kc * heightH u x ρ) * (4 * εp + 144 * εp ^ 2) := by
          rw [← e20]
          gcongr
  -- the pointwise bound
  set w : Fin n → Rn n := fun i => a i - x with hw
  set Gp : Rn n → ℝ := fun z => ∑ i, 800 * (ρ⁻¹) ^ 2 * (2 * F x z + 2 * F (a i) z) +
    800 * n * t ^ 2 * ‖gradient u z‖ ^ 2 with hGp
  have hpt : ∀ z, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ Gp z := by
    intro z
    refine (norm_sub_inner_smul_sq_le_sum hρ0 (w := w) hdist (gradient u z)).trans ?_
    rw [hGp]
    dsimp only
    gcongr with i
    have key : ⟪w i, gradient u z⟫ = (⟪gradient u z, z - x⟫ - l * u z) -
        (⟪gradient u z, z - a i⟫ - l * u z) := by
      rw [hw]
      dsimp only
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm (gradient u z) (a i),
        real_inner_comm (gradient u z) x]
      ring
    rw [key, hF]
    dsimp only
    nlinarith [sq_nonneg ((⟪gradient u z, z - x⟫ - l * u z) +
      (⟪gradient u z, z - a i⟫ - l * u z))]
  have hρΩ : ball x ρ ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hRΩ)
  have hgint : IntegrableOn (fun z => ‖gradient u z‖ ^ 2) A :=
    (h.integrableOn_norm_gradient_sq hQ hρΩ).mono_set sdiff_subset
  have hsumint : ∀ i, IntegrableOn (fun z => 800 * (ρ⁻¹) ^ 2 * (2 * F x z + 2 * F (a i) z)) A :=
    fun i => (((hFint x).const_mul 2).add ((hFint (a i)).const_mul 2)).const_mul _
  have hGpint : IntegrableOn Gp A := by
    rw [hGp]
    exact (integrable_finsetSum _ fun i _ => hsumint i).add (hgint.const_mul _)
  have hle : ∫ z in A, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ ∫ z in A, Gp z :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hGpint
      (Eventually.of_forall hpt)
  set Hx := heightH u x ρ with hHx
  have hH : 0 < Hx := h.heightH_pos hQ hx.2.1 hρ0
    ((closedBall_subset_closedBall (by linarith)).trans hRΩ)
  set P := (2 * ρ) ^ (n + 2) * (Kc * Hx) * (4 * εp + 144 * εp ^ 2) with hP
  have hGval : ∫ z in A, Gp z = ∑ i, 800 * (ρ⁻¹) ^ 2 *
      (2 * (∫ z in A, F x z) + 2 * ∫ z in A, F (a i) z) +
      800 * n * t ^ 2 * ∫ z in A, ‖gradient u z‖ ^ 2 := by
    rw [hGp]
    dsimp only
    rw [integral_add (integrable_finsetSum _ fun i _ => hsumint i) (hgint.const_mul _),
      integral_finsetSum _ fun i _ => hsumint i, integral_const_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_add ((hFint x).const_mul 2) ((hFint (a i)).const_mul 2),
      integral_const_mul, integral_const_mul]
  have hgrad : ∫ z in A, ‖gradient u z‖ ^ 2 ≤ K₀ * (ρ ^ n * Hx) :=
    (setIntegral_mono_set (h.integrableOn_norm_gradient_sq hQ hρΩ)
      (Eventually.of_forall fun z => sq_nonneg _) (sdiff_subset (s := ball x ρ)).eventuallyLE).trans
      (hen ρ ⟨hρ0, hρ1⟩)
  have hsum : ∑ i : Fin n, 800 * (ρ⁻¹) ^ 2 * (2 * (∫ z in A, F x z) + 2 * ∫ z in A, F (a i) z) ≤
      n * (800 * (ρ⁻¹) ^ 2 * (4 * P)) := by
    calc ∑ i : Fin n, 800 * (ρ⁻¹) ^ 2 * (2 * (∫ z in A, F x z) + 2 * ∫ z in A, F (a i) z) ≤
        ∑ _i : Fin n, 800 * (ρ⁻¹) ^ 2 * (4 * P) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 := hFbound x hpx
          have h2 := hFbound (a i) (hpa i)
          linarith
      _ = n * (800 * (ρ⁻¹) ^ 2 * (4 * P)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have htot : ∫ z in A, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ G t * (ρ ^ n * Hx) := by
    refine hle.trans ?_
    rw [hGval]
    have h3 := mul_le_mul_of_nonneg_left hgrad (by positivity : (0 : ℝ) ≤ 800 * n * t ^ 2)
    have e : n * (800 * (ρ⁻¹) ^ 2 * (4 * P)) + 800 * n * t ^ 2 * (K₀ * (ρ ^ n * Hx)) =
        G t * (ρ ^ n * Hx) := by
      rw [hP, hGdef, hεp]
      dsimp only
      field_simp
      ring
    linarith
  have hnn : 0 ≤ (ρ ^ n)⁻¹ * (∫ y in A, ‖gradient u y - ⟪gradient u y, ν⟫ • ν‖ ^ 2) / Hx :=
    div_nonneg (mul_nonneg (by positivity)
      (setIntegral_nonneg hAm fun _ _ => sq_nonneg _)) hH.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hρn : 0 < ρ ^ n := pow_pos hρ0 n
  calc (ρ ^ n)⁻¹ * (∫ y in A, ‖gradient u y - ⟪gradient u y, ν⟫ • ν‖ ^ 2) / Hx ≤
      (ρ ^ n)⁻¹ * (G t * (ρ ^ n * Hx)) / Hx := by gcongr
    _ = G t := by field_simp
    _ < ε := htG

/-- **Step 5**: Theorem 5.3 with a Lipschitz coefficient (`approx1DQ_limit_tendsto_profile`) at
the scales `ρ → 0`, rescaled back to `u`. On the annuli `A(ρ) = B_{7ρ/8}(x) \ B_{5ρ/8}(x)`, with
the normalization of scale `ρ`, `u` is `W^{1,2}`-close to `√H_x(ρ) α(n) |(y − x)·ν|`. -/
theorem tendsto_annulus_profileQ (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1)
    (hflat : IsFlatAtQ Ω Q u χ x ν) :
    Tendsto (fun ρ => (∫ y in annulusAt x ρ,
        ‖u y - (√(heightH u x ρ) * alphaN n) • absProfile ν x y‖ ^ 2) /
        (ρ ^ (n + 2) * heightH u x ρ)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ρ => (∫ y in annulusAt x ρ,
        ‖gradient u y - (√(heightH u x ρ) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
        (ρ ^ n * heightH u x ρ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hR, hRΩ, hκR⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  have hk := hQ.weissKappa_nonneg hx.1
  set κ := weissKappa L c C' with hκdef
  have htan := tendsto_tangentialQ hQ h hx hN hν hflat
  have h2 : Tendsto (fun ρ => modFrequencyN κ Q u χ x (2 * ρ)) (𝓝[>] 0) (𝓝 1) :=
    hN.comp (tendsto_const_mul_nhdsGT_zero two_pos)
  have hhalf : Tendsto (fun ρ => modFrequencyN κ Q u χ x (1 / 2 * ρ)) (𝓝[>] 0) (𝓝 1) :=
    hN.comp (tendsto_const_mul_nhdsGT_zero (by norm_num))
  set F₁ : ℝ → ℝ := fun ρ => (∫ y in annulusAt x ρ,
    ‖u y - (√(heightH u x ρ) * alphaN n) • absProfile ν x y‖ ^ 2) /
    (ρ ^ (n + 2) * heightH u x ρ) with hF₁
  set F₂ : ℝ → ℝ := fun ρ => (∫ y in annulusAt x ρ,
    ‖gradient u y - (√(heightH u x ρ) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
    (ρ ^ n * heightH u x ρ) with hF₂
  -- the sequential statement
  have key : ∀ ρs : ℕ → ℝ, Tendsto ρs atTop (𝓝[>] 0) →
      (∀ k, 0 < ρs k ∧ 3 * ρs k < R ∧ modFrequencyN κ Q u χ x (2 * ρs k) ≤ 2) →
      Tendsto (F₁ ∘ ρs) atTop (𝓝 0) ∧ Tendsto (F₂ ∘ ρs) atTop (𝓝 0) := by
    intro ρs hρs hgood
    have hρ : ∀ k, 0 < ρs k := fun k => (hgood k).1
    have hHρ : ∀ k, heightH (oneHomRescale u x (ρs k)) 0 1 = heightH u x (ρs k) := fun k => by
      have := Dichotomy.heightH_oneHomRescale u x (hρ k) 1
      rwa [mul_one] at this
    have hΩ' : ∀ k, ball (0 : Rn n) 3 ⊆ (fun y => x + ρs k • y) ⁻¹' Ω := by
      intro k y hy
      refine hRΩ ?_
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (hρ k).le]
      have := mem_ball_zero_iff.1 hy
      nlinarith [(hgood k).2.1, hρ k]
    have hsol' : ∀ k, IsVariationalSolutionQ (ball (0 : Rn n) 3) C (fun y => Q (x + ρs k • y))
        (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) := fun k =>
      (h.rescale x (hρ k)).mono isOpen_ball (hΩ' k)
    have hQ' : ∀ k, QBounds (ball (0 : Rn n) 3) (fun y => Q (x + ρs k • y))
        (Real.toNNReal (ρs k) * L) c C' := fun k => (hQ.rescale x (hρ k)).mono (hΩ' k)
    have hκk : ∀ k, weissKappa (Real.toNNReal (ρs k) * L) c C' = ρs k * κ := fun k =>
      weissKappa_toNNReal_mul (hρ k).le L c C'
    have hκ2 : ∀ k, weissKappa (Real.toNNReal (ρs k) * L) c C' * 2 ≤ 1 / 2 := fun k => by
      rw [hκk]
      have := mul_le_mul_of_nonneg_left
        (show 2 * ρs k ≤ R by linarith [(hgood k).2.1, hρ k]) hk
      linarith
    have hcl' : ∀ k, (0 : Rn n) ∈ closure {y | 0 < oneHomRescale u x (ρs k) y} := fun k =>
      (Dichotomy.zero_mem_closure_oneHomRescale_iff u x (hρ k)).2 hx.2.1
    have hZ' : ∀ k, 0 ≤ modMonotonicityM (weissKappa (Real.toNNReal (ρs k) * L) c C')
        (fun y => Q (x + ρs k • y)) (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0
          (1 / 2) := fun k => by
      rw [hκk, modMonotonicityM_oneHomRescale Q u χ x (hρ k)]
      have := hρ k
      exact h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hx (by positivity)
        ((mul_le_mul_of_nonneg_left (by linarith [(hgood k).2.1]) hk).trans hκR)
        ((closedBall_subset_closedBall (by nlinarith [(hgood k).2.1])).trans hRΩ)
    have hN' : ∀ k, modFrequencyN (weissKappa (Real.toNNReal (ρs k) * L) c C')
        (fun y => Q (x + ρs k • y)) (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0 2 ≤
          2 := fun k => by
      rw [hκk, modFrequencyN_oneHomRescale Q u χ x (hρ k), mul_comm]
      exact (hgood k).2.2
    have hδ' : Tendsto (fun k => modFrequencyN (weissKappa (Real.toNNReal (ρs k) * L) c C')
        (fun y => Q (x + ρs k • y)) (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0 2 -
        modFrequencyN (weissKappa (Real.toNNReal (ρs k) * L) c C')
        (fun y => Q (x + ρs k • y)) (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0
          (1 / 2)) atTop (𝓝 0) := by
      have := (h2.comp hρs).sub (hhalf.comp hρs)
      rw [sub_self] at this
      refine this.congr fun k => ?_
      simp only [Function.comp_apply, hκk, modFrequencyN_oneHomRescale Q u χ x (hρ k)]
      rw [mul_comm (ρs k) 2, mul_comm (ρs k) (1 / 2)]
    have htan' : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (oneHomRescale u x (ρs k)) y -
          ⟪gradient (oneHomRescale u x (ρs k)) y, ν⟫ • ν‖ ^ 2) /
        heightH (oneHomRescale u x (ρs k)) 0 1) atTop (𝓝 0) := by
      refine (htan.comp hρs).congr fun k => ?_
      simp only [Function.comp_apply]
      rw [Dichotomy.setIntegral_tangential_oneHomRescale u x (hρ k) ν, hHρ]
    obtain ⟨-, hL, hG⟩ := approx1DQ_limit_tendsto_profile hn (ν := fun _ => ν) (fun _ => hν)
      hQ' hsol' (closedBall_subset_ball (by norm_num)) hκ2 hcl' hZ' hN' hδ' htan'
    refine ⟨hL.congr fun k => ?_, hG.congr fun k => ?_⟩
    · have hρk := hρ k
      have hH : 0 < heightH u x (ρs k) := h.heightH_pos hQ hx.2.1 hρk
        ((closedBall_subset_closedBall (by nlinarith [(hgood k).2.1])).trans hRΩ)
      rw [hHρ]
      simp only [Function.comp_apply, hF₁, annulusAt]
      generalize ρs k = ρ at hρk hH ⊢
      set c := √(heightH u x ρ) * alphaN n with hc
      have e1 : ∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
          (oneHomRescale u x ρ y - √(heightH u x ρ) * alphaN n * absProfile ν 0 y) ^ 2 =
          ∫ y in annulus (5 / 8) (7 / 8),
            (fun z => (ρ⁻¹) ^ 2 * ‖u z - c • absProfile ν x z‖ ^ 2) (x + ρ • y) := by
        rw [setIntegral_congr_set (Dichotomy.ball_diff_closedBall_ae_eq 0 (by norm_num) (7 / 8)),
          annulus_def]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        simp only [oneHomRescale_apply, absProfile_apply, sub_zero, add_sub_cancel_left,
          real_inner_smul_left, Real.norm_eq_abs, sq_abs, smul_eq_mul, abs_mul, abs_of_pos hρk]
        field_simp
        ring
      have e2 := setIntegral_annulus_comp_add_smul
        (fun z => (ρ⁻¹) ^ 2 * ‖u z - c • absProfile ν x z‖ ^ 2) x hρk (5 / 8) (7 / 8)
      rw [e1, e2, integral_const_mul]
      field_simp
      ring
    · have hρk := hρ k
      rw [hHρ]
      simp only [Function.comp_apply, hF₂, annulusAt]
      generalize ρs k = ρ at hρk ⊢
      set c := √(heightH u x ρ) * alphaN n with hc
      have e1 : ∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
          ‖gradient (oneHomRescale u x ρ) y - c • gradient (absProfile ν 0) y‖ ^ 2 =
          ∫ y in annulus (5 / 8) (7 / 8),
            (fun z => ‖gradient u z - c • gradient (absProfile ν x) z‖ ^ 2) (x + ρ • y) := by
        rw [setIntegral_congr_set (Dichotomy.ball_diff_closedBall_ae_eq 0 (by norm_num) (7 / 8)),
          annulus_def]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [Dichotomy.gradient_oneHomRescale u x hρk.ne', absProfile_zero_eq_oneHomRescale ν x hρk,
          Dichotomy.gradient_oneHomRescale _ x hρk.ne']
      have e2 := setIntegral_annulus_comp_add_smul
        (fun z => ‖gradient u z - c • gradient (absProfile ν x) z‖ ^ 2) x hρk (5 / 8) (7 / 8)
      rw [e1, e2, inv_mul_eq_div, div_div]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ 3 * ρ < R ∧ modFrequencyN κ Q u χ x (2 * ρ) ≤ 2 := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < R / 3),
      h2.eventually (ge_mem_nhds one_lt_two)] with ρ hρ hρR hN2
    exact ⟨hρ, by linarith [hρR.2], hN2⟩
  have hseq : ∀ ρs : ℕ → ℝ, Tendsto ρs atTop (𝓝[>] 0) →
      Tendsto (F₁ ∘ ρs) atTop (𝓝 0) ∧ Tendsto (F₂ ∘ ρs) atTop (𝓝 0) := by
    intro ρs hρs
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hρs.eventually hev)
    have hK' := key (fun k => ρs (k + K)) ((tendsto_add_atTop_iff_nat K).2 hρs)
      (fun k => hK _ (Nat.le_add_left _ _))
    exact ⟨(tendsto_add_atTop_iff_nat K).1 hK'.1, (tendsto_add_atTop_iff_nat K).1 hK'.2⟩
  exact ⟨tendsto_iff_seq_tendsto.2 fun ρs hρs => (hseq ρs hρs).1,
    tendsto_iff_seq_tendsto.2 fun ρs hρs => (hseq ρs hρs).2⟩

/-- **Lemma 8.5 (1) at a flat point**, with a Lipschitz coefficient. If `x ∈ Σ^H_Q`,
`Ñ_x(u; 0+) = 1` and `Σ^H_Q` is flat at `x` in direction `ν`, then for every `R > 0`
* `(r^{n+2} H_x(r))⁻¹ ∫_{B_{Rr}(x)} (u − √H_x(r) α(n) |(y−x)·ν|)² → 0`,
* `(r^n H_x(r))⁻¹ ∫_{B_{Rr}(x)} |∇u − √H_x(r) α(n) ∇|(y−x)·ν||² → 0`. -/
theorem tendsto_profile_of_isFlatAtQ (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1)
    (hflat : IsFlatAtQ Ω Q u χ x ν) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun r => (∫ y in ball x (R * r),
        (u y - √(heightH u x r) * alphaN n * absProfile ν x y) ^ 2) /
        (r ^ (n + 2) * heightH u x r)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun r => (∫ y in ball x (R * r),
        ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
        (r ^ n * heightH u x r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Rx, hRx, hRΩ, hκR⟩ := exists_radius_of_mem_sigmaHQ hQ h hx
  have hk := hQ.weissKappa_nonneg hx.1
  obtain ⟨K₀, hK₀, r₁, hr₁, hen⟩ := exists_integral_norm_gradient_sq_leQ hQ h hx hN
  obtain ⟨hcons₁, hcons₂⟩ := tendsto_annulus_profileQ hQ h hx hN hn hν hflat
  set r₀ := min r₁ Rx with hr₀
  have hr₀0 : 0 < r₀ := lt_min hr₁ hRx
  have hsΩ : ∀ s, s ≤ r₀ → closedBall x s ⊆ Ω := fun s hs =>
    (closedBall_subset_closedBall (hs.trans (min_le_right _ _))).trans hRΩ
  have hHpos : ∀ s ∈ Ioo 0 r₀, 0 < heightH u x s := fun s hs =>
    h.heightH_pos hQ hx.2.1 hs.1 (hsΩ s hs.2.le)
  have hHmono : ∀ s ∈ Ioo 0 r₀, ∀ r ∈ Ioo 0 r₀, s ≤ r →
      heightH u x s ≤ 2 * heightH u x r := by
    intro s hs r hr hsr
    have hrR : r ≤ Rx := hr.2.le.trans (min_le_right _ _)
    have h1 := heightH_le_exp_mul_of_mem_sigmaHQ hQ h hx hRΩ hκR hs.1 hsr le_rfl hrR
    have h2 := (exp_sq_mul_sq_div_eight_le hk hr.1.le
      ((mul_le_mul_of_nonneg_left hrR hk).trans hκR)).trans exp_one_div_thirtyTwo_le_two
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (heightH_nonneg u x hr.1.le))
  have hratio := fun c (hc : (0 : ℝ) < c) => tendsto_heightH_mul_divQ hQ h hx hN hc
  set p := absProfile ν x with hpdef
  have hp : Continuous p := by rw [hpdef]; unfold absProfile; fun_prop
  have hpy : ∀ s, ∀ y ∈ ball x s, p y ^ 2 ≤ s ^ 2 := by
    intro s y hy
    rw [hpdef, absProfile_apply, sq_abs]
    have h1 : |⟪y - x, ν⟫| ≤ ‖y - x‖ := (abs_real_inner_le_norm _ _).trans (by rw [hν, mul_one])
    have h2 : ‖y - x‖ < s := by rw [← dist_eq_norm]; exact hy
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2.le) 2
  have hvolB : ∀ s, 0 < s → ∀ c : ℝ, ∫ _ in ball x s, c = c * (s ^ n * unitBallVolume n) := by
    intro s hs c
    rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hs, mul_comm]
  constructor
  · -- the `L²` part: `E = ℝ`, `f = u`, `q = p`
    have hint : ∀ k : ℝ, IntegrableOn (fun y => ‖u y - k • p y‖ ^ 2) (ball x r₀) := by
      intro k
      have hu' := h.continuousOn.mono (hsΩ r₀ le_rfl)
      have hc : ContinuousOn (fun y => ‖u y - k • p y‖ ^ 2) (closedBall x r₀) := by fun_prop
      exact (hc.integrableOn_compact (isCompact_closedBall x r₀)).mono_set ball_subset_closedBall
    have hqint' : ∀ s, IntegrableOn (fun y => ‖p y‖ ^ 2) (ball x s) := fun s =>
      ((show Continuous fun y => ‖p y‖ ^ 2 by fun_prop).continuousOn.integrableOn_compact
        (isCompact_closedBall x s)).mono_set
        ball_subset_closedBall
    have hf : ∀ s ∈ Ioo 0 r₀, ∫ y in ball x s, ‖u y‖ ^ 2 ≤ 1 * (s ^ (n + 2) * heightH u x s) := by
      intro s hs
      simp only [Real.norm_eq_abs, sq_abs, one_mul]
      exact h.integral_ball_sq_le hQ hs.1 (hsΩ s hs.2.le)
    have hq : ∀ s, 0 < s → ∫ y in ball x s, ‖p y‖ ^ 2 ≤ unitBallVolume n * s ^ (n + 2) := by
      intro s hs
      calc ∫ y in ball x s, ‖p y‖ ^ 2 ≤ ∫ _ in ball x s, s ^ 2 :=
            setIntegral_mono_on (hqint' s) (integrableOn_const measure_ball_lt_top.ne)
              measurableSet_ball fun y hy => by
                rw [Real.norm_eq_abs, sq_abs]; exact hpy s y hy
        _ = unitBallVolume n * s ^ (n + 2) := by rw [hvolB s hs]; ring
    have := tendsto_ball_of_tendsto_annulus' (E := ℝ) (f := u) (q := p) (m := n + 2)
      (H := heightH u x) (α := alphaN n) zero_le_two (by omega) hr₀0 hHpos hHmono hratio hint
      (hqint' r₀) zero_le_one hf hq hcons₁ hR
    refine this.congr fun r => ?_
    simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul]
  · -- the gradient part: `E = ℝⁿ`, `f = ∇u`, `q = ∇p`
    have hgp : ∀ y, ‖gradient p y‖ ≤ 1 := fun y => norm_gradient_absProfile_le hν x y
    have hint : ∀ k : ℝ, IntegrableOn (fun y => ‖gradient u y - k • gradient p y‖ ^ 2)
        (ball x r₀) := by
      intro k
      refine IntegrableOn.of_bound measure_ball_lt_top
        (((measurable_gradient u).sub ((measurable_gradient p).const_smul k)).norm.pow_const
          2).aestronglyMeasurable (((C : ℝ) + |k|) ^ 2)
        ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
      have hyΩ : y ∈ Ω := hsΩ r₀ le_rfl (ball_subset_closedBall hy)
      have h1 : ‖gradient u y - k • gradient p y‖ ≤ (C : ℝ) + |k| := by
        refine (norm_sub_le _ _).trans (add_le_add (h.norm_gradient_le hyΩ) ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hgp y)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hqint' : ∀ s, IntegrableOn (fun y => ‖gradient p y‖ ^ 2) (ball x s) := fun s =>
      IntegrableOn.of_bound measure_ball_lt_top
        ((measurable_gradient p).norm.pow_const 2).aestronglyMeasurable 1
        (.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have := hgp y
          nlinarith [norm_nonneg (gradient p y)])
    have hq : ∀ s, 0 < s → ∫ y in ball x s, ‖gradient p y‖ ^ 2 ≤ unitBallVolume n * s ^ n := by
      intro s hs
      calc ∫ y in ball x s, ‖gradient p y‖ ^ 2 ≤ ∫ _ in ball x s, (1 : ℝ) :=
            setIntegral_mono_on (hqint' s) (integrableOn_const measure_ball_lt_top.ne)
              measurableSet_ball fun y _ => by
                have := hgp y
                nlinarith [norm_nonneg (gradient p y)]
        _ = unitBallVolume n * s ^ n := by rw [hvolB s hs]; ring
    have hf : ∀ s ∈ Ioo 0 r₀, ∫ y in ball x s, ‖gradient u y‖ ^ 2 ≤
        K₀ * (s ^ n * heightH u x s) := fun s hs =>
      hen s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
    exact tendsto_ball_of_tendsto_annulus' (E := Rn n) (f := gradient u) (q := gradient p)
      (m := n) (H := heightH u x) (α := alphaN n) zero_le_two (NeZero.ne n) hr₀0 hHpos hHmono
      hratio hint (hqint' r₀) hK₀ hf hq hcons₂ hR

end Frequency

end Singular

end InnerVariational
