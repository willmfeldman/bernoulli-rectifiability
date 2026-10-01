/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Singular.Annuli
public import InnerVariational.Singular.HeightLimit
public import InnerVariational.Blowup.Approx1D
public import InnerVariational.Estimates.Dichotomy.Setup
public import InnerVariational.Frequency.SigmaH
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Estimates.Dichotomy.Rescale
import InnerVariational.Homogeneity.RayCalculus
import InnerVariational.Frequency.Concrete
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.VariationalSolution

/-!
# Lemma 8.5 (1) at a flat point

Proof of Lemma 8.5 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure,
and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). We fix a point
`x ∈ Σ^H` with
* `N_x(u; r) → 1` as `r → 0+` (Theorem 7.2 (3));
* `Σ^H` *flat at `x` in direction `ν`*: for every `p ⊥ ν` and `τ > 0`, the ball `B_{τr}(x + r p)`
  meets `Σ^H` for all small `r` (`IsFlatAt`; a consequence of the approximate tangent plane
  `ν^⊥`, see `Singular/Tangent.lean`),

and show that `v_{x,r} → α(n)|y·ν|` in `W^{1,2}(B_R)` for every `R`
(`tendsto_profile_of_isFlatAt`), in the integral form of `renormalized_tendsto_alpha_ae`.

## Steps

1. `exists_frequencyN_le`: `N_y(u; s) ≤ 1 + η` for `y ∈ Σ^H` near `x` and small `s`
   (continuity of `y ↦ N_y(u; s)` and monotonicity in `s`).
2. `exists_integral_norm_gradient_sq_le`: `∫_{B_s(x)} |∇u|² ≤ K₀ s^n H_x(s)` for small `s`
   (identity (4.11) and Lemma 4.5).
3. `tendsto_heightH_mul_div`: `H_x(c r)/H_x(r) → 1` for every `c > 0` (Lemma 4.3 with `N₊ ↓ 1`).
4. `tendsto_tangential`: the tangential energy `ρ^{-n} H_x(ρ)⁻¹ ∫_{B_ρ \ B_{ρ/2}} |∇u − (∇u·ν)ν|²`
   tends to `0`. Points `a_i ∈ Σ^H` near `x + ρ q_i`, with `q_i` the projections
   of `e_i/20` to `ν^⊥`, are pinched (`Dichotomy.IsPinched`) at level `1 + t`, and
   `∇u·(a_i − x)` is the difference of the homogeneity defects about `x` and about `a_i`.
   As in the proof of Theorem 6.3 (`Dichotomy.exists_tangential_bound`), Lemma 6.2 is not
   needed: both degrees are the same number `1 + t`.
5. `tendsto_annulus_profile`: Theorem 5.3, in the form `approx1D_limit_tendsto_profile`, at the
   scales `ρ_k → 0`, rescaled back: convergence on the annuli `B_{7ρ/8} \ B_{5ρ/8}`.
6. `tendsto_profile_of_isFlatAt`: the assembly of the annuli (`Singular/Annuli.lean`).

## Deviations from the paper's proof

* The paper gets convergence on the annulus `B_1 \ B_{1/2}` and then "a rescaled version of the
  same argument" on every annulus; we apply Theorem 5.3 at every scale and assemble finitely many
  annuli plus a small ball (`tendsto_ball_of_tendsto_annulus`). The change of normalization
  between scales uses `H_x(cr)/H_x(r) → 1`, which the paper leaves implicit.
* The paper's points `y_{i,k}` near `r_k e_i/10` are replaced by points near
  `ρ q_i`, `q_i = (e_i − (e_i·ν)ν)/20`, `i = 1, …, n`, which avoids choosing coordinates with
  `ν = e_n`; the identity `|g − (g·ν)ν|² = Σ_i (20 q_i·g)²` replaces the coordinate sum.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

namespace Singular

variable {n : ℕ} {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- `Σ^H` is *flat at `x` in direction `ν`*: for every `p ⊥ ν` and `τ > 0`, `B_{τr}(x + r p)`
meets `Σ^H` for all small `r > 0`. This is what the approximate tangent plane `ν^⊥` of `Σ^H` at
`x` gives (proof of Lemma 8.5). -/
def IsFlatAt (Ω : Set (Rn n)) (u χ : Rn n → ℝ) (x ν : Rn n) : Prop :=
  ∀ p : Rn n, ⟪p, ν⟫ = 0 → ∀ τ : ℝ, 0 < τ → ∀ᶠ r in 𝓝[>] (0 : ℝ),
    (sigmaH Ω u χ ∩ ball (x + r • p) (τ * r)).Nonempty

/-- An eventual property on `𝓝[>] 0` holds on an interval `(0, r₀)`. -/
theorem exists_Ioo_of_eventually {p : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r) :
    ∃ r₀, 0 < r₀ ∧ ∀ r ∈ Ioo 0 r₀, p r := by
  obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨r₀, hr₀, fun r hr => hsub hr⟩

/-- `r ↦ c r` maps `𝓝[>] 0` to itself for `c > 0`. -/
theorem tendsto_const_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h := ((continuous_const_mul c).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_pos hc hs

/-! ### Linear algebra: the directions `q_i` -/

/-- `q_i = (e_i − (e_i·ν)ν)/20`, the projection of `e_i/20` to `ν^⊥`. -/
def tangentDir (ν : Rn n) (i : Fin n) : Rn n :=
  (1 / 20 : ℝ) • (EuclideanSpace.single i (1 : ℝ) - ⟪EuclideanSpace.single i (1 : ℝ), ν⟫ • ν)

theorem inner_tangentDir {ν : Rn n} (hν : ‖ν‖ = 1) (i : Fin n) : ⟪tangentDir ν i, ν⟫ = 0 := by
  rw [tangentDir, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hν]
  ring

theorem norm_tangentDir_le {ν : Rn n} (hν : ‖ν‖ = 1) (i : Fin n) : ‖tangentDir ν i‖ ≤ 1 / 20 := by
  set e : Rn n := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hsq : ‖e - ⟪e, ν⟫ • ν‖ ^ 2 ≤ 1 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hν, he, mul_one]
    nlinarith [sq_abs ⟪e, ν⟫, sq_nonneg ⟪e, ν⟫]
  have h1 : ‖e - ⟪e, ν⟫ • ν‖ ≤ 1 := by
    nlinarith [norm_nonneg (e - ⟪e, ν⟫ • ν)]
  rw [tangentDir, norm_smul, Real.norm_of_nonneg (by norm_num)]
  nlinarith

/-- The tangential part of `g` is controlled by `⟪w_i, g⟫` for vectors `w_i` close to `ρ q_i`:
`|g − (g·ν)ν|² ≤ Σ_i 800 ρ⁻² ⟪w_i, g⟫² + 800 n t² |g|²` when `|w_i − ρ q_i| ≤ t ρ`. -/
theorem norm_sub_inner_smul_sq_le_sum {ν : Rn n} {ρ t : ℝ} (hρ : 0 < ρ) {w : Fin n → Rn n}
    (hw : ∀ i, ‖w i - ρ • tangentDir ν i‖ ≤ t * ρ) (g : Rn n) :
    ‖g - ⟪g, ν⟫ • ν‖ ^ 2 ≤
      ∑ i, 800 * (ρ⁻¹) ^ 2 * ⟪w i, g⟫ ^ 2 + 800 * n * t ^ 2 * ‖g‖ ^ 2 := by
  have hterm : ∀ i, (g - ⟪g, ν⟫ • ν) i ^ 2 ≤
      800 * (ρ⁻¹) ^ 2 * ⟪w i, g⟫ ^ 2 + 800 * t ^ 2 * ‖g‖ ^ 2 := by
    intro i
    set X := ⟪tangentDir ν i, g⟫ with hXdef
    set d := w i - ρ • tangentDir ν i with hd
    set W := ⟪w i, g⟫
    set D := ⟪d, g⟫
    have hv : (g - ⟪g, ν⟫ • ν) i = 20 * X := by
      rw [hXdef, tangentDir, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
        EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left, real_inner_comm ν g]
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, map_one, one_mul]
      ring
    have hW : W = ρ * X + D := by
      have : w i = ρ • tangentDir ν i + d := by rw [hd]; abel
      simp only [W, D, X, this, inner_add_left, real_inner_smul_left]
    have hD : D ^ 2 ≤ (t * ρ) ^ 2 * ‖g‖ ^ 2 := by
      have h1 : |D| ≤ ‖d‖ * ‖g‖ := abs_real_inner_le_norm d g
      have h2 : ‖d‖ * ‖g‖ ≤ t * ρ * ‖g‖ := mul_le_mul_of_nonneg_right (hw i) (norm_nonneg _)
      rw [← sq_abs D, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    have hX : X = ρ⁻¹ * (W - D) := by
      rw [hW]; field_simp; ring
    have hρ2 : 0 < (ρ⁻¹) ^ 2 := by positivity
    rw [hv, hX]
    have hD' : (ρ⁻¹) ^ 2 * D ^ 2 ≤ t ^ 2 * ‖g‖ ^ 2 := by
      calc (ρ⁻¹) ^ 2 * D ^ 2 ≤ (ρ⁻¹) ^ 2 * ((t * ρ) ^ 2 * ‖g‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hD hρ2.le
        _ = t ^ 2 * ‖g‖ ^ 2 := by field_simp
    nlinarith [sq_nonneg (W + D), mul_nonneg hρ2.le (sq_nonneg (W + D))]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc ∑ i, (g - ⟪g, ν⟫ • ν) i ^ 2 ≤
      ∑ i, (800 * (ρ⁻¹) ^ 2 * ⟪w i, g⟫ ^ 2 + 800 * t ^ 2 * ‖g‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

/-- `absProfile ν 0 = (absProfile ν x)_{x,ρ}`: the profile is one-homogeneous about `x`. -/
theorem absProfile_zero_eq_oneHomRescale (ν x : Rn n) {ρ : ℝ} (hρ : 0 < ρ) :
    absProfile ν 0 = oneHomRescale (absProfile ν x) x ρ := by
  funext y
  rw [oneHomRescale_apply, absProfile_apply, absProfile_apply, sub_zero, add_sub_cancel_left,
    real_inner_smul_left, abs_mul, abs_of_pos hρ, mul_div_cancel_left₀ _ hρ.ne']

/-- `absProfile ν x` is `1`-Lipschitz for a unit vector `ν`. -/
theorem lipschitzWith_absProfile' {ν : Rn n} (hν : ‖ν‖ = 1) (x : Rn n) :
    LipschitzWith 1 (absProfile ν x) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [absProfile_apply, NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  rw [← inner_sub_left, sub_sub_sub_cancel_right]
  exact (abs_real_inner_le_norm _ _).trans (by rw [hν, mul_one])

theorem norm_gradient_absProfile_le {ν : Rn n} (hν : ‖ν‖ = 1) (x y : Rn n) :
    ‖gradient (absProfile ν x) y‖ ≤ 1 := by
  rw [gradient, LinearIsometryEquiv.norm_map]
  simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_absProfile' hν x) (x₀ := y)

section Frequency

variable [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ sigmaH Ω u χ)
  (hN : Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1))
include h hx hN

/-- **Step 1**. For every `η > 0` there is `δ > 0` with `N_y(u; s) ≤ 1 + η`
for all `y ∈ Σ^H ∩ B_δ(x)` and `s ∈ (0, δ]`. -/
theorem exists_frequencyN_le {η : ℝ} (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ y ∈ sigmaH Ω u χ, dist y x < δ → ∀ s, 0 < s → s ≤ δ →
      frequencyN u χ y s ≤ 1 + η := by
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  obtain ⟨s₀, hs₀N, hs₀⟩ := ((hN.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + η))).and
    (Ioo_mem_nhdsGT (half_pos hR))).exists
  have hs₀Ω : closedBall x s₀ ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith [hs₀.2])).trans hRΩ
  have hH := h.heightH_pos hx.2.1 hs₀.1 hs₀Ω
  have hc := h.continuousAt_frequencyN hs₀.1 hs₀Ω hH.ne'
  obtain ⟨δ', hδ', hδ'N⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hs₀N))
  refine ⟨min δ' s₀, lt_min hδ' hs₀.1, fun y hy hyx s hs hsδ => ?_⟩
  have hyΩ : closedBall y s₀ ⊆ Ω := by
    refine (closedBall_subset_closedBall' ?_).trans hRΩ
    have := hyx.trans_le (min_le_right _ _)
    linarith [hs₀.2]
  have h1 : frequencyN u χ y s₀ < 1 + η := hδ'N (hyx.trans_le (min_le_left _ _))
  have hss₀ : s ≤ s₀ := hsδ.trans (min_le_right _ _)
  exact ((h.monotoneOn_frequencyN_of_mem_sigmaH hy hyΩ) ⟨hs, hss₀⟩ ⟨hs₀.1, le_rfl⟩ hss₀).trans
    h1.le

/-- **Step 2**: the energy bound `∫_{B_s(x)} |∇u|² ≤ K₀ s^n H_x(u; s)` for small `s`, from
`N + V = s^{-n} ∫_{B_s} |∇u|² / H` (identity (4.11)), `N_x(s) < 2` and Lemma 4.5. -/
theorem exists_integral_norm_gradient_sq_le :
    ∃ K₀, 0 ≤ K₀ ∧ ∃ r₀, 0 < r₀ ∧ ∀ s ∈ Ioo 0 r₀,
      ∫ y in ball x s, ‖gradient u y‖ ^ 2 ≤ K₀ * (s ^ n * heightH u x s) := by
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  have h2 : Tendsto (fun s => frequencyN u χ x (2 * s)) (𝓝[>] 0) (𝓝 1) :=
    hN.comp (tendsto_const_mul_nhdsGT_zero two_pos)
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), frequencyN u χ x (2 * s) < 2 ∧
      frequencyN u χ x (2 * s) - frequencyN u χ x s < 1 ∧ s < R / 2 := by
    have hd : Tendsto (fun s => frequencyN u χ x (2 * s) - frequencyN u χ x s) (𝓝[>] 0)
        (𝓝 (1 - 1)) := h2.sub hN
    rw [sub_self] at hd
    filter_upwards [h2.eventually (gt_mem_nhds one_lt_two), hd.eventually (gt_mem_nhds one_pos),
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
  have hV := h.volumeV_le_sqrt hx.2.1 hs0 le_rfl (hx.2.2 s hs0 hsΩ) h2sΩ hN2 hδ
  rw [Real.sqrt_one, mul_one] at hV
  have hNs : frequencyN u χ x s ≤ frequencyN u χ x (2 * s) :=
    (h.monotoneOn_frequencyN_of_mem_sigmaH hx h2sΩ) ⟨hs0, by linarith⟩ ⟨by linarith, le_rfl⟩
      (by linarith)
  have hid := h.frequencyN_add_volumeV_eq hs0 (ball_subset_closedBall.trans hsΩ)
  have hH := h.heightH_pos hx.2.1 hs0 hsΩ
  have hsn : 0 < s ^ n := pow_pos hs0 n
  have hle : (s ^ n)⁻¹ * (∫ y in ball x s, ‖gradient u y‖ ^ 2) / heightH u x s ≤ K₀ := by
    rw [← hid, hK₀]
    linarith
  rw [div_le_iff₀ hH, inv_mul_le_iff₀ hsn] at hle
  linarith

/-- Lemma 4.3 with `N₊ ↓ 1`: `H_x(r/2) / H_x(r) → 1`. -/
theorem tendsto_heightH_half_div :
    Tendsto (fun r => heightH u x (r / 2) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  -- `C(1 + θ) → 1` as `θ → 0+`
  have hC : Tendsto (fun θ => Abstract.RadialData.doublingConst (1 + θ)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun θ : ℝ => Real.exp (2 * (1 + θ - 1) + 4 * √(1 + θ - 1)) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Abstract.RadialData.doublingConst] using this
  rw [tendsto_order]
  constructor
  · intro a ha
    -- choose `θ > 0` with `a · C(1 + θ) < 1`
    have hCa : Tendsto (fun θ => a * Abstract.RadialData.doublingConst (1 + θ)) (𝓝[>] 0)
        (𝓝 (a * 1)) := hC.const_mul a
    rw [mul_one] at hCa
    obtain ⟨θ, hθa, hθ⟩ := ((hCa.eventually (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    have hθ0 : (0 : ℝ) < θ := hθ
    filter_upwards [hN.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + θ)),
      Ioo_mem_nhdsGT hR] with r hr hrR
    have hr0 := hrR.1
    have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
    have hH2 := h.heightH_pos hx.2.1 (half_pos hr0)
      ((closedBall_subset_closedBall (by linarith)).trans hrΩ)
    obtain ⟨-, hd⟩ := h.heightH_doubling hx.2.1 (half_pos hr0) (by linarith) (by linarith)
      (hx.2.2 _ (half_pos hr0) ((closedBall_subset_closedBall (by linarith)).trans hrΩ)) hrΩ
      (by linarith : (1 : ℝ) < 1 + θ) hr.le ⟨le_rfl, by linarith⟩
    have hH := h.heightH_pos hx.2.1 hr0 hrΩ
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
    filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
    have hr0 := hrR.1
    have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
    have hH := h.heightH_pos hx.2.1 hr0 hrΩ
    have hle : heightH u x (r / 2) ≤ heightH u x r :=
      (monotoneOn_heightH_of_mem_sigmaH h hx hrΩ) ⟨half_pos hr0, by linarith⟩ ⟨hr0, le_rfl⟩
        (by linarith)
    rw [div_lt_iff₀ hH]
    nlinarith

/-- `H_x(r/2^j) / H_x(r) → 1`. -/
theorem tendsto_heightH_div_pow_div (j : ℕ) :
    Tendsto (fun r => heightH u x (r / 2 ^ j) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  induction j with
  | zero => exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
      have hH := h.heightH_pos hx.2.1 hrR.1 ((closedBall_subset_closedBall hrR.2.le).trans hRΩ)
      simp [div_self hH.ne'])
  | succ j ih =>
    have hj : Tendsto (fun r : ℝ => r / 2 ^ j) (𝓝[>] 0) (𝓝[>] 0) := by
      simpa [div_eq_inv_mul] using tendsto_const_mul_nhdsGT_zero (c := (2 ^ j)⁻¹) (by positivity)
    have h2 := (tendsto_heightH_half_div h hx hN).comp hj
    have := ih.mul h2
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
    have hH := h.heightH_pos hx.2.1 (div_pos hrR.1 (by positivity) : 0 < r / 2 ^ j)
      ((closedBall_subset_closedBall (by
        have : r / 2 ^ j ≤ r := div_le_self hrR.1.le (one_le_pow₀ one_le_two)
        linarith [hrR.2])).trans hRΩ)
    simp only [Function.comp_apply, pow_succ]
    rw [div_div]
    field_simp

/-- **Step 3**: `H_x(c r) / H_x(r) → 1` for every `c > 0`. -/
theorem tendsto_heightH_mul_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r => heightH u x (c * r) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  -- the case `c ≤ 1`
  have hle : ∀ c : ℝ, 0 < c → c ≤ 1 →
      Tendsto (fun r => heightH u x (c * r) / heightH u x r) (𝓝[>] 0) (𝓝 1) := by
    intro c hc hc1
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt c⁻¹ one_lt_two
    have hj' : 1 / 2 ^ j ≤ c := by
      rw [div_le_iff₀ (by positivity)]
      have := (inv_lt_iff_one_lt_mul₀' hc).1 hj
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_heightH_div_pow_div h hx hN j)
      tendsto_const_nhds ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
      have hr0 := hrR.1
      have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
      have hH := h.heightH_pos hx.2.1 hr0 hrΩ
      refine div_le_div_of_nonneg_right ?_ hH.le
      refine (monotoneOn_heightH_of_mem_sigmaH h hx hrΩ) ⟨by positivity, ?_⟩
        ⟨by positivity, by nlinarith⟩ ?_
      · exact div_le_self hr0.le (one_le_pow₀ one_le_two)
      · calc r / 2 ^ j = 1 / 2 ^ j * r := by ring
          _ ≤ c * r := mul_le_mul_of_nonneg_right hj' hr0.le
    · filter_upwards [Ioo_mem_nhdsGT hR] with r hrR
      have hr0 := hrR.1
      have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrR.2.le).trans hRΩ
      have hH := h.heightH_pos hx.2.1 hr0 hrΩ
      rw [div_le_one hH]
      exact (monotoneOn_heightH_of_mem_sigmaH h hx hrΩ) ⟨by positivity, by nlinarith⟩
        ⟨hr0, le_rfl⟩ (by nlinarith)
  rcases le_or_gt c 1 with hc1 | hc1
  · exact hle c hc hc1
  · have h1 := (hle c⁻¹ (inv_pos.2 hc) (inv_le_one_of_one_le₀ hc1.le)).comp
      (tendsto_const_mul_nhdsGT_zero hc)
    have h2 := h1.inv₀ one_ne_zero
    rw [inv_one] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [Function.comp_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, inv_div]

/-- **Step 4**: the renormalized tangential energy on `B_ρ(x) \ B_{ρ/2}(x)`
tends to `0` at a flat point. -/
theorem tendsto_tangential {ν : Rn n} (hν : ‖ν‖ = 1) (hflat : IsFlatAt Ω u χ x ν) :
    Tendsto (fun ρ => (ρ ^ n)⁻¹ * (∫ y in ball x ρ \ ball x (ρ / 2),
      ‖gradient u y - ⟪gradient u y, ν⟫ • ν‖ ^ 2) / heightH u x ρ) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Q, hQ, hcomp⟩ := Dichotomy.exists_heightH_comparison n 2
  obtain ⟨K₀, hK₀, r₁, hr₁, hen⟩ := exists_integral_norm_gradient_sq_le h hx hN
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  set G : ℝ → ℝ := fun t => 3200 * n * (2 ^ (n + 2) * Q * (2 * t + 2 * (2 * t) ^ 2)) +
    800 * n * t ^ 2 * K₀ with hGdef
  have hG : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous G := by rw [hGdef]; fun_prop
    simpa [hGdef] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, htG, ht⟩ := ((hG.eventually (gt_mem_nhds hε)).and
    (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 20))).exists
  have ht0 : 0 < t := ht.1
  obtain ⟨δ, hδ, hδN⟩ := exists_frequencyN_le h hx hN ht0
  have hflat' : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ i,
      (sigmaH Ω u χ ∩ ball (x + ρ • tangentDir ν i) (t * ρ)).Nonempty :=
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
  have e5 : 10 * r' / 2 = ρ / 2 := by rw [hr']; ring
  have e20 : 20 * r' = 2 * ρ := by rw [hr']; ring
  have hΩ50 : ball x (50 * r') ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by rw [hr']; linarith)).trans hRΩ)
  set l := 1 + t with hl
  set εp := 2 * t with hεp
  have hpin : ∀ y ∈ sigmaH Ω u χ, dist y x ≤ r' → Dichotomy.IsPinched u χ x r' l εp y := by
    intro y hy hyx
    have hyΩ : closedBall y r' ⊆ Ω := by
      refine (closedBall_subset_closedBall' ?_).trans hRΩ
      rw [hr'] at hyx ⊢
      linarith
    refine ⟨mem_closedBall.2 hyx, hy.2.1, ⟨r', hr'0, le_rfl, hy.2.2 r' hr'0 hyΩ⟩, ?_, ?_⟩
    · exact hδN y hy (by rw [hr'] at hyx; linarith) (20 * r') (by positivity)
        (by rw [e20]; linarith)
    · have := h.one_le_frequencyN_of_mem_sigmaH hy hr'0 hyΩ
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
  have hpa : ∀ i, Dichotomy.IsPinched u χ x r' l εp (a i) := fun i => hpin _ (ha i).1 (hax i)
  -- the homogeneity defects on `A = B_ρ(x) \ B_{ρ/2}(x)`
  set A : Set (Rn n) := ball x ρ \ ball x (ρ / 2) with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  set F : Rn n → Rn n → ℝ := fun y z => (⟪gradient u z, z - y⟫ - l * u z) ^ 2 with hF
  have hlip := h.lipschitzOnWith x (50 * r') hΩ50
  have hA50 : A ⊆ ball x (50 * r') := sdiff_subset.trans (ball_subset_ball (by rw [hr']; linarith))
  have hFint : ∀ y, IntegrableOn (F y) A := fun y =>
    Dichotomy.integrableOn_sq_inner_gradient_sub_mul_of_lipschitzOnWith hlip hAm hA50 y l
  have hFbound : ∀ y, Dichotomy.IsPinched u χ x r' l εp y →
      ∫ z in A, F y z ≤ (2 * ρ) ^ (n + 2) * (Q * heightH u x ρ) * (εp + 2 * εp ^ 2) := by
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
    have h2 := hy.setIntegral_homogeneity_le h hr'0 hΩ50
    have hH20 : heightH u y (20 * r') ≤ Q * heightH u x ρ := by
      have hc := hcomp Ω C u χ x x y r' l εp h hr'0 hΩ50 (by rw [hl]; linarith [ht.2]) hpx hy
      rw [e10] at hc
      exact hc.2
    have hε0 : 0 ≤ εp + 2 * εp ^ 2 := by positivity
    calc ∫ z in A, F y z ≤ _ := h1
      _ ≤ (20 * r') ^ (n + 2) * heightH u y (20 * r') * (εp + 2 * εp ^ 2) := h2
      _ ≤ (2 * ρ) ^ (n + 2) * (Q * heightH u x ρ) * (εp + 2 * εp ^ 2) := by
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
  have hgint : IntegrableOn (fun z => ‖gradient u z‖ ^ 2) A :=
    (h.integrableOn_norm_gradient_sq (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith)).trans hRΩ))).mono_set sdiff_subset
  have hsumint : ∀ i, IntegrableOn (fun z => 800 * (ρ⁻¹) ^ 2 * (2 * F x z + 2 * F (a i) z)) A :=
    fun i => (((hFint x).const_mul 2).add ((hFint (a i)).const_mul 2)).const_mul _
  have hGpint : IntegrableOn Gp A := by
    rw [hGp]
    exact (integrable_finsetSum _ fun i _ => hsumint i).add (hgint.const_mul _)
  have hle : ∫ z in A, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ ∫ z in A, Gp z :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hGpint
      (Eventually.of_forall hpt)
  set Hx := heightH u x ρ with hHx
  have hH : 0 < Hx := h.heightH_pos hx.2.1 hρ0
    ((closedBall_subset_closedBall (by linarith)).trans hRΩ)
  set P := (2 * ρ) ^ (n + 2) * (Q * Hx) * (εp + 2 * εp ^ 2) with hP
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
    (setIntegral_mono_set (h.integrableOn_norm_gradient_sq (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith)).trans hRΩ)))
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

/-- **Step 5**: Theorem 5.3 (`approx1D_limit_tendsto_profile`) at the scales `ρ → 0`, rescaled
back to `u`. On the annuli `A(ρ) = B_{7ρ/8}(x) \ B_{5ρ/8}(x)`, with the normalization of scale `ρ`,
`u` is `W^{1,2}`-close to `√H_x(ρ) α(n) |(y − x)·ν|`. -/
theorem tendsto_annulus_profile (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1)
    (hflat : IsFlatAt Ω u χ x ν) :
    Tendsto (fun ρ => (∫ y in annulusAt x ρ,
        ‖u y - (√(heightH u x ρ) * alphaN n) • absProfile ν x y‖ ^ 2) /
        (ρ ^ (n + 2) * heightH u x ρ)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ρ => (∫ y in annulusAt x ρ,
        ‖gradient u y - (√(heightH u x ρ) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
        (ρ ^ n * heightH u x ρ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  have htan := tendsto_tangential h hx hN hν hflat
  have h2 : Tendsto (fun ρ => frequencyN u χ x (2 * ρ)) (𝓝[>] 0) (𝓝 1) :=
    hN.comp (tendsto_const_mul_nhdsGT_zero two_pos)
  have hhalf : Tendsto (fun ρ => frequencyN u χ x (1 / 2 * ρ)) (𝓝[>] 0) (𝓝 1) :=
    hN.comp (tendsto_const_mul_nhdsGT_zero (by norm_num))
  set F₁ : ℝ → ℝ := fun ρ => (∫ y in annulusAt x ρ,
    ‖u y - (√(heightH u x ρ) * alphaN n) • absProfile ν x y‖ ^ 2) /
    (ρ ^ (n + 2) * heightH u x ρ) with hF₁
  set F₂ : ℝ → ℝ := fun ρ => (∫ y in annulusAt x ρ,
    ‖gradient u y - (√(heightH u x ρ) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
    (ρ ^ n * heightH u x ρ) with hF₂
  -- the sequential statement
  have key : ∀ ρs : ℕ → ℝ, Tendsto ρs atTop (𝓝[>] 0) →
      (∀ k, 0 < ρs k ∧ 3 * ρs k < R ∧ frequencyN u χ x (2 * ρs k) ≤ 2) →
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
    have hsol' : ∀ k, IsVariationalSolution (ball (0 : Rn n) 3) C (oneHomRescale u x (ρs k))
        (chiRescale χ x (ρs k)) := fun k =>
      (h.rescale x (hρ k)).mono isOpen_ball (hΩ' k)
    have hcl' : ∀ k, (0 : Rn n) ∈ closure {y | 0 < oneHomRescale u x (ρs k) y} := fun k =>
      (Dichotomy.zero_mem_closure_oneHomRescale_iff u x (hρ k)).2 hx.2.1
    have hM' : ∀ k, unitBallVolume n ≤
        monotonicityM (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0 (1 / 2) := fun k => by
      rw [Dichotomy.monotonicityM_oneHomRescale u χ x (hρ k)]
      have := hρ k
      exact hx.2.2 _ (by positivity) ((closedBall_subset_closedBall
        (by nlinarith [(hgood k).2.1])).trans hRΩ)
    have hN' : ∀ k, frequencyN (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0 2 ≤ 2 :=
        fun k => by
      rw [Dichotomy.frequencyN_oneHomRescale u χ x (hρ k), mul_comm]
      exact (hgood k).2.2
    have hδ' : Tendsto (fun k => frequencyN (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0 2 -
        frequencyN (oneHomRescale u x (ρs k)) (chiRescale χ x (ρs k)) 0 (1 / 2)) atTop (𝓝 0) := by
      have := (h2.comp hρs).sub (hhalf.comp hρs)
      rw [sub_self] at this
      refine this.congr fun k => ?_
      simp only [Function.comp_apply, Dichotomy.frequencyN_oneHomRescale u χ x (hρ k)]
      rw [mul_comm (ρs k) 2, mul_comm (ρs k) (1 / 2)]
    have htan' : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (oneHomRescale u x (ρs k)) y -
          ⟪gradient (oneHomRescale u x (ρs k)) y, ν⟫ • ν‖ ^ 2) /
        heightH (oneHomRescale u x (ρs k)) 0 1) atTop (𝓝 0) := by
      refine (htan.comp hρs).congr fun k => ?_
      simp only [Function.comp_apply]
      rw [Dichotomy.setIntegral_tangential_oneHomRescale u x (hρ k) ν, hHρ]
    obtain ⟨-, hL, hG⟩ := approx1D_limit_tendsto_profile hn (ν := fun _ => ν) (fun _ => hν)
      hsol' (closedBall_subset_ball (by norm_num)) hcl' hM' hN' hδ' htan'
    refine ⟨hL.congr fun k => ?_, hG.congr fun k => ?_⟩
    · have hρk := hρ k
      have hH : 0 < heightH u x (ρs k) := h.heightH_pos hx.2.1 hρk
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
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ ∧ 3 * ρ < R ∧ frequencyN u χ x (2 * ρ) ≤ 2 := by
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

/-- **Lemma 8.5 (1) at a flat point**. If `x ∈ Σ^H`, `N_x(u; 0+) = 1` and
`Σ^H` is flat at `x` in direction `ν`, then for every `R > 0`
* `(r^{n+2} H_x(r))⁻¹ ∫_{B_{Rr}(x)} (u − √H_x(r) α(n) |(y−x)·ν|)² → 0`,
* `(r^n H_x(r))⁻¹ ∫_{B_{Rr}(x)} |∇u − √H_x(r) α(n) ∇|(y−x)·ν||² → 0`. -/
theorem tendsto_profile_of_isFlatAt (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1)
    (hflat : IsFlatAt Ω u χ x ν) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun r => (∫ y in ball x (R * r),
        (u y - √(heightH u x r) * alphaN n * absProfile ν x y) ^ 2) /
        (r ^ (n + 2) * heightH u x r)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun r => (∫ y in ball x (R * r),
        ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
        (r ^ n * heightH u x r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Rx, hRx, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  obtain ⟨K₀, hK₀, r₁, hr₁, hen⟩ := exists_integral_norm_gradient_sq_le h hx hN
  obtain ⟨hcons₁, hcons₂⟩ := tendsto_annulus_profile h hx hN hn hν hflat
  set r₀ := min r₁ Rx with hr₀
  have hr₀0 : 0 < r₀ := lt_min hr₁ hRx
  have hsΩ : ∀ s, s ≤ r₀ → closedBall x s ⊆ Ω := fun s hs =>
    (closedBall_subset_closedBall (hs.trans (min_le_right _ _))).trans hRΩ
  have hHpos : ∀ s ∈ Ioo 0 r₀, 0 < heightH u x s := fun s hs =>
    h.heightH_pos hx.2.1 hs.1 (hsΩ s hs.2.le)
  have hHmono : MonotoneOn (heightH u x) (Ioo 0 r₀) :=
    (monotoneOn_heightH_of_mem_sigmaH h hx hRΩ).mono fun s hs =>
      ⟨hs.1, hs.2.le.trans (min_le_right _ _)⟩
  have hratio := fun c (hc : (0 : ℝ) < c) => tendsto_heightH_mul_div h hx hN hc
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
      exact h.integral_ball_sq_le hs.1 (hsΩ s hs.2.le)
    have hq : ∀ s, 0 < s → ∫ y in ball x s, ‖p y‖ ^ 2 ≤ unitBallVolume n * s ^ (n + 2) := by
      intro s hs
      calc ∫ y in ball x s, ‖p y‖ ^ 2 ≤ ∫ _ in ball x s, s ^ 2 :=
            setIntegral_mono_on (hqint' s) (integrableOn_const measure_ball_lt_top.ne)
              measurableSet_ball fun y hy => by
                rw [Real.norm_eq_abs, sq_abs]; exact hpy s y hy
        _ = unitBallVolume n * s ^ (n + 2) := by rw [hvolB s hs]; ring
    have := tendsto_ball_of_tendsto_annulus (E := ℝ) (f := u) (q := p) (m := n + 2)
      (H := heightH u x) (α := alphaN n) (by omega) hr₀0 hHpos hHmono hratio hint (hqint' r₀)
      zero_le_one hf hq hcons₁ hR
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
    exact tendsto_ball_of_tendsto_annulus (E := Rn n) (f := gradient u) (q := gradient p)
      (m := n) (H := heightH u x) (α := alphaN n) (NeZero.ne n) hr₀0 hHpos hHmono hratio hint
      (hqint' r₀) hK₀ hf hq hcons₂ hR

end Frequency

end Singular

end InnerVariational
