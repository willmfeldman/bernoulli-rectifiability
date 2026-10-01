/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.RenormalizationQ
public import InnerVariational.Blowup.Profile
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InnerVariational.Blowup.Limit
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Sobolev.Lipschitz

/-!
# Frequency blow-ups with a Lipschitz coefficient: Theorem 5.3

Theorem 5.3 of Kriventsov–Weiss (full reference below) for variational solutions with Lipschitz
coefficients `Q_k`, in the form used by the proof of Theorem 6.3.

## Setting

`(u_k, χ_k)` are variational solutions on `Ω ⊇ B̄_2` for coefficients `Q_k` with
`QBounds Ω Q_k L_k c_k C'_k`, and `κ_k = 2 C'_k L_k / c_k²` (`weissKappa`) with `2 κ_k ≤ 1/2`.
We assume
* `0 ∈ closure {u_k > 0}` and `Z_0(u_k; 1/2) ≥ 0` (the shifted Weiss energy, `modMonotonicityM`),
* `Ñ_0(u_k; 2) ≤ N₊` and `Ñ_0(u_k; 2) − Ñ_0(u_k; 1/2) → 0`, where `Ñ = N + κ² s² / 2` is the
  modified frequency (`modFrequencyN`).

The pinching forces `κ_k → 0` (`tendsto_weissKappa_of_pinching`): `(15/32) κ_k² ≤ Ñ(2) − Ñ(1/2)`.
Hence the renormalized sequence `v_k = u_k / √H_0(u_k; 1)` satisfies the hypotheses of the
compactness results of `Blowup/Limit.lean` and `Blowup/Profile.lean`, which do not involve the
coefficient: the errors in the frequency identities are bounded by `κ_k` times `V_0(u_k; 1)`,
which is bounded by Lemma 4.5. In particular the blow-up limits solve the constant-coefficient
problem. This file only proves the analogue of `renormalized_properties`
(`renormalizedQ_properties`) and then applies `eq_one_of_renormalized` and
`tendsto_profile_of_renormalized`.

## Main statements

* `approx1DQ_limit_frequency_eq_one`: if the tangential energy
  `∫_A |∇u_k − ⟪∇u_k, ν_k⟫ν_k|² / H_0(u_k; 1)` tends to `0` on `A = B_1 \ B̄_{1/2}`, then
  `Ñ_0(u_k; 1/2) → 1` and `N_0(u_k; 1/2) → 1`.
* `approx1DQ_limit_tendsto_profile`: the strong `W^{1,2}` convergence to the one-dimensional
  profile `α(n)|y·ν_k|` on `B_{7/8} \ B̄_{5/8}`.

## Differences from the paper

The paper treats `Q ≡ 1`. With a Lipschitz coefficient, the hypotheses are stated for the
modified frequency `Ñ` and the shifted Weiss energy `Z`. As in `Blowup/Approx1D.lean`, the
direction `ν_k` may depend on `k` and the conclusions hold along the whole sequence.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

section Sequences

variable [NeZero n] {Ω : Set (Rn n)} {C_V : ℕ → ℝ≥0} {Q u χ : ℕ → Rn n → ℝ} {L : ℕ → ℝ≥0}
  {c C' : ℕ → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n}

/-- **The pinching forces `κ_k → 0`.** -/
theorem tendsto_weissKappa_of_pinching (hQ : ∀ k, QBounds Ω (Q k) (L k) (c k) (C' k))
    (hsol : ∀ k, IsVariationalSolutionQ Ω (C_V k) (Q k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω) (hκ : ∀ k, weissKappa (L k) (c k) (C' k) * 2 ≤ 1 / 2)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hZ : ∀ k, 0 ≤ modMonotonicityM (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
    (hδ : Tendsto (fun k =>
      modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 -
        modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0)) :
    Tendsto (fun k => weissKappa (L k) (c k) (C' k)) atTop (𝓝 0) := by
  have hk0 : ∀ k, 0 ≤ weissKappa (L k) (c k) (C' k) := fun k =>
    IsVariationalSolutionQ.weissKappa_nonneg' (hQ k) hΩ
  have hs : Tendsto (fun k => √(32 / 15 *
      (modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 -
        modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))))
      atTop (𝓝 0) := by
    have h := hδ.const_mul (32 / 15)
    rw [mul_zero] at h
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h
    rwa [Real.sqrt_zero] at h2
  refine squeeze_zero hk0 (fun k => ?_) hs
  have h1 := IsVariationalSolutionQ.weissKappa_sq_le_modFrequencyN_sub (hQ k) (hsol k) hΩ (hκ k)
    (hcl k) (hZ k)
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  linarith

/-- **The renormalized sequence `v_k = u_k / √H_0(u_k; 1)` and its properties**, with Lipschitz
coefficients: the conclusions of `renormalized_properties`, under the hypotheses of
`approx1DQ_limit_frequency_eq_one` and `Ñ_0(u_k; 1/2) → N_∞`. -/
theorem renormalizedQ_properties (hQ : ∀ k, QBounds Ω (Q k) (L k) (c k) (C' k))
    (hsol : ∀ k, IsVariationalSolutionQ Ω (C_V k) (Q k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω) (hκ : ∀ k, weissKappa (L k) (c k) (C' k) * 2 ≤ 1 / 2)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hZ : ∀ k, 0 ≤ modMonotonicityM (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k =>
      modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 -
        modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0))
    {Ninf : ℝ} (hlim : Tendsto (fun k =>
      modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2)) atTop (𝓝 Ninf))
    (v : ℕ → Rn n → ℝ) (hv : ∀ k y, v k y = (√(heightH (u k) 0 1))⁻¹ * u k y) :
    (∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1)) ∧
    (∃ C, ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤ C) ∧
    (∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y) ∧
    Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      (⟪gradient (v k) y, y⟫ - Ninf * v k y) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) atTop (𝓝 0) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ ≤ ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), v k y ^ 2) ∧
    (∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ e : Rn n,
      Tendsto (fun k => ∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y) atTop (𝓝 0)) ∧
    (∀ η : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ k,
      ∫ y, ‖gradient (v k) y‖ ^ 2 * η y = -∫ y, v k y * ⟪gradient (v k) y, gradient η y⟫) ∧
    (Ninf = 1 → Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), v k y ^ 2)
      atTop (𝓝 (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)))) := by
  obtain rfl : v = fun k y => (√(heightH (u k) 0 1))⁻¹ * u k y := funext fun k => funext (hv k)
  clear hv
  set κ : ℕ → ℝ := fun k => weissKappa (L k) (c k) (C' k) with hκdef
  set Nt : ℕ → ℝ → ℝ := fun k s => modFrequencyN (κ k) (Q k) (u k) (χ k) 0 s with hNt
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  have hAB : A ⊆ ball (0 : Rn n) 1 := sdiff_subset
  have hB1 : ball (0 : Rn n) 1 ⊆ Ω :=
    ball_subset_closedBall.trans (closedBall_one_subset_of_two hΩ)
  have hcB1 : closedBall (0 : Rn n) 1 ⊆ Ω := closedBall_one_subset_of_two hΩ
  set H : ℕ → ℝ := fun k => heightH (u k) 0 1 with hHdef
  have hH : ∀ k, 0 < H k := fun k =>
    IsVariationalSolutionQ.heightH_one_pos (hQ k) (hsol k) hΩ (hcl k)
  have hk0 : ∀ k, 0 ≤ κ k := fun k =>
    IsVariationalSolutionQ.weissKappa_nonneg' (hQ k) hΩ
  have hk4 : ∀ k, κ k ≤ 1 / 4 := fun k => by have := hκ k; simp only [hκdef]; linarith
  have hκt : Tendsto κ atTop (𝓝 0) :=
    tendsto_weissKappa_of_pinching hQ hsol hΩ hκ hcl hZ hδ
  have hfreq := fun k => IsVariationalSolutionQ.modFrequencyN_half_le_one_le_two (hQ k) (hsol k)
    hΩ (hκ k) (hcl k) (hZ k)
  have hNinf : 1 ≤ Ninf := ge_of_tendsto' hlim fun k => (hfreq k).1
  have hNp : 1 < Nplus + 1 := by linarith [(hfreq 0).1, (hfreq 0).2.1, (hfreq 0).2.2, hN 0]
  -- `Ñ_0(u_k; 1) → N_∞`.
  have hlim1 : Tendsto (fun k => Nt k 1) atTop (𝓝 Ninf) := by
    have h2 : Tendsto (fun k => Nt k (1 / 2) + (Nt k 2 - Nt k (1 / 2))) atTop (𝓝 Ninf) := by
      simpa using hlim.add hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim h2 (fun k => (hfreq k).2.1)
      fun k => ?_
    have := (hfreq k).2.2
    simp only [hNt]
    linarith
  -- `V_0(u_k; 1)` is bounded and tends to `0` (Lemma 4.5).
  set K := Abstract.RadialData.doublingConst (Nplus + 1) with hK
  have hKpos : 0 < K := Abstract.RadialData.doublingConst_pos _
  have hV : ∀ k δ, Nt k 2 - Nt k 1 < δ →
      weightedVolumeV (Q k) (u k) (χ k) 0 1 ≤ 2 ^ n * K * √(3 * δ) := fun k δ hδ' =>
    IsVariationalSolutionQ.weightedVolumeV_one_le (hQ k) (hsol k) hΩ (hκ k) (hcl k) (hZ k)
      (by linarith [hN k]) hδ'
  have hVnn : ∀ k, 0 ≤ weightedVolumeV (Q k) (u k) (χ k) 0 1 := fun k =>
    (hsol k).weightedVolumeV_nonneg zero_le_one hB1
  have hVbd : ∀ k, weightedVolumeV (Q k) (u k) (χ k) 0 1 ≤ 2 ^ n * K * √(3 * Nplus) := fun k =>
    hV k Nplus (by linarith [(hfreq k).1, (hfreq k).2.1, (hfreq k).2.2, hN k])
  have hV0 : Tendsto (fun k => weightedVolumeV (Q k) (u k) (χ k) 0 1) atTop (𝓝 0) := by
    have hd : Tendsto (fun k : ℕ => Nt k 2 - Nt k (1 / 2) + 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using hδ.add tendsto_one_div_add_atTop_nhds_zero_nat
    have hs : Tendsto (fun k : ℕ => 2 ^ n * K * √(3 * (Nt k 2 - Nt k (1 / 2) +
        1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      have h := hd.const_mul 3
      rw [mul_zero] at h
      have h2 := ((Real.continuous_sqrt.tendsto 0).comp h).const_mul (2 ^ n * K)
      rwa [Real.sqrt_zero, mul_zero] at h2
    refine squeeze_zero hVnn (fun k => hV k _ ?_) hs
    have := (hfreq k).2.1
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  -- The renormalized sequence.
  set cc : ℕ → ℝ := fun k => (√(H k))⁻¹ with hc
  have hc2 : ∀ k, cc k ^ 2 = 1 / H k := fun k => by
    simp only [hc, inv_pow, Real.sq_sqrt (hH k).le, one_div]
  have hc0 : ∀ k, 0 ≤ cc k := fun k => inv_nonneg.2 (Real.sqrt_nonneg _)
  set v : ℕ → Rn n → ℝ := fun k y => cc k * u k y with hv
  have hgrad : ∀ k y, gradient (v k) y = cc k • gradient (u k) y := fun k y =>
    gradient_const_mul (cc k) (u k) y
  -- Lipschitz bound.
  have hLip : ∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1) := fun k =>
    ⟨_, ((lipschitzWith_smul (cc k)).comp_lipschitzOnWith ((hsol k).lipschitzOnWith 0 2
      (ball_subset_closedBall.trans hΩ))).mono (closedBall_subset_ball (by norm_num))⟩
  -- `W^{1,2}(B_1)` bound.
  have hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤
      1 + (Nplus + 2 ^ n * K * √(3 * Nplus)) := by
    intro k
    have hpt : ∀ y, v k y ^ 2 + ‖gradient (v k) y‖ ^ 2 =
        (u k y ^ 2 + ‖gradient (u k) y‖ ^ 2) / H k := fun y => by
      rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 k)]
      simp only [hv]
      rw [mul_pow, mul_pow, hc2]
      ring
    simp_rw [hpt]
    rw [integral_div, integral_add ((hsol k).integrableOn_sq_of_closedBall hcB1)
      ((hsol k).integrableOn_norm_gradient_sq (hQ k) hB1),
      IsVariationalSolutionQ.integral_ball_one_norm_gradient_sq_eq (hQ k) (hsol k) hΩ (hH k),
      div_le_iff₀ (hH k)]
    have h1 := IsVariationalSolutionQ.integral_ball_one_sq_le (hQ k) (hsol k) hΩ
    have hN1 : weightedFrequencyN (Q k) (u k) (χ k) 0 1 ≤ Nplus :=
      ((weightedFrequencyN_le_modFrequencyN _ _ _ _ _ _).trans (hfreq k).2.2).trans (hN k)
    have h2 : weightedFrequencyN (Q k) (u k) (χ k) 0 1 + weightedVolumeV (Q k) (u k) (χ k) 0 1 ≤
        Nplus + 2 ^ n * K * √(3 * Nplus) := add_le_add hN1 (hVbd k)
    have h3 := mul_le_mul_of_nonneg_right h2 (hH k).le
    simp only [hHdef] at h3 ⊢
    nlinarith
  -- Nonnegativity.
  have hnn : ∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y := fun k y hy =>
    mul_nonneg (hc0 k) ((hsol k).nonneg y (hB1 hy))
  -- Euler defect.
  have hE : Tendsto (fun k => ∫ y in A, (⟪gradient (v k) y, y⟫ - Ninf * v k y) ^ 2) atTop
      (𝓝 0) := by
    have hR : Tendsto (fun k => Real.exp (κ k ^ 2 / 8) * (2 * (Nt k 1 - Nt k (1 / 2)) +
        2 * max ((Nt k 1 - Ninf) ^ 2) ((Nt k (1 / 2) - κ k ^ 2 / 2 - Ninf) ^ 2))) atTop
        (𝓝 0) := by
      have he : Tendsto (fun k => Real.exp (κ k ^ 2 / 8)) atTop (𝓝 1) := by
        have h : Tendsto (fun k => κ k ^ 2 / 8) atTop (𝓝 0) := by
          simpa using (hκt.pow 2).div_const 8
        have h2 := (Real.continuous_exp.tendsto 0).comp h
        rwa [Real.exp_zero] at h2
      have h1 := hlim1.sub hlim
      have h2 := ((hlim1.sub_const Ninf).pow 2).max
        ((((hlim.sub ((hκt.pow 2).div_const 2)).sub_const Ninf)).pow 2)
      have h3 := he.mul ((h1.const_mul 2).add (h2.const_mul 2))
      simpa using h3
    refine squeeze_zero (fun k => setIntegral_nonneg (isOpen_ball.sdiff isClosed_closedBall
      |>.measurableSet) fun y _ => sq_nonneg _) (fun k => ?_) hR
    have hpt : ∀ y, (⟪gradient (v k) y, y⟫ - Ninf * v k y) ^ 2 =
        (⟪gradient (u k) y, y⟫ - Ninf * u k y) ^ 2 / H k := fun y => by
      rw [hgrad, inner_smul_left]
      simp only [hv, conj_trivial]
      rw [show cc k * ⟪gradient (u k) y, y⟫ - Ninf * (cc k * u k y) =
        cc k * (⟪gradient (u k) y, y⟫ - Ninf * u k y) by ring, mul_pow, hc2]
      ring
    simp_rw [hpt]
    rw [integral_div, div_le_iff₀ (hH k)]
    have := IsVariationalSolutionQ.integral_annulus_euler_le (hQ k) (hsol k) hΩ (hκ k) (hcl k)
      (hZ k) Ninf
    calc _ ≤ _ := this
      _ = _ := by simp only [hHdef, hNt, hκdef]; ring
  -- Tangential energy.
  have htan' : Tendsto (fun k => ∫ y in A,
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) atTop (𝓝 0) := by
    refine htan.congr fun k => ?_
    have hpt : ∀ y, ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2 =
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2 / H k := fun y => by
      rw [hgrad, inner_smul_left, conj_trivial, ← smul_smul, ← smul_sub, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs, hc2]
      ring
    simp_rw [hpt]
    rw [integral_div]
  -- Mass on `A`.
  have hmass : ∀ k, 1 / 4 * ((3 / 4) ^ (n + 1) / K) ≤ ∫ y in A, v k y ^ 2 := by
    intro k
    have hpt : ∀ y, v k y ^ 2 = u k y ^ 2 / H k := fun y => by
      simp only [hv]
      rw [mul_pow, hc2]
      ring
    simp_rw [hpt]
    rw [integral_div, le_div_iff₀ (hH k)]
    have := IsVariationalSolutionQ.mul_heightH_le_integral_annulus_sq (hQ k) (hsol k) hΩ (hκ k)
      (hcl k) (hZ k) hNp ((hfreq k).2.2.trans ((hN k).trans (by linarith)))
    calc 1 / 4 * ((3 / 4) ^ (n + 1) / K) * H k =
        1 / 4 * ((3 / 4) ^ (n + 1) * heightH (u k) 0 1 / K) := by simp only [hHdef]; ring
      _ ≤ _ := this
  -- Domain-variation defect.
  have hdv : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ A → ∀ e : Rn n,
      Tendsto (fun k => ∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y) atTop (𝓝 0) := by
    intro φ hφ hφc hφA e
    have hξ : IsSmoothTestField (ball (0 : Rn n) 1) (fun z => φ z • e) :=
      ⟨hφ.smul contDiff_const, hφc.smul_right, (tsupport_smul_subset_left _ _).trans
        (hφA.trans hAB)⟩
    obtain ⟨D, hD⟩ := hξ.isLipTestField.1
    obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
    set M := Mφ * ‖e‖ with hMdef
    have hM : ∀ y, ‖φ y • e‖ ≤ M := fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hMφ y) (norm_nonneg _)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hpt : ∀ k y, Kernel.gradVariation (v k) (fun z => φ z • e) y =
        Kernel.gradVariation (u k) (fun z => φ z • e) y / H k := fun k y => by
      simp only [Kernel.gradVariation, hgrad, norm_smul, map_smul, inner_smul_left,
        inner_smul_right, conj_trivial, Real.norm_eq_abs, abs_of_nonneg (hc0 k)]
      rw [div_eq_mul_one_div _ (H k), ← hc2 k]
      ring
    have hbound : ∀ k, ‖∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y‖ ≤
        (n * D + 1 / 4 * M) * weightedVolumeV (Q k) (u k) (χ k) 0 1 := fun k => by
      simp_rw [hpt k]
      rw [integral_div, Real.norm_eq_abs, abs_div, abs_of_pos (hH k), div_le_iff₀ (hH k)]
      have := IsVariationalSolutionQ.abs_integral_gradVariation_le_weightedVolumeV (hQ k)
        (hsol k) hΩ (hH k) hξ.isLipTestField hD hM
      have hκM : κ k * M ≤ 1 / 4 * M := mul_le_mul_of_nonneg_right (hk4 k) hM0
      have hVH : 0 ≤ weightedVolumeV (Q k) (u k) (χ k) 0 1 * heightH (u k) 0 1 :=
        mul_nonneg (hVnn k) (hH k).le
      calc |∫ y, Kernel.gradVariation (u k) (fun z => φ z • e) y|
          ≤ (n * D + κ k * M) * (weightedVolumeV (Q k) (u k) (χ k) 0 1 * heightH (u k) 0 1) :=
            this
        _ ≤ (n * D + 1 / 4 * M) *
            (weightedVolumeV (Q k) (u k) (χ k) 0 1 * heightH (u k) 0 1) :=
            mul_le_mul_of_nonneg_right (by linarith) hVH
        _ = _ := by simp only [hHdef]; ring
    have hl : Tendsto (fun k => ((n : ℝ) * D + 1 / 4 * M) *
        weightedVolumeV (Q k) (u k) (χ k) 0 1) atTop (𝓝 0) := by
      simpa using hV0.const_mul ((n : ℝ) * D + 1 / 4 * M)
    exact tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) hbound hl)
  -- The energy identity (`v_k` is harmonic where positive).
  have henergy : ∀ η : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ A →
      ∀ k, ∫ y, ‖gradient (v k) y‖ ^ 2 * η y = -∫ y, v k y * ⟪gradient (v k) y, gradient η y⟫ := by
    intro η hη hηc hηA k
    have h := ((hsol k).isLipHarmonicPos (hQ k)).integral_norm_gradient_sq_mul
      (hη.lipschitzWith_of_hasCompactSupport hηc (by simp)) hηc (hηA.trans (hAB.trans hB1))
    have e1 : ∀ y, ‖gradient (v k) y‖ ^ 2 * η y =
        cc k ^ 2 * (‖gradient (u k) y‖ ^ 2 * η y) := fun y => by
      rw [hgrad, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have e2 : ∀ y, v k y * ⟪gradient (v k) y, gradient η y⟫ =
        cc k ^ 2 * (u k y * ⟪gradient (u k) y, gradient η y⟫) := fun y => by
      rw [hgrad, inner_smul_left, conj_trivial]
      simp only [hv]
      ring
    simp_rw [e1, e2, integral_const_mul, h]
    ring
  -- The radial mass identity in the limit `N_∞ = 1`.
  have hmassLim : Ninf = 1 → Tendsto (fun k => ∫ y in A, v k y ^ 2) atTop
      (𝓝 (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1))) := by
    rintro rfl
    set m := ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) with hm
    set Np : ℕ → ℝ := fun k => Nt k 1 + 1 / ((k : ℝ) + 1) with hNpdef
    have hk0' : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    have hNp1 : ∀ k, 1 < Np k := fun k => by
      have := (hfreq k).1.trans (hfreq k).2.1
      simp only [hNpdef]
      linarith [hk0' k]
    have hNpN : ∀ k, Nt k 1 ≤ Np k := fun k => by
      simp only [hNpdef]
      linarith [hk0' k]
    have hNpt : Tendsto Np atTop (𝓝 1) := by
      have := hlim1.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at this
      exact this
    have hDc : Continuous Abstract.RadialData.doublingConst := by
      unfold Abstract.RadialData.doublingConst
      fun_prop
    have hDt : Tendsto (fun k => Abstract.RadialData.doublingConst (Np k)) atTop (𝓝 1) := by
      have := (hDc.tendsto 1).comp hNpt
      have hD1 : Abstract.RadialData.doublingConst 1 = 1 := by
        simp [Abstract.RadialData.doublingConst]
      rw [hD1] at this
      exact this
    have he : Tendsto (fun k => Real.exp (κ k ^ 2 / 8)) atTop (𝓝 1) := by
      have h : Tendsto (fun k => κ k ^ 2 / 8) atTop (𝓝 0) := by
        simpa using (hκt.pow 2).div_const 8
      have h2 := (Real.continuous_exp.tendsto 0).comp h
      rwa [Real.exp_zero] at h2
    have hpt : ∀ k, ∫ y in A, v k y ^ 2 =
        (∫ y in A, u k y ^ 2) / heightH (u k) 0 1 := fun k => by
      rw [← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hv]
      rw [mul_pow, hc2]
      simp only [hHdef]
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun k => m / Abstract.RadialData.doublingConst (Np k))
      (h := fun k => Real.exp (κ k ^ 2 / 8) * m) ?_ ?_ (fun k => ?_) (fun k => ?_)
    · have h := (tendsto_const_nhds (x := m)).div hDt one_ne_zero
      rw [div_one] at h
      exact h
    · simpa using he.mul_const m
    · have hb := (IsVariationalSolutionQ.integral_annulus_sq_mem_Icc (hQ k) (hsol k) hΩ (hκ k)
        (hcl k) (hZ k) (hNp1 k) (hNpN k)).1
      have hH' : 0 < heightH (u k) 0 1 := hH k
      rw [hpt, le_div_iff₀ hH']
      calc m / Abstract.RadialData.doublingConst (Np k) * heightH (u k) 0 1
          = heightH (u k) 0 1 * m / Abstract.RadialData.doublingConst (Np k) := by ring
        _ ≤ _ := hb
    · have hb := (IsVariationalSolutionQ.integral_annulus_sq_mem_Icc (hQ k) (hsol k) hΩ (hκ k)
        (hcl k) (hZ k) (hNp1 k) (hNpN k)).2
      have hH' : 0 < heightH (u k) 0 1 := hH k
      rw [hpt, div_le_iff₀ hH']
      calc _ ≤ _ := hb
        _ = Real.exp (κ k ^ 2 / 8) * m * heightH (u k) 0 1 := by ring
  exact ⟨hLip, ⟨_, hbd⟩, hnn, hE, htan', ⟨_, by positivity, hmass⟩, hdv, henergy, hmassLim⟩

/-- **Theorem 5.3 with Lipschitz coefficients, along a sequence with `Ñ_0(u_k; 1/2) → N_∞`:
`N_∞ = 1`.** -/
theorem eq_one_of_tendsto_modFrequencyN_half (hν : ∀ k, ‖ν k‖ = 1)
    (hQ : ∀ k, QBounds Ω (Q k) (L k) (c k) (C' k))
    (hsol : ∀ k, IsVariationalSolutionQ Ω (C_V k) (Q k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω) (hκ : ∀ k, weissKappa (L k) (c k) (C' k) * 2 ≤ 1 / 2)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hZ : ∀ k, 0 ≤ modMonotonicityM (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k =>
      modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 -
        modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0))
    {Ninf : ℝ} (hlim : Tendsto (fun k =>
      modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2)) atTop (𝓝 Ninf)) :
    Ninf = 1 := by
  have hNinf : 1 ≤ Ninf := ge_of_tendsto' hlim fun k =>
    (IsVariationalSolutionQ.modFrequencyN_half_le_one_le_two (hQ k) (hsol k) hΩ (hκ k) (hcl k)
      (hZ k)).1
  obtain ⟨hLip, ⟨C, hbd⟩, hnn, hE, htan', ⟨c₀, hc₀, hmass⟩, hdv, -, -⟩ :=
    renormalizedQ_properties hQ hsol hΩ hκ hcl hZ hN hδ htan hlim _ fun _ _ => rfl
  exact eq_one_of_renormalized _ (by linarith) hc₀ hν hLip hbd hnn hE htan' hmass hdv

/-- **Theorem 5.3 with Lipschitz coefficients, direction-free form: `N_∞ = 1`.**
Let `(u_k, χ_k)` be variational solutions on `Ω ⊇ B̄_2` for coefficients `Q_k` with
`QBounds Ω Q_k L_k c_k C'_k` and `2 κ_k ≤ 1/2`, where `κ_k = weissKappa L_k c_k C'_k`. Assume
`0 ∈ closure {u_k > 0}`, `Z_0(u_k; 1/2) ≥ 0`, `Ñ_0(u_k; 2) ≤ N₊`, and
`Ñ_0(u_k; 2) − Ñ_0(u_k; 1/2) → 0`. If for unit vectors `ν_k` the tangential part of the
renormalized energy on `A = B_1 \ B̄_{1/2}` vanishes in the limit, then `Ñ_0(u_k; 1/2) → 1`,
`N_0(u_k; 1/2) → 1` and `κ_k → 0`. -/
theorem approx1DQ_limit_frequency_eq_one (_hn : 2 ≤ n) (hν : ∀ k, ‖ν k‖ = 1)
    (hQ : ∀ k, QBounds Ω (Q k) (L k) (c k) (C' k))
    (hsol : ∀ k, IsVariationalSolutionQ Ω (C_V k) (Q k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω) (hκ : ∀ k, weissKappa (L k) (c k) (C' k) * 2 ≤ 1 / 2)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hZ : ∀ k, 0 ≤ modMonotonicityM (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k =>
      modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 -
        modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0)) :
    Tendsto (fun k => modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
        atTop (𝓝 1) ∧
      Tendsto (fun k => weightedFrequencyN (Q k) (u k) (χ k) 0 (1 / 2)) atTop (𝓝 1) ∧
      Tendsto (fun k => weissKappa (L k) (c k) (C' k)) atTop (𝓝 0) := by
  have hκt := tendsto_weissKappa_of_pinching hQ hsol hΩ hκ hcl hZ hδ
  have h1 : Tendsto (fun k => modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0
      (1 / 2)) atTop (𝓝 1) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    have hfreq := fun k => IsVariationalSolutionQ.modFrequencyN_half_le_one_le_two (hQ k)
      (hsol k) hΩ (hκ k) (hcl k) (hZ k)
    have hb : ∀ k, modFrequencyN (weissKappa (L (ns k)) (c (ns k)) (C' (ns k))) (Q (ns k))
        (u (ns k)) (χ (ns k)) 0 (1 / 2) ∈ Icc 1 Nplus := fun k =>
      ⟨(hfreq _).1, (hfreq _).2.1.trans ((hfreq _).2.2.trans (hN _))⟩
    obtain ⟨Ninf, -, ms, hms, hlim⟩ := isCompact_Icc.tendsto_subseq hb
    have hns' : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
    have h1 := eq_one_of_tendsto_modFrequencyN_half (u := fun k => u (ns (ms k)))
      (χ := fun k => χ (ns (ms k))) (Q := fun k => Q (ns (ms k)))
      (L := fun k => L (ns (ms k))) (c := fun k => c (ns (ms k))) (C' := fun k => C' (ns (ms k)))
      (C_V := fun k => C_V (ns (ms k))) (ν := fun k => ν (ns (ms k)))
      (fun k => hν _) (fun k => hQ _) (fun k => hsol _) hΩ (fun k => hκ _) (fun k => hcl _)
      (fun k => hZ _) (fun k => hN _) (hδ.comp hns') (htan.comp hns') (Ninf := Ninf) hlim
    exact ⟨ms, h1 ▸ hlim⟩
  refine ⟨h1, ?_, hκt⟩
  have := h1.sub (((hκt.pow 2).mul_const ((1 / 2 : ℝ) ^ 2)).div_const 2)
  simp only [zero_pow two_ne_zero, zero_mul, zero_div, sub_zero] at this
  refine this.congr fun k => ?_
  simp only [modFrequencyN]
  ring

/-- **Theorem 5.3 with Lipschitz coefficients, refined form** (strong `W^{1,2}` convergence on
`A' = B_{7/8} \ B̄_{5/8}`), under the hypotheses of `approx1DQ_limit_frequency_eq_one`, with
`H_k = H_0(u_k; 1)`: `Ñ_0(u_k; 1/2) → 1`,
`∫_{A'} (u_k − √H_k α(n) |y·ν_k|)² / H_k → 0` and
`∫_{A'} |∇u_k − √H_k α(n) ∇|y·ν_k||² / H_k → 0`. -/
theorem approx1DQ_limit_tendsto_profile (hn : 2 ≤ n) (hν : ∀ k, ‖ν k‖ = 1)
    (hQ : ∀ k, QBounds Ω (Q k) (L k) (c k) (C' k))
    (hsol : ∀ k, IsVariationalSolutionQ Ω (C_V k) (Q k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω) (hκ : ∀ k, weissKappa (L k) (c k) (C' k) * 2 ≤ 1 / 2)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hZ : ∀ k, 0 ≤ modMonotonicityM (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k =>
      modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 2 -
        modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0)) :
    Tendsto (fun k => modFrequencyN (weissKappa (L k) (c k) (C' k)) (Q k) (u k) (χ k) 0 (1 / 2))
        atTop (𝓝 1) ∧
    Tendsto (fun k => (∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        (u k y - √(heightH (u k) 0 1) * alphaN n * absProfile (ν k) 0 y) ^ 2) /
          heightH (u k) 0 1) atTop (𝓝 0) ∧
    Tendsto (fun k => (∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        ‖gradient (u k) y -
          (√(heightH (u k) 0 1) * alphaN n) • gradient (absProfile (ν k) 0) y‖ ^ 2) /
          heightH (u k) 0 1) atTop (𝓝 0) := by
  have h1 := (approx1DQ_limit_frequency_eq_one hn hν hQ hsol hΩ hκ hcl hZ hN hδ htan).1
  refine ⟨h1, ?_⟩
  obtain ⟨hLip, ⟨C, hbd⟩, hnn, hE, htan', -, hdv, henergy, hmassLim⟩ :=
    renormalizedQ_properties hQ hsol hΩ hκ hcl hZ hN hδ htan h1
      (fun k y => (√(heightH (u k) 0 1))⁻¹ * u k y) fun _ _ => rfl
  obtain ⟨hR1, hR2⟩ := tendsto_profile_of_renormalized hn _ hν hLip hbd hnn
    (by simpa only [one_mul] using hE) htan' (hmassLim rfl) hdv henergy
  have hH : ∀ k, 0 < heightH (u k) 0 1 := fun k =>
    IsVariationalSolutionQ.heightH_one_pos (hQ k) (hsol k) hΩ (hcl k)
  refine ⟨hR1.congr fun k => ?_, hR2.congr fun k => ?_⟩
  · have hs0 : √(heightH (u k) 0 1) ≠ 0 := (Real.sqrt_pos.2 (hH k)).ne'
    have hs2 : √(heightH (u k) 0 1) ^ 2 = heightH (u k) 0 1 := Real.sq_sqrt (hH k).le
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    have e : (√(heightH (u k) 0 1))⁻¹ * u k y - alphaN n * absProfile (ν k) 0 y =
        (√(heightH (u k) 0 1))⁻¹ *
          (u k y - √(heightH (u k) 0 1) * alphaN n * absProfile (ν k) 0 y) := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    rw [e, mul_pow, inv_pow, hs2, inv_mul_eq_div]
  · have hs0 : √(heightH (u k) 0 1) ≠ 0 := (Real.sqrt_pos.2 (hH k)).ne'
    have hs2 : √(heightH (u k) 0 1) ^ 2 = heightH (u k) 0 1 := Real.sq_sqrt (hH k).le
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [gradient_const_mul]
    have e : (√(heightH (u k) 0 1))⁻¹ • gradient (u k) y -
        alphaN n • gradient (absProfile (ν k) 0) y =
        (√(heightH (u k) 0 1))⁻¹ • (gradient (u k) y -
          (√(heightH (u k) 0 1) * alphaN n) • gradient (absProfile (ν k) 0) y) := by
      rw [smul_sub, smul_smul, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    rw [e, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, hs2, inv_mul_eq_div]

end Sequences

end InnerVariational
