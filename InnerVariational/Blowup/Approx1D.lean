/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Profile
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Blowup.Renormalization
import InnerVariational.Blowup.Limit
import InnerVariational.Frequency.Concrete
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.Quantities
public import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Sobolev.Lipschitz

/-!
# Frequency blow-ups: Lemma 5.1 and Theorem 5.3 in the form used later

Lemma 5.1 and Theorem 5.3 of Kriventsov–Weiss (full reference below), stated for the
variational solutions `u_k` themselves, in the form used by the proofs of Theorem 6.3 (frequency
drop dichotomy, `Estimates/Dichotomy.lean`) and Lemma 8.5 (singular points of density one,
`Singular/FlatPoint.lean`). The statements do not mention Sobolev spaces; the Sobolev machinery
stays inside `InnerVariational/Blowup/`.

## Setting (the standing assumptions of Section 5)

`(u_k, χ_k)` are variational solutions on `Ω ⊇ B̄_2` with
* `0 ∈ closure {u_k > 0}` and `M_0(u_k; 1/2) ≥ |B_1|` (the paper writes `M_0(u; 1/2)`, and
  `0 ∈ {u_k > 0}` and `B_2 ⊆ Ω`; we use the closure and `B̄_2 ⊆ Ω`);
* `N_0(u_k; 2) ≤ N₊` and `δ_k = N_0(u_k; 2) − N_0(u_k; 1/2) → 0`.

The Lipschitz constants `C_V k` may vary with `k`. The paper imposes no uniform bound, and none is
kept under the renormalization `v_k = u_k / √H_0(u_k; 1)`.

## Main statements

* `approx1D_limit_frequency_eq_one`: Theorem 5.3's conclusion `N_∞ = 1` in its direction-free
  form. If the tangential energy `∫_A |∇u_k − ⟪∇u_k, ν_k⟫ν_k|² / H_0(u_k; 1)` tends to `0` on
  `A = B_1 \ B̄_{1/2}` for unit vectors `ν_k`, then `N_0(u_k; 1/2) → 1`.
* `approx1D_limit_frequency_eq_one_coord`: the paper's coordinate form (`ν = e_n`, as in the
  statement of Theorem 5.3), derived from the direction-free form.
* `approx1D_limit_tendsto_profile`: the refined form used in the proof of Lemma 8.5.
  `v_k − α(n)|y·ν_k| → 0` strongly in `W^{1,2}(B_{7/8} \ B̄_{5/8})`, written with `u_k` and
  `H_0(u_k; 1)` in the style of `Statements.main_theorem_iv`.

## Proof of `approx1D_limit_frequency_eq_one`

Every subsequence has a further subsequence along which `N_0(u_k; 1/2) → N_∞ ∈ [1, N₊]`
(`eq_one_of_tendsto_frequencyN_half` shows `N_∞ = 1`). There the renormalized sequence
`v_k = u_k / √H_0(u_k; 1)` is fed to `eq_one_of_renormalized` (`Blowup/Limit.lean`: Lemma 5.1 and
steps (a)–(c) of the proof of Theorem 5.3); the frequency input comes from
`Blowup/Renormalization.lean` (Lemmas 4.1, 4.3–4.5 and equation (4.13) integrated over `A`). The
only compactness theorem used is Rellich's (`Registry.rellich_trace_weak_compactness`).
The hypothesis `2 ≤ n` is not used here: step (a) is argued on the connected half-annuli
(`Blowup/ExplicitForm.lean`), which works for every `n`.

## Proof of `approx1D_limit_tendsto_profile`

`renormalized_properties` collects the facts about `v_k` (including the energy identity and, since
`N_0(u_k; 1/2) → 1`, the radial mass identity `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds`), and
`tendsto_profile_of_renormalized` (`Blowup/Profile.lean`: Theorem 5.3, steps (d)–(e) and the
normalization `β = α(n)`) gives the `W^{1,2}(A')` convergence. Again only Rellich's theorem
is used; the compactness of the trace on `∂B_1` is not.

## Faithfulness notes

* **Direction-free form, direction depending on `k`.** Rotate each `u_k` by an isometry `R_k`
  with `R_k e_n = ν_k`. Every hypothesis and conclusion concerns one `u_k` at a time and is
  invariant under isometries fixing `0`, so this form is equivalent to the paper's coordinate
  form and not stronger. It spares the users the rotation step: in the proof of Theorem 6.3 the
  basis `e_1, …, e_n` is built from the points `a_i^k`, so the direction `e_n` depends on `k`.
* **Full sequence.** The paper's conclusions hold along the subsequence of Lemma 5.1. Their
  limits (`1`, and the profile `α(n)|y·ν_k|` in rotated coordinates) do not depend on the
  subsequence, and every hypothesis passes to subsequences. So the full sequence converges.
* **Independence of `x'`.** The paper calls the `x'`-independence of the limit "immediate from
  the assumption". For `n = 2` it does not follow from the vanishing of tangential derivatives
  alone; it uses the homogeneity of the limit. We use the weak Euler identity on the two
  half-annuli (`Blowup/ExplicitForm.lean`).
* **Scale in the proof of Theorem 6.3.** The paper renormalizes at scale `18` there, which uses
  frequency pinching on `[9, 36]`, while `[1, 20]` is what is controlled. We apply these
  statements at scale `10` (see `approx1D_limit_frequency_eq_one`).

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

/-- **The renormalized sequence `v_k = u_k / √H_0(u_k; 1)` and its properties** (the setting of
Section 5 and the proof of Lemma 5.1). Under the hypotheses of `approx1D_limit_frequency_eq_one`,
with
`N_0(u_k; 1/2) → N_∞`:
* `v_k` is Lipschitz on `B̄_1`, nonnegative, and bounded in `W^{1,2}(B_1)`: `∫_{B_1} v_k² ≤ 1` and
  `∫_{B_1} |∇v_k|² = N(1) + V(1)` (by (4.11), as in the proof of Lemma 5.1);
* the Euler defect `∫_A (∇v_k·y − N_∞ v_k)²` tends to `0` ((4.13) integrated over `A`, as in the
  proof of Lemma 5.1);
* the tangential energy tends to `0` (the hypothesis);
* the mass on `A` is bounded below (Lemma 4.3);
* the domain-variation defect `≤ n D V_0(u_k; 1)` tends to `0` (Lemma 4.5, as in step (c) of the
  proof of Theorem 5.3);
* the energy identity `∫ |∇v_k|² η = −∫ v_k ∇v_k·∇η` holds for `η ∈ C_c^∞(A)` (`v_k` is harmonic
  where positive, as in step (d) of the proof of Theorem 5.3);
* if `N_∞ = 1`, then `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds` (Lemma 4.3 with `C(N₊) → 1`; this radial
  mass identity replaces the normalization `∫_{∂B_1} v_k² = 1`). -/
theorem renormalized_properties [NeZero n] {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n}
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0))
    {Ninf : ℝ} (hlim : Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 Ninf))
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
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  have hAB : A ⊆ ball (0 : Rn n) 1 := diff_subset
  have hB1 : ball (0 : Rn n) 1 ⊆ Ω :=
    ball_subset_closedBall.trans (closedBall_one_subset_of_two hΩ)
  have hcB1 : closedBall (0 : Rn n) 1 ⊆ Ω := closedBall_one_subset_of_two hΩ
  set H : ℕ → ℝ := fun k => heightH (u k) 0 1 with hHdef
  have hH : ∀ k, 0 < H k := fun k => (hsol k).heightH_one_pos hΩ (hcl k)
  have hfreq := fun k => (hsol k).frequencyN_half_le_one_le_two hΩ (hcl k) (hM k)
  have hNinf : 1 ≤ Ninf := ge_of_tendsto' hlim fun k => (hfreq k).1
  have hNp : 1 < Nplus + 1 := by linarith [(hfreq 0).1, (hfreq 0).2.1, (hfreq 0).2.2, hN 0]
  -- `N_0(u_k; 1) → N_∞`.
  have hlim1 : Tendsto (fun k => frequencyN (u k) (χ k) 0 1) atTop (𝓝 Ninf) := by
    have h2 : Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2) +
        (frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))) atTop (𝓝 Ninf) := by
      simpa using hlim.add hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim h2 (fun k => (hfreq k).2.1)
      fun k => ?_
    have := (hfreq k).2.2
    simp only
    linarith
  -- `V_0(u_k; 1)` is bounded and tends to `0` (Lemma 4.5).
  set K := Abstract.RadialData.doublingConst (Nplus + 1) with hK
  have hKpos : 0 < K := Abstract.RadialData.doublingConst_pos _
  have hV : ∀ k δ, frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 1 < δ →
      volumeV (u k) (χ k) 0 1 ≤ 2 ^ n * K * √δ := fun k δ hδ' =>
    (hsol k).volumeV_one_le hΩ (hcl k) (hM k) (by linarith [hN k]) hδ'
  have hVnn : ∀ k, 0 ≤ volumeV (u k) (χ k) 0 1 := fun k => (hsol k).volumeV_nonneg one_pos hB1
  have hVbd : ∀ k, volumeV (u k) (χ k) 0 1 ≤ 2 ^ n * K * √Nplus := fun k =>
    hV k Nplus (by linarith [(hfreq k).1, (hfreq k).2.1, (hfreq k).2.2, hN k])
  have hV0 : Tendsto (fun k => volumeV (u k) (χ k) 0 1) atTop (𝓝 0) := by
    have hd : Tendsto (fun k : ℕ => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2) +
        1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using hδ.add tendsto_one_div_add_atTop_nhds_zero_nat
    have hs : Tendsto (fun k : ℕ => 2 ^ n * K * √(frequencyN (u k) (χ k) 0 2 -
        frequencyN (u k) (χ k) 0 (1 / 2) + 1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.tendsto 0).comp hd).const_mul (2 ^ n * K)
    refine squeeze_zero hVnn (fun k => hV k _ ?_) hs
    have := (hfreq k).2.1
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  -- The renormalized sequence.
  set c : ℕ → ℝ := fun k => (√(H k))⁻¹ with hc
  have hc2 : ∀ k, c k ^ 2 = 1 / H k := fun k => by
    simp only [hc, inv_pow, Real.sq_sqrt (hH k).le, one_div]
  have hc0 : ∀ k, 0 ≤ c k := fun k => inv_nonneg.2 (Real.sqrt_nonneg _)
  set v : ℕ → Rn n → ℝ := fun k y => c k * u k y with hv
  have hgrad : ∀ k y, gradient (v k) y = c k • gradient (u k) y := fun k y =>
    gradient_const_mul (c k) (u k) y
  -- Lipschitz bound.
  have hLip : ∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1) := fun k =>
    ⟨_, ((lipschitzWith_smul (c k)).comp_lipschitzOnWith ((hsol k).lipschitzOnWith 0 2
      (ball_subset_closedBall.trans hΩ))).mono (closedBall_subset_ball (by norm_num))⟩
  -- `W^{1,2}(B_1)` bound.
  have hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤
      1 + (Nplus + 2 ^ n * K * √Nplus) := by
    intro k
    have hpt : ∀ y, v k y ^ 2 + ‖gradient (v k) y‖ ^ 2 =
        (u k y ^ 2 + ‖gradient (u k) y‖ ^ 2) / H k := fun y => by
      rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 k)]
      simp only [hv]
      rw [mul_pow, mul_pow, hc2]
      ring
    simp_rw [hpt]
    rw [integral_div, integral_add ((hsol k).integrableOn_sq_of_closedBall hcB1)
      ((hsol k).integrableOn_norm_gradient_sq hB1),
      (hsol k).integral_ball_one_norm_gradient_sq_eq hΩ (hH k), div_le_iff₀ (hH k)]
    have h1 := (hsol k).integral_ball_one_sq_le hΩ
    have h2 : frequencyN (u k) (χ k) 0 1 + volumeV (u k) (χ k) 0 1 ≤
        Nplus + 2 ^ n * K * √Nplus := add_le_add ((hfreq k).2.2.trans (hN k)) (hVbd k)
    have h3 := mul_le_mul_of_nonneg_right h2 (hH k).le
    simp only [hHdef] at h3 ⊢
    nlinarith
  -- Nonnegativity.
  have hnn : ∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y := fun k y hy =>
    mul_nonneg (hc0 k) ((hsol k).nonneg y (hB1 hy))
  -- Euler defect.
  have hE : Tendsto (fun k => ∫ y in A, (⟪gradient (v k) y, y⟫ - Ninf * v k y) ^ 2) atTop
      (𝓝 0) := by
    have hR : Tendsto (fun k => (frequencyN (u k) (χ k) 0 1 - frequencyN (u k) (χ k) 0 (1 / 2)) +
        2 * max ((frequencyN (u k) (χ k) 0 1 - Ninf) ^ 2)
          ((frequencyN (u k) (χ k) 0 (1 / 2) - Ninf) ^ 2)) atTop (𝓝 0) := by
      have h1 := hlim1.sub hlim
      have h2 := ((hlim1.sub_const Ninf).pow 2).max ((hlim.sub_const Ninf).pow 2)
      simpa using h1.add (h2.const_mul 2)
    refine squeeze_zero (fun k => setIntegral_nonneg (isOpen_ball.sdiff isClosed_closedBall
      |>.measurableSet) fun y _ => sq_nonneg _) (fun k => ?_) hR
    have hpt : ∀ y, (⟪gradient (v k) y, y⟫ - Ninf * v k y) ^ 2 =
        (⟪gradient (u k) y, y⟫ - Ninf * u k y) ^ 2 / H k := fun y => by
      rw [hgrad, inner_smul_left]
      simp only [hv, conj_trivial]
      rw [show c k * ⟪gradient (u k) y, y⟫ - Ninf * (c k * u k y) =
        c k * (⟪gradient (u k) y, y⟫ - Ninf * u k y) by ring, mul_pow, hc2]
      ring
    simp_rw [hpt]
    rw [integral_div, div_le_iff₀ (hH k), mul_comm]
    exact (hsol k).integral_annulus_euler_le hΩ (hcl k) (hM k) Ninf
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
    have := (hsol k).mul_heightH_le_integral_annulus_sq hΩ (hcl k) (hM k) hNp
      ((hfreq k).2.2.trans ((hN k).trans (by linarith)))
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
    have hpt : ∀ k y, Kernel.gradVariation (v k) (fun z => φ z • e) y =
        Kernel.gradVariation (u k) (fun z => φ z • e) y / H k := fun k y => by
      simp only [Kernel.gradVariation, hgrad, norm_smul, map_smul, inner_smul_left,
        inner_smul_right, conj_trivial, Real.norm_eq_abs, abs_of_nonneg (hc0 k)]
      rw [div_eq_mul_one_div _ (H k), ← hc2 k]
      ring
    have hbound : ∀ k, ‖∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y‖ ≤
        n * D * volumeV (u k) (χ k) 0 1 := fun k => by
      simp_rw [hpt k]
      rw [integral_div, Real.norm_eq_abs, abs_div, abs_of_pos (hH k), div_le_iff₀ (hH k)]
      have := (hsol k).abs_integral_gradVariation_le_volumeV hΩ (hH k) hξ.isLipTestField hD
      simp only [hHdef]
      linarith
    have hl : Tendsto (fun k => (n : ℝ) * D * volumeV (u k) (χ k) 0 1) atTop (𝓝 0) := by
      simpa using hV0.const_mul ((n : ℝ) * D)
    exact tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) hbound hl)
  -- The energy identity (`v_k` is harmonic where positive).
  have henergy : ∀ η : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ A →
      ∀ k, ∫ y, ‖gradient (v k) y‖ ^ 2 * η y = -∫ y, v k y * ⟪gradient (v k) y, gradient η y⟫ := by
    intro η hη hηc hηA k
    have h := (hsol k).isLipHarmonicPos.integral_norm_gradient_sq_mul
      (hη.lipschitzWith_of_hasCompactSupport hηc (by simp)) hηc (hηA.trans (hAB.trans hB1))
    have e1 : ∀ y, ‖gradient (v k) y‖ ^ 2 * η y =
        c k ^ 2 * (‖gradient (u k) y‖ ^ 2 * η y) := fun y => by
      rw [hgrad, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have e2 : ∀ y, v k y * ⟪gradient (v k) y, gradient η y⟫ =
        c k ^ 2 * (u k y * ⟪gradient (u k) y, gradient η y⟫) := fun y => by
      rw [hgrad, inner_smul_left, conj_trivial]
      simp only [hv]
      ring
    simp_rw [e1, e2, integral_const_mul, h]
    ring
  -- The radial mass identity in the limit `N_∞ = 1`.
  have hmassLim : Ninf = 1 → Tendsto (fun k => ∫ y in A, v k y ^ 2) atTop
      (𝓝 (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1))) := by
    rintro rfl
    set Np : ℕ → ℝ := fun k => frequencyN (u k) (χ k) 0 1 + 1 / ((k : ℝ) + 1) with hNpdef
    have hk0 : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    have hNp1 : ∀ k, 1 < Np k := fun k => by
      have := (hfreq k).1.trans (hfreq k).2.1
      simp only [hNpdef]
      linarith [hk0 k]
    have hNpN : ∀ k, frequencyN (u k) (χ k) 0 1 ≤ Np k := fun k => by
      simp only [hNpdef]
      linarith [hk0 k]
    have hNpt : Tendsto Np atTop (𝓝 1) := by
      have := hlim1.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at this
      exact this
    have hDc : Continuous Abstract.RadialData.doublingConst := by
      unfold Abstract.RadialData.doublingConst
      fun_prop
    have hDt : Tendsto (fun k => Abstract.RadialData.doublingConst (Np k)) atTop (𝓝 1) := by
      have := (hDc.tendsto 1).comp hNpt
      simpa [Abstract.RadialData.doublingConst] using this
    have hpt : ∀ k, ∫ y in A, v k y ^ 2 =
        (∫ y in A, u k y ^ 2) / heightH (u k) 0 1 := fun k => by
      rw [← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hv]
      rw [mul_pow, hc2]
      simp only [hHdef]
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun k => (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)) /
        Abstract.RadialData.doublingConst (Np k))
      (h := fun _ => ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)) ?_ tendsto_const_nhds (fun k => ?_)
      (fun k => ?_)
    · simpa using (tendsto_const_nhds (x := ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1))).div hDt
        one_ne_zero
    · have hb := ((hsol k).integral_annulus_sq_mem_Icc hΩ (hcl k) (hM k) (hNp1 k) (hNpN k)).1
      have hH' : 0 < heightH (u k) 0 1 := hH k
      rw [hpt, le_div_iff₀ hH']
      calc (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)) / Abstract.RadialData.doublingConst (Np k) *
            heightH (u k) 0 1
          = heightH (u k) 0 1 * (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)) /
            Abstract.RadialData.doublingConst (Np k) := by ring
        _ ≤ _ := hb
    · have hb := ((hsol k).integral_annulus_sq_mem_Icc hΩ (hcl k) (hM k) (hNp1 k) (hNpN k)).2
      have hH' : 0 < heightH (u k) 0 1 := hH k
      rw [hpt, div_le_iff₀ hH', mul_comm]
      exact hb
  exact ⟨hLip, ⟨_, hbd⟩, hnn, hE, htan', ⟨_, by positivity, hmass⟩, hdv, henergy, hmassLim⟩

/-- **Theorem 5.3 along a sequence with `N_0(u_k; 1/2) → N_∞`: `N_∞ = 1`.** This is the core of
`approx1D_limit_frequency_eq_one`. The renormalized sequence `v_k = u_k / √H_0(u_k; 1)` satisfies
the hypotheses of `eq_one_of_renormalized` (`renormalized_properties`). -/
theorem eq_one_of_tendsto_frequencyN_half [NeZero n] {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0))
    {Ninf : ℝ} (hlim : Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 Ninf)) :
    Ninf = 1 := by
  have hNinf : 1 ≤ Ninf := ge_of_tendsto' hlim fun k =>
    ((hsol k).frequencyN_half_le_one_le_two hΩ (hcl k) (hM k)).1
  obtain ⟨hLip, ⟨C, hbd⟩, hnn, hE, htan', ⟨c₀, hc₀, hmass⟩, hdv, -, -⟩ :=
    renormalized_properties hsol hΩ hcl hM hN hδ htan hlim _ fun _ _ => rfl
  exact eq_one_of_renormalized _ (by linarith) hc₀ hν hLip hbd hnn hE htan' hmass hdv

/-- **Theorem 5.3, direction-free form for the solutions `u_k`: `N_∞ = 1`.**
Let `(u_k, χ_k)` be variational solutions on `Ω ⊇ B̄_2` (constants `C_V k`, not uniform) with
`0 ∈ closure {u_k > 0}`, `M_0(u_k; 1/2) ≥ |B_1|`, `N_0(u_k; 2) ≤ N₊`, and
`N_0(u_k; 2) − N_0(u_k; 1/2) → 0`. Suppose that for unit vectors `ν_k` the tangential part of
the renormalized energy on `A = B_1 \ B̄_{1/2}` vanishes in the limit:
`∫_A |∇u_k − ⟪∇u_k, ν_k⟫ ν_k|² / H_0(u_k; 1) → 0`. Then `N_0(u_k; 1/2) → 1`.

This is the paper's hypothesis `Σ_{i<n} ∫_A |∂_i v_k|² → 0` for `v_k = u_k/√H_0(u_k;1)`, with
`e_n` replaced by `ν_k` (see `approx1D_limit_frequency_eq_one_coord`). Rotating `u_k` by an
isometry sending `e_n` to `ν_k` reduces this form to the paper's. The paper concludes along
the subsequence of Lemma 5.1. The limit `1` does not depend on the subsequence, so the whole
sequence converges.

**Use in the proof of Theorem 6.3.** The paper renormalizes at `a_0^k` at scale `18`, which
uses the pinching `N_{a_0}(u_k; 36) − N_{a_0}(u_k; 9) → 0`, while `[1, 20]` is the range
controlled. We apply this theorem to `ũ_k(y) = u_k(a_0 + 10 y)/10` instead
(any scale in `[8, 10]` works). The pinching interval `[1/2, 2]` then maps into
`[5, 20] ⊆ [1, 20]`, and `A ↦ B_{10}(a_0) \ B̄_5(a_0) ⊆ B_{18}(a_0) \ B_4(a_0)`. -/
theorem approx1D_limit_frequency_eq_one [NeZero n] (_hn : 2 ≤ n) {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0)) :
    Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 1) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hfreq := fun k => (hsol k).frequencyN_half_le_one_le_two hΩ (hcl k) (hM k)
  have hb : ∀ k, frequencyN (u (ns k)) (χ (ns k)) 0 (1 / 2) ∈ Icc 1 Nplus := fun k =>
    ⟨(hfreq _).1, (hfreq _).2.1.trans ((hfreq _).2.2.trans (hN _))⟩
  obtain ⟨Ninf, -, ms, hms, hlim⟩ := isCompact_Icc.tendsto_subseq hb
  have hns' : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  have h1 := eq_one_of_tendsto_frequencyN_half (u := fun k => u (ns (ms k)))
    (χ := fun k => χ (ns (ms k))) (C_V := fun k => C_V (ns (ms k))) (ν := fun k => ν (ns (ms k)))
    (fun k => hν _) (fun k => hsol _) hΩ (fun k => hcl _) (fun k => hM _) (fun k => hN _)
    (hδ.comp hns') (htan.comp hns') (Ninf := Ninf) hlim
  exact ⟨ms, h1 ▸ hlim⟩

/-- **Theorem 5.3, refined form (strong `W^{1,2}` convergence on `A' = B_{7/8} \ B̄_{5/8}`).**
Under the hypotheses of `approx1D_limit_frequency_eq_one`, with `H_k = H_0(u_k; 1)`:
* `N_0(u_k; 1/2) → 1`;
* `∫_{A'} (u_k − √H_k α(n) |y·ν_k|)² / H_k → 0`;
* `∫_{A'} |∇u_k − √H_k α(n) ∇|y·ν_k||² / H_k → 0`.

The last two say `v_k = u_k/√H_k` is `W^{1,2}(A')`-close to `α(n)|y·ν_k|`. For constant `ν_k = ν`
this is strong convergence `v_k → α(n)|y·ν|`. This is the paper's `v = α(n)|x_n|` on `A` (the
conclusion of Theorem 5.3, with `α(n)` fixed by the normalization) together with the strong
convergence on `A'` from step (d) of its proof. The proof is `tendsto_profile_of_renormalized`
applied to `v_k = u_k/√H_k` (`renormalized_properties`). `∇|y·ν_k|` is Mathlib's `gradient`,
which is `sgn(y·ν_k) ν_k` off the null hyperplane `{y·ν_k = 0}`. The paper gets these along a
subsequence. The limit profile does not depend on the subsequence, so they hold for the whole
sequence. -/
theorem approx1D_limit_tendsto_profile [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0)) :
    Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 1) ∧
    Tendsto (fun k => (∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        (u k y - √(heightH (u k) 0 1) * alphaN n * absProfile (ν k) 0 y) ^ 2) /
          heightH (u k) 0 1) atTop (𝓝 0) ∧
    Tendsto (fun k => (∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        ‖gradient (u k) y -
          (√(heightH (u k) 0 1) * alphaN n) • gradient (absProfile (ν k) 0) y‖ ^ 2) /
          heightH (u k) 0 1) atTop (𝓝 0) := by
  have h1 := approx1D_limit_frequency_eq_one hn hν hsol hΩ hcl hM hN hδ htan
  refine ⟨h1, ?_⟩
  obtain ⟨hLip, ⟨C, hbd⟩, hnn, hE, htan', -, hdv, henergy, hmassLim⟩ :=
    renormalized_properties hsol hΩ hcl hM hN hδ htan h1
      (fun k y => (√(heightH (u k) 0 1))⁻¹ * u k y) fun _ _ => rfl
  obtain ⟨hR1, hR2⟩ := tendsto_profile_of_renormalized hn _ hν hLip hbd hnn
    (by simpa only [one_mul] using hE) htan' (hmassLim rfl) hdv henergy
  have hH : ∀ k, 0 < heightH (u k) 0 1 := fun k => (hsol k).heightH_one_pos hΩ (hcl k)
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

/-! ### The paper's coordinate form -/

/-- The last coordinate index `n - 1 : Fin n` (the paper's `x_n`). -/
def lastCoord (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) one_pos⟩

/-- The tangential part of a vector with respect to `e_n` has squared norm
`Σ_{i < n-1} vᵢ²`. -/
theorem norm_sub_inner_single_lastCoord_sq [NeZero n] (g : Rn n) :
    ‖g - ⟪g, EuclideanSpace.single (lastCoord n) (1 : ℝ)⟫ •
      EuclideanSpace.single (lastCoord n) 1‖ ^ 2 =
      ∑ i : Fin n, if (i : ℕ) < n - 1 then g i ^ 2 else 0 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hlast : ((lastCoord n : Fin n) : ℕ) = n - 1 := rfl
  have hi : (i : ℕ) < n - 1 ↔ i ≠ lastCoord n := by
    rw [Ne, Fin.ext_iff, hlast]
    have := i.isLt
    omega
  simp only [EuclideanSpace.inner_single_right, one_mul, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, conj_trivial]
  by_cases h : i = lastCoord n
  · subst h
    simp [hi]
  · simp [h, hi]

/-- **Theorem 5.3, the paper's coordinate form**: the hypothesis
`Σ_{i<n} ∫_A |∂_i v_k|² → 0` in coordinates, the free direction being the last coordinate `x_n`,
as in the statement of Theorem 5.3. It is derived from `approx1D_limit_frequency_eq_one` with
`ν = e_n`. -/
theorem approx1D_limit_frequency_eq_one_coord [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ}
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∑ i : Fin n, if (i : ℕ) < n - 1 then
        ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
          (fderiv ℝ (u k) y (EuclideanSpace.single i 1)) ^ 2 else 0) /
        heightH (u k) 0 1) atTop (𝓝 0)) :
    Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 1) := by
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  set ν : Rn n := EuclideanSpace.single (lastCoord n) 1
  have hν : ∀ _ : ℕ, ‖ν‖ = 1 := fun _ => by simp [ν]
  refine approx1D_limit_frequency_eq_one (ν := fun _ => ν) hn hν hsol hΩ hcl hM hN hδ ?_
  refine htan.congr fun k => ?_
  congr 1
  -- `A` lies in `B_2`, where `u k` is `C_V k`-Lipschitz, so the partials are bounded there.
  have hAB : A ⊆ ball (0 : Rn n) 2 := fun y hy =>
    mem_ball.2 ((mem_ball.1 (diff_subset hy)).trans (by norm_num))
  have hlip := (hsol k).lipschitzOnWith 0 2 (ball_subset_closedBall.trans hΩ)
  have hAfin : volume A ≠ ⊤ := (measure_mono (diff_subset.trans (subset_refl _))).trans_lt
    (measure_ball_lt_top (x := (0 : Rn n)) (r := 1)) |>.ne
  have hint : ∀ i : Fin n,
      IntegrableOn (fun y => (fderiv ℝ (u k) y (EuclideanSpace.single i 1)) ^ 2) A := by
    intro i
    refine Measure.integrableOn_of_bounded (M := (C_V k : ℝ) ^ 2) hAfin
      ((measurable_fderiv_apply_const ℝ (u k) _).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_ball.diff measurableSet_closedBall)]
      with y hy
    have h1 : ‖fderiv ℝ (u k) y (EuclideanSpace.single i 1)‖ ≤ C_V k := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
      rw [this, mul_one]
      exact norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds (hAB hy)) hlip
    rw [Real.norm_eq_abs, abs_pow, sq_abs, ← sq_abs]
    rw [Real.norm_eq_abs] at h1
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hpt : ∀ y, ‖gradient (u k) y - ⟪gradient (u k) y, ν⟫ • ν‖ ^ 2 =
      ∑ i : Fin n, if (i : ℕ) < n - 1 then
        (fderiv ℝ (u k) y (EuclideanSpace.single i 1)) ^ 2 else 0 := by
    intro y
    rw [norm_sub_inner_single_lastCoord_sq]
    simp_rw [gradient_apply_eq_fderiv]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [hA]
  · split_ifs
    · exact hint i
    · exact integrableOn_zero

end InnerVariational
