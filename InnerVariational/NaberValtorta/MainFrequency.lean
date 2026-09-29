/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Main
public import InnerVariational.Kernel.Rescale
public import InnerVariational.Estimates.Dichotomy.Rescale
import InnerVariational.NaberValtorta.Instance
import InnerVariational.NaberValtorta.CoveringLimit
import InnerVariational.NaberValtorta.Reifenberg
public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Defs.VariationalSolution

/-!
# Theorem 7.2 (3): `N_x(u; 0+) = 1` at `ℋ^{n-1}`-a.e. point of `Σ^H`

`NaberValtorta.sigmaH_main_frequency` has exactly the statement of
`Statements.sigmaH_main_frequency`, Theorem 7.2 (3) of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2), which is proved by it.

## Proof

1. **Local form** (`hausdorffN_not_tendsto_frequencyN_ball_eq_zero`). For a variational solution
   on an open `Ω ⊇ B̄_1` with `0 ∈ Σ^H(B_1)`, the exceptional set inside `Σ^H(B_1) ∩ B_{1/100}` is
   `ℋ^{n-1}`-null. This is the fourth conclusion of `hausdorffN_le_and_rectifiable_and_frequency`
   on each ball of the finite cover of `sigmaH_main`, with the data of `NaberValtorta/Instance.lean`
   and `N₊ := N_0(u; 1)` (the terminal balls of the covering, as in the paper's proof of (3)).
2. **Rescaling** (`hausdorffN_not_tendsto_frequencyN_inter_ball_eq_zero`). For `x₀ ∈ Σ^H(Ω)` and
   `B̄_{ρ₀}(x₀) ⊆ Ω`, the rescaling `u_{x₀,ρ₀}` is a solution on `T⁻¹Ω ⊇ B̄_1`, `T y = x₀ + ρ₀ y`,
   with `0 ∈ Σ^H(B_1)`. The frequencies transform by `N_y(u_{x₀,ρ₀}; s) = N_{Ty}(u; ρ₀ s)`, and
   `ℋ^{n-1}(A) = ρ₀^{n-1} ℋ^{n-1}(T⁻¹A)`, so the exceptional set in `B_{ρ₀/100}(x₀)` is null.
3. **Countable cover** (`hausdorffN_not_tendsto_frequencyN_eq_zero`). The balls
   `B_{ρ(x₀)/100}(x₀)`, `x₀ ∈ Σ^H(Ω)`, have a countable subcover (Lindelöf).

The hypotheses `N_0(u; 1) ≤ N₊` and `0 ∈ Σ^H ∨ 0 ∈ Σ^H_t` of the printed statement are not needed:
the conclusion is local and qualitative, and every point of `Σ^H` serves as a centre. In particular
the conclusion does not read `u` on `∂B_1` (unlike (1)–(2), see `Statements.sigmaH_main`), and it
holds for every open `Ω`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Rescaling at a general point -/

section Rescale

theorem oneHomRescale_oneHomRescale_one (u : Rn n → ℝ) (a y : Rn n) (ρ : ℝ) :
    oneHomRescale (oneHomRescale u a ρ) y 1 = oneHomRescale u (a + ρ • y) ρ := by
  funext z
  simp only [oneHomRescale_apply, one_smul, div_one, smul_add, add_assoc]

theorem chiRescale_chiRescale_one (χ : Rn n → ℝ) (a y : Rn n) (ρ : ℝ) :
    chiRescale (chiRescale χ a ρ) y 1 = chiRescale χ (a + ρ • y) ρ := by
  funext z
  simp only [chiRescale_apply, one_smul, smul_add, add_assoc]

/-- `N_y(u_{a,ρ}; s) = N_{a+ρy}(u; ρ s)`. -/
theorem frequencyN_oneHomRescale_apply [NeZero n] (u χ : Rn n → ℝ) (a y : Rn n) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) :
    frequencyN (oneHomRescale u a ρ) (chiRescale χ a ρ) y s =
      frequencyN u χ (a + ρ • y) (ρ * s) := by
  have h1 := Dichotomy.frequencyN_oneHomRescale (oneHomRescale u a ρ) (chiRescale χ a ρ) y
    one_pos s
  rw [one_mul, oneHomRescale_oneHomRescale_one, chiRescale_chiRescale_one] at h1
  rw [← h1, Dichotomy.frequencyN_oneHomRescale u χ (a + ρ • y) hρ]

/-- `M_y(u_{a,ρ}; s) = M_{a+ρy}(u; ρ s)`. -/
theorem monotonicityM_oneHomRescale_apply [NeZero n] (u χ : Rn n → ℝ) (a y : Rn n) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) :
    monotonicityM (oneHomRescale u a ρ) (chiRescale χ a ρ) y s =
      monotonicityM u χ (a + ρ • y) (ρ * s) := by
  have h1 := Dichotomy.monotonicityM_oneHomRescale (oneHomRescale u a ρ) (chiRescale χ a ρ) y
    one_pos s
  rw [one_mul, oneHomRescale_oneHomRescale_one, chiRescale_chiRescale_one] at h1
  rw [← h1, Dichotomy.monotonicityM_oneHomRescale u χ (a + ρ • y) hρ]

/-- `y ∈ closure {u_{a,ρ} > 0}` if and only if `a + ρ y ∈ closure {u > 0}`. -/
theorem mem_closure_oneHomRescale_iff (u : Rn n → ℝ) (a y : Rn n) {ρ : ℝ} (hρ : 0 < ρ) :
    y ∈ closure {z | 0 < oneHomRescale u a ρ z} ↔ a + ρ • y ∈ closure {z | 0 < u z} := by
  rw [← Dichotomy.zero_mem_closure_oneHomRescale_iff (oneHomRescale u a ρ) y one_pos,
    oneHomRescale_oneHomRescale_one, Dichotomy.zero_mem_closure_oneHomRescale_iff u _ hρ]

/-- If `B̄_r(y) ⊆ B_1`, then `B̄_{ρr}(a + ρy) ⊆ B_ρ(a)`. -/
theorem closedBall_add_smul_subset_ball {a y : Rn n} {ρ r : ℝ} (hρ : 0 < ρ)
    (hy : closedBall y r ⊆ ball 0 1) : closedBall (a + ρ • y) (ρ * r) ⊆ ball a ρ := by
  intro z hz
  set w : Rn n := y + ρ⁻¹ • (z - (a + ρ • y)) with hw
  have hwy : w ∈ closedBall y r := by
    rw [mem_closedBall, dist_eq_norm, hw, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hρ, ← dist_eq_norm]
    rw [mem_closedBall] at hz
    rw [inv_mul_le_iff₀ hρ]
    exact hz
  have hw1 : ‖w‖ < 1 := by simpa using hy hwy
  have hza : z - a = ρ • w := by
    rw [hw, smul_add, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
    abel
  rw [mem_ball, dist_eq_norm, hza, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  calc ρ * ‖w‖ < ρ * 1 := mul_lt_mul_of_pos_left hw1 hρ
    _ = ρ := mul_one ρ

/-- `s ↦ s / ρ` maps `𝓝[>] 0` to itself for `ρ > 0`. -/
theorem tendsto_div_const_nhdsGT_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun s : ℝ => s / ρ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h := ((continuous_id.div_const ρ).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact div_pos hs hρ

end Rescale

/-! ### Theorem 7.2 (3) -/

/-- **Theorem 7.2 (3), local form**. For a variational solution on an
open `Ω ⊇ B̄_1` with `0 ∈ Σ^H(B_1)`, `N_x(u; r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e.
`x ∈ Σ^H(B_1) ∩ B_{1/100}`. -/
theorem hausdorffN_not_tendsto_frequencyN_ball_eq_zero (hn : 2 ≤ n) {Ω : Set (Rn n)}
    {C_V : ℝ≥0} {u χ : Rn n → ℝ} (h : IsVariationalSolution Ω C_V u χ)
    (hΩ : closedBall 0 1 ⊆ Ω) (h0 : (0 : Rn n) ∈ sigmaH (ball 0 1) u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100) ∧
      ¬ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)} = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  -- constants, with `N₊ := N_0(u; 1)`
  obtain ⟨Np, hNp⟩ := Inputs.frequencyN_change_of_point n (frequencyN u χ 0 1)
  obtain ⟨CJ, hCJ⟩ := Inputs.jonesBetaSq_le n Np
  set ε := dichotomyEps n hn Np with hε_def
  have hεpos : ∀ δ, 0 < δ → 0 < ε δ := fun δ hδ => (dichotomyEps_spec n hn Np hδ).1.1
  obtain ⟨C₂, -, H₂⟩ := hausdorffN_le_and_rectifiable_and_frequency hn CJ Np ε hεpos
  -- the cover
  set r₀ : ℝ := 1 / 240 with hr₀_def
  have hr₀ : 0 < r₀ := by norm_num [hr₀_def]
  obtain ⟨F', hF'sub, hF'fin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Rn n) (1 / 100)) hr₀
  set F := hF'fin.toFinset with hF_def
  have hcK : ∀ c ∈ F, closedBall c (5 * r₀) ⊆ closedBall (0 : Rn n) (1 / 10) := by
    intro c hc
    have := mem_closedBall.1 (hF'sub (hF'fin.mem_toFinset.1 hc))
    refine closedBall_subset_closedBall' ?_
    rw [hr₀_def]
    linarith
  have hBK : ball (0 : Rn n) (1 / 100) ⊆ closedBall 0 (1 / 10) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  -- the specialised upstream facts
  have hCJu := fun x r μ => hCJ Ω C_V u χ x r μ h
  have hεu : ∀ δ, 0 < δ → ∀ (x : Rn n) (r t : ℝ), 0 < r → ball x (50 * r) ⊆ Ω →
      t ∈ Icc 0 r → (closedBall x r ∩ sigmaHr Ω u χ t).Nonempty →
      let Nmax := sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ L : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ L.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHr Ω u χ t | Nmax - frequencyN u χ y r < ε δ} ⊆
          thickening (δ * r) (L : Set (Rn n)) :=
    fun δ hδ x r t => (dichotomyEps_spec n hn Np hδ).2 Ω C_V u χ x r t h
  have hM4 : unitBallVolume n ≤ monotonicityM u χ 0 (1 / 4) :=
    h0.2.2 (1 / 4) (by norm_num) (closedBall_subset_ball' (by norm_num))
  have hN : ∀ z ∈ closedBall (0 : Rn n) (1 / 10), ∀ ρ, 0 < ρ → ρ < 1 / 2 →
      frequencyN u χ z ρ ≤ Np := by
    intro z hz ρ hρ hρ2
    refine hNp Ω C_V u χ 0 1 h one_pos hΩ h0.2.1 hM4 le_rfl z ?_ ρ hρ (by linarith)
    have := mem_closedBall.1 hz
    rw [mem_ball]
    linarith
  let J := solJonesData h hΩ hCJu (sigmaH (ball 0 1) u χ ∩ closedBall 0 (1 / 10)) 0 le_rfl
    (measurableSet_sigmaH_inter h hΩ) inter_subset_right
    (fun z hz ρ hρ _ hρ6 => (mem_sigmaHr_ball_iff hΩ hz.2 (by linarith)).1
      (mem_sigmaHr_of_mem_sigmaH hz.1 hρ (closedBall_subset_ball_one hz.2 (by linarith))))
    (fun z hz => hN z hz.2)
  have hD : ∀ c ∈ F, ∀ s, 0 < s → ∃ D : NVData n CJ Np ε, D.t ≤ s ∧
      J.S ∩ closedBall c (5 * r₀) ⊆ D.S ∧
      (∀ z ∈ J.S ∩ closedBall c (5 * r₀), D.N z = J.N z) ∧
      2 * r₀ ≤ D.R ∧ closedBall c (5 * r₀) ⊆ D.K := by
    intro c hc s hs
    have hτ : 0 < min s r₀ := lt_min hs hr₀
    have hτR : min s r₀ ≤ 1 / 120 := (min_le_right _ _).trans (by rw [hr₀_def]; norm_num)
    refine ⟨solNVData h hΩ hCJu ε hεu (min s r₀) hτ hτR hN, min_le_left _ _, ?_,
      fun z _ => rfl, by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num, hcK c hc⟩
    rintro z ⟨⟨hzH, hzK⟩, -⟩
    refine ⟨(mem_sigmaHr_ball_iff hΩ hzK (by linarith)).1
      (mem_sigmaHr_of_mem_sigmaH hzH hτ (closedBall_subset_ball_one hzK (by linarith))), hzK⟩
  have H := fun c (hc : c ∈ F) => H₂ J c r₀ rfl hr₀
    (by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num) (hD c hc)
  refine measure_mono_null ?_
    ((measure_biUnion_null_iff F.countable_toSet).2 fun c hc => (H c hc).2.2.2)
  rintro x ⟨⟨hxH, hxB⟩, hxN⟩
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcover (ball_subset_closedBall hxB))
  refine mem_iUnion₂.2 ⟨c, hF'fin.mem_toFinset.2 hc, ⟨⟨hxH, hBK hxB⟩, hxc⟩, fun hT => hxN ?_⟩
  refine hT.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
  exact solN_eq h hΩ (hBK hxB) hr.1.le (by linarith [hr.2])

/-- **Theorem 7.2 (3), rescaled local form.** Let `(u, χ)` be a variational solution on `Ω`,
`x₀ ∈ Σ^H(Ω)` and `B̄_{ρ₀}(x₀) ⊆ Ω`. Then `N_x(u; r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e.
`x ∈ Σ^H(Ω) ∩ B_{ρ₀/100}(x₀)`. Proof: the local form for `u_{x₀,ρ₀}` on `T⁻¹Ω ⊇ B̄_1`,
`T y = x₀ + ρ₀ y`. -/
theorem hausdorffN_not_tendsto_frequencyN_inter_ball_eq_zero (hn : 2 ≤ n) {Ω : Set (Rn n)}
    {C_V : ℝ≥0} {u χ : Rn n → ℝ} (h : IsVariationalSolution Ω C_V u χ) {x₀ : Rn n}
    (hx₀ : x₀ ∈ sigmaH Ω u χ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hB : closedBall x₀ ρ₀ ⊆ Ω) :
    hausdorffN n (n - 1) {x | (x ∈ sigmaH Ω u χ ∧ ¬ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)) ∧
      x ∈ ball x₀ (ρ₀ / 100)} = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have hsol := h.rescale x₀ hρ₀
  have hΩ' : closedBall (0 : Rn n) 1 ⊆ (fun y => x₀ + ρ₀ • y) ⁻¹' Ω := by
    intro y hy
    refine hB ?_
    rw [mem_closedBall, dist_zero_right] at hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ₀.le]
    calc ρ₀ * ‖y‖ ≤ ρ₀ * 1 := mul_le_mul_of_nonneg_left hy hρ₀.le
      _ = ρ₀ := mul_one ρ₀
  have hmem : ∀ y : Rn n, x₀ + ρ₀ • y ∈ sigmaH Ω u χ → ‖y‖ < 1 →
      y ∈ sigmaH (ball 0 1) (oneHomRescale u x₀ ρ₀) (chiRescale χ x₀ ρ₀) := by
    intro y hy hy1
    refine ⟨mem_ball_zero_iff.2 hy1, (mem_closure_oneHomRescale_iff u x₀ y hρ₀).2 hy.2.1,
      fun r hr hrB => ?_⟩
    rw [monotonicityM_oneHomRescale_apply u χ x₀ y hρ₀]
    exact hy.2.2 (ρ₀ * r) (mul_pos hρ₀ hr)
      ((closedBall_add_smul_subset_ball hρ₀ hrB).trans (ball_subset_closedBall.trans hB))
  have h0 : (0 : Rn n) ∈ sigmaH (ball 0 1) (oneHomRescale u x₀ ρ₀) (chiRescale χ x₀ ρ₀) :=
    hmem 0 (by simpa using hx₀) (by simp)
  have hloc := hausdorffN_not_tendsto_frequencyN_ball_eq_zero hn hsol hΩ' h0
  rw [hausdorffN_eq_mul_preimage_affine (p := x₀) hρ₀ (n - 1)]
  refine mul_eq_zero_of_right _ (measure_mono_null ?_ hloc)
  rintro y ⟨⟨hyH, hyN⟩, hyB⟩
  have hy : ‖y‖ < 1 / 100 := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ₀.le]
      at hyB
    have h1 : ρ₀ * ‖y‖ < ρ₀ * (1 / 100) := by linarith
    exact lt_of_mul_lt_mul_left h1 hρ₀.le
  refine ⟨⟨hmem y hyH (by linarith), mem_ball_zero_iff.2 hy⟩, fun hT => hyN ?_⟩
  refine (hT.comp (tendsto_div_const_nhdsGT_zero hρ₀)).congr fun s => ?_
  rw [Function.comp_apply, frequencyN_oneHomRescale_apply u χ x₀ y hρ₀]
  congr 1
  field_simp

/-- **Theorem 7.2 (3)**, for a variational solution on any open `Ω`:
`N_x(u; r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e. `x ∈ Σ^H(Ω)`. Proof: cover `Σ^H(Ω)` by countably
many balls `B_{ρ(x₀)/100}(x₀)`, `x₀ ∈ Σ^H(Ω)`, `B̄_{ρ(x₀)}(x₀) ⊆ Ω` (Lindelöf), and use the
rescaled local form on each. -/
theorem hausdorffN_not_tendsto_frequencyN_eq_zero (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0}
    {u χ : Rn n → ℝ} (h : IsVariationalSolution Ω C_V u χ) :
    hausdorffN n (n - 1)
      {x | x ∈ sigmaH Ω u χ ∧ ¬ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)} = 0 := by
  have hρ : ∀ x ∈ Ω, ∃ ρ, 0 < ρ ∧ closedBall x ρ ⊆ Ω := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hx
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεΩ⟩
  choose! ρ hρpos hρsub using hρ
  set E := {x | x ∈ sigmaH Ω u χ ∧ ¬ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)} with hE
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : sigmaH Ω u χ => ball (i : Rn n) (ρ i / 100)) fun _ => isOpen_ball
  have hcov : E ⊆ ⋃ i ∈ T, E ∩ ball (i : Rn n) (ρ i / 100) := by
    intro x hx
    have hx' : x ∈ ⋃ i : sigmaH Ω u χ, ball (i : Rn n) (ρ i / 100) := by
      have := hρpos x hx.1.1
      exact mem_iUnion.2 ⟨⟨x, hx.1⟩, mem_ball_self (by positivity)⟩
    rw [← hTU] at hx'
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx'
    exact mem_iUnion₂.2 ⟨i, hi, hx, hxi⟩
  refine measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
  exact hausdorffN_not_tendsto_frequencyN_inter_ball_eq_zero hn h i.2 (hρpos i i.2.1)
    (hρsub i i.2.1)

/-- **Theorem 7.2 (3)**, with exactly the statement of
`Statements.sigmaH_main_frequency`: `N_x(u; 0+) = 1` for `ℋ^{n-1}`-a.e. `x ∈ Σ^H(B_1)`.
The hypotheses `N_0(u; 1) ≤ N₊` and `0 ∈ Σ^H ∨ 0 ∈ Σ^H_t` are not used (see the module
docstring): this is `hausdorffN_not_tendsto_frequencyN_eq_zero` for `Ω = B_1`. -/
theorem sigmaH_main_frequency (hn : 2 ≤ n) {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution (ball 0 1) C_V u χ) (Nplus : ℝ) (_hN : frequencyN u χ 0 1 ≤ Nplus)
    (_h0 : (0 : Rn n) ∈ sigmaH (ball 0 1) u χ ∨
      ∃ t : ℝ, 0 < t ∧ (0 : Rn n) ∈ sigmaHr (ball 0 1) u χ t) :
    hausdorffN n (n - 1)
      {x | x ∈ sigmaH (ball 0 1) u χ ∧ ¬ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)} = 0 :=
  hausdorffN_not_tendsto_frequencyN_eq_zero hn h

end InnerVariational.NaberValtorta
