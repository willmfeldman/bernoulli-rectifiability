/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.ConcreteQ.ChangeOfPoint
public import InnerVariational.Monotonicity.LimitsQ
public import InnerVariational.Defs.HighestDensity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `Σ^H` and `Σ^H_r` with a Lipschitz coefficient (preamble of Section 6)

Let `(u, χ)` be a variational solution for a Lipschitz coefficient `Q` with
`QBounds Ω Q L c C'`, and `κ = 2 C' L / c²` (`weissKappa L c C'`). The set of highest density is
`Σ^H_Q = sigmaHQ Ω Q u χ = {x : M^{Q(x)}_x(0+) ≥ Q(x)² |B_1|}` (`Defs/VariationalSolutionQ.lean`).
Its radius-`r` version is defined here through the shifted Weiss energy
`Z_x(r) = M^w_x(r) − Q(x)² |B_1| + (κ² r² / 8) H_x(r)` (`modMonotonicityM`):

`Σ^H_{Q,r} = sigmaHQr Ω Q u χ κ r = {x ∈ Ω : B̄_r(x) ⊆ Ω, x ∈ closure {u > 0}, Z_x(r) ≥ 0}`.

For `Q ≡ 1` we have `κ = 0` and `Z_x(r) = M_x(r) − |B_1|`, so this is `Σ^H_r`.

## Main results

* `IsVariationalSolutionQ.modMonotonicityM_nonneg_of_mem_sigmaHQ`: `Z_x(0+) ≥ 0` on `Σ^H_Q`,
  hence `Z_x(r) ≥ 0` for every admissible `r` with `κ r ≤ 1/2`. The proof compares `M^w` with
  the Weiss energy with frozen coefficient (`abs_monotonicityMq_sub_le`, the two differ by
  `O(s)`) and propagates `Z ≥ −ε` from a small radius with the first-crossing bound for `Z`.
* `IsVariationalSolutionQ.mem_sigmaHQr_of_mem_sigmaHQ`: `Σ^H_Q ∩ Ω_r ⊆ Σ^H_{Q,r}` when
  `κ r ≤ 1/2`.
* `IsVariationalSolutionQ.mem_sigmaHQr_of_le`: `Σ^H_{Q,s} ∩ Ω_r ⊆ Σ^H_{Q,r}` for `s ≤ r`,
  `κ r ≤ 1/2`.
* `IsVariationalSolutionQ.closure_sigmaHQr_inter_subset`: `Σ^H_{Q,r}` is relatively closed in
  `Ω_r = {x : B̄_r(x) ⊆ Ω}`.
* On `Σ^H_Q`: `N_x ≥ 1 − κ² s² / 8`, `Ñ_x ≥ 1`, `Ñ_x` is nondecreasing, and
  `Ñ_x(0+) = N_x(0+) ≥ 1` exists (`exists_tendsto_modFrequencyN_zero`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The radius-`r` set of highest density for a Lipschitz coefficient,
`Σ^H_{Q,r} = {x ∈ Ω : B̄_r(x) ⊆ Ω, x ∈ closure {u > 0}, Z_x(r) ≥ 0}`, where `Z` is the shifted
Weiss energy `modMonotonicityM κ`. -/
def sigmaHQr (Ω : Set (Rn n)) (Q u χ : Rn n → ℝ) (κ r : ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ closedBall x r ⊆ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    0 ≤ modMonotonicityM κ Q u χ x r}

theorem sigmaHQr_subset (Ω : Set (Rn n)) (Q u χ : Rn n → ℝ) (κ r : ℝ) :
    sigmaHQr Ω Q u χ κ r ⊆ Ω :=
  fun _ hx => hx.1

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
include hQ h

/-- `Σ^H_{Q,s} ∩ Ω_r ⊆ Σ^H_{Q,r}` for `0 < s ≤ r` with `κ r ≤ 1/2`: `Z ≥ 0` propagates outwards. -/
theorem mem_sigmaHQr_of_le {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hκ : weissKappa L c C' * r ≤ 1 / 2) (hx : x ∈ sigmaHQr Ω Q u χ (weissKappa L c C') s)
    (hr : closedBall x r ⊆ Ω) : x ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r :=
  ⟨hx.1, hr, hx.2.2.1, h.modMonotonicityM_nonneg hQ hx.2.2.1 hs hx.2.2.2 hκ hr ⟨hsr, le_rfl⟩⟩

/-- **`Σ^H_{Q,r}` is relatively closed in `Ω_r`**: a limit point of `Σ^H_{Q,r}` that lies in
`Ω_r = {x : B̄_r(x) ⊆ Ω}` lies in `Σ^H_{Q,r}`, by the continuity of `x ↦ Z_x(r)`. -/
theorem closure_sigmaHQr_inter_subset (κ : ℝ) {r : ℝ} (hr : 0 < r) :
    closure (sigmaHQr Ω Q u χ κ r) ∩ {x | closedBall x r ⊆ Ω} ⊆ sigmaHQr Ω Q u χ κ r := by
  rintro y ⟨hycl, hyr⟩
  have hyr' : closedBall y r ⊆ Ω := hyr
  refine ⟨hyr' (mem_closedBall_self hr.le), hyr', ?_, ?_⟩
  · exact closure_minimal (fun z (hz : z ∈ sigmaHQr Ω Q u χ κ r) => hz.2.2.1) isClosed_closure
      hycl
  · have hc := h.continuousAt_modMonotonicityM hQ κ hr hyr'
    haveI := mem_closure_iff_nhdsWithin_neBot.1 hycl
    exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun z (hz : z ∈ sigmaHQr Ω Q u χ κ r) => hz.2.2.2)

/-- **`Z(0+) ≥ 0` on `Σ^H_Q`**: if `x ∈ Σ^H_Q`, `0 < r`, `κ r ≤ 1/2` and `B̄_r(x) ⊆ Ω`, then
`Z_x(r) ≥ 0`.

Given `ε > 0`, the limit `M^{Q(x)}_x(0+) ≥ Q(x)² |B_1|` and the comparison
`|M^{Q(x)}_x(a) − M^w_x(a)| ≤ B a` give `Z_x(a) ≥ M^w_x(a) − Q(x)² |B_1| ≥ −2ε` at some small
radius `a`; the first-crossing bound gives `Z_x(r) ≥ −2 e^{2κ r} ε ≥ −2e ε`. -/
theorem modMonotonicityM_nonneg_of_mem_sigmaHQ (hx : x ∈ sigmaHQ Ω Q u χ) {r : ℝ} (hr : 0 < r)
    (hκ : weissKappa L c C' * r ≤ 1 / 2) (hΩ : closedBall x r ⊆ Ω) :
    0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x r := by
  set κ := weissKappa L c C' with hκdef
  set ω := Q x ^ 2 * unitBallVolume n with hω
  have hxΩ : x ∈ Ω := hx.1
  have hk : 0 ≤ κ := hQ.weissKappa_nonneg hxΩ
  set B := weissCompConst n L C' with hB
  have hB0 : 0 ≤ B := hQ.weissCompConst_nonneg hxΩ
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen hr.le hΩ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a small radius `a` with `M^w_x(a) > ω − ε/4`
  have hlt : (((ω - ε / 8 : ℝ)) : EReal) < MzeroQ (Q x) u χ x :=
    (EReal.coe_lt_coe_iff.2 (by linarith)).trans_le hx.2.2
  have hev1 := (h.tendsto_MzeroQ hQ hxΩ).eventually (lt_mem_nhds hlt)
  have hev2 : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < r ∧ B * a < ε / 8 := by
    have ht : Tendsto (fun a : ℝ => B * a) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_mul_nhdsGT_zero B
    filter_upwards [Ioo_mem_nhdsGT hr, ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 8)),
      self_mem_nhdsWithin] with a ha1 ha2 _
    exact ⟨ha1.2, ha2⟩
  obtain ⟨a, ha, ⟨har, haB⟩, ha0⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
  have ha0' : 0 < a := ha0
  have haΩ : ball x a ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall har.le).trans hΩ)
  have hcomp := (abs_le.1 (h.abs_monotonicityMq_sub_le hQ ha0' haΩ)).2
  have hMa : ω - ε / 8 < monotonicityMq (Q x) u χ x a := EReal.coe_lt_coe_iff.1 ha
  -- `Z_x(a) ≥ −ε/4`
  have hHa : 0 ≤ heightH u x a := heightH_nonneg u x ha0'.le
  have hZa : -(ε / 4) ≤ modMonotonicityM κ Q u χ x a := by
    have : 0 ≤ κ ^ 2 * a ^ 2 / 8 * heightH u x a := by positivity
    rw [modMonotonicityM]
    linarith
  -- first crossing on `[a, r]`
  let d := h.radialDataErr hQ hR' ha0' har.le hRR'
  have hH : ∀ s ∈ Icc a r, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hQ hx.2.1 (ha0'.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  have hcross := d.modM_ge hH hκ (right_mem_Icc.2 har.le)
  have hexp : Real.exp (2 * κ * (r - a)) ≤ 3 := by
    have h1 : 2 * κ * (r - a) ≤ 1 := by nlinarith
    exact (Real.exp_le_exp.2 h1).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hmin : -(ε / 4) ≤ min (d.modM a) 0 := le_min hZa (by linarith)
  have hmin0 : min (d.modM a) 0 ≤ 0 := min_le_right _ _
  have hE0 : 0 ≤ Real.exp (2 * κ * (r - a)) := (Real.exp_pos _).le
  have h3 : 3 * -(ε / 4) ≤ Real.exp (2 * κ * (r - a)) * min (d.modM a) 0 := by
    nlinarith
  have hZr : 3 * -(ε / 4) ≤ modMonotonicityM κ Q u χ x r := h3.trans hcross
  linarith

/-- `Σ^H_Q ∩ Ω_r ⊆ Σ^H_{Q,r}` when `κ r ≤ 1/2`. -/
theorem mem_sigmaHQr_of_mem_sigmaHQ (hx : x ∈ sigmaHQ Ω Q u χ) {r : ℝ} (hr : 0 < r)
    (hκ : weissKappa L c C' * r ≤ 1 / 2) (hΩ : closedBall x r ⊆ Ω) :
    x ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r :=
  ⟨hx.1, hΩ, hx.2.1, h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hx hr hκ hΩ⟩

/-- On `Σ^H_Q`: `Ñ_x` is nondecreasing on `(0, R]` when `B̄_R(x) ⊆ Ω` and `κ R ≤ 1/2`. -/
theorem monotoneOn_modFrequencyN_of_mem_sigmaHQ (hx : x ∈ sigmaHQ Ω Q u χ) {R : ℝ}
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (modFrequencyN (weissKappa L c C') Q u χ x) (Ioc 0 R) := by
  intro s hs t ht hst
  have hk := hQ.weissKappa_nonneg hx.1
  have hκs : weissKappa L c C' * s ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hs.2 hk).trans hκ
  exact h.monotoneOn_modFrequencyN hQ hx.2.1 hs.1
    (h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hx hs.1 hκs
      ((closedBall_subset_closedBall hs.2).trans hΩ)) hκ hΩ ⟨le_rfl, hs.2⟩ ⟨hst, ht.2⟩ hst

/-- On `Σ^H_Q`: `N_x(s) ≥ 1 − κ² s² / 8` and `Ñ_x(s) ≥ 1` for `0 < s`, `κ s ≤ 1/2` and
`B̄_s(x) ⊆ Ω`. -/
theorem frequency_bounds_of_mem_sigmaHQ (hx : x ∈ sigmaHQ Ω Q u χ) {s : ℝ} (hs : 0 < s)
    (hκ : weissKappa L c C' * s ≤ 1 / 2) (hΩ : closedBall x s ⊆ Ω) :
    1 - weissKappa L c C' ^ 2 * s ^ 2 / 8 ≤ weightedFrequencyN Q u χ x s ∧
      1 ≤ modFrequencyN (weissKappa L c C') Q u χ x s := by
  have hb := h.frequency_bounds hQ hx.2.1 hs
    (h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ hx hs hκ hΩ) hκ hΩ ⟨le_rfl, le_rfl⟩
  exact ⟨hb.2.2.1, hb.2.2.2⟩

/-- **`Ñ_x(0+) = N_x(0+)` exists and is `≥ 1`** on `Σ^H_Q`. -/
theorem exists_tendsto_modFrequencyN_zero (hx : x ∈ sigmaHQ Ω Q u χ) :
    ∃ N₀, 1 ≤ N₀ ∧ Tendsto (modFrequencyN (weissKappa L c C') Q u χ x) (𝓝[>] 0) (𝓝 N₀) ∧
      Tendsto (weightedFrequencyN Q u χ x) (𝓝[>] 0) (𝓝 N₀) := by
  set κ := weissKappa L c C' with hκdef
  have hk : 0 ≤ κ := hQ.weissKappa_nonneg hx.1
  obtain ⟨R₀, hR₀, hΩ₀⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.isOpen.mem_nhds hx.1)
  set R := min R₀ (1 / (2 * (κ + 1))) with hRdef
  have hR : 0 < R := lt_min hR₀ (by positivity)
  have hΩ : closedBall x R ⊆ Ω := (closedBall_subset_closedBall (min_le_left _ _)).trans hΩ₀
  have hκR : κ * R ≤ 1 / 2 := by
    calc κ * R ≤ κ * (1 / (2 * (κ + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hk
      _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith
  have hmono := (h.monotoneOn_modFrequencyN_of_mem_sigmaHQ hQ hx hκR hΩ).mono Ioo_subset_Ioc_self
  have hne : (Ioo (0 : ℝ) R).Nonempty := nonempty_Ioo.2 hR
  have hge : ∀ b ∈ modFrequencyN κ Q u χ x '' Ioo 0 R, 1 ≤ b := by
    rintro _ ⟨s, hs, rfl⟩
    exact (h.frequency_bounds_of_mem_sigmaHQ hQ hx hs.1
      ((mul_le_mul_of_nonneg_left hs.2.le hk).trans hκR)
      ((closedBall_subset_closedBall hs.2.le).trans hΩ)).2
  set N₀ := sInf (modFrequencyN κ Q u χ x '' Ioo 0 R)
  have hlim : Tendsto (modFrequencyN κ Q u χ x) (𝓝[>] 0) (𝓝 N₀) :=
    hmono.tendsto_nhdsWithin_Ioo_right hne ⟨1, hge⟩
  refine ⟨N₀, le_csInf (hne.image _) hge, hlim, ?_⟩
  have hq : Tendsto (fun s : ℝ => κ ^ 2 * s ^ 2 / 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => κ ^ 2 * s ^ 2 / 2) (𝓝 0) (𝓝 (κ ^ 2 * 0 ^ 2 / 2)) :=
      ((continuous_const.mul (continuous_pow 2)).div_const 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have := hlim.sub hq
  rw [sub_zero] at this
  refine this.congr fun s => ?_
  simp [modFrequencyN]

end IsVariationalSolutionQ

/-! ### The coefficient `Q ≡ 1` -/

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- For `Q ≡ 1`, `Σ^H_{Q,r}` is `Σ^H_r`. -/
theorem sigmaHQr_one (h : IsVariationalSolution Ω C u χ) {r : ℝ} (hr : 0 < r) :
    sigmaHQr Ω (fun _ => 1) u χ 0 r = sigmaHr Ω u χ r := by
  ext y
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [h.modMonotonicityM_one hr (ball_subset_closedBall.trans h2)] at h4
    linarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [h.modMonotonicityM_one hr (ball_subset_closedBall.trans h2)]
    linarith

end IsVariationalSolution

end InnerVariational
