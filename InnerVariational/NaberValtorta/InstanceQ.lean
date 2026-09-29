/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Instance
public import InnerVariational.Estimates.DichotomyQ
public import InnerVariational.Estimates.L2SubspaceQ
public import InnerVariational.Monotonicity.HighestDensityQ

/-!
# The Naber–Valtorta data of a variational solution with a Lipschitz coefficient

This file instantiates the abstract data of `NaberValtorta/Data.lean` for a variational solution
`(u, χ)` with a Lipschitz coefficient `Q` (`QBounds Ω Q L c C'`, `κ = weissKappa L c C'`) on an
open set `Ω ⊇ B̄_1` with `κ ≤ 1/2`, for Section 7 of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2). The abstract Naber–Valtorta theory (Lemma 7.1, the covering argument, the
Reifenberg theorems) does not see the coefficient and is used unchanged.

## The data

As for `Q ≡ 1` (`NaberValtorta/Instance.lean`), `K = B̄_{1/10}` and `R = 1/120`. The frequency is
the modified frequency `Ñ = N + κ² s²/2` (`modFrequencyN`), which is nondecreasing and `≥ 1` on
`Σ^H_{Q,t}` (Lemma 4.1 with a Lipschitz coefficient). Every scale used is at most `1`, so `κ ≤ 1/2`
gives the smallness `κ s ≤ 1/2` needed by Lemmas 4.1 and 4.6 and by Theorems 6.1 and 6.3.

* `N z r := Ñ_z(ũ; r)` for the extensions by zero `Q̃, ũ, χ̃` of `Q, u, χ` outside `Ω`
  (`solNQ`). It is measurable in `z` (`measurable_modFrequencyN`) and agrees with `Ñ_z(u; r)` when
  `B̄_r(z) ⊆ Ω` (`solNQ_eq`).
* `solJonesDataQ`: a `JonesData` on a measurable `S ⊆ K` with `S ⊆ Σ^H_{Q,ρ}(Ω)` for
  `ρ ∈ [t, 1/6]`, `ρ > 0`, and `Ñ_z(u; ρ) ≤ N'` for `ρ ∈ (0, 1/2)`. The Jones field is
  Theorem 6.1 with a Lipschitz coefficient (`jonesBetaSqQ_le`).
* `solNVDataQ`: for `t ∈ (0, R]`, the `NVData` with `S = Σ^H_{Q,t}(Ω) ∩ K`; the dichotomy is
  Theorem 6.3 with a Lipschitz coefficient (`frequency_drop_dichotomyQ`).

`Σ^H_{Q,t}` and `Σ^H_Q` are measurable because they are relatively closed
(`measurableSet_sigmaHQr_inter`, `measurableSet_sigmaHQ`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Measurability in the centre -/

section Measurability

theorem measurable_weightedEnergyD {Q u χ : Rn n → ℝ} (hQ : Measurable Q) (hχ : Measurable χ)
    (r : ℝ) : Measurable fun z => weightedEnergyD Q u χ z r :=
  ((measurable_setIntegral_ball (((measurable_gradient u).norm.pow_const 2).sub
    ((hQ.pow_const 2).mul (measurable_const.sub hχ))) r).const_mul _).add
    ((hQ.pow_const 2).mul_const _)

theorem measurable_weightedFrequencyN {Q u χ : Rn n → ℝ} (hQ : Measurable Q) (hu : Measurable u)
    (hχ : Measurable χ) (r : ℝ) : Measurable fun z => weightedFrequencyN Q u χ z r :=
  ((measurable_weightedEnergyD hQ hχ r).sub ((hQ.pow_const 2).mul_const _)).div
    (measurable_heightH hu r)

/-- `z ↦ Ñ_z(u; r)` is measurable. -/
theorem measurable_modFrequencyN (κ : ℝ) {Q u χ : Rn n → ℝ} (hQ : Measurable Q)
    (hu : Measurable u) (hχ : Measurable χ) (r : ℝ) :
    Measurable fun z => modFrequencyN κ Q u χ z r :=
  (measurable_weightedFrequencyN hQ hu hχ r).add_const _

end Measurability

/-! ### Extension by zero outside `Ω` -/

section Indicator

variable {Ω : Set (Rn n)} {Q u χ : Rn n → ℝ} {z : Rn n} {r : ℝ}

theorem weightedEnergyD_indicator (hΩ : IsOpen Ω) (hr : 0 ≤ r) (hz : closedBall z r ⊆ Ω) :
    weightedEnergyD (Ω.indicator Q) (Ω.indicator u) (Ω.indicator χ) z r =
      weightedEnergyD Q u χ z r := by
  have hzΩ : z ∈ Ω := hz (mem_closedBall_self hr)
  unfold weightedEnergyD
  rw [indicator_of_mem hzΩ]
  congr 2
  refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
  have hyΩ := hz (ball_subset_closedBall hy)
  have hev : Ω.indicator u =ᶠ[𝓝 y] u :=
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds hyΩ) fun w hw => indicator_of_mem hw u
  simp only [hev.gradient_eq, indicator_of_mem hyΩ]

theorem weightedFrequencyN_indicator (hΩ : IsOpen Ω) (hr : 0 ≤ r) (hz : closedBall z r ⊆ Ω) :
    weightedFrequencyN (Ω.indicator Q) (Ω.indicator u) (Ω.indicator χ) z r =
      weightedFrequencyN Q u χ z r := by
  unfold weightedFrequencyN
  rw [weightedEnergyD_indicator hΩ hr hz, heightH_indicator hr hz,
    indicator_of_mem (hz (mem_closedBall_self hr))]

theorem modFrequencyN_indicator (κ : ℝ) (hΩ : IsOpen Ω) (hr : 0 ≤ r)
    (hz : closedBall z r ⊆ Ω) :
    modFrequencyN κ (Ω.indicator Q) (Ω.indicator u) (Ω.indicator χ) z r =
      modFrequencyN κ Q u χ z r := by
  unfold modFrequencyN
  rw [weightedFrequencyN_indicator hΩ hr hz]

end Indicator

/-! ### `Σ^H_{Q,t}` on `K = B̄_{1/10}` -/

section Geometry

variable {Ω : Set (Rn n)} {z : Rn n}

/-- On `K = B̄_{1/10}` and for `t < 9/10`, `Σ^H_{Q,t}` relative to `B_1` is `Σ^H_{Q,t}` relative
to any `Ω ⊇ B_1`. -/
theorem mem_sigmaHQr_ball_iff {Q u χ : Rn n → ℝ} {κ : ℝ} (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω)
    (hz : z ∈ closedBall (0 : Rn n) (1 / 10)) {t : ℝ} (ht : t < 9 / 10) :
    z ∈ sigmaHQr (ball 0 1) Q u χ κ t ↔ z ∈ sigmaHQr Ω Q u χ κ t := by
  have hB : ball (0 : Rn n) 1 ⊆ Ω := ball_subset_closedBall.trans hΩ
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hB h1, h2.trans hB, h3, h4⟩
  · rintro ⟨-, -, h3, h4⟩
    exact ⟨mem_ball_one_of_mem_K hz, closedBall_subset_ball_one hz ht, h3, h4⟩

end Geometry

/-! ### The data -/

section Data

variable [NeZero n] {Ω : Set (Rn n)} {C_V : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- The frequency used in the data: `Ñ_z(u; r)` computed for the extensions by zero of
`(Q, u, χ)` outside `Ω`. It is measurable in `z` and agrees with `Ñ_z(u; r)` when `B̄_r(z) ⊆ Ω`. -/
abbrev solNQ (Ω : Set (Rn n)) (κ : ℝ) (Q u χ : Rn n → ℝ) : Rn n → ℝ → ℝ :=
  modFrequencyN κ (Ω.indicator Q) (Ω.indicator u) (Ω.indicator χ)

omit [NeZero n] in
theorem solNQ_eq (h : IsVariationalSolutionQ Ω C_V Q u χ) (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω)
    (κ : ℝ) {z : Rn n} (hz : z ∈ closedBall (0 : Rn n) (1 / 10)) {r : ℝ} (hr : 0 ≤ r)
    (hr' : r < 9 / 10) : solNQ Ω κ Q u χ z r = modFrequencyN κ Q u χ z r :=
  modFrequencyN_indicator κ h.isOpen hr (closedBall_subset_of_mem_K hΩ hz hr')

omit [NeZero n] in
theorem measurable_solNQ (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C_V Q u χ)
    (κ r : ℝ) : Measurable fun z => solNQ Ω κ Q u χ z r :=
  measurable_modFrequencyN κ (measurable_indicator_of_continuousOn h.isOpen hQ.continuousOn)
    (measurable_indicator_of_continuousOn h.isOpen h.continuousOn) h.measurable_chi r

omit [NeZero n] in
theorem weissKappa_nonneg_of_closedBall (hQ : QBounds Ω Q L c C')
    (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) : 0 ≤ weissKappa L c C' :=
  hQ.weissKappa_nonneg (hΩ (mem_closedBall_self zero_le_one))

/-- The Jones data of a variational solution with a Lipschitz coefficient on a set
`S ⊆ B̄_{1/10}` (see the module docstring). The hypotheses: `S ⊆ Σ^H_{Q,ρ}(Ω)` for every
`ρ ∈ [t, 1/6]`, `ρ > 0`; `Ñ_z(u; ρ) ≤ N'` on `S` for `ρ ∈ (0, 1/2)`; and Theorem 6.1 for
`(u, χ)` with the bound `N'` and the constant `CJ`. -/
def solJonesDataQ (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C_V Q u χ)
    (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) (hκ : weissKappa L c C' ≤ 1 / 2) {CJ Np : ℝ}
    (hCJ : ∀ (x : Rn n) (r : ℝ) (μ : Measure (Rn n)), 0 < r →
      weissKappa L c C' * (50 * r) ≤ 1 / 2 → closedBall x (50 * r) ⊆ Ω → IsFiniteMeasure μ →
      μ (sigmaHQr Ω Q u χ (weissKappa L c C') r)ᶜ = 0 →
      x ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r →
      modFrequencyN (weissKappa L c C') Q u χ x (50 * r) ≤ Np →
      jonesBetaSq μ x r ≤ ENNReal.ofReal (CJ / r ^ (n - 1)) *
        ∫⁻ y in ball x r, ENNReal.ofReal (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
          modFrequencyN (weissKappa L c C') Q u χ y r) ∂μ)
    (S : Set (Rn n)) (t : ℝ) (ht : 0 ≤ t) (hSm : MeasurableSet S)
    (hSK : S ⊆ closedBall 0 (1 / 10))
    (hS : ∀ z ∈ S, ∀ ρ, 0 < ρ → t ≤ ρ → ρ ≤ 1 / 6 →
      z ∈ sigmaHQr Ω Q u χ (weissKappa L c C') ρ)
    (hN : ∀ z ∈ S, ∀ ρ, 0 < ρ → ρ < 1 / 2 → modFrequencyN (weissKappa L c C') Q u χ z ρ ≤ Np) :
    JonesData n CJ where
  S := S
  N := solNQ Ω (weissKappa L c C') Q u χ
  t := t
  R := 1 / 120
  t_nonneg := ht
  R_pos := by norm_num
  measurableSet_S := hSm
  measurable_N r _ _ := measurable_solNQ hQ h _ r
  monotoneOn z hz a ha b hb hab := by
    have hk := weissKappa_nonneg_of_closedBall hQ hΩ
    have ha0 : 0 < a := lt_of_le_of_lt ht ha.1
    have hmem := hS z hz ((t + a) / 2) (by linarith [ha.1]) (by linarith [ha.1])
      (by linarith [ha.1, ha.2])
    have hmono := h.monotoneOn_modFrequencyN hQ hmem.2.2.1 (by linarith [ha.1]) hmem.2.2.2
      (by nlinarith : weissKappa L c C' * (1 / 6) ≤ 1 / 2)
      (closedBall_subset_of_mem_K hΩ (hSK hz) (r := 1 / 6) (by norm_num))
    rw [solNQ_eq h hΩ _ (hSK hz) ha0.le (by linarith [ha.2]),
      solNQ_eq h hΩ _ (hSK hz) (ha0.trans_le hab).le (by linarith [hb.2])]
    exact hmono ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [ha.1], by linarith [hb.2]⟩
      hab
  one_le z hz a ha := by
    have hk := weissKappa_nonneg_of_closedBall hQ hΩ
    have ha0 : 0 < a := lt_of_le_of_lt ht ha.1
    have hmem := hS z hz ((t + a) / 2) (by linarith [ha.1]) (by linarith [ha.1])
      (by linarith [ha.1, ha.2])
    rw [solNQ_eq h hΩ _ (hSK hz) ha0.le (by linarith [ha.2])]
    exact h.one_le_modFrequencyN hQ hmem.2.2.1 (by linarith [ha.1]) hmem.2.2.2
      (by nlinarith : weissKappa L c C' * (1 / 6) ≤ 1 / 2)
      (closedBall_subset_of_mem_K hΩ (hSK hz) (r := 1 / 6) (by norm_num))
      ⟨by linarith [ha.1], by linarith [ha.2]⟩
  jones μ hμ hμS y hy ρ hρ htρ hρR := by
    have hk := weissKappa_nonneg_of_closedBall hQ hΩ
    have hae : ∀ᵐ z ∂μ, z ∈ S := mem_ae_iff.2 hμS
    have hsub : S ⊆ sigmaHQr Ω Q u χ (weissKappa L c C') ρ := fun z hz =>
      hS z hz ρ hρ htρ (by linarith)
    have key := hCJ y ρ μ hρ (by nlinarith)
      (closedBall_subset_of_mem_K hΩ (hSK hy) (by linarith)) hμ
      (measure_mono_null (compl_subset_compl.2 hsub) hμS) (hsub hy)
      (hN y hy (50 * ρ) (by linarith) (by linarith))
    refine key.trans_eq ?_
    congr 1
    refine lintegral_congr_ae (ae_restrict_of_ae (hae.mono fun z hz => ?_))
    simp only [solNQ_eq h hΩ _ (hSK hz) (by linarith : (0 : ℝ) ≤ 20 * ρ) (by linarith),
      solNQ_eq h hΩ _ (hSK hz) hρ.le (by linarith)]

/-- `Σ^H_{Q,t}(Ω) ∩ B̄_{1/10}` is measurable for `0 < t < 9/10`: it is closed, since `Σ^H_{Q,t}` is
relatively closed in `{x : B̄_t(x) ⊆ Ω}`. -/
theorem measurableSet_sigmaHQr_inter (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C_V Q u χ) (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) (κ : ℝ) {t : ℝ}
    (ht : 0 < t) (ht' : t < 9 / 10) :
    MeasurableSet (sigmaHQr Ω Q u χ κ t ∩ closedBall 0 (1 / 10)) := by
  have heq : sigmaHQr Ω Q u χ κ t ∩ closedBall 0 (1 / 10) =
      closure (sigmaHQr Ω Q u χ κ t) ∩ closedBall 0 (1 / 10) := by
    refine Subset.antisymm (inter_subset_inter_left _ subset_closure) ?_
    rintro z ⟨hzc, hz⟩
    exact ⟨h.closure_sigmaHQr_inter_subset hQ κ ht
      ⟨hzc, closedBall_subset_of_mem_K hΩ hz ht'⟩, hz⟩
  rw [heq]
  exact (isClosed_closure.inter isClosed_closedBall).measurableSet

/-- `Σ^H_Q` is Borel: it is relatively closed in the open set `Ω`. -/
theorem measurableSet_sigmaHQ (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C_V Q u χ) : MeasurableSet (sigmaHQ Ω Q u χ) := by
  have heq : sigmaHQ Ω Q u χ = closure (sigmaHQ Ω Q u χ) ∩ Ω :=
    Subset.antisymm (fun y hy => ⟨subset_closure hy, hy.1⟩)
      (h.closure_sigmaHQ_inter_subset' hQ)
  rw [heq]
  exact isClosed_closure.measurableSet.inter h.isOpen.measurableSet

/-- `Σ^H_Q(B_1) ∩ B̄_{1/10}` is measurable. -/
theorem measurableSet_sigmaHQ_inter (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C_V Q u χ) (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) :
    MeasurableSet (sigmaHQ (ball 0 1) Q u χ ∩ closedBall 0 (1 / 10)) := by
  rw [← sigmaHQ_inter_of_subset (ball_subset_closedBall.trans hΩ)]
  exact ((measurableSet_sigmaHQ hQ h).inter measurableSet_ball).inter measurableSet_closedBall

/-- The Naber–Valtorta data of a variational solution with a Lipschitz coefficient at the scale
`t ∈ (0, 1/120]`: `S = Σ^H_{Q,t}(Ω) ∩ B̄_{1/10}`, `K = B̄_{1/10}`, `R = 1/120`. The dichotomy is
Theorem 6.3 with a Lipschitz coefficient, with the bound `N'` and the function `ε`. -/
def solNVDataQ (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C_V Q u χ)
    (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) (hκ : weissKappa L c C' ≤ 1 / 2) {CJ Np : ℝ}
    (hCJ : ∀ (x : Rn n) (r : ℝ) (μ : Measure (Rn n)), 0 < r →
      weissKappa L c C' * (50 * r) ≤ 1 / 2 → closedBall x (50 * r) ⊆ Ω → IsFiniteMeasure μ →
      μ (sigmaHQr Ω Q u χ (weissKappa L c C') r)ᶜ = 0 →
      x ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r →
      modFrequencyN (weissKappa L c C') Q u χ x (50 * r) ≤ Np →
      jonesBetaSq μ x r ≤ ENNReal.ofReal (CJ / r ^ (n - 1)) *
        ∫⁻ y in ball x r, ENNReal.ofReal (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
          modFrequencyN (weissKappa L c C') Q u χ y r) ∂μ)
    (ε : ℝ → ℝ)
    (hε : ∀ δ, 0 < δ → ∀ (x : Rn n) (r t : ℝ), 0 < r → weissKappa L c C' * (50 * r) ≤ 1 / 2 →
      ball x (50 * r) ⊆ Ω → t ∈ Ioc 0 r →
      let Nmax := sSup ((fun y => modFrequencyN (weissKappa L c C') Q u χ y (20 * r)) ''
        (closedBall x r ∩ sigmaHQr Ω Q u χ (weissKappa L c C') t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ P : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ P.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHQr Ω Q u χ (weissKappa L c C') t |
          Nmax - modFrequencyN (weissKappa L c C') Q u χ y r < ε δ} ⊆
          thickening (δ * r) (P : Set (Rn n)))
    (t : ℝ) (ht : 0 < t) (htR : t ≤ 1 / 120)
    (hN : ∀ z ∈ closedBall (0 : Rn n) (1 / 10), ∀ ρ, 0 < ρ → ρ < 1 / 2 →
      modFrequencyN (weissKappa L c C') Q u χ z ρ ≤ Np) : NVData n CJ Np ε where
  toJonesData := solJonesDataQ hQ h hΩ hκ hCJ
    (sigmaHQr Ω Q u χ (weissKappa L c C') t ∩ closedBall 0 (1 / 10)) t ht.le
    (measurableSet_sigmaHQr_inter hQ h hΩ _ ht (by linarith)) inter_subset_right
    (fun z hz ρ hρ htρ hρ6 => h.mem_sigmaHQr_of_le hQ ht htρ
      (by have := weissKappa_nonneg_of_closedBall hQ hΩ; nlinarith) hz.1
      (closedBall_subset_of_mem_K hΩ hz.2 (by linarith)))
    (fun z hz => hN z hz.2)
  K := closedBall 0 (1 / 10)
  le_Nplus z hz r hr := by
    change solNQ Ω (weissKappa L c C') Q u χ z r ≤ Np
    have hr0 : 0 < r := ht.trans hr.1
    have hr6 : r ≤ 1 / 6 := by
      have : r ≤ 20 * (1 / 120 : ℝ) := hr.2
      linarith
    rw [solNQ_eq h hΩ _ hz.2 hr0.le (by linarith)]
    exact hN z hz.2 r hr0 (by linarith)
  dichotomy δ hδ x r hr htr hrR hxK hne := by
    change r ≤ 1 / 120 at hrR
    set κ := weissKappa L c C' with hκdef
    set S := sigmaHQr Ω Q u χ κ t ∩ closedBall 0 (1 / 10) with hSdef
    change maxFrequency S (solNQ Ω κ Q u χ) x r < 1 + δ ∨
      ∃ P : AffineSubspace ℝ (Rn n), Module.finrank ℝ P.direction ≤ n - 2 ∧
        {y | y ∈ S ∩ closedBall x r ∧
          maxFrequency S (solNQ Ω κ Q u χ) x r - solNQ Ω κ Q u χ y r < ε δ} ⊆
          thickening (δ * r) (P : Set (Rn n))
    change (S ∩ closedBall x r).Nonempty at hne
    have hk := weissKappa_nonneg_of_closedBall hQ hΩ
    have hx : x ∈ closedBall (0 : Rn n) (1 / 10) := hxK (mem_closedBall_self hr.le)
    have hset : S ∩ closedBall x r = closedBall x r ∩ sigmaHQr Ω Q u χ κ t := by
      ext y
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨⟨h1, hxK h2⟩, h2⟩
    have hmax : maxFrequency S (solNQ Ω κ Q u χ) x r =
        sSup ((fun y => modFrequencyN κ Q u χ y (20 * r)) ''
          (closedBall x r ∩ sigmaHQr Ω Q u χ κ t)) := by
      unfold maxFrequency
      rw [hset]
      congr 1
      refine image_congr fun y hy => ?_
      exact solNQ_eq h hΩ _ (hxK hy.1) (by linarith) (by linarith)
    rw [hset] at hne
    have hx50 : ball x (50 * r) ⊆ Ω := by
      refine ball_subset_closedBall.trans (closedBall_subset_of_mem_K hΩ hx ?_)
      linarith
    have hNmax : sSup ((fun y => modFrequencyN κ Q u χ y (20 * r)) ''
        (closedBall x r ∩ sigmaHQr Ω Q u χ κ t)) ≤ Np := by
      refine csSup_le (hne.image _) (forall_mem_image.2 fun y hy => ?_)
      exact hN y (hxK hy.1) (20 * r) (by linarith) (by linarith)
    rcases hε δ hδ x r t hr (by nlinarith) hx50 ⟨ht, htr⟩ hNmax with h1 | ⟨P, hP, hsub⟩
    · left
      rw [hmax]
      exact h1
    · right
      refine ⟨P, hP, fun y hy => hsub ⟨?_, ?_⟩⟩
      · rw [← hset]
        exact hy.1
      · have := hy.2
        rw [hmax, solNQ_eq h hΩ _ (hxK hy.1.2) (by linarith) (by linarith)] at this
        exact this

end Data

end InnerVariational.NaberValtorta
