/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.DensityQ
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.EMetricSpace.Paracompact
import InnerVariational.Basic.Polar

/-!
# `Σ^H` with a Lipschitz coefficient

Let `(u, χ)` be a variational solution on `Ω` for a coefficient `Q` with `QBounds Ω Q L c C'`.
The set of highest density is
`Σ^H = {x ∈ Ω ∩ closure {u > 0} : M^{Q(x)}_x(u; 0+) ≥ Q(x)² |B_1|}` (`sigmaHQ`), where
`M^{Q(x)}_x` is the Weiss energy with the coefficient frozen at `Q(x)` (`monotonicityMq`).

* `mem_sigmaHQ_iff_tendsto_volume` (density characterization): `x ∈ Σ^H` if and only if
  `x ∈ Ω`, `x ∈ closure {u > 0}`, `u(x) = 0`, and `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1`;
  `mem_sigmaHQ_iff_frontier_inter'` states it with the relative free boundary
  `frontier {y ∈ Ω | u(y) > 0}`.
* `closure_sigmaHQ_inter_subset'`: `Σ^H` is relatively closed in `Ω`.

As for `Q ≡ 1` (`Monotonicity/HighestDensity.lean`), the density characterization uses the density
formula `M^{Q(x)}_x(0+) = Q(x)² lim r^{-n} |{χ = 1} ∩ B_r(x)|` and the bound
`M^{Q(x)}_x(0+) ≤ Q(x)² |B_1|` (`Monotonicity/DensityQ.lean`); relative closedness uses the upper
semicontinuity of `x ↦ M^{Q(x)}_x(0+)` (`Monotonicity/LimitsQ.lean`) and the continuity of `Q`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-! ### `∫ χ` as a volume -/

/-- `∫_{B_r(x)} χ = |{χ = 1} ∩ B_r(x)|` when `B_r(x) ⊆ Ω`, since `χ ∈ {0, 1}` on `Ω`. -/
theorem setIntegral_chi_eq_measureReal (h : IsVariationalSolutionQ Ω C Q u χ) {r : ℝ}
    (hball : ball x r ⊆ Ω) :
    ∫ y in ball x r, χ y = volume.real ({y | χ y = 1} ∩ ball x r) := by
  set E : Set (Rn n) := {y | Ω.indicator χ y = 1} with hEdef
  have hE : MeasurableSet E := h.measurable_chi (measurableSet_singleton 1)
  have hmem : ∀ y ∈ ball x r, y ∈ E ↔ χ y = 1 := fun y hy => by
    simp only [hEdef, mem_ofPred_eq, indicator_of_mem (hball hy)]
  have hEB : E ∩ ball x r = {y | χ y = 1} ∩ ball x r := by
    ext y
    exact ⟨fun hy => ⟨(hmem y hy.2).1 hy.1, hy.2⟩, fun hy => ⟨(hmem y hy.2).2 hy.1, hy.2⟩⟩
  have hint : ∫ y in ball x r, χ y = ∫ y in ball x r, E.indicator 1 y := by
    refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
    rcases h.chi_mem y (hball hy) with h0 | h1
    · have : y ∉ E := fun hyE => by rw [(hmem y hy).1 hyE] at h0; exact one_ne_zero h0
      rw [indicator_of_notMem this, h0]
    · rw [indicator_of_mem ((hmem y hy).2 h1), h1, Pi.one_apply]
  rw [hint, integral_indicator_one hE, measureReal_restrict_apply hE, hEB]

/-- The density ratio `|{χ = 1} ∩ B_r(x)| / |B_r(x)| = r^{-n} ∫_{B_r(x)} χ / |B_1|`. -/
theorem volume_inter_ball_div_volume_ball (h : IsVariationalSolutionQ Ω C Q u χ) {r : ℝ}
    (hr : 0 < r) (hball : ball x r ⊆ Ω) :
    volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r) =
      ENNReal.ofReal ((r ^ n)⁻¹ * (∫ y in ball x r, χ y) / unitBallVolume n) := by
  have hB : volume (ball x r) = ENNReal.ofReal (r ^ n * unitBallVolume n) := by
    rw [← volume_ball_toReal x hr, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  have hEB : volume ({y | χ y = 1} ∩ ball x r) =
      ENNReal.ofReal (volume.real ({y | χ y = 1} ∩ ball x r)) :=
    (ofReal_measureReal ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne).symm
  have hpos : 0 < r ^ n * unitBallVolume n := mul_pos (pow_pos hr n) (unitBallVolume_pos n)
  rw [hEB, hB, ← ENNReal.ofReal_div_of_pos hpos, h.setIntegral_chi_eq_measureReal hball]
  congr 1
  have := unitBallVolume_pos n
  have := pow_pos hr n
  field_simp

/-- For `u(x) = 0`: `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` if and only if
`M^{Q(x)}_x(0+) = Q(x)² |B_1|`. -/
theorem tendsto_volume_ratio_iff [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hux : u x = 0) :
    Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0) (𝓝 1) ↔
      MzeroQ (Q x) u χ x = ((Q x ^ 2 * unitBallVolume n : ℝ) : EReal) := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  obtain ⟨m, hm, -, hd⟩ := h.tendsto_monotonicityMq_zero hQ hx hux
  have hB := unitBallVolume_pos n
  have hq : 0 < Q x ^ 2 := pow_pos (hQ.pos_of_mem hx) 2
  have hqB : 0 < Q x ^ 2 * unitBallVolume n := mul_pos hq hB
  set d : ℝ → ℝ := fun r => (r ^ n)⁻¹ * (∫ y in ball x r, χ y) / unitBallVolume n with hddef
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 R := Ioo_mem_nhdsGT hR0
  have heq : (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) =ᶠ[𝓝[>] 0]
      fun r => ENNReal.ofReal (d r) := by
    filter_upwards [hsmall] with r hr
    exact h.volume_inter_ball_div_volume_ball hr.1 ((ball_subset_ball hr.2.le).trans hR)
  have hdlim : Tendsto d (𝓝[>] 0) (𝓝 (m / (Q x ^ 2 * unitBallVolume n))) := by
    refine (hd.div_const (Q x ^ 2 * unitBallVolume n)).congr fun r => ?_
    simp only [hddef]
    rw [mul_div_mul_comm, div_self hq.ne', one_mul]
  rw [hm, EReal.coe_eq_coe_iff]
  constructor
  · intro hlim
    have h1 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (hlim.congr' heq)
    have h2 : Tendsto d (𝓝[>] 0) (𝓝 1) := by
      refine h1.congr' ?_
      filter_upwards [hsmall] with r hr
      have hball := (ball_subset_ball hr.2.le).trans hR
      exact ENNReal.toReal_ofReal (div_nonneg (h.density_mem_Icc hr.1 hball).1 hB.le)
    have := tendsto_nhds_unique hdlim h2
    rwa [div_eq_one_iff_eq hqB.ne'] at this
  · intro hmB
    refine Tendsto.congr' heq.symm ?_
    have := ENNReal.tendsto_ofReal hdlim
    rwa [hmB, div_self hqB.ne', ENNReal.ofReal_one] at this

/-! ### The free boundary -/

/-- For `x ∈ Ω`: `x ∈ frontier {u > 0}` if and only if `x ∈ closure {u > 0}` and `u(x) = 0`. -/
theorem mem_frontier_pos_iff (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) :
    x ∈ frontier {y | 0 < u y} ↔ x ∈ closure {y | 0 < u y} ∧ u x = 0 := by
  rw [frontier, Set.mem_sdiff]
  constructor
  · rintro ⟨hcl, hint⟩
    refine ⟨hcl, le_antisymm (not_lt.1 fun hpos => hint ?_) (h.nonneg x hx)⟩
    rw [mem_interior_iff_mem_nhds]
    exact (h.continuousOn.continuousAt (h.isOpen.mem_nhds hx)).preimage_mem_nhds
      (Ioi_mem_nhds hpos)
  · rintro ⟨hcl, hux⟩
    refine ⟨hcl, fun hint => ?_⟩
    have hmem : x ∈ {y | 0 < u y} := interior_subset hint
    have : 0 < u x := hmem
    rw [hux] at this
    exact lt_irrefl _ this

/-- For `x ∈ Ω`: `x ∈ frontier {y ∈ Ω | u(y) > 0}` if and only if `x ∈ frontier {u > 0}`. -/
theorem mem_frontier_pos_inter_iff (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) :
    x ∈ frontier {y | y ∈ Ω ∧ 0 < u y} ↔ x ∈ frontier {y | 0 < u y} := by
  have e : {y | y ∈ Ω ∧ 0 < u y} = Ω ∩ {y | 0 < u y} := rfl
  rw [e, frontier, frontier, Set.mem_sdiff, Set.mem_sdiff, interior_inter, h.isOpen.interior_eq]
  have hcl : x ∈ closure (Ω ∩ {y | 0 < u y}) ↔ x ∈ closure {y | 0 < u y} :=
    ⟨fun hc => closure_mono inter_subset_right hc, fun hc => h.isOpen.inter_closure ⟨hx, hc⟩⟩
  rw [hcl]
  exact and_congr_right' ⟨fun hn hi => hn ⟨hx, hi⟩, fun hn hi => hn hi.2⟩

/-! ### Characterizations of `Σ^H` -/

/-- `u(x) = 0` on `Σ^H`. -/
theorem eq_zero_of_mem_sigmaHQ [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hxS : x ∈ sigmaHQ Ω Q u χ) : u x = 0 := by
  obtain ⟨hx, -, hM⟩ := hxS
  rcases (h.nonneg x hx).lt_or_eq with hpos | h0
  · rw [h.MzeroQ_eq_bot_of_pos hQ hx hpos] at hM
    exact absurd hM (not_le.2 (EReal.bot_lt_coe _))
  · exact h0.symm

/-- `M^{Q(x)}_x(0+) = Q(x)² |B_1|` on `Σ^H`. -/
theorem MzeroQ_eq_of_mem_sigmaHQ [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hxS : x ∈ sigmaHQ Ω Q u χ) :
    MzeroQ (Q x) u χ x = ((Q x ^ 2 * unitBallVolume n : ℝ) : EReal) :=
  le_antisymm (h.MzeroQ_le_sq_mul_unitBallVolume hQ hxS.1) hxS.2.2

/-- **Density characterization of `Σ^H`**: `x ∈ Σ^H` if and only if `x ∈ Ω`,
`x ∈ closure {u > 0}`, `u(x) = 0`, and `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` as `r → 0+`. -/
theorem mem_sigmaHQ_iff_tendsto_volume [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    x ∈ sigmaHQ Ω Q u χ ↔ x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧ u x = 0 ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1) := by
  refine ⟨fun hxS => ?_, fun ⟨hx, hcl, hux, hlim⟩ => ?_⟩
  · have hux := h.eq_zero_of_mem_sigmaHQ hQ hxS
    exact ⟨hxS.1, hxS.2.1, hux,
      (h.tendsto_volume_ratio_iff hQ hxS.1 hux).2 (h.MzeroQ_eq_of_mem_sigmaHQ hQ hxS)⟩
  · exact ⟨hx, hcl, ((h.tendsto_volume_ratio_iff hQ hx hux).1 hlim).ge⟩

/-- **Density characterization of `Σ^H`**, with the relative free boundary
`frontier {y ∈ Ω | u(y) > 0}`. -/
theorem mem_sigmaHQ_iff_frontier_inter' [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    x ∈ sigmaHQ Ω Q u χ ↔ x ∈ Ω ∧ x ∈ frontier {y | y ∈ Ω ∧ 0 < u y} ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1) := by
  rw [h.mem_sigmaHQ_iff_tendsto_volume hQ]
  constructor
  · rintro ⟨hx, hcl, hux, hlim⟩
    exact ⟨hx, (h.mem_frontier_pos_inter_iff hx).2 ((h.mem_frontier_pos_iff hx).2 ⟨hcl, hux⟩),
      hlim⟩
  · rintro ⟨hx, hfr, hlim⟩
    obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 ((h.mem_frontier_pos_inter_iff hx).1 hfr)
    exact ⟨hx, hcl, hux, hlim⟩

/-! ### Relative closedness -/

/-- **`Σ^H` is relatively closed in `Ω`**, from the upper semicontinuity of
`x ↦ M^{Q(x)}_x(0+)` and the continuity of `Q`. -/
theorem closure_sigmaHQ_inter_subset' [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    closure (sigmaHQ Ω Q u χ) ∩ Ω ⊆ sigmaHQ Ω Q u χ := by
  rintro x ⟨hcl, hx⟩
  have hsub : sigmaHQ Ω Q u χ ⊆ closure {y | 0 < u y} := fun _ hy => hy.2.1
  refine ⟨hx, closure_minimal hsub isClosed_closure hcl, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y, hy1, hy2⟩ := exists_between hlt
  have hev := h.upperSemicontinuousOn_MzeroQ hQ x hx y hy1
  rw [h.isOpen.nhdsWithin_eq hx] at hev
  have hQc : ContinuousAt Q x := hQ.continuousOn.continuousAt (h.isOpen.mem_nhds hx)
  have hv : ContinuousAt (fun z => ((Q z ^ 2 * unitBallVolume n : ℝ) : EReal)) x :=
    continuous_coe_real_ereal.continuousAt.comp ((hQc.pow 2).mul continuousAt_const)
  have hev2 : ∀ᶠ z in 𝓝 x, y < ((Q z ^ 2 * unitBallVolume n : ℝ) : EReal) :=
    hv.eventually (lt_mem_nhds hy2)
  obtain ⟨z, hzS, hz1, hz2⟩ :=
    ((mem_closure_iff_frequently.1 hcl).and_eventually (hev.and hev2)).exists
  exact absurd (hzS.2.2.trans_lt hz1) (not_lt.2 hz2.le)

end IsVariationalSolutionQ

/-- `Σ^H` is local: for `V ⊆ U` open, `Σ^H(U) ∩ V = Σ^H(V)`. -/
theorem sigmaHQ_inter_of_subset {U V : Set (Rn n)} (hVU : V ⊆ U) (Q u χ : Rn n → ℝ) :
    sigmaHQ U Q u χ ∩ V = sigmaHQ V Q u χ := by
  ext y
  exact ⟨fun ⟨⟨_, h1, h2⟩, hy⟩ => ⟨hy, h1, h2⟩, fun ⟨hy, h1, h2⟩ => ⟨⟨hVU hy, h1, h2⟩, hy⟩⟩

end InnerVariational
