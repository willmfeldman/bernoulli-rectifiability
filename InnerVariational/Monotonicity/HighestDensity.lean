/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Density
public import InnerVariational.Defs.HighestDensity
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.EMetricSpace.Paracompact
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Basic.Polar

/-!
# `Σ^H` through `M_x(0+)` and through the density of `{χ = 1}`

Consequences of Propositions 3.4 and 3.5 of Kriventsov–Weiss (see the references) for the set of
highest density `Σ^H`, defined at the start of Section 6 of the paper. Let `(u, χ)` be a
variational solution on `Ω`.

* `mem_sigmaH_iff_le_Mzero`: `x ∈ Σ^H` if and only if `x ∈ Ω ∩ closure{u > 0}` and
  `M_x(u; 0+) ≥ |B_1|`, the definition of `Σ^H` in Section 6. This library defines `Σ^H` (`sigmaH`)
  instead by `M_x(u; r) ≥ |B_1|` for every `r > 0` with `B̄_r(x) ⊆ Ω`; by the monotonicity of
  `M_x` (Proposition 3.4) the two agree.
* `mem_sigmaH_iff_tendsto_volume` (density characterization): `x ∈ Σ^H` if and only if
  `x ∈ Ω`, `x ∈ closure{u > 0}`, `u(x) = 0`, and `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1`.
  `mem_sigmaH_iff_frontier` and `mem_sigmaH_iff_frontier_inter` state it with
  `x ∈ frontier {u > 0}`, resp. `x ∈ frontier {y ∈ Ω | u(y) > 0}` (the free boundary relative
  to `Ω`).
* `closure_sigmaH_inter_subset` (relative closedness, from the upper semicontinuity in
  Proposition 3.5): `closure Σ^H ∩ Ω ⊆ Σ^H`.

The density characterization uses (3.10) and `M_x(0+) ≤ |B_1|`: `M_x(0+) ≥ |B_1|` forces
`u(x) = 0` (otherwise `M_x(0+) = −∞`) and then `M_x(0+) = lim r^{-n} |{χ = 1} ∩ B_r(x)| = |B_1|`.

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

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### `∫ χ` as a volume -/

/-- `∫_{B_r(x)} χ = |{χ = 1} ∩ B_r(x)|` when `B_r(x) ⊆ Ω`, since `χ ∈ {0, 1}` on `Ω`. -/
theorem setIntegral_chi_eq_measureReal (h : IsVariationalSolution Ω C u χ) {r : ℝ}
    (hball : ball x r ⊆ Ω) :
    ∫ y in ball x r, χ y = volume.real ({y | χ y = 1} ∩ ball x r) := by
  set E : Set (Rn n) := {y | Ω.indicator χ y = 1} with hEdef
  have hE : MeasurableSet E := h.measurable_chi (measurableSet_singleton 1)
  have hmem : ∀ y ∈ ball x r, y ∈ E ↔ χ y = 1 := fun y hy => by
    simp only [hEdef, mem_setOf_eq, indicator_of_mem (hball hy)]
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
theorem volume_inter_ball_div_volume_ball (h : IsVariationalSolution Ω C u χ) {r : ℝ}
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

/-- For `u(x) = 0`: `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` if and only if `M_x(0+) = |B_1|`. -/
theorem tendsto_volume_ratio_iff [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hux : u x = 0) :
    Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0) (𝓝 1) ↔
      Mzero u χ x = unitBallVolume n := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨m, hm, -, hd⟩ := h.tendsto_monotonicityM_zero hx hux
  have hB := unitBallVolume_pos n
  set d : ℝ → ℝ := fun r => (r ^ n)⁻¹ * (∫ y in ball x r, χ y) / unitBallVolume n with hddef
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 R := Ioo_mem_nhdsGT hR0
  have heq : (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) =ᶠ[𝓝[>] 0]
      fun r => ENNReal.ofReal (d r) := by
    filter_upwards [hsmall] with r hr
    exact h.volume_inter_ball_div_volume_ball hr.1 ((ball_subset_ball hr.2.le).trans hR)
  have hdlim : Tendsto d (𝓝[>] 0) (𝓝 (m / unitBallVolume n)) := hd.div_const _
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
    rwa [div_eq_one_iff_eq hB.ne'] at this
  · intro hmB
    refine Tendsto.congr' heq.symm ?_
    have := ENNReal.tendsto_ofReal hdlim
    rwa [hmB, div_self hB.ne', ENNReal.ofReal_one] at this

/-! ### Characterizations of `Σ^H` -/

/-- **The definition of `Σ^H` in Section 6**: `x ∈ Σ^H` if and only if `x ∈ Ω`,
`x ∈ closure {u > 0}`, and `M_x(u; 0+) ≥ |B_1|`. The library's `sigmaH` asks instead for
`M_x(u; r) ≥ |B_1|` at every radius `r > 0` with `B̄_r(x) ⊆ Ω`; this theorem shows the two agree
for variational solutions. -/
theorem mem_sigmaH_iff_le_Mzero [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    x ∈ sigmaH Ω u χ ↔
      x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧ (unitBallVolume n : EReal) ≤ Mzero u χ x := by
  constructor
  · rintro ⟨hx, hcl, hM⟩
    exact ⟨hx, hcl, (h.le_Mzero_iff_closedBall hx).2 fun r hr hball =>
      EReal.coe_le_coe_iff.2 (hM r hr hball)⟩
  · rintro ⟨hx, hcl, hM⟩
    exact ⟨hx, hcl, fun r hr hball =>
      EReal.coe_le_coe_iff.1 ((h.le_Mzero_iff_closedBall hx).1 hM r hr hball)⟩

/-- `u(x) = 0` on `Σ^H`. -/
theorem eq_zero_of_mem_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hxS : x ∈ sigmaH Ω u χ) : u x = 0 := by
  obtain ⟨hx, -, hM⟩ := h.mem_sigmaH_iff_le_Mzero.1 hxS
  rcases (h.nonneg x hx).lt_or_eq with hpos | h0
  · rw [h.Mzero_eq_bot_of_pos hx hpos] at hM
    exact absurd hM (not_le.2 (EReal.bot_lt_coe _))
  · exact h0.symm

/-- `M_x(u; 0+) = |B_1|` on `Σ^H`. -/
theorem Mzero_eq_of_mem_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hxS : x ∈ sigmaH Ω u χ) : Mzero u χ x = unitBallVolume n :=
  le_antisymm (h.Mzero_le_unitBallVolume hxS.1) (h.mem_sigmaH_iff_le_Mzero.1 hxS).2.2

/-- **Density characterization of `Σ^H`** (Props 3.4, 3.5): `x ∈ Σ^H` if and only if `x ∈ Ω`,
`x ∈ closure {u > 0}`, `u(x) = 0`, and `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` as `r → 0+`. -/
theorem mem_sigmaH_iff_tendsto_volume [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    x ∈ sigmaH Ω u χ ↔ x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧ u x = 0 ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1) := by
  refine ⟨fun hxS => ?_, fun ⟨hx, hcl, hux, hlim⟩ => ?_⟩
  · have hux := h.eq_zero_of_mem_sigmaH hxS
    exact ⟨hxS.1, hxS.2.1, hux,
      (h.tendsto_volume_ratio_iff hxS.1 hux).2 (h.Mzero_eq_of_mem_sigmaH hxS)⟩
  · exact h.mem_sigmaH_iff_le_Mzero.2
      ⟨hx, hcl, ((h.tendsto_volume_ratio_iff hx hux).1 hlim).ge⟩

/-- For `x ∈ Ω`: `x ∈ frontier {u > 0}` if and only if `x ∈ closure {u > 0}` and `u(x) = 0`. -/
theorem mem_frontier_pos_iff (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    x ∈ frontier {y | 0 < u y} ↔ x ∈ closure {y | 0 < u y} ∧ u x = 0 := by
  rw [frontier, mem_diff]
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
theorem mem_frontier_pos_inter_iff (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    x ∈ frontier {y | y ∈ Ω ∧ 0 < u y} ↔ x ∈ frontier {y | 0 < u y} := by
  have e : {y | y ∈ Ω ∧ 0 < u y} = Ω ∩ {y | 0 < u y} := rfl
  rw [e, frontier, frontier, mem_diff, mem_diff, interior_inter, h.isOpen.interior_eq]
  have hcl : x ∈ closure (Ω ∩ {y | 0 < u y}) ↔ x ∈ closure {y | 0 < u y} :=
    ⟨fun hc => closure_mono inter_subset_right hc, fun hc => h.isOpen.inter_closure ⟨hx, hc⟩⟩
  rw [hcl]
  exact and_congr_right' ⟨fun hn hi => hn ⟨hx, hi⟩, fun hn hi => hn hi.2⟩

/-- **Density characterization of `Σ^H`**, with `frontier {u > 0}`. -/
theorem mem_sigmaH_iff_frontier [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    x ∈ sigmaH Ω u χ ↔ x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1) := by
  rw [h.mem_sigmaH_iff_tendsto_volume]
  constructor
  · rintro ⟨hx, hcl, hux, hlim⟩
    exact ⟨hx, (h.mem_frontier_pos_iff hx).2 ⟨hcl, hux⟩, hlim⟩
  · rintro ⟨hx, hfr, hlim⟩
    obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 hfr
    exact ⟨hx, hcl, hux, hlim⟩

/-- **Density characterization of `Σ^H`**, with the relative free boundary
`frontier {y ∈ Ω | u(y) > 0}`: `x ∈ Σ^H` if and only if `x ∈ Ω` lies on it and
`|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` as `r → 0+`. -/
theorem mem_sigmaH_iff_frontier_inter [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    x ∈ sigmaH Ω u χ ↔ x ∈ Ω ∧ x ∈ frontier {y | y ∈ Ω ∧ 0 < u y} ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1) := by
  rw [h.mem_sigmaH_iff_frontier]
  exact ⟨fun ⟨hx, hfr, hlim⟩ => ⟨hx, (h.mem_frontier_pos_inter_iff hx).2 hfr, hlim⟩,
    fun ⟨hx, hfr, hlim⟩ => ⟨hx, (h.mem_frontier_pos_inter_iff hx).1 hfr, hlim⟩⟩

/-! ### Relative closedness -/

/-- **`Σ^H` is relatively closed in `Ω`** (from the upper semicontinuity in Proposition 3.5). -/
theorem closure_sigmaH_inter_subset [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    closure (sigmaH Ω u χ) ∩ Ω ⊆ sigmaH Ω u χ := by
  rintro x ⟨hcl, hx⟩
  refine h.mem_sigmaH_iff_le_Mzero.2
    ⟨hx, closure_minimal (sigmaH_subset_closure Ω u χ) isClosed_closure hcl, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hev := h.upperSemicontinuousOn_Mzero x hx _ hlt
  rw [h.isOpen.nhdsWithin_eq hx] at hev
  obtain ⟨y, hyS, hy⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually hev).exists
  exact absurd (h.mem_sigmaH_iff_le_Mzero.1 hyS).2.2 (not_le.2 hy)

end IsVariationalSolution

end InnerVariational
