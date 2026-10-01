/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import InnerVariational.Kernel.VariationalQ
public import InnerVariational.Registry.GMT
public import GMTFoundations.Defs.GMT
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Blowup.ChiLimitQ
import InnerVariational.Monotonicity.DensityQ
import InnerVariational.Monotonicity.HighestDensityQ
import InnerVariational.Regular.ChiInteriorQ
import InnerVariational.Registry.Harmonic

/-!
# The density dichotomy at zeros of `u` with a Lipschitz coefficient (Lemma 8.1)

Lemma 8.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for a variational
solution `(u, χ)` on `Ω` with a coefficient `Q`, `QBounds Ω Q L c C'`, `2 ≤ n`, and `x ∈ Ω` with
`u(x) = 0`. The paper treats `Q ≡ 1`; we write `M^{Q(x)}_x(u; 0+)` for the Weiss energy with the
coefficient frozen at `Q(x)` (`MzeroQ`). Then

* `M^{Q(x)}_x(u; 0+) ∈ {0} ∪ [Q(x)² |B_1|/2, Q(x)² |B_1|]` (`MzeroQ_eq_zero_or_half_le`);
* `M^{Q(x)}_x(u; 0+) = 0` only if `x ∈ {u = 0}°` (`mem_interior_of_MzeroQ_eq_zero`);
* if `x ∈ ∂{u > 0}` and the blow-ups `u(x + r ·)/r` tend to `0` along some `r_k → 0+`, then
  `M^{Q(x)}_x(u; 0+) = Q(x)² |B_1|` (`MzeroQ_eq_of_tendsto_rescale_zero`).

Consequently `Q(x)² |B_1|/2 ≤ M^{Q(x)}_x(u; 0+) ≤ Q(x)² |B_1|` on `Ω ∩ ∂{u > 0}`
(`half_le_MzeroQ_of_mem_frontier`). The statements for `Q ≡ 1` (`Regular/Density.lean`) are the
special case.

## Proof

The blow-up statements are phrased with the density `d = lim r^{-n} ∫_{B_r(x)} χ`; the formula
`M^{Q(x)}_x(u; 0+) = Q(x)² d` (`tendsto_monotonicityMq_zero`) translates them. Along a blow-up
sequence `u_{x,r_k} → u₀`, a subsequence of `χ_{x,r_k}` converges to `χ₀` with `(u₀, χ₀)` a
variational solution on `ℝⁿ` for the constant coefficient `Q(x)` (`exists_blowup_limit_ae`), so
`∫_{B_1} χ₀ = d` (`exists_blowup_limit_density`).

* If `u₀ ≢ 0`, Sperner's inequality (E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf
  Sphären*, Math. Z. 134 (1973), 317–327; `Registry.sperner_half_volume`) gives
  `|{u₀ > 0} ∩ B_1| ≥ |B_1|/2`, and `χ₀ ≥ χ_{u₀>0}` gives `|{u₀ > 0} ∩ B_1| ≤ ∫_{B_1} χ₀ = d`.
* If `u₀ ≡ 0`, the inner variation of `(0, χ₀)` gives `∫ χ₀ div ξ = 0`, so `χ₀` is a.e. a
  constant in `{0, 1}` (`IsVariationalSolutionQ.exists_ae_eq_const_of_eq_zero`) and
  `d ∈ {0, |B_1|}`.

The openness argument (third paragraph of the proof) uses the upper semicontinuity of
`x ↦ M^{Q(x)}_x(u; 0+)` (`upperSemicontinuousOn_MzeroQ`) and the lower bound `c ≤ Q`: near a point
with `M^{Q(x)}_x(u; 0+) = 0` every zero `y` of `u` has `M^{Q(y)}_y(u; 0+) < c² |B_1|/4`, hence
density `0`, and every `y` with `u(y) > 0` has density `1`. Federer's theorem
(`Registry.ae_trivial_of_essentialBoundary_inter_ball`) then makes `{χ = 1}` null or full near
`x`, as for `Q ≡ 1`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-- `∫_{B_1} χ_{x,r_k} → m` when `r^{-n} ∫_{B_r(x)} χ → m` and `r_k → 0+`. -/
theorem tendsto_setIntegral_chiRescale {χ : Rn n → ℝ} {x : Rn n} {m : ℝ}
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, chiRescale χ x (r k) y) atTop (𝓝 m) := by
  have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
  refine (hd.comp h1).congr fun k => ?_
  rw [Function.comp_apply, setIntegral_chiRescale χ x (hr k) 1, mul_one]

end Regular

namespace QBounds

/-- A positive constant coefficient satisfies the bounds with Lipschitz constant `0`. -/
theorem const (Ω : Set (Rn n)) {a : ℝ} (ha : 0 < a) : QBounds Ω (fun _ => a) 0 a a where
  lipschitzOnWith := (LipschitzWith.const a).lipschitzOnWith
  pos := ha
  le _ _ := le_rfl
  le' _ _ := le_rfl

end QBounds

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-- A variational solution for a positive constant coefficient `a` is, after dividing `u` by
`a`, a variational solution with coefficient `1` (`isVariationalSolutionQ_const_iff`). -/
theorem toConst {a : ℝ} (h : IsVariationalSolutionQ Ω C (fun _ => a) u χ) (ha : 0 < a) :
    IsVariationalSolution Ω (C / a.toNNReal) (fun y => u y / a) χ := by
  have e : a = ((a.toNNReal : ℝ≥0) : ℝ) := (Real.coe_toNNReal _ ha.le).symm
  have h' : IsVariationalSolutionQ Ω C (fun _ => ((a.toNNReal : ℝ≥0) : ℝ)) u χ := by
    rw [← e]; exact h
  have := (isVariationalSolutionQ_const_iff (Real.toNNReal_pos.2 ha)).1 h'
  rwa [← e] at this

/-! ### Densities of `{χ = 1}` -/

/-- The Lebesgue density of `Ω ∩ {χ = 1}` at `x` is `d / |B_1|` when `r^{-n} ∫_{B_r(x)} χ → d`. -/
theorem hasDensity_of_tendsto (h : IsVariationalSolutionQ Ω C Q u χ) {δ : ℝ} (hδ : 0 < δ)
    (hδΩ : ball x δ ⊆ Ω) {d : ℝ}
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 d)) :
    HasDensity (Ω ∩ {y | χ y = 1}) x (d / unitBallVolume n) := by
  unfold HasDensity
  refine (hd.div_const (unitBallVolume n)).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hball : ball x r ⊆ Ω := (ball_subset_ball hr.2.le).trans hδΩ
  have hE : Ω ∩ {y | χ y = 1} ∩ ball x r = {y | χ y = 1} ∩ ball x r := by
    ext y
    exact ⟨fun hy => ⟨hy.1.2, hy.2⟩, fun hy => ⟨⟨hball hy.2, hy.1⟩, hy.2⟩⟩
  have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.1.ne'
  have hB : unitBallVolume n ≠ 0 := (unitBallVolume_pos n).ne'
  rw [hE, volume_ball_toReal x hr.1, ← measureReal_def, ← h.setIntegral_chi_eq_measureReal hball]
  field_simp

/-- Near a point with `u > 0`, `{χ = 1}` has density `1`. -/
theorem hasDensity_one_of_pos (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω)
    (hpos : 0 < u x) : HasDensity (Ω ∩ {y | χ y = 1}) x 1 := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 h.isOpen_pos x ⟨hx, hpos⟩
  have hc : ∀ᵐ z ∂(volume.restrict (ball x ε)), χ z = 1 := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [h.ae_chi_eq_one] with z hz hzb
    exact hz (hεsub hzb).1 (hεsub hzb).2
  have := h.hasDensity_of_tendsto hε (hεsub.trans inter_subset_left)
    (Regular.tendsto_density_of_ae_eq_const hε hc)
  rwa [one_mul, div_self (unitBallVolume_pos n).ne'] at this

/-! ### Blow-ups at a zero of `u` -/

/-- Every sequence `r_k → 0+` has a subsequence along which `u_{x,r_k}` converges locally
uniformly (Arzelà–Ascoli, as in the proof of Proposition 3.5), provided `u(x) = 0`. -/
theorem exists_tendsto_rescale (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω)
    (hux : u x = 0) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => oneHomRescale u x (r (φ k))) u₀ atTop := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  have hρ : Tendsto (fun k => R / r k) atTop atTop := by
    have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
    simpa [div_eq_mul_inv] using (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hR0
  have hLip : ∀ k, LipschitzOnWith C (oneHomRescale u x (r k)) (ball 0 (R / r k)) := fun k =>
    (h.rescale x (hr k)).lipschitzOnWith 0 _ (ball_div_subset_preimage (hr k) hR)
  have hM0 : ∀ k, |oneHomRescale u x (r k) 0| ≤ 0 := fun k => by simp [hux]
  obtain ⟨φ, hφ, u₀, -, hconv⟩ := exists_blowup_subseq hρ (fun k => div_pos hR0 (hr k)) hLip hM0
  exact ⟨φ, hφ, u₀, hconv⟩

section Blowup

variable (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) {d : ℝ}
  (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 d))
  {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
include hQ h hx hd hr hr0

/-- **Blow-up pairs with a density.** If `r^{-n} ∫_{B_r(x)} χ → d` and `u_{x,r_k} → u₀`, there is
`χ₀` with `(u₀, χ₀)` a variational solution on `ℝⁿ` for the constant coefficient `Q(x)` and
`∫_{B_1} χ₀ = d`. -/
theorem exists_blowup_limit_density {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    ∃ χ₀, IsVariationalSolutionQ univ C (fun _ => Q x) u₀ χ₀ ∧
      ∫ y in ball (0 : Rn n) 1, χ₀ y = d := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  obtain ⟨φ, hφ, χ₀, hsol, hae, -⟩ := exists_blowup_limit_ae hQ h hx hr hr0 hconv
  refine ⟨χ₀, hsol, tendsto_nhds_unique ?_ (Regular.tendsto_setIntegral_chiRescale hd
    (fun k => hr (φ k)) (hr0.comp hφ.tendsto_atTop))⟩
  have hev := hφ.tendsto_atTop.eventually (h.eventually_rescale_ball hQ hR0 hR hr hr0 one_pos)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
    (integrableOn_const measure_ball_lt_top.ne) (ae_restrict_of_ae hae)
  · filter_upwards [hev] with k hk
    exact hk.1.aestronglyMeasurable_chi measurableSet_ball subset_rfl
  · filter_upwards [hev] with k hk
    exact (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact hk.1.abs_chi_le_one hy)

/-- **Lower semicontinuity of the positivity set** (proof of Lemma 8.1): for a blow-up `u₀`,
`|{u₀ > 0} ∩ B_1| ≤ lim r^{-n} ∫_{B_r(x)} χ`. -/
theorem measureReal_pos_inter_ball_le {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) ≤ d := by
  obtain ⟨χ₀, hsol, hint⟩ := exists_blowup_limit_density hQ h hx hd hr hr0 hconv
  rw [← hint]
  have hu₀c : Continuous u₀ := continuousOn_univ.1 hsol.continuousOn
  have hP : MeasurableSet {y | 0 < u₀ y} := (isOpen_lt continuous_const hu₀c).measurableSet
  have e : volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) =
      ∫ y in ball (0 : Rn n) 1, posIndicator u₀ y := by
    rw [posIndicator, setIntegral_indicator hP]
    simp only [Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one, inter_comm]
  rw [e]
  refine setIntegral_mono_ae_restrict ?_ ?_ ?_
  · exact IntegrableOn.of_bound measure_ball_lt_top
      ((measurable_one.indicator hP).aestronglyMeasurable) 1 (.of_forall fun y => by
        rw [posIndicator]; by_cases hy : y ∈ {y | 0 < u₀ y} <;> simp [hy])
  · exact IntegrableOn.of_bound measure_ball_lt_top
      (hsol.aestronglyMeasurable_chi measurableSet_ball (subset_univ _)) 1
      (.of_forall fun y => by rw [Real.norm_eq_abs]; exact hsol.abs_chi_le_one (mem_univ y))
  · have := hsol.posIndicator_le_chi
    rw [Measure.restrict_univ] at this
    exact ae_restrict_of_ae this

/-- **Sperner step** (proof of Lemma 8.1): if a blow-up `u₀` is not identically zero, then
`lim r^{-n} ∫_{B_r(x)} χ ≥ |B_1|/2`. Uses Sperner's inequality (`Registry.sperner_half_volume`). -/
theorem half_le_of_tendsto_rescale (hn : 2 ≤ n) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {y₀ : Rn n}
    (hy₀ : 0 < u₀ y₀) : unitBallVolume n / 2 ≤ d := by
  have : NeZero n := ⟨by omega⟩
  have hH := blowup_isLipHarmonicPos hQ h hx hr hr0 hconv
  have hR07 := Registry.sperner_half_volume hn ⟨C, blowup_lipschitzWith hQ h hx hr hr0 hconv⟩
    (fun y => hH.nonneg y trivial) (fun y t ht => blowup_homogeneous' hQ h hx hr hr0 hconv t ht y)
    hy₀ (fun y hy => hH.harmonicAt y trivial
      (connectedComponentIn_subset _ _ hy : y ∈ {y | 0 < u₀ y}))
  refine hR07.1.trans ((ENNReal.toReal_mono ?_ (measure_mono
    (inter_subset_inter_left _ (connectedComponentIn_subset _ _)))).trans
    (measureReal_pos_inter_ball_le hQ h hx hd hr hr0 hconv))
  exact ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne

/-- **Zero blow-ups** (last paragraph of the proof of Lemma 8.1). If `u_{x,r_k} → 0` locally
uniformly along some `r_k → 0+`, then `lim r^{-n} ∫_{B_r(x)} χ ∈ {0, |B_1|}`. -/
theorem eq_zero_or_eq_of_tendsto_rescale_zero
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) (fun _ => 0) atTop) :
    d = 0 ∨ d = unitBallVolume n := by
  obtain ⟨χ₀, hsol, hint⟩ := exists_blowup_limit_density hQ h hx hd hr hr0 hconv
  obtain ⟨c₀, hc01, hc⟩ := hsol.exists_ae_eq_const_of_eq_zero (QBounds.const univ
    (hQ.pos_of_mem hx)) isOpen_ball (convex_ball (0 : Rn n) 1).isPreconnected (subset_univ _)
    (fun _ _ => rfl)
  have hdc : d = c₀ * unitBallVolume n := by
    rw [← hint,
      setIntegral_congr_ae measurableSet_ball ((ae_restrict_iff' measurableSet_ball).1 hc),
      setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal _ one_pos, one_pow,
      one_mul, mul_comm]
  rcases hc01 with h0 | h1
  · left; rw [hdc, h0, zero_mul]
  · right; rw [hdc, h1, one_mul]

end Blowup

/-! ### Lemma 8.1 -/

/-- **Lemma 8.1**, first claim, in terms of the density: if `2 ≤ n`, `u(x) = 0` and
`r^{-n} ∫_{B_r(x)} χ → d`, then `d = 0` or `d ≥ |B_1|/2`. -/
theorem density_eq_zero_or_half_le (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hux : u x = 0) {d : ℝ}
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 d)) :
    d = 0 ∨ unitBallVolume n / 2 ≤ d := by
  have hr : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hr0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, u₀, hconv⟩ := h.exists_tendsto_rescale hx hux hr hr0
  have hr' : ∀ k, 0 < 1 / ((φ k : ℝ) + 1) := fun k => hr (φ k)
  have hr0' : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  by_cases hpos : ∃ y₀, 0 < u₀ y₀
  · obtain ⟨y₀, hy₀⟩ := hpos
    exact Or.inr (half_le_of_tendsto_rescale hQ h hx hd hr' hr0' hn hconv hy₀)
  · push Not at hpos
    have : NeZero n := ⟨by omega⟩
    have hH := blowup_isLipHarmonicPos hQ h hx hr' hr0' hconv
    have hu₀ : u₀ = fun _ => 0 := funext fun y => le_antisymm (hpos y) (hH.nonneg y trivial)
    rw [hu₀] at hconv
    rcases eq_zero_or_eq_of_tendsto_rescale_zero hQ h hx hd hr' hr0' hconv with h0 | h1
    · exact Or.inl h0
    · right; rw [h1]; linarith [unitBallVolume_pos n]

/-- The density form of `M^{Q(x)}_x(u; 0+)`: if `u(x) = 0`, then `M^{Q(x)}_x(u; 0+)` is a real
number `Q(x)² d`, where `d = lim r^{-n} ∫_{B_r(x)} χ`. -/
theorem exists_MzeroQ_eq_sq_mul [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hux : u x = 0) :
    ∃ d : ℝ, MzeroQ (Q x) u χ x = ((Q x ^ 2 * d : ℝ) : EReal) ∧
      Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 d) := by
  obtain ⟨m, hmM, -, hlim⟩ := h.tendsto_monotonicityMq_zero hQ hx hux
  have hq2 : Q x ^ 2 ≠ 0 := (pow_pos (hQ.pos_of_mem hx) 2).ne'
  refine ⟨m / Q x ^ 2, by rw [hmM, mul_div_cancel₀ _ hq2], ?_⟩
  refine (hlim.div_const (Q x ^ 2)).congr fun r => ?_
  rw [mul_div_cancel_left₀ _ hq2]

/-- **Lemma 8.1**, first claim. If `2 ≤ n`, `x ∈ Ω` and `u(x) = 0`, then `M^{Q(x)}_x(u; 0+)` is a
real number `m ∈ {0} ∪ [Q(x)² |B_1|/2, Q(x)² |B_1|]`. -/
theorem MzeroQ_eq_zero_or_half_le (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hux : u x = 0) :
    ∃ m : ℝ, MzeroQ (Q x) u χ x = m ∧ (m = 0 ∨ Q x ^ 2 * unitBallVolume n / 2 ≤ m) ∧
      m ≤ Q x ^ 2 * unitBallVolume n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨d, hdM, hd⟩ := h.exists_MzeroQ_eq_sq_mul hQ hx hux
  have hq2 : 0 < Q x ^ 2 := pow_pos (hQ.pos_of_mem hx) 2
  refine ⟨Q x ^ 2 * d, hdM, ?_, ?_⟩
  · rcases density_eq_zero_or_half_le hn hQ h hx hux hd with h0 | hhalf
    · left; rw [h0, mul_zero]
    · right
      calc Q x ^ 2 * unitBallVolume n / 2 = Q x ^ 2 * (unitBallVolume n / 2) := by ring
        _ ≤ Q x ^ 2 * d := mul_le_mul_of_nonneg_left hhalf hq2.le
  · have := h.MzeroQ_le_sq_mul_unitBallVolume hQ hx
    rwa [hdM, EReal.coe_le_coe_iff] at this

/-- **Lemma 8.1**, second claim. `M^{Q(x)}_x(u; 0+) = 0` only if `x` is in the interior of
`{u = 0}`. -/
theorem mem_interior_of_MzeroQ_eq_zero (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hM : MzeroQ (Q x) u χ x = 0) :
    x ∈ interior {y | u y = 0} := by
  have : NeZero n := ⟨by omega⟩
  have hB := unitBallVolume_pos n
  have hc2 : 0 < c ^ 2 := pow_pos hQ.pos 2
  have hev : ∀ᶠ y in 𝓝 x, MzeroQ (Q y) u χ y < ((c ^ 2 * unitBallVolume n / 4 : ℝ) : EReal) := by
    have := h.upperSemicontinuousOn_MzeroQ hQ x hx
      ((c ^ 2 * unitBallVolume n / 4 : ℝ) : EReal) (by
        change MzeroQ (Q x) u χ x < ((c ^ 2 * unitBallVolume n / 4 : ℝ) : EReal)
        rw [hM]
        exact_mod_cast (by positivity : (0 : ℝ) < c ^ 2 * unitBallVolume n / 4))
    rwa [h.isOpen.nhdsWithin_eq hx] at this
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (hev.and (h.isOpen.mem_nhds hx))
  set E : Set (Rn n) := Ω ∩ {y | χ y = 1} with hEdef
  have hess : essentialBoundary E ∩ ball x δ = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hyE, hyB⟩ => ?_
    obtain ⟨hyM, hyΩ⟩ := hδsub hyB
    rcases (h.nonneg y hyΩ).lt_or_eq with hpos | hzero
    · exact hyE.2 (h.hasDensity_one_of_pos hyΩ hpos)
    · obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 h.isOpen y hyΩ
      obtain ⟨d, hdM, hd⟩ := h.exists_MzeroQ_eq_sq_mul hQ hyΩ hzero.symm
      have hd0 : d = 0 := by
        rcases density_eq_zero_or_half_le hn hQ h hyΩ hzero.symm hd with h0 | hhalf
        · exact h0
        · exfalso
          rw [hdM] at hyM
          have h1 := EReal.coe_lt_coe_iff.1 hyM
          have h2 : c ^ 2 * (unitBallVolume n / 2) ≤ Q y ^ 2 * d :=
            mul_le_mul (hQ.sq_le_sq hyΩ) hhalf (by positivity) (sq_nonneg _)
          nlinarith
      have := h.hasDensity_of_tendsto hε hεΩ hd
      rw [hd0, zero_div] at this
      exact hyE.1 this
  rcases Registry.ae_trivial_of_essentialBoundary_inter_ball hn h.measurableSet_chi_eq_one hess
    with h0 | h1
  · -- `{χ = 1}` is null in `B_δ(x)`, so `{u > 0} ∩ B_δ(x) = ∅`
    have hnull : volume (Ω ∩ {y | 0 < u y} ∩ ball x δ) = 0 := by
      refine measure_mono_null_ae ?_ h0
      filter_upwards [h.ae_chi_eq_one] with z hz
      rintro ⟨⟨hzΩ, hzp⟩, hzb⟩
      exact ⟨⟨hzΩ, hz hzΩ hzp⟩, hzb⟩
    have hempty : Ω ∩ {y | 0 < u y} ∩ ball x δ = ∅ :=
      ((h.isOpen_pos.inter isOpen_ball).measure_eq_zero_iff volume).1 hnull
    rw [mem_interior]
    refine ⟨ball x δ, fun y hy => ?_, isOpen_ball, mem_ball_self hδ⟩
    have hyΩ := (hδsub hy).2
    refine le_antisymm (not_lt.1 fun hp => ?_) (h.nonneg y hyΩ)
    exact eq_empty_iff_forall_notMem.1 hempty y ⟨⟨hyΩ, hp⟩, hy⟩
  · -- `{χ = 1}` is full in `B_δ(x)`: contradicts density `0` at `x`
    exfalso
    have hux : u x = 0 := by
      rcases (h.nonneg x hx).lt_or_eq with hpos | h0
      · rw [h.MzeroQ_eq_bot_of_pos hQ hx hpos] at hM; exact absurd hM EReal.bot_ne_zero
      · exact h0.symm
    obtain ⟨d, hdM, hd⟩ := h.exists_MzeroQ_eq_sq_mul hQ hx hux
    have hq2 : Q x ^ 2 ≠ 0 := (pow_pos (hQ.pos_of_mem hx) 2).ne'
    have hd0 : d = 0 := by
      rw [hM] at hdM
      have : Q x ^ 2 * d = 0 := by exact_mod_cast hdM.symm
      exact (mul_eq_zero.1 this).resolve_left hq2
    have hc : ∀ᵐ z ∂(volume.restrict (ball x δ)), χ z = 1 := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with z hz hzb
      by_contra hne
      exact hz ⟨hzb, fun hzE => hne hzE.2⟩
    have := tendsto_nhds_unique hd (Regular.tendsto_density_of_ae_eq_const hδ hc)
    rw [hd0, one_mul] at this
    linarith

/-- **Lemma 8.1**, last claim. If `x ∈ Ω ∩ ∂{u > 0}` and `u_{x,r_k} → 0` locally uniformly along
some `r_k → 0+`, then `M^{Q(x)}_x(u; 0+) = Q(x)² |B_1|`. -/
theorem MzeroQ_eq_of_tendsto_rescale_zero (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y})
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) (fun _ => 0) atTop) :
    MzeroQ (Q x) u χ x = ((Q x ^ 2 * unitBallVolume n : ℝ) : EReal) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 hfr
  obtain ⟨d, hdM, hd⟩ := h.exists_MzeroQ_eq_sq_mul hQ hx hux
  rcases eq_zero_or_eq_of_tendsto_rescale_zero hQ h hx hd hr hr0 hconv with h0 | h1
  · exfalso
    have hint := mem_interior_of_MzeroQ_eq_zero hn hQ h hx (by rw [hdM, h0, mul_zero,
      EReal.coe_zero])
    obtain ⟨y, hyint, hypos⟩ := mem_closure_iff.1 hcl _ isOpen_interior hint
    have hy0 : u y = 0 := interior_subset (s := {y | u y = 0}) hyint
    have hyp : 0 < u y := hypos
    rw [hy0] at hyp
    exact lt_irrefl _ hyp
  · rw [hdM, h1]

/-- On the free boundary, `Q(x)² |B_1|/2 ≤ M^{Q(x)}_x(u; 0+) ≤ Q(x)² |B_1|`. -/
theorem half_le_MzeroQ_of_mem_frontier (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) :
    ∃ m : ℝ, MzeroQ (Q x) u χ x = m ∧ Q x ^ 2 * unitBallVolume n / 2 ≤ m ∧
      m ≤ Q x ^ 2 * unitBallVolume n := by
  obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 hfr
  obtain ⟨m, hmM, hm01, hm1⟩ := MzeroQ_eq_zero_or_half_le hn hQ h hx hux
  refine ⟨m, hmM, ?_, hm1⟩
  rcases hm01 with h0 | hhalf
  · exfalso
    have hint := mem_interior_of_MzeroQ_eq_zero hn hQ h hx (by rw [hmM, h0, EReal.coe_zero])
    obtain ⟨y, hyint, hypos⟩ := mem_closure_iff.1 hcl _ isOpen_interior hint
    have hy0 : u y = 0 := interior_subset (s := {y | u y = 0}) hyint
    have hyp : 0 < u y := hypos
    rw [hy0] at hyp
    exact lt_irrefl _ hyp
  · exact hhalf

end IsVariationalSolutionQ

end InnerVariational
