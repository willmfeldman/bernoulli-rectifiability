/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Limit
public import InnerVariational.Blowup.Renormalization
public import InnerVariational.Kernel.Harmonic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Blowup.ExplicitForm
import InnerVariational.Blowup.DomainVariation
public import InnerVariational.Blowup.Sobolev
import InnerVariational.Sobolev.WeakGradient
public import InnerVariational.Defs.Quantities
public import InnerVariational.Kernel.BV
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
import InnerVariational.Sobolev.Lipschitz
public import InnerVariational.Blowup.Profile.L2Limits

/-!
# The limit profile in Theorem 5.3, steps (d)–(e)

Steps (d) and (e) of the proof of Theorem 5.3 of Kriventsov–Weiss for the explicit blow-up limit
`v = β₊ ⟪ν₀, y⟫₊ + β₋ ⟪ν₀, y⟫₋` (see `Blowup/Profile/Normalization.lean` for the overview): `v`
satisfies the energy identity, step (e) gives `β₊² = β₋²`, and the `L²` distances to the profiles
`α |⟪y, ν_k⟫|` tend to zero when `ν_k → ν₀`.

## Main results

* `integral_mul_inner_gradient_eq_of_explicit`: the limit satisfies the energy identity.
* `sq_eq_sq_of_integral_mul_fderiv_eq_zero`: step (e).

## Faithfulness notes

* Step (e) uses the test function `φ(y) = b(y − ⟪ν₀, y⟫ ν₀) θ(⟪ν₀, y⟫)` instead of the paper's
  symmetric `ξ_n`, and never forms the hyperplane integral `∫_{x_n = 0} ξ_n dℋ^{n-1}`: only the
  sign of `∫_{⟪ν₀, y⟫ > 0} ∂_{ν₀} φ` is needed. It uses `n ≥ 2` exactly where the paper does.
* The paper's integration by parts `∫ |∇v|² η = −∫ v ∇η·∇v − ∫ v η Δv` in step (d) is formal,
  since `Δv` is a measure on the hyperplane where `v = 0`. It is proved here directly from the
  explicit form.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### The limit profile -/

/-- **The blow-up limit satisfies the energy identity** (`v Δv = 0`, step (d)). Let
`v = β₊ ⟪ν₀, y⟫₊ + β₋ ⟪ν₀, y⟫₋` a.e. on `A`, with gradient `G = ±β_± ν₀` on `{±⟪ν₀, y⟫ > 0}`.
Then `∫_A v ⟪∇v, ∇η⟫ = −∫_A |∇v|² η` for `η ∈ C_c^∞(A)`. On each side of the hyperplane this is
the one-dimensional integration by parts `integral_indicator_add_max_inner_mul_fderiv`. -/
theorem integral_mul_inner_gradient_eq_of_explicit {A : Set (Rn n)} {ν₀ : Rn n} (hν₀ : ‖ν₀‖ = 1)
    {βp βm : ℝ} {F : Rn n → ℝ} {G : Rn n → Rn n}
    (hF : MemLp F 2 (volume.restrict A)) (hG : MemLp G 2 (volume.restrict A))
    (hside : ∀ᵐ y ∂(volume.restrict A),
      (0 < ⟪ν₀, y⟫ → F y = βp * ⟪ν₀, y⟫ ∧ ⟪G y, ν₀⟫ = βp) ∧
      (⟪ν₀, y⟫ < 0 → F y = βm * -⟪ν₀, y⟫ ∧ ⟪G y, ν₀⟫ = -βm))
    (htan : ∀ᵐ y ∂(volume.restrict A), G y = ⟪G y, ν₀⟫ • ν₀)
    (hnull : ∀ᵐ y ∂(volume.restrict A), ⟪ν₀, y⟫ ≠ 0)
    {η : Rn n → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηA : tsupport η ⊆ A) :
    ∫ y in A, F y * ⟪G y, gradient η y⟫ = -∫ y in A, ‖G y‖ ^ 2 * η y := by
  obtain ⟨Lη, hLη⟩ := hη.lipschitzWith_of_hasCompactSupport hηc (by simp)
  obtain ⟨Cη, hCη⟩ := hη.continuous.bounded_above_of_compact_support hηc
  have hgη : ∀ y, ‖gradient η y‖ ≤ Lη := Kernel.norm_gradient_le_of_lipschitz hLη
  have hgηm : AEStronglyMeasurable (gradient η) (volume.restrict A) :=
    (measurable_gradient η).aestronglyMeasurable
  have hηm : AEStronglyMeasurable η (volume.restrict A) := hη.continuous.aestronglyMeasurable
  have hηout : ∀ y ∉ A, η y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hηA h)
  have hFgη : MemLp (fun y => F y • gradient η y) 2 (volume.restrict A) := by
    refine (hF.const_mul (Lη : ℝ)).of_le (hF.aestronglyMeasurable.smul hgηm)
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (NNReal.coe_nonneg Lη), mul_comm]
    exact mul_le_mul_of_nonneg_right (hgη y) (abs_nonneg _)
  have iG : Integrable (fun y => ‖G y‖ ^ 2 * η y) (volume.restrict A) :=
    (MemLp.integrable_norm_sq hG).mul_bdd hηm (Eventually.of_forall hCη)
  have iF : Integrable (fun y => F y * ⟪G y, gradient η y⟫) (volume.restrict A) := by
    refine (MemLp.integrable_inner_two hG hFgη).congr (Eventually.of_forall fun y => ?_)
    simp only [inner_smul_right]
  set Pf : Rn n → Rn n → ℝ := fun e y =>
    {y | 0 < ⟪e, y⟫}.indicator η y + max ⟪e, y⟫ 0 * fderiv ℝ η y e with hPf
  have hPint : ∀ e, Integrable (Pf e) := by
    intro e
    have hi1 : Integrable ({y : Rn n | 0 < ⟪e, y⟫}.indicator η) :=
      (hη.continuous.integrable_of_hasCompactSupport hηc).indicator
        (measurableSet_lt measurable_const (measurable_const.inner measurable_id))
    have hc2 : Continuous fun y => max ⟪e, y⟫ 0 * fderiv ℝ η y e :=
      ((continuous_const.inner continuous_id).max continuous_const).mul
        ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact hi1.add (hc2.integrable_of_hasCompactSupport (hηc.fderiv_apply (𝕜 := ℝ) e).mul_left)
  have hP0 : ∀ e : Rn n, ‖e‖ = 1 → ∫ y in A, Pf e y = 0 := by
    intro e he
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_]
    · exact integral_indicator_add_max_inner_mul_fderiv he hη hηc
    · have h1 : η y = 0 := hηout y hy
      have h2 : fderiv ℝ η y = 0 := fderiv_of_notMem_tsupport ℝ fun h => hy (hηA h)
      simp [hPf, h1, h2, indicator_apply]
  have hpt : ∀ᵐ y ∂(volume.restrict A), ‖G y‖ ^ 2 * η y + F y * ⟪G y, gradient η y⟫ =
      βp ^ 2 * Pf ν₀ y + βm ^ 2 * Pf (-ν₀) y := by
    filter_upwards [hside, htan, hnull] with y hs ht h0
    have hgi : ⟪G y, gradient η y⟫ = ⟪G y, ν₀⟫ * fderiv ℝ η y ν₀ := by
      conv_lhs => rw [ht]
      rw [inner_smul_left, conj_trivial, Kernel.inner_gradient_right]
    have hn' : ‖G y‖ ^ 2 = ⟪G y, ν₀⟫ ^ 2 := by
      conv_lhs => rw [ht]
      rw [norm_smul, hν₀, mul_one, Real.norm_eq_abs, sq_abs]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · obtain ⟨hF', hg⟩ := hs.2 hneg
      have hi2 : 0 < ⟪-ν₀, y⟫ := by rw [inner_neg_left]; linarith
      have e1 : Pf ν₀ y = 0 := by
        simp only [hPf]
        rw [indicator_of_notMem (show y ∉ {y : Rn n | 0 < ⟪ν₀, y⟫} from not_lt.2 hneg.le),
          max_eq_right hneg.le, zero_mul, zero_add]
      have e2 : Pf (-ν₀) y = η y + -⟪ν₀, y⟫ * -fderiv ℝ η y ν₀ := by
        simp only [hPf]
        rw [indicator_of_mem (show y ∈ {y : Rn n | 0 < ⟪-ν₀, y⟫} from hi2),
          max_eq_left hi2.le, inner_neg_left, map_neg]
      rw [e1, e2, hgi, hn', hF', hg]
      ring
    · obtain ⟨hF', hg⟩ := hs.1 hpos
      have hi2 : ¬ 0 < ⟪-ν₀, y⟫ := by rw [inner_neg_left]; linarith
      have e1 : Pf ν₀ y = η y + ⟪ν₀, y⟫ * fderiv ℝ η y ν₀ := by
        simp only [hPf]
        rw [indicator_of_mem (show y ∈ {y : Rn n | 0 < ⟪ν₀, y⟫} from hpos), max_eq_left hpos.le]
      have e2 : Pf (-ν₀) y = 0 := by
        simp only [hPf]
        rw [indicator_of_notMem (show y ∉ {y : Rn n | 0 < ⟪-ν₀, y⟫} from hi2),
          max_eq_right (not_lt.1 hi2), zero_mul, zero_add]
      rw [e1, e2, hgi, hn', hF', hg]
      ring
  have h := integral_congr_ae hpt
  rw [integral_add iG iF, integral_add ((hPint _).integrableOn.const_mul _)
    ((hPint _).integrableOn.const_mul _), integral_const_mul, integral_const_mul, hP0 ν₀ hν₀,
    hP0 (-ν₀) (by rw [norm_neg, hν₀])] at h
  linarith

/-- **Step (e) of the proof of Theorem 5.3: `β₊² = β₋²`.** If `⟪G, ν₀⟫ = β₊` on `{⟪ν₀, y⟫ > 0}`
and `= −β₋` on `{⟪ν₀, y⟫ < 0}` a.e. on `A'`, and the limit domain variation identity
`∫_{A'} ⟪G, ν₀⟫² ∂_{ν₀} φ = 0` holds for a test function `φ ∈ C_c^∞(A')` with
`∫_{⟪ν₀, y⟫ > 0} ∂_{ν₀} φ ≠ 0` (`exists_jump_testFunction`), then `β₊² = β₋²`. Since
`∫ ∂_{ν₀} φ = 0`, the identity reads `(β₊² − β₋²) ∫_{⟪ν₀, y⟫ > 0} ∂_{ν₀} φ = 0`. -/
theorem sq_eq_sq_of_integral_mul_fderiv_eq_zero {A' : Set (Rn n)} {ν₀ : Rn n} {βp βm : ℝ}
    {F : Rn n → ℝ} {G : Rn n → Rn n}
    (hside : ∀ᵐ y ∂(volume.restrict A'),
      (0 < ⟪ν₀, y⟫ → F y = βp * ⟪ν₀, y⟫ ∧ ⟪G y, ν₀⟫ = βp) ∧
      (⟪ν₀, y⟫ < 0 → F y = βm * -⟪ν₀, y⟫ ∧ ⟪G y, ν₀⟫ = -βm))
    (hnull : ∀ᵐ y ∂(volume.restrict A'), ⟪ν₀, y⟫ ≠ 0)
    {φ : Rn n → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφA' : tsupport φ ⊆ A')
    (hjump : ∫ y, {y | 0 < ⟪ν₀, y⟫}.indicator (fun y => fderiv ℝ φ y ν₀) y < 0)
    (h0 : ∫ y in A', ⟪G y, ν₀⟫ ^ 2 * fderiv ℝ φ y ν₀ = 0) : βp ^ 2 = βm ^ 2 := by
  have hdφc : Continuous fun y => fderiv ℝ φ y ν₀ :=
    (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφi : Integrable fun y => fderiv ℝ φ y ν₀ :=
    hdφc.integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) ν₀)
  have hgi : Integrable ({y : Rn n | 0 < ⟪ν₀, y⟫}.indicator fun y => fderiv ℝ φ y ν₀) :=
    hdφi.indicator (measurableSet_lt measurable_const (measurable_const.inner measurable_id))
  have hpt : ∀ᵐ y ∂(volume.restrict A'), ⟪G y, ν₀⟫ ^ 2 * fderiv ℝ φ y ν₀ =
      βm ^ 2 * fderiv ℝ φ y ν₀ +
        (βp ^ 2 - βm ^ 2) * {y | 0 < ⟪ν₀, y⟫}.indicator (fun y => fderiv ℝ φ y ν₀) y := by
    filter_upwards [hside, hnull] with y hs h0
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · rw [(hs.2 hneg).2,
        indicator_of_notMem (show y ∉ {y : Rn n | 0 < ⟪ν₀, y⟫} from not_lt.2 hneg.le)]
      ring
    · rw [(hs.1 hpos).2, indicator_of_mem (show y ∈ {y : Rn n | 0 < ⟪ν₀, y⟫} from hpos)]
      ring
  have hout : ∀ y ∉ A', βm ^ 2 * fderiv ℝ φ y ν₀ +
      (βp ^ 2 - βm ^ 2) * {y | 0 < ⟪ν₀, y⟫}.indicator (fun y => fderiv ℝ φ y ν₀) y = 0 := by
    intro y hy
    have h1 : fderiv ℝ φ y ν₀ = 0 := by
      rw [fderiv_of_notMem_tsupport ℝ fun h => hy (hφA' h)]
      rfl
    simp [h1, indicator_apply]
  rw [integral_congr_ae hpt, setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    integral_add (hdφi.const_mul _) (hgi.const_mul _), integral_const_mul, integral_const_mul,
    integral_fderiv_apply_eq_zero hφs hφc, mul_zero, zero_add] at h0
  have := (mul_eq_zero.1 h0).resolve_right hjump.ne
  linarith

/-- If `F = α |⟪y, ν₀⟫|` a.e. on `S ⊆ B̄_1` and `ν_k → ν₀` (unit vectors), then
`∫_S (F − α |⟪y, ν_k⟫|)² → 0` (dominated convergence). -/
theorem tendsto_setIntegral_sq_sub_absProfile {S : Set (Rn n)} (hS : MeasurableSet S)
    [IsFiniteMeasure (volume.restrict S)] (hSb : ∀ y ∈ S, ‖y‖ ≤ 1) {F : Rn n → ℝ}
    (hF : MemLp F 2 (volume.restrict S)) {α : ℝ} {ν : ℕ → Rn n} {ν₀ : Rn n}
    (hν : ∀ k, ‖ν k‖ = 1) (hνt : Tendsto ν atTop (𝓝 ν₀))
    (hFα : ∀ᵐ y ∂(volume.restrict S), F y = α * |⟪y, ν₀⟫|) :
    Tendsto (fun k => ∫ y in S, (F y - α * absProfile (ν k) 0 y) ^ 2) atTop (𝓝 0) := by
  have habs : ∀ k, ∀ y ∈ S, |⟪y, ν k⟫| ≤ 1 := fun k y hy =>
    (abs_real_inner_le_norm _ _).trans (by rw [hν, mul_one]; exact hSb y hy)
  have hprof : ∀ k, MemLp (fun y => α * absProfile (ν k) 0 y) 2 (volume.restrict S) := fun k => by
    refine MemLp.of_bound (continuous_const.mul
      (lipschitzWith_absProfile (hν k)).continuous).aestronglyMeasurable |α| ?_
    filter_upwards [self_mem_ae_restrict hS] with y hy
    simp only [absProfile, sub_zero, Real.norm_eq_abs, abs_mul, abs_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (habs k y hy)
  have := tendsto_integral_of_dominated_convergence (μ := volume.restrict S)
    (F := fun k y => (F y - α * absProfile (ν k) 0 y) ^ 2) (f := fun _ => 0)
    (fun y => 2 * F y ^ 2 + 2 * α ^ 2)
    (fun k => ((hF.sub (hprof k)).integrable_sq).aestronglyMeasurable)
    ((hF.integrable_sq.const_mul 2).add (integrable_const _)) (fun k => ?_) ?_
  · simpa using this
  · filter_upwards [self_mem_ae_restrict hS] with y hy
    have ha := habs k y hy
    have ha0 := abs_nonneg ⟪y, ν k⟫
    have h1 : (F y - α * |⟪y, ν k⟫|) ^ 2 ≤ 2 * F y ^ 2 + 2 * (α * |⟪y, ν k⟫|) ^ 2 := by
      nlinarith [sq_nonneg (F y + α * |⟪y, ν k⟫|)]
    have h2 : (α * |⟪y, ν k⟫|) ^ 2 ≤ α ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg α) (pow_le_one₀ ha0 ha)
    simp only [absProfile, sub_zero, Real.norm_eq_abs, abs_pow, sq_abs]
    linarith
  · filter_upwards [hFα] with y hy
    have h1 : Tendsto (fun k => ⟪y, ν k⟫) atTop (𝓝 ⟪y, ν₀⟫) :=
      ((continuous_const.inner continuous_id).tendsto ν₀).comp hνt
    have h2 := ((h1.abs.const_mul α).const_sub (F y)).pow 2
    have hlim0 : (F y - α * |⟪y, ν₀⟫|) ^ 2 = 0 := by rw [hy]; ring
    rw [hlim0] at h2
    simpa only [absProfile, sub_zero] using h2

/-- If `G = ±α ν₀` a.e. on `{±⟪y, ν₀⟫ > 0} ∩ S`, the hyperplane is null in `S`, and `ν_k → ν₀`
(unit vectors), then `∫_S |G − α ∇|⟪y, ν_k⟫||² → 0` (dominated convergence). -/
theorem tendsto_setIntegral_norm_sub_gradient_absProfile {S : Set (Rn n)}
    [IsFiniteMeasure (volume.restrict S)] {G : Rn n → Rn n}
    (hG : MemLp G 2 (volume.restrict S)) {α : ℝ} {ν : ℕ → Rn n} {ν₀ : Rn n}
    (hν : ∀ k, ‖ν k‖ = 1) (hνt : Tendsto ν atTop (𝓝 ν₀))
    (hGα : ∀ᵐ y ∂(volume.restrict S),
      (0 < ⟪y, ν₀⟫ → G y = α • ν₀) ∧ (⟪y, ν₀⟫ < 0 → G y = -(α • ν₀)))
    (hnull : ∀ᵐ y ∂(volume.restrict S), ⟪y, ν₀⟫ ≠ 0) :
    Tendsto (fun k => ∫ y in S, ‖G y - α • gradient (absProfile (ν k) 0) y‖ ^ 2) atTop
      (𝓝 0) := by
  have hgradle : ∀ k y, ‖α • gradient (absProfile (ν k) 0) y‖ ≤ |α| := fun k y => by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    have := Kernel.norm_gradient_le_of_lipschitz (lipschitzWith_absProfile (hν k)) y
    simpa using this
  have hgprof : ∀ k, MemLp (fun y => α • gradient (absProfile (ν k) 0) y) 2
      (volume.restrict S) := fun k =>
    MemLp.of_bound ((measurable_gradient _).aestronglyMeasurable.const_smul α) |α|
      (Eventually.of_forall fun y => hgradle k y)
  have := tendsto_integral_of_dominated_convergence (μ := volume.restrict S)
    (F := fun k y => ‖G y - α • gradient (absProfile (ν k) 0) y‖ ^ 2) (f := fun _ => 0)
    (fun y => 2 * ‖G y‖ ^ 2 + 2 * α ^ 2)
    (fun k => (MemLp.integrable_norm_sq (hG.sub (hgprof k))).aestronglyMeasurable)
    (((MemLp.integrable_norm_sq hG).const_mul 2).add (integrable_const _)) (fun k => ?_) ?_
  · simpa using this
  · refine Eventually.of_forall fun y => ?_
    set a := ‖G y‖
    set b := ‖α • gradient (absProfile (ν k) 0) y‖
    have h1 : ‖G y - α • gradient (absProfile (ν k) 0) y‖ ≤ a + b := norm_sub_le _ _
    have h4 : ‖G y - α • gradient (absProfile (ν k) 0) y‖ ^ 2 ≤ (a + b) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h5 : b ^ 2 ≤ α ^ 2 := by
      rw [← sq_abs α]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgradle k y) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (a - b)]
  · filter_upwards [hGα, hnull] with y hG' h0
    have h1 : Tendsto (fun k => ⟪y, ν k⟫) atTop (𝓝 ⟪y, ν₀⟫) :=
      ((continuous_const.inner continuous_id).tendsto ν₀).comp hνt
    have h3 : Tendsto (fun k => ‖α • ν₀ - α • ν k‖ ^ 2) atTop (𝓝 0) := by
      have := ((hνt.const_smul α).const_sub (α • ν₀)).norm.pow 2
      simpa using this
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · refine h3.congr' ?_
      filter_upwards [h1.eventually (gt_mem_nhds hneg)] with k hk
      rw [hG'.2 hneg, gradient_absProfile_of_neg hk, ← norm_neg]
      congr 2
      rw [smul_neg]
      abel
    · refine h3.congr' ?_
      filter_upwards [h1.eventually (lt_mem_nhds hpos)] with k hk
      rw [hG'.1 hpos, gradient_absProfile_of_pos hk]

end InnerVariational
