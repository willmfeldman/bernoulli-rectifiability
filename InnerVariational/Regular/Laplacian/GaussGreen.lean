/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Viscosity
public import InnerVariational.Regular.Bump
public import InnerVariational.Singular.Density
public import InnerVariational.Defs.LaplacianMeasure
public import InnerVariational.Main.RieszMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Regular.HarmonicCone
import InnerVariational.Regular.Perimeter
import InnerVariational.Regular.Density
import InnerVariational.Registry.GMT
import InnerVariational.Vendor.Analysis.LocalCompactness
import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.HighestDensity
import InnerVariational.Monotonicity.Density
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar

/-!
# Subharmonic Laplacian measures and Gauss–Green pairs

Auxiliary results for Corollary 8.4 of Kriventsov–Weiss (see `Regular/Laplacian/BlowUp.lean`
for the overview). This file bounds the Laplacian measure of a subharmonic function on balls by
a cutoff argument, and collects facts on Gauss–Green pairs and essential boundaries of sets of
locally finite perimeter: restriction to an open set, half-space densities, the limits of bump
integrals against a Gauss–Green measure at reduced-boundary points, and a Lebesgue-point
identification of the density.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace Laplacian
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

theorem tendsto_two_mul_nhdsGT : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun r hr =>
    Set.mem_Ioi.2 (mul_pos two_pos hr)⟩
  have : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_const.mul continuous_id : Continuous fun r : ℝ => 2 * r).tendsto 0)
  exact this.mono_left nhdsWithin_le_nhds

/-! ### The Laplacian measure of a subharmonic function -/

/-- A continuous function with compact support in `Ω` is integrable for a measure that is finite
on compact subsets of `Ω`. -/
theorem integrable_of_tsupport_subset {Ω : Set (Rn n)} {ρ : Measure (Rn n)}
    (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ∞) {φ : Rn n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hΩ : tsupport φ ⊆ Ω) : Integrable φ ρ := by
  have hK : IsCompact (tsupport φ) := hc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  have hon : IntegrableOn φ (tsupport φ) ρ :=
    IntegrableOn.of_bound (hρ _ hK hΩ) hφ.aestronglyMeasurable M
      ((ae_restrict_iff' (isClosed_tsupport φ).measurableSet).2 (.of_forall hM))
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)).1 hon

/-- `ρ(B_{r/2}(x)) ≤ ∫ u Δψ` with `ψ = bump((· − x)/r)`. -/
theorem measure_ball_le_of_hasDistribLaplacianOn {Ω : Set (Rn n)} {u : Rn n → ℝ}
    {ρ : Measure (Rn n)} (hρ : HasDistribLaplacianOn Ω u ρ) {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hB : closedBall x r ⊆ Ω) :
    ρ (ball x (r / 2)) ≤ ENNReal.ofReal (∫ y, u y * Δ (scaledBump x r) y) := by
  have hψ := isTestFunction_scaledBump hr hB
  rw [hρ.2 _ hψ]
  have hint : Integrable (scaledBump x r) ρ := integrable_of_tsupport_subset hρ.1
    (contDiff_scaledBump x r).continuous (hasCompactSupport_scaledBump hr) hψ.2.2
  rw [ofReal_integral_eq_lintegral_ofReal hint (.of_forall (scaledBump_nonneg x r))]
  calc ρ (ball x (r / 2)) = ∫⁻ y, (ball x (r / 2)).indicator 1 y ∂ρ :=
        (lintegral_indicator_one measurableSet_ball).symm
    _ ≤ _ := lintegral_mono fun y => by
        by_cases hy : y ∈ ball x (r / 2)
        · rw [indicator_of_mem hy, Pi.one_apply, scaledBump_eq_one hr hy, ENNReal.ofReal_one]
        · rw [indicator_of_notMem hy]
          exact bot_le

/-! ### Gauss–Green pairs and essential boundaries -/

/-- Set integrals of functions vanishing off an open `Ω` only see `E ∩ Ω`. -/
theorem setIntegral_inter_eq {Ω E : Set (Rn n)} (hΩ : IsOpen Ω) {f : Rn n → ℝ}
    (hf : ∀ y ∉ Ω, f y = 0) : ∫ y in Ω ∩ E, f y = ∫ y in E, f y := by
  rw [inter_comm, ← setIntegral_indicator hΩ.measurableSet]
  congr 1
  funext y
  by_cases hy : y ∈ Ω
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, hf y hy]

/-- Gauss–Green pairs only see `E ∩ Ω`. -/
theorem isGaussGreenPair_inter_iff {Ω E : Set (Rn n)} (hΩ : IsOpen Ω) {μ : Measure (Rn n)}
    {ν : Rn n → Rn n} : IsGaussGreenPair Ω (Ω ∩ E) μ ν ↔ IsGaussGreenPair Ω E μ ν := by
  have key : ∀ φ, IsSmoothTestField Ω φ →
      ∫ y in Ω ∩ E, divergence φ y = ∫ y in E, divergence φ y := fun φ hφ =>
    setIntegral_inter_eq hΩ fun y hy =>
      divergence_eq_zero_of_notMem_tsupport fun h' => hy (hφ.2.2 h')
  constructor
  · intro h
    refine { h with integral_divergence := fun φ hφ => ?_ }
    rw [← key φ hφ]
    exact h.integral_divergence φ hφ
  · intro h
    refine { h with integral_divergence := fun φ hφ => ?_ }
    rw [key φ hφ]
    exact h.integral_divergence φ hφ

theorem reducedBoundary_inter {Ω E : Set (Rn n)} (hΩ : IsOpen Ω) :
    reducedBoundary Ω (Ω ∩ E) = reducedBoundary Ω E := by
  ext x
  simp only [reducedBoundary, mem_setOf_eq, isGaussGreenPair_inter_iff hΩ]

theorem essentialBoundary_subset_frontier (E : Set (Rn n)) : essentialBoundary E ⊆ frontier E := by
  intro x hx
  rw [frontier, mem_diff]
  constructor
  · by_contra hcl
    obtain ⟨δ, hδ, hδE⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hcl
    apply hx.1
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have : E ∩ ball x r = ∅ := eq_empty_of_forall_notMem fun y hy =>
      hδE (ball_subset_ball hr.2.le hy.2) (subset_closure hy.1)
    rw [this, measure_empty, ENNReal.toReal_zero, zero_div]
  · intro hint
    obtain ⟨δ, hδ, hδE⟩ := Metric.isOpen_iff.1 isOpen_interior x hint
    apply hx.2
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have : E ∩ ball x r = ball x r :=
      inter_eq_right.2 ((ball_subset_ball hr.2.le).trans (hδE.trans interior_subset))
    rw [this, div_self (ENNReal.toReal_pos (measure_ball_pos volume x hr.1).ne'
      measure_ball_lt_top.ne).ne']

/-- Densities only depend on the set up to null sets near the point. -/
theorem hasDensity_congr_of_ae {A B : Set (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (h : ∀ᵐ y ∂(volume.restrict (ball x r)), y ∈ A ↔ y ∈ B) {d : ℝ} :
    HasDensity A x d ↔ HasDensity B x d := by
  have h' := (ae_restrict_iff' measurableSet_ball).1 h
  have hev : (fun s => (volume (A ∩ ball x s)).toReal / (volume (ball x s)).toReal) =ᶠ[𝓝[>] 0]
      (fun s => (volume (B ∩ ball x s)).toReal / (volume (ball x s)).toReal) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    have e : volume (A ∩ ball x s) = volume (B ∩ ball x s) := by
      refine measure_congr ?_
      filter_upwards [h'] with y hy
      refine propext ⟨fun hy' => ⟨(hy (ball_subset_ball hs.2.le hy'.2)).1 hy'.1, hy'.2⟩,
        fun hy' => ⟨(hy (ball_subset_ball hs.2.le hy'.2)).2 hy'.1, hy'.2⟩⟩
    rw [e]
  exact ⟨fun hA => hA.congr' hev, fun hB => hB.congr' hev.symm⟩

/-- **De Giorgi's blow-up theorem** at reduced-boundary points (Evans–Gariepy 5.7.2, Thm 1;
Maggi, Thm 15.5; Federer 4.5.5). Let `(μ, ν)` be a Gauss–Green pair for `E` in `Ω` and let `x ∈ Ω`
be a point of `supp μ` at which the averages of the outer normal `ν` converge to a unit vector `v`
(so `x ∈ ∂*E`). Then the blow-ups `(E − x)/r` converge in `L¹_loc` to the half-space
`{⟪z, v⟫ < 0}`: `{y : ⟪y − x, v⟫ < 0} △ E` has density `0` at `x`. Proved in gmt-foundations
(`Registry.hasDensity_symmDiff_halfSpace`). The sign convention matches `IsGaussGreenPair`
(`∫_E div φ = ∫ ⟪φ, ν⟫ dμ`, so `ν` is the outer normal), as in Maggi's `H_x = {⟪y, ν_E(x)⟫ < 0}`. -/
theorem hasDensity_symmDiff_halfSpace (hn : 2 ≤ n) {Ω E : Set (Rn n)} (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν)
    {x : Rn n} (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    HasDensity (symmDiff E {y | ⟪y - x, v⟫ < 0}) x 0 :=
  Registry.hasDensity_symmDiff_halfSpace hn hΩ hE h hx hpos hv hlim

/-- Rescaling the half-space flux: `∫_{⟪y − x, v⟫ < 0} ⟪∇ψ_r, v⟫ = r^{n-1} halfSpaceFlux v`. -/
theorem setIntegral_halfSpace_inner_gradient_scaledBump [NeZero n] (x v : Rn n) {r : ℝ}
    (hr : 0 < r) :
    ∫ y in {y | ⟪y - x, v⟫ < 0}, ⟪gradient (scaledBump x r) y, v⟫ =
      r ^ (n - 1) * halfSpaceFlux v := by
  have hH : MeasurableSet {z : Rn n | ⟪z, v⟫ < 0} := (isOpen_halfSpace_neg v).measurableSet
  have hHx : MeasurableSet {y : Rn n | ⟪y - x, v⟫ < 0} :=
    (isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const)
      continuous_const).measurableSet
  have hiff : ∀ y, ⟪r⁻¹ • (y - x), v⟫ < 0 ↔ ⟪y - x, v⟫ < 0 := fun y => by
    rw [real_inner_smul_left]
    constructor
    · intro h'
      by_contra hc
      exact (not_lt.2 (mul_nonneg (inv_nonneg.2 hr.le) (not_lt.1 hc))) h'
    · exact fun h' => mul_neg_of_pos_of_neg (inv_pos.2 hr) h'
  have e : ∀ y, {y : Rn n | ⟪y - x, v⟫ < 0}.indicator
      (fun y => ⟪gradient (scaledBump x r) y, v⟫) y =
      r⁻¹ * {z : Rn n | ⟪z, v⟫ < 0}.indicator (fun z => ⟪gradient bump z, v⟫)
        (r⁻¹ • (y - x)) := fun y => by
    by_cases hy : ⟪y - x, v⟫ < 0
    · rw [indicator_of_mem (show y ∈ {y : Rn n | ⟪y - x, v⟫ < 0} from hy),
        indicator_of_mem (show r⁻¹ • (y - x) ∈ {z : Rn n | ⟪z, v⟫ < 0} from (hiff y).2 hy),
        gradient_scaledBump, real_inner_smul_left]
    · rw [indicator_of_notMem (show y ∉ {y : Rn n | ⟪y - x, v⟫ < 0} from hy),
        indicator_of_notMem (show r⁻¹ • (y - x) ∉ {z : Rn n | ⟪z, v⟫ < 0} from
          fun h' => hy ((hiff y).1 h')), mul_zero]
  rw [halfSpaceFlux, ← integral_indicator hHx, ← integral_indicator hH, integral_congr_ae
    (.of_forall e), integral_const_mul, integral_comp_rescale _ x hr]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos
    (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  rw [Nat.add_sub_cancel, pow_succ', ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- The Lebesgue part of the blow-up: if `E` blows up to `{⟪z, v⟫ < 0}` at `x`, then
`r^{1-n} ∫_E ⟪∇ψ_r, v⟫ → halfSpaceFlux v`. -/
theorem tendsto_setIntegral_inner_gradient_scaledBump [NeZero n] {E : Set (Rn n)}
    (hE : MeasurableSet E) {x v : Rn n}
    (hDG : HasDensity (symmDiff E {y | ⟪y - x, v⟫ < 0}) x 0) :
    Tendsto (fun r => (r ^ (n - 1))⁻¹ * ∫ y in E, ⟪gradient (scaledBump x r) y, v⟫)
      (𝓝[>] 0) (𝓝 (halfSpaceFlux v)) := by
  set Hx : Set (Rn n) := {y | ⟪y - x, v⟫ < 0} with hHxdef
  have hHx : MeasurableSet Hx :=
    (isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const)
      continuous_const).measurableSet
  set A : Set (Rn n) := symmDiff E Hx with hAdef
  have hA : MeasurableSet A := hE.symmDiff hHx
  obtain ⟨M, hM⟩ := exists_norm_gradient_bump_le (n := n)
  set M' := M * ‖v‖ with hM'def
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM'0 : 0 ≤ M' := mul_nonneg hM0 (norm_nonneg _)
  set B := unitBallVolume n with hBdef
  set q : ℝ → ℝ := fun s => (volume (A ∩ ball x s)).toReal / (volume (ball x s)).toReal
    with hqdef
  -- the error term
  set D : ℝ → ℝ := fun r => (∫ y in E, ⟪gradient (scaledBump x r) y, v⟫) -
    ∫ y in Hx, ⟪gradient (scaledBump x r) y, v⟫ with hDdef
  have hDbd : ∀ r, 0 < r → |(r ^ (n - 1))⁻¹ * D r| ≤ M' * 2 ^ n * B * q (2 * r) := by
    intro r hr
    set g : Rn n → ℝ := fun y => ⟪gradient (scaledBump x r) y, v⟫ with hgdef
    have hgc : Continuous g := (continuous_gradient_scaledBump x r).inner continuous_const
    have hgi : Integrable g := hgc.integrable_of_hasCompactSupport
      ((hasCompactSupport_gradient_scaledBump x hr).mono fun y hy h0 => hy (by
        simp only [hgdef, h0, inner_zero_left]))
    have hgb : ∀ y, |g y| ≤ r⁻¹ * M' := fun y => by
      simp only [hgdef]
      rw [gradient_scaledBump, real_inner_smul_left, abs_mul,
        abs_of_pos (inv_pos.2 hr), hM'def]
      exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))) (inv_nonneg.2 hr.le)
    have hg0 : ∀ y ∉ closedBall x r, g y = 0 := fun y hy => by
      simp only [hgdef]
      rw [Kernel.gradient_eq_zero_of_notMem_tsupport
        (fun h' => hy (tsupport_scaledBump_subset hr h')), inner_zero_left]
    have hpt : ∀ y, |E.indicator g y - Hx.indicator g y| ≤
        (A ∩ closedBall x r).indicator (fun _ => r⁻¹ * M') y := fun y => by
      have hc0 : 0 ≤ r⁻¹ * M' := mul_nonneg (inv_nonneg.2 hr.le) hM'0
      by_cases hyA : y ∈ A
      · by_cases hyB : y ∈ closedBall x r
        · rw [indicator_of_mem (show y ∈ A ∩ closedBall x r from ⟨hyA, hyB⟩)]
          rw [hAdef, Set.mem_symmDiff] at hyA
          rcases hyA with ⟨hyE, hyH⟩ | ⟨hyH, hyE⟩
          · rw [indicator_of_mem hyE, indicator_of_notMem hyH, sub_zero]; exact hgb y
          · rw [indicator_of_mem hyH, indicator_of_notMem hyE, zero_sub, abs_neg]; exact hgb y
        · rw [indicator_of_notMem (show y ∉ A ∩ closedBall x r from fun h' => hyB h'.2)]
          by_cases hyE : y ∈ E <;> by_cases hyH : y ∈ Hx <;>
            simp [indicator, hyE, hyH, hg0 y hyB]
      · rw [indicator_of_notMem (show y ∉ A ∩ closedBall x r from fun h' => hyA h'.1)]
        rw [hAdef, Set.mem_symmDiff] at hyA
        push Not at hyA
        by_cases hyE : y ∈ E
        · rw [indicator_of_mem hyE, indicator_of_mem (hyA.1 hyE), sub_self, abs_zero]
        · have hyH : y ∉ Hx := fun h' => hyE (hyA.2 h')
          rw [indicator_of_notMem hyE, indicator_of_notMem hyH, sub_self, abs_zero]
    have hDeq : D r = ∫ y, (E.indicator g y - Hx.indicator g y) := by
      rw [hDdef, integral_sub (hgi.indicator hE) (hgi.indicator hHx), integral_indicator hE,
        integral_indicator hHx]
    have hAB : MeasurableSet (A ∩ closedBall x r) := hA.inter isClosed_closedBall.measurableSet
    have h1 : |D r| ≤ r⁻¹ * M' * (volume (A ∩ closedBall x r)).toReal := by
      rw [hDeq, ← Real.norm_eq_abs]
      have hInt : Integrable ((A ∩ closedBall x r).indicator (fun _ => r⁻¹ * M')) :=
        (integrable_indicator_iff hAB).2 (integrableOn_const
          ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne)
      have := norm_integral_le_of_norm_le hInt
        (.of_forall fun y => by rw [Real.norm_eq_abs]; exact hpt y)
      rwa [integral_indicator_const _ hAB, smul_eq_mul, measureReal_def, mul_comm] at this
    have h2 : (volume (A ∩ closedBall x r)).toReal ≤ q (2 * r) * ((2 * r) ^ n * B) := by
      have h2r : (0 : ℝ) < 2 * r := by positivity
      have hBpos := unitBallVolume_pos n
      have hB2 : (volume (ball x (2 * r))).toReal = (2 * r) ^ n * B := volume_ball_toReal x h2r
      have hne : (volume (ball x (2 * r))).toReal ≠ 0 := by rw [hB2]; positivity
      calc (volume (A ∩ closedBall x r)).toReal ≤ (volume (A ∩ ball x (2 * r))).toReal :=
            ENNReal.toReal_mono ((measure_mono inter_subset_right).trans_lt
              measure_ball_lt_top).ne
              (measure_mono (inter_subset_inter_right _ (closedBall_subset_ball (by linarith))))
        _ = q (2 * r) * ((2 * r) ^ n * B) := by
            rw [← hB2]
            simp only [hqdef]
            field_simp
    have hq0 : 0 ≤ q (2 * r) := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hrn : 0 < r ^ (n - 1) := pow_pos hr _
    rw [abs_mul, abs_of_pos (inv_pos.2 hrn)]
    calc (r ^ (n - 1))⁻¹ * |D r|
        ≤ (r ^ (n - 1))⁻¹ * (r⁻¹ * M' * (q (2 * r) * ((2 * r) ^ n * B))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2
            (mul_nonneg (inv_nonneg.2 hr.le) hM'0))) (inv_nonneg.2 hrn.le)
      _ = M' * 2 ^ n * B * q (2 * r) := by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos
            (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
          rw [Nat.add_sub_cancel, mul_pow]
          field_simp
          ring
  -- `q(2r) → 0`
  have h2 := tendsto_two_mul_nhdsGT
  have hq : Tendsto (fun r => q (2 * r)) (𝓝[>] 0) (𝓝 0) := hDG.comp h2
  have hD0 : Tendsto (fun r => (r ^ (n - 1))⁻¹ * D r) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hq.const_mul (M' * 2 ^ n * B))
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Real.norm_eq_abs]
    exact hDbd r hr
  have hD1 := hD0.const_add (halfSpaceFlux v)
  rw [add_zero] at hD1
  refine hD1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have := setIntegral_halfSpace_inner_gradient_scaledBump x v (n := n) hr
  rw [← hHxdef] at this
  simp only [hDdef]
  rw [mul_sub, this, ← mul_assoc, inv_mul_cancel₀ (pow_pos hr _).ne', one_mul]
  ring

/-- **The perimeter side of the blow-up.** For a Gauss–Green pair `(μ, ν)` of `E` in `Ω`, at a
point `x` where the averages of `ν` converge to the unit vector `v`, `E` blows up to
`{⟪z, v⟫ < 0}`, and `μ(B_r(x)) ≤ K r^{n-1}` for small `r`:
`r^{1-n} ∫ bump((· − x)/r) dμ → halfSpaceFlux v`. -/
theorem tendsto_integral_scaledBump_of_isGaussGreenPair [NeZero n] {Ω E : Set (Rn n)}
    (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) {μ : Measure (Rn n)} {ν : Rn n → Rn n} (hpair : IsGaussGreenPair Ω E μ ν)
    {x : Rn n} (hx : x ∈ Ω) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    (hDG : HasDensity (symmDiff E {y | ⟪y - x, v⟫ < 0}) x 0) {K : ℝ}
    (hK : ∀ᶠ r in 𝓝[>] 0, μ (ball x r) ≤ ENNReal.ofReal (K * r ^ (n - 1))) :
    Tendsto (fun r => (r ^ (n - 1))⁻¹ * ∫ y, scaledBump x r y ∂μ) (𝓝[>] 0)
      (𝓝 (halfSpaceFlux v)) := by
  obtain ⟨R₀, hR₀, hR₀Ω⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx)
  have hνae : ∀ᵐ y ∂μ, |⟪v, ν y⟫| ≤ 1 := hpair.norm_normal.mono fun y hy => by
    have := abs_real_inner_le_norm v (ν y)
    rwa [hv, hy, one_mul] at this
  have hνm : Measurable fun y => ⟪v, ν y⟫ := measurable_const.inner hpair.measurable_normal
  -- integrability of bounded functions supported in a ball `B̄_s(x) ⊆ Ω`
  have hint : ∀ s, s ≤ R₀ → ∀ g : Rn n → ℝ, AEStronglyMeasurable g μ →
      (∀ᵐ y ∂μ, |g y| ≤ 1) → (∀ y ∉ closedBall x s, g y = 0) → Integrable g μ := by
    intro s hs g hg hgb hg0
    have hfin : μ (closedBall x s) < ∞ := hpair.lt_top_of_isCompact _ (isCompact_closedBall x s)
      ((closedBall_subset_closedBall hs).trans hR₀Ω)
    have hon : IntegrableOn g (closedBall x s) μ := IntegrableOn.of_bound hfin hg.restrict 1
      (ae_restrict_of_ae (hgb.mono fun y hy => by rwa [Real.norm_eq_abs]))
    exact (integrableOn_iff_integrable_of_support_subset fun y hy => by
      by_contra h'; exact hy (hg0 y h')).1 hon
  set J : ℝ → ℝ := fun r => ∫ y, scaledBump x r y * ⟪v, ν y⟫ ∂μ with hJdef
  set T : ℝ → ℝ := fun r => ∫ y, scaledBump x r y ∂μ - J r with hTdef
  set m : ℝ → ℝ := fun s => (μ (ball x s)).toReal with hmdef
  set a : ℝ → Rn n := fun s => (μ (ball x s)).toReal⁻¹ • ∫ y in ball x s, ν y ∂μ with hadef
  -- (1) `J(r) = ∫_E ⟪∇ψ_r, v⟫`
  have hJ : ∀ r, 0 < r → r ≤ R₀ → J r = ∫ y in E, ⟪gradient (scaledBump x r) y, v⟫ := by
    intro r hr hrR
    have hφ : IsSmoothTestField Ω (fun y => scaledBump x r y • v) :=
      ⟨(contDiff_scaledBump x r).smul contDiff_const,
        (hasCompactSupport_scaledBump hr).smul_right,
        (tsupport_smul_subset_left _ _).trans ((tsupport_scaledBump_subset hr).trans
          ((closedBall_subset_closedBall hrR).trans hR₀Ω))⟩
    have hGG := hpair.integral_divergence _ hφ
    simp only [divergence_smul_const ((contDiff_scaledBump x r).differentiable (by simp)),
      real_inner_smul_left] at hGG
    rw [hJdef]
    simp only
    rw [← hGG]
    refine setIntegral_congr_fun hE fun y _ => ?_
    rw [Kernel.inner_gradient_left]
  -- (2) `r^{1-n} J(r) → flux`
  have h2 := tendsto_setIntegral_inner_gradient_scaledBump hE hDG (n := n)
  have hJlim : Tendsto (fun r => (r ^ (n - 1))⁻¹ * J r) (𝓝[>] 0) (𝓝 (halfSpaceFlux v)) := by
    refine h2.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR₀] with r hr
    rw [hJ r hr.1 hr.2.le]
  -- (3) `0 ≤ T(r) ≤ m(2r) (1 − ⟪v, a(2r)⟫)`
  have hT : ∀ r, 0 < r → 2 * r ≤ R₀ → |T r| ≤ m (2 * r) * |1 - ⟪v, a (2 * r)⟫| := by
    intro r hr hrR
    have hrR' : r ≤ R₀ := by linarith
    have hψm : AEStronglyMeasurable (scaledBump x r) μ :=
      (contDiff_scaledBump x r).continuous.aestronglyMeasurable
    have hψ0 : ∀ y ∉ closedBall x r, scaledBump x r y = 0 := fun y hy =>
      scaledBump_eq_zero hr fun h' => hy (ball_subset_closedBall h')
    have hi1 : Integrable (scaledBump x r) μ := hint r hrR' _ hψm
      (.of_forall fun y => by
        rw [abs_of_nonneg (scaledBump_nonneg x r y)]; exact scaledBump_le_one x r y) hψ0
    have hi2 : Integrable (fun y => scaledBump x r y * ⟪v, ν y⟫) μ := hint r hrR' _
      (hψm.mul hνm.aestronglyMeasurable)
      (hνae.mono fun y hy => by
        rw [abs_mul, abs_of_nonneg (scaledBump_nonneg x r y)]
        exact mul_le_one₀ (scaledBump_le_one x r y) (abs_nonneg _) hy)
      fun y hy => by rw [hψ0 y hy, zero_mul]
    have hB2 : ball x (2 * r) ⊆ closedBall x R₀ :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall hrR)
    have hfin2 : μ (ball x (2 * r)) < ∞ :=
      (measure_mono hB2).trans_lt (hpair.lt_top_of_isCompact _ (isCompact_closedBall x R₀) hR₀Ω)
    have hνi : IntegrableOn ν (ball x (2 * r)) μ := IntegrableOn.of_bound hfin2
      hpair.measurable_normal.aestronglyMeasurable 1
      (ae_restrict_of_ae (hpair.norm_normal.mono fun y hy => hy.le))
    have hTeq : T r = ∫ y, scaledBump x r y * (1 - ⟪v, ν y⟫) ∂μ := by
      rw [hTdef, hJdef]
      simp only
      rw [← integral_sub hi1 hi2]
      congr 1
      funext y
      ring
    have hT0 : 0 ≤ T r := by
      rw [hTeq]
      exact integral_nonneg_of_ae (hνae.mono fun y hy => mul_nonneg (scaledBump_nonneg x r y)
        (by linarith [le_abs_self ⟪v, ν y⟫]))
    have hTle : T r ≤ ∫ y in ball x (2 * r), (1 - ⟪v, ν y⟫) ∂μ := by
      rw [hTeq, ← integral_indicator measurableSet_ball]
      refine integral_mono_ae ((hi1.sub hi2).congr
        (.of_forall fun y => by simp only [Pi.sub_apply]; ring))
        ((integrable_indicator_iff measurableSet_ball).2
          ((integrableOn_const (C := (1 : ℝ)) hfin2.ne).sub (hνi.const_inner v))) ?_
      filter_upwards [hνae] with y hy
      have h1 : 0 ≤ 1 - ⟪v, ν y⟫ := by linarith [le_abs_self ⟪v, ν y⟫]
      by_cases hyB : y ∈ ball x (2 * r)
      · rw [indicator_of_mem hyB]
        exact mul_le_of_le_one_left h1 (scaledBump_le_one x r y)
      · rw [indicator_of_notMem hyB, scaledBump_eq_zero hr fun h' => hyB
          (ball_subset_ball (by linarith) h'), zero_mul]
    have hW : ∫ y in ball x (2 * r), (1 - ⟪v, ν y⟫) ∂μ = m (2 * r) * (1 - ⟪v, a (2 * r)⟫) := by
      rw [integral_sub (integrableOn_const (C := (1 : ℝ)) hfin2.ne) (hνi.const_inner v),
        setIntegral_const,
        smul_eq_mul, mul_one, integral_inner hνi v]
      simp only [hmdef, hadef]
      by_cases hm0 : (μ (ball x (2 * r))).toReal = 0
      · have hμ0 : μ (ball x (2 * r)) = 0 := by
          rcases (ENNReal.toReal_eq_zero_iff _).1 hm0 with h0 | h0
          · exact h0
          · exact absurd h0 hfin2.ne
        rw [Measure.restrict_eq_zero.2 hμ0, integral_zero_measure, inner_zero_right, hm0,
          measureReal_def, hμ0, ENNReal.toReal_zero]
        ring
      · rw [real_inner_smul_right, measureReal_def]
        field_simp
    rw [abs_of_nonneg hT0]
    calc T r ≤ m (2 * r) * (1 - ⟪v, a (2 * r)⟫) := hTle.trans_eq hW
      _ ≤ m (2 * r) * |1 - ⟪v, a (2 * r)⟫| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) ENNReal.toReal_nonneg
  -- (4) `r^{1-n} T(r) → 0`
  have h2r := tendsto_two_mul_nhdsGT
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have ha : Tendsto (fun r => |1 - ⟪v, a (2 * r)⟫|) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun w : Rn n => |1 - ⟪v, w⟫| :=
      (continuous_const.sub (continuous_const.inner continuous_id)).abs
    have := (hc.tendsto v).comp (hlim.comp h2r)
    rw [hvv, sub_self, abs_zero] at this
    exact this
  have hK' : ∀ᶠ r in 𝓝[>] 0, m (2 * r) ≤ |K| * 2 ^ (n - 1) * r ^ (n - 1) := by
    filter_upwards [h2r.eventually hK, self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    calc m (2 * r) ≤ (ENNReal.ofReal (K * (2 * r) ^ (n - 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
      _ = max (K * (2 * r) ^ (n - 1)) 0 := ENNReal.toReal_ofReal'
      _ ≤ |K| * (2 * r) ^ (n - 1) := max_le (mul_le_mul_of_nonneg_right (le_abs_self K)
          (by positivity)) (by positivity)
      _ = |K| * 2 ^ (n - 1) * r ^ (n - 1) := by rw [mul_pow]; ring
  have hTlim : Tendsto (fun r => (r ^ (n - 1))⁻¹ * T r) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using ha.const_mul (|K| * 2 ^ (n - 1)))
    filter_upwards [hK', self_mem_nhdsWithin, Ioo_mem_nhdsGT (half_pos hR₀)] with r hr hr0 hrR
    have hr0' : (0 : ℝ) < r := hr0
    have hrn : 0 < r ^ (n - 1) := pow_pos hr0' _
    rw [norm_mul, norm_inv, Real.norm_of_nonneg hrn.le, Real.norm_eq_abs, inv_mul_le_iff₀ hrn]
    calc |T r| ≤ m (2 * r) * |1 - ⟪v, a (2 * r)⟫| := hT r hr0' (by linarith [hrR.2])
      _ ≤ (|K| * 2 ^ (n - 1) * r ^ (n - 1)) * |1 - ⟪v, a (2 * r)⟫| :=
          mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      _ = r ^ (n - 1) * (|K| * 2 ^ (n - 1) * |1 - ⟪v, a (2 * r)⟫|) := by ring
  have := hJlim.add hTlim
  rw [add_zero] at this
  refine this.congr fun r => ?_
  simp only [hTdef]
  ring

/-- A measure that vanishes off an open set `Ω` and is finite on its compact subsets is
`σ`-finite. -/
theorem sigmaFinite_of_isCompact {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {μ : Measure (Rn n)}
    (h0 : μ Ωᶜ = 0) (hK : ∀ K, IsCompact K → K ⊆ Ω → μ K < ∞) : SigmaFinite μ :=
  Measure.FiniteSpanningSetsIn.sigmaFinite (C := univ)
    { set := fun j => Vendor.Analysis.exhaust Ω j ∪ Ωᶜ
      set_mem := fun _ => mem_univ _
      finite := fun j => (measure_union_le _ _).trans_lt (by
        rw [h0, add_zero]
        exact hK _ (Vendor.Analysis.isCompact_exhaust Ω j) (Vendor.Analysis.exhaust_subset Ω j))
      spanning := eq_univ_of_forall fun y => by
        by_cases hy : y ∈ Ω
        · obtain ⟨j, hj⟩ := Vendor.Analysis.exists_subset_exhaust hΩ isCompact_singleton
            (singleton_subset_iff.2 hy)
          exact mem_iUnion.2 ⟨j, Or.inl (hj rfl)⟩
        · exact mem_iUnion.2 ⟨0, Or.inr hy⟩ }

/-- **Densities at Lebesgue points.** Let `x` be a Lebesgue point of `f` for `σ` (along closed
balls), with `σ(B̄_r(x)) ≤ K r^{n-1}` for small `r`. If along `r_k → 0+` both
`r_k^{1-n} ∫ ψ_{r_k} f dσ` and `r_k^{1-n} ∫ ψ_{r_k} dσ` tend to the same `c > 0`, then
`f(x) = 1`. -/
theorem eq_one_of_tendsto_integral_scaledBump {σ : Measure (Rn n)} {f : Rn n → ℝ} {x : Rn n}
    {R K c : ℝ} (hR : 0 < R) (hfin : σ (closedBall x R) < ∞)
    (hfi : IntegrableOn f (closedBall x R) σ)
    (hK : ∀ r ∈ Ioo 0 R, σ (closedBall x r) ≤ ENNReal.ofReal (K * r ^ (n - 1)))
    (hleb : Tendsto (fun r => (∫⁻ y in closedBall x r, ‖f y - f x‖ₑ ∂σ) / σ (closedBall x r))
      (𝓝[>] 0) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) (hc : 0 < c)
    (h1 : Tendsto (fun k => (r k ^ (n - 1))⁻¹ * ∫ y, scaledBump x (r k) y * f y ∂σ) atTop (𝓝 c))
    (h2 : Tendsto (fun k => (r k ^ (n - 1))⁻¹ * ∫ y, scaledBump x (r k) y ∂σ) atTop (𝓝 c)) :
    f x = 1 := by
  set g : ℝ → ℝ := fun s => ∫ y, scaledBump x s y * f y ∂σ - f x * ∫ y, scaledBump x s y ∂σ
    with hgdef
  set q : ℝ → ℝ≥0∞ := fun s =>
    (∫⁻ y in closedBall x s, ‖f y - f x‖ₑ ∂σ) / σ (closedBall x s) with hqdef
  -- the key estimate `|g(s)| ≤ |K| q(s) s^{n-1}` for `0 < s < R`
  have hest : ∀ s ∈ Ioo 0 R, |g s| ≤ |K| * (q s).toReal * s ^ (n - 1) := by
    intro s hs
    have hsR : closedBall x s ⊆ closedBall x R := closedBall_subset_closedBall hs.2.le
    have hfin_s : σ (closedBall x s) < ∞ := (measure_mono hsR).trans_lt hfin
    have hψc : ContinuousOn (scaledBump x s) (closedBall x s) :=
      (contDiff_scaledBump x s).continuous.continuousOn
    have hfis : IntegrableOn f (closedBall x s) σ := hfi.mono_set hsR
    have hψi : IntegrableOn (scaledBump x s) (closedBall x s) σ :=
      IntegrableOn.of_bound hfin_s (contDiff_scaledBump x s).continuous.aestronglyMeasurable 1
        (.of_forall fun y => by
          rw [Real.norm_of_nonneg (scaledBump_nonneg x s y)]; exact scaledBump_le_one x s y)
    have hψfi : IntegrableOn (fun y => scaledBump x s y * f y) (closedBall x s) σ :=
      hfis.continuousOn_mul hψc (isCompact_closedBall x s)
    have hzero : ∀ y ∉ closedBall x s, scaledBump x s y = 0 := fun y hy =>
      scaledBump_eq_zero hs.1 fun h' => hy (ball_subset_closedBall h')
    have e1 : ∫ y, scaledBump x s y * f y ∂σ = ∫ y in closedBall x s, scaledBump x s y * f y ∂σ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        rw [hzero y hy, zero_mul]).symm
    have e2 : ∫ y, scaledBump x s y ∂σ = ∫ y in closedBall x s, scaledBump x s y ∂σ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hzero y hy).symm
    have e3 : g s = ∫ y in closedBall x s, scaledBump x s y * (f y - f x) ∂σ := by
      simp only [hgdef]
      rw [e1, e2, ← integral_const_mul, ← integral_sub hψfi (hψi.const_mul _)]
      congr 1
      funext y
      ring
    have hdi : IntegrableOn (fun y => f y - f x) (closedBall x s) σ :=
      hfis.sub (integrableOn_const hfin_s.ne)
    have e4 : ∫ y in closedBall x s, ‖f y - f x‖ ∂σ =
        (∫⁻ y in closedBall x s, ‖f y - f x‖ₑ ∂σ).toReal :=
      integral_norm_eq_lintegral_enorm hdi.aestronglyMeasurable
    have hle1 : |g s| ≤ (∫⁻ y in closedBall x s, ‖f y - f x‖ₑ ∂σ).toReal := by
      rw [e3, ← e4, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hdi.norm (.of_forall fun y => ?_)
      rw [norm_mul, Real.norm_of_nonneg (scaledBump_nonneg x s y)]
      exact mul_le_of_le_one_left (norm_nonneg _) (scaledBump_le_one x s y)
    have hle2 : (∫⁻ y in closedBall x s, ‖f y - f x‖ₑ ∂σ).toReal ≤
        (q s).toReal * (σ (closedBall x s)).toReal := by
      by_cases h0 : σ (closedBall x s) = 0
      · rw [setLIntegral_measure_zero _ _ h0, ENNReal.toReal_zero]
        exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      · rw [← ENNReal.toReal_mul, hqdef, ENNReal.div_mul_cancel h0 hfin_s.ne]
    have hle3 : (σ (closedBall x s)).toReal ≤ |K| * s ^ (n - 1) := by
      have := (hK s hs).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hs.1.le _)))
      rw [← ENNReal.ofReal_toReal hfin_s.ne] at this
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (abs_nonneg K) (pow_nonneg hs.1.le _))).1 this
    calc |g s| ≤ (q s).toReal * (σ (closedBall x s)).toReal := hle1.trans hle2
      _ ≤ (q s).toReal * (|K| * s ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left hle3 ENNReal.toReal_nonneg
      _ = |K| * (q s).toReal * s ^ (n - 1) := by ring
  -- hence `s^{1-n} g(s) → 0`
  have hq : Tendsto (fun s => (q s).toReal) (𝓝[>] 0) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hleb
    rwa [ENNReal.toReal_zero] at this
  have hg0 : Tendsto (fun s => (s ^ (n - 1))⁻¹ * g s) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun s => |K| * (q s).toReal) (𝓝[>] 0) (𝓝 0) := by
      simpa using hq.const_mul |K|
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT hR] with s hs
    have hsn : 0 < s ^ (n - 1) := pow_pos hs.1 _
    rw [norm_mul, norm_inv, Real.norm_of_nonneg hsn.le, Real.norm_eq_abs,
      inv_mul_le_iff₀ hsn]
    calc |g s| ≤ |K| * (q s).toReal * s ^ (n - 1) := hest s hs
      _ = s ^ (n - 1) * (|K| * (q s).toReal) := by ring
  have hrk : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
  have hlim1 := hg0.comp hrk
  have hlim2 : Tendsto (fun k => (r k ^ (n - 1))⁻¹ * g (r k)) atTop (𝓝 (c - f x * c)) := by
    refine (h1.sub (h2.const_mul (f x))).congr fun k => ?_
    simp only [hgdef]
    ring
  have hc0 : c - f x * c = 0 := tendsto_nhds_unique hlim2 hlim1
  have : c * (1 - f x) = 0 := by linear_combination hc0
  linarith [(mul_eq_zero.1 this).resolve_left hc.ne']

/-- Strong `L²(B̄_1)` convergence of uniformly bounded gradients gives
`∫ ⟪∇w_k, ∇bump⟫ → ∫ ⟪∇w₀, ∇bump⟫`. -/
theorem tendsto_integral_inner_gradient_bump {w : ℕ → Rn n → ℝ} {w₀ : Rn n → ℝ} {L : ℝ}
    (hwb : ∀ k, ∀ y ∈ closedBall (0 : Rn n) 1, ‖gradient (w k) y‖ ≤ L)
    (hw0b : ∀ y ∈ closedBall (0 : Rn n) 1, ‖gradient w₀ y‖ ≤ L)
    (hlim : Tendsto (fun k => ∫ y in closedBall (0 : Rn n) 1,
      ‖gradient (w k) y - gradient w₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ z, ⟪gradient (w k) z, gradient bump z⟫) atTop
      (𝓝 (∫ z, ⟪gradient w₀ z, gradient bump z⟫)) := by
  set K := closedBall (0 : Rn n) 1 with hKdef
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hL1 := tendsto_setIntegral_norm_sub_of_sq hK.measurableSet hK.measure_lt_top
    (fun k => measurable_gradient (w k)) (measurable_gradient w₀) hwb hw0b hlim
  obtain ⟨M, hM⟩ := exists_norm_gradient_bump_le (n := n)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb0 : ∀ z ∉ K, gradient (bump (n := n)) z = 0 := fun z hz => by
    rw [hKdef, mem_closedBall_zero_iff, not_le] at hz
    exact gradient_bump_eq_zero_of_one_lt_norm hz
  have hint : ∀ g : Rn n → ℝ, (∀ y ∈ K, ‖gradient g y‖ ≤ L) →
      Integrable fun z => ⟪gradient g z, gradient bump z⟫ := fun g hg =>
    Kernel.integrable_of_bound_of_isCompact hK
      ((measurable_gradient g).inner continuous_gradient_bump.measurable).aestronglyMeasurable
      (M := L * M) (fun y hy => (norm_inner_le_norm _ _).trans
        (mul_le_mul (hg y hy) (hM y) (norm_nonneg _) ((norm_nonneg _).trans (hg y hy))))
      (fun y hy => by rw [hb0 y hy, inner_zero_right])
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) (by simpa using hL1.const_mul M)
  rw [← integral_sub (hint _ (hwb k)) (hint _ hw0b),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun y hy => by
      rw [hb0 y hy, inner_zero_right, inner_zero_right, sub_zero]),
    ← integral_const_mul]
  have hnm : IntegrableOn (fun y => ‖gradient (w k) y - gradient w₀ y‖) K :=
    IntegrableOn.of_bound hK.measure_lt_top
      ((measurable_gradient _).sub (measurable_gradient _)).norm.aestronglyMeasurable (2 * L)
      ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by linarith [hwb k y hy, hw0b y hy])))
  refine norm_integral_le_of_norm_le (hnm.const_mul M) (.of_forall fun y => ?_)
  rw [← inner_sub_left, Real.norm_eq_abs, mul_comm]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _))

/-- `|∫ g₁ div ξ − ∫ g₂ div ξ| ≤ n D ∫_{B_1} |g₁ − g₂|` for `|g_i| ≤ 1` and a `D`-Lipschitz test
field `ξ` supported in `B_1`. -/
theorem abs_integral_mul_divergence_sub_le {g₁ g₂ : Rn n → ℝ} (hg₁ : Measurable g₁)
    (hg₂ : Measurable g₂) (hb₁ : ∀ y, |g₁ y| ≤ 1) (hb₂ : ∀ y, |g₂ y| ≤ 1) {ξ : Rn n → Rn n}
    {D : ℝ≥0} (hD : LipschitzWith D ξ) (hc : HasCompactSupport ξ)
    (hB : tsupport ξ ⊆ ball (0 : Rn n) 1) :
    |(∫ y, g₁ y * divergence ξ y) - ∫ y, g₂ y * divergence ξ y| ≤
      n * D * ∫ y in ball (0 : Rn n) 1, |g₁ y - g₂ y| := by
  have hdi : Integrable (divergence ξ) := Kernel.integrable_divergence hD hc
  have hi : ∀ g : Rn n → ℝ, Measurable g → (∀ y, |g y| ≤ 1) →
      Integrable fun y => g y * divergence ξ y := fun g hg hb =>
    hdi.bdd_mul hg.aestronglyMeasurable (c := 1) (.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  rw [← integral_sub (hi g₁ hg₁ hb₁) (hi g₂ hg₂ hb₂),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Rn n) 1) (fun y hy => by
      rw [divergence_eq_zero_of_notMem_tsupport fun h' => hy (hB h'), mul_zero, mul_zero,
        sub_zero]),
    ← integral_const_mul, ← Real.norm_eq_abs]
  have hon : IntegrableOn (fun y => |g₁ y - g₂ y|) (ball (0 : Rn n) 1) :=
    IntegrableOn.of_bound measure_ball_lt_top (hg₁.sub hg₂).abs.aestronglyMeasurable 2
      (.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (by linarith [hb₁ y, hb₂ y]))
  refine norm_integral_le_of_norm_le (hon.const_mul _) (.of_forall fun y => ?_)
  rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (Kernel.abs_divergence_le hD y) (abs_nonneg _)

end Regular

end InnerVariational
