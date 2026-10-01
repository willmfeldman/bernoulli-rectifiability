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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
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
public import InnerVariational.Regular.Laplacian.GaussGreen

/-!
# The Laplacian measure of a variational solution

Steps 1 and 2 of the proof of Corollary 8.4 of Kriventsov–Weiss (see
`Regular/Laplacian/BlowUp.lean` for the overview). If `(u, χ)` is a variational solution on `Ω`,
then `Δu = ρ` is a Radon measure on `Ω` that lives on `Ω ∩ ∂{u > 0}` and satisfies
`ρ(B_r(x)) ≤ K r^{n-1}` (cutoff argument of Lemma 3.3). For `2 ≤ n`, the positivity set
`Ω ∩ {u > 0}` has locally finite perimeter in `Ω` (Lemma 8.2 on balls), and `Ω ∩ ∂{u > 0}` is
its essential boundary in `Ω` (Lemma 8.1).

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

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### The Laplacian measure of a variational solution -/

/-- `u` is harmonic or zero near every point of `Ω \ ∂{u > 0}`. -/
theorem exists_integral_mul_laplacian_eq_zero (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hfr : x ∉ frontier {y | 0 < u y}) :
    ∃ δ > 0, closedBall x δ ⊆ Ω ∧
      ∀ φ, IsTestFunction (ball x δ) φ → ∫ y, u y * Δ φ y = 0 := by
  have hH := h.isLipHarmonicPos
  rcases (h.nonneg x hx).lt_or_eq with hpos | hzero
  · obtain ⟨δ, hδ, hδU⟩ :=
      Metric.nhds_basis_closedBall.mem_iff.1 (h.isOpen_pos.mem_nhds ⟨hx, hpos⟩)
    refine ⟨δ, hδ, hδU.trans inter_subset_left, fun φ hφ => ?_⟩
    have hBU : ball x δ ⊆ Ω ∩ {y | 0 < u y} := ball_subset_closedBall.trans hδU
    rw [Kernel.integral_mul_laplacian_eq_neg isOpen_ball
      (hH.locallyLipschitzOn.mono (hBU.trans inter_subset_left)) hφ,
      Kernel.integral_inner_gradient_eq_neg_laplacian isOpen_ball (h.contDiffOn.mono hBU)
        (ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)) hφ.2.1 hφ.2.2]
    have : ∀ y, φ y * Δ u y = 0 := fun y => by
      by_cases hy : y ∈ ball x δ
      · rw [h.laplacian_eq_zero (hBU hy), mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (fun h' => hy (hφ.2.2 h')), zero_mul]
    simp [this]
  · have hncl : x ∉ closure {y | 0 < u y} := fun hcl =>
      hfr ((h.mem_frontier_pos_iff hx).2 ⟨hcl, hzero.symm⟩)
    obtain ⟨δ, hδ, hδΩ, hu0⟩ := h.exists_ball_eq_zero hx hncl
    refine ⟨δ / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hδΩ,
      fun φ hφ => ?_⟩
    have hBΩ : ball x (δ / 2) ⊆ Ω := (ball_subset_ball (by linarith)).trans hδΩ
    rw [Kernel.integral_mul_laplacian_eq_neg isOpen_ball (hH.locallyLipschitzOn.mono hBΩ) hφ]
    have : ∀ y, ⟪gradient u y, gradient φ y⟫ = 0 := fun y => by
      by_cases hy : y ∈ ball x (δ / 2)
      · rw [hH.gradient_eq_zero_of_eq_zero (hBΩ hy)
          (hu0 y (ball_subset_ball (by linarith) hy)), inner_zero_left]
      · rw [Kernel.gradient_eq_zero_of_notMem_tsupport (fun h' => hy (hφ.2.2 h')),
          inner_zero_right]
    simp [this]

/-- The Laplacian measure lives on the free boundary `Ω ∩ ∂{u > 0}`. -/
theorem measure_compl_inter_frontier_eq_zero (h : IsVariationalSolution Ω C u χ)
    {ρ : Measure (Rn n)} (hρΩ : ρ Ωᶜ = 0) (hρ : HasDistribLaplacianOn Ω u ρ) :
    ρ (Ω ∩ frontier {y | 0 < u y})ᶜ = 0 := by
  have hloc : ρ (Ω ∩ (frontier {y | 0 < u y})ᶜ) = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨δ, hδ, hδΩ, hzero⟩ := h.exists_integral_mul_laplacian_eq_zero hx.1 hx.2
    refine ⟨ball x (δ / 2 / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (by positivity)), ?_⟩
    have hB : closedBall x (δ / 2) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hδΩ
    have hle := Regular.measure_ball_le_of_hasDistribLaplacianOn hρ (x := x) (r := δ / 2)
      (by positivity) hB
    rw [hzero _ ⟨Regular.contDiff_scaledBump x _, Regular.hasCompactSupport_scaledBump
      (by positivity), (Regular.tsupport_scaledBump_subset (by positivity)).trans
        (closedBall_subset_ball (by linarith))⟩, ENNReal.ofReal_zero] at hle
    exact le_antisymm hle bot_le
  refine measure_mono_null (fun y hy => ?_) (measure_union_null hρΩ hloc)
  by_cases hyΩ : y ∈ Ω
  · exact Or.inr ⟨hyΩ, fun hf => hy ⟨hyΩ, hf⟩⟩
  · exact Or.inl hyΩ

/-- `∫ bump((· − x)/r) dρ = −r^{n-1} ∫ ⟪∇u_{x,r}, ∇bump⟫`. -/
theorem integral_scaledBump_eq [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {ρ : Measure (Rn n)}
    (hρ : HasDistribLaplacianOn Ω u ρ) {r : ℝ} (hr : 0 < r) (hB : closedBall x r ⊆ Ω) :
    ∫ y, Regular.scaledBump x r y ∂ρ =
      -(r ^ (n - 1) * ∫ z, ⟪gradient (oneHomRescale u x r) z, gradient Regular.bump z⟫) := by
  have hψ := Regular.isTestFunction_scaledBump hr hB
  rw [← hρ.2 _ hψ,
    Kernel.integral_mul_laplacian_eq_neg h.isOpen h.isLipHarmonicPos.locallyLipschitzOn hψ]
  congr 1
  have hg : ∀ z, gradient (oneHomRescale u x r) z = gradient u (x + r • z) := fun z => by
    exact Kernel.gradient_comp_similarity u x hr (LinearIsometryEquiv.refl ℝ (Rn n)) z
  simp_rw [hg, Regular.gradient_scaledBump, real_inner_smul_right]
  rw [integral_const_mul]
  have hcv := Regular.integral_comp_rescale
    (fun z => ⟪gradient u (x + r • z), gradient Regular.bump z⟫) x hr
  simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel] at hcv
  rw [hcv, ← mul_assoc]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos
    (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  rw [Nat.add_sub_cancel, pow_succ', ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- **Upper density bound for the Laplacian measure** (the cutoff argument of the proof of
Lemma 3.3): `ρ(B_r(x)) ≤ K r^{n-1}` whenever `B̄_{2r}(x) ⊆ Ω`. -/
theorem exists_measure_ball_le [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {ρ : Measure (Rn n)}
    (hρ : HasDistribLaplacianOn Ω u ρ) :
    ∃ K : ℝ, ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω →
      ρ (ball x r) ≤ ENNReal.ofReal (K * r ^ (n - 1)) := by
  set I := ∫ z : Rn n, ‖gradient Regular.bump z‖ with hIdef
  refine ⟨C * 2 ^ (n - 1) * I, fun x r hr hB => ?_⟩
  have h2r : (0 : ℝ) < 2 * r := by positivity
  have hle := Regular.measure_ball_le_of_hasDistribLaplacianOn hρ h2r hB
  rw [show 2 * r / 2 = r by ring] at hle
  refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
  have hψ := Regular.isTestFunction_scaledBump h2r hB
  rw [Kernel.integral_mul_laplacian_eq_neg h.isOpen h.isLipHarmonicPos.locallyLipschitzOn hψ]
  have hbd : ∀ y, ‖⟪gradient u y, gradient (Regular.scaledBump x (2 * r)) y⟫‖ ≤
      C * ‖gradient (Regular.scaledBump x (2 * r)) y‖ := fun y => by
    by_cases hy : y ∈ tsupport (Regular.scaledBump x (2 * r))
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (h.norm_gradient_le (hψ.2.2 hy)) (norm_nonneg _))
    · rw [Kernel.gradient_eq_zero_of_notMem_tsupport hy]
      simp
  have h1 := norm_integral_le_of_norm_le
    ((Regular.integrable_norm_gradient_scaledBump x h2r).const_mul C) (.of_forall hbd)
  have h2 : ∫ y, C * ‖gradient (Regular.scaledBump x (2 * r)) y‖ =
      C * ((2 * r) ^ (n - 1) * I) := by
    rw [integral_const_mul]
    congr 1
    simp_rw [Regular.gradient_scaledBump, norm_smul, norm_inv, Real.norm_of_nonneg h2r.le]
    rw [integral_const_mul,
      Regular.integral_comp_rescale (fun z => ‖gradient Regular.bump z‖) x h2r]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos
      (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
    rw [Nat.add_sub_cancel, pow_succ', ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ h2r.ne', one_mul]
  calc -∫ y, ⟪gradient u y, gradient (Regular.scaledBump x (2 * r)) y⟫
      ≤ ‖∫ y, ⟪gradient u y, gradient (Regular.scaledBump x (2 * r)) y⟫‖ := by
        rw [Real.norm_eq_abs]; exact neg_le_abs _
    _ ≤ _ := h1
    _ = C * ((2 * r) ^ (n - 1) * I) := h2
    _ = C * 2 ^ (n - 1) * I * r ^ (n - 1) := by rw [mul_pow]; ring

/-! ### The positivity set as a set of locally finite perimeter -/

/-- On a ball around a free boundary point, `χ = χ_{u>0}` a.e. (Lemma 8.2 on the ball). -/
theorem ae_chi_eq_posIndicator_of_mem_frontier [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) (hx : x ∈ frontier {y | 0 < u y})
    {r : ℝ} (hr : 0 < r) (hB : ball x r ⊆ Ω) :
    ∀ᵐ y ∂(volume.restrict (ball x r)), χ y = posIndicator u y := by
  have hB' := h.mono isOpen_ball hB
  have hSB : sigmaH (ball x r) u χ = ∅ := by
    rw [h.sigmaH_eq_inter_of_subset isOpen_ball hB, hS, empty_inter]
  rcases hB'.eq_zero_or_ae_chi_eq_posIndicator hn (convex_ball x r).isPreconnected hSB with
    ⟨hu0, -⟩ | hae
  · exfalso
    obtain ⟨y, hyB, hy⟩ := mem_closure_iff.1 (frontier_subset_closure hx) (ball x r) isOpen_ball
      (mem_ball_self hr)
    exact (ne_of_gt (show 0 < u y from hy)) (hu0 y hyB)
  · exact hae

/-- **Lemma 8.2**, global form: `Ω ∩ {u > 0}` has locally finite perimeter in `Ω` (a Gauss–Green
pair on all of `Ω`), by Lemma 3.3 on balls and the local BV structure theorem. -/
theorem hasLocallyFinitePerimeter_inter_pos [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) :
    HasLocallyFinitePerimeter Ω (Ω ∩ {y | 0 < u y}) := by
  refine Registry.hasLocallyFinitePerimeter_of_local hn h.isOpen h.isOpen_pos.measurableSet
    fun x hx => ?_
  obtain ⟨ε, hε, hεΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.isOpen.mem_nhds hx)
  set r := ε / 2 with hrdef
  have hr : 0 < r := by positivity
  have h2r : closedBall x (2 * r) ⊆ Ω := by rw [hrdef, mul_div_cancel₀ _ two_ne_zero]; exact hεΩ
  have hBΩ : ball x r ⊆ Ω := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans h2r)
  set K := 2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * (C : ℝ) ^ 2 * r ^ (n - 1) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨r, hr, hBΩ, K, fun φ hφ => ?_⟩
  have hsup : 0 ≤ ⨆ y, ‖φ y‖ := Real.iSup_nonneg fun y => norm_nonneg _
  have hloc : ∫ y in Ω ∩ {y | 0 < u y}, divergence φ y =
      ∫ y in ball x r ∩ (Ω ∩ {y | 0 < u y}), divergence φ y :=
    (Regular.setIntegral_inter_eq isOpen_ball fun y hy =>
      divergence_eq_zero_of_notMem_tsupport fun h' => hy (hφ.2.2 h')).symm
  have hSB : sigmaH (ball x r) u χ = ∅ := by
    rw [h.sigmaH_eq_inter_of_subset isOpen_ball hBΩ, hS, empty_inter]
  rcases (h.mono isOpen_ball hBΩ).eq_zero_or_ae_chi_eq_posIndicator hn
    (convex_ball x r).isPreconnected hSB with ⟨hu0, -⟩ | hae
  · have hempty : ball x r ∩ (Ω ∩ {y | 0 < u y}) = ∅ := eq_empty_of_forall_notMem
      fun y hy => (ne_of_gt (show 0 < u y from hy.2.2)) (hu0 y hy.1)
    rw [hloc, hempty, Measure.restrict_empty, integral_zero_measure, abs_zero]
    exact mul_nonneg hK0 hsup
  · have hset : (ball x r ∩ (Ω ∩ {y | 0 < u y}) : Set (Rn n)) =ᵐ[volume]
        (ball x r ∩ (Ω ∩ {y | χ y = 1}) : Set (Rn n)) := by
      filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hae] with y hy
      refine propext ⟨fun hy' => ⟨hy'.1, hy'.2.1, ?_⟩, fun hy' => ⟨hy'.1, hy'.2.1, ?_⟩⟩
      · rw [mem_ofPred_eq, hy hy'.1, posIndicator_of_pos hy'.2.2]
      · have h1 := hy'.2.2
        rw [mem_ofPred_eq, hy hy'.1] at h1
        by_contra hp
        rw [posIndicator_of_nonpos (not_lt.1 hp)] at h1
        exact zero_ne_one h1
    have hloc' : ∫ y in Ω ∩ {y | χ y = 1}, divergence φ y =
        ∫ y in ball x r ∩ (Ω ∩ {y | χ y = 1}), divergence φ y :=
      (Regular.setIntegral_inter_eq isOpen_ball fun y hy =>
        divergence_eq_zero_of_notMem_tsupport fun h' => hy (hφ.2.2 h')).symm
    rw [hloc, setIntegral_congr_set hset, ← hloc']
    have hφ' : IsSmoothTestField (ball x (3 * r / 2)) φ :=
      ⟨hφ.1, hφ.2.1, hφ.2.2.trans (ball_subset_ball (by linarith))⟩
    refine (h.abs_setIntegral_divergence_le hr h2r hφ').trans (le_of_eq ?_)
    rw [hKdef]
    ring

/-- `Ω ∩ ∂{u > 0} = Ω ∩ ∂ᵉ(Ω ∩ {u > 0})` when `Σ^H = ∅` (Lemma 8.1). -/
theorem inter_frontier_pos_eq [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hS : sigmaH Ω u χ = ∅) :
    Ω ∩ frontier {y | 0 < u y} = Ω ∩ essentialBoundary (Ω ∩ {y | 0 < u y}) := by
  ext x
  constructor
  · rintro ⟨hxΩ, hxf⟩
    refine ⟨hxΩ, ?_⟩
    have hmem := h.frontier_pos_inter_subset_essentialBoundary hn hS ⟨hxΩ, hxf⟩
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hxΩ
    have hae := h.ae_chi_eq_posIndicator_of_mem_frontier hn hS hxf hr hrΩ
    have hiff : ∀ᵐ y ∂(volume.restrict (ball x r)),
        y ∈ Ω ∩ {y | χ y = 1} ↔ y ∈ Ω ∩ {y | 0 < u y} := by
      filter_upwards [hae, ae_restrict_mem measurableSet_ball] with y hy hyB
      have hyΩ := hrΩ hyB
      rw [mem_inter_iff, mem_inter_iff, mem_ofPred_eq, mem_ofPred_eq, hy]
      by_cases hp : 0 < u y
      · simp [posIndicator_of_pos hp, hp, hyΩ]
      · simp [posIndicator_of_nonpos (not_lt.1 hp), hp, hyΩ]
    exact ⟨fun h0 => hmem.1 ((Regular.hasDensity_congr_of_ae hr hiff).2 h0),
      fun h1 => hmem.2 ((Regular.hasDensity_congr_of_ae hr hiff).2 h1)⟩
  · rintro ⟨hxΩ, hxe⟩
    refine ⟨hxΩ, ?_⟩
    have hfr := Regular.essentialBoundary_subset_frontier _ hxe
    rw [frontier, Set.mem_sdiff] at hfr ⊢
    refine ⟨closure_mono inter_subset_right hfr.1, fun hint => hfr.2 ?_⟩
    rw [interior_inter, h.isOpen.interior_eq]
    exact ⟨hxΩ, hint⟩

/-- `ℋ^{n-1}(B̄_r(x) ∩ Ω ∩ ∂{u > 0}) ≤ K r^{n-1}` whenever `B̄_{4r}(x) ⊆ Ω` (Lemma 8.2). -/
theorem exists_hausdorffN_closedBall_inter_le [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) :
    ∃ K : ℝ, ∀ x r, 0 < r → closedBall x (4 * r) ⊆ Ω →
      hausdorffN n (n - 1) (closedBall x r ∩ (Ω ∩ frontier {y | 0 < u y})) ≤
        ENNReal.ofReal (K * r ^ (n - 1)) := by
  refine ⟨2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * 2 ^ (n - 1),
    fun x r hr hB => ?_⟩
  have h2r : 0 < 2 * r := by positivity
  have hB' : closedBall x (2 * (2 * r)) ⊆ Ω := by
    rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]
    exact hB
  have hsub : closedBall x r ∩ (Ω ∩ frontier {y | 0 < u y}) ⊆
      frontier {y | 0 < u y} ∩ ball x (2 * r) := fun y hy =>
    ⟨hy.2.2, closedBall_subset_ball (by linarith) hy.1⟩
  refine (measure_mono hsub).trans
    ((h.hausdorffN_frontier_pos_inter_ball_le hn hS h2r hB').trans (le_of_eq ?_))
  congr 1
  rw [mul_pow]
  ring

end IsVariationalSolution

end InnerVariational
