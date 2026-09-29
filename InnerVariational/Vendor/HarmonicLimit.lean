/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Vendor.Harnack
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Convolution
import InnerVariational.Vendor.Analysis.Weyl
public import InnerVariational.Vendor.Analysis.MeanValue
import InnerVariational.Vendor.Analysis.LaplacianInvariance

/-!
# Interior gradient estimate and limits of harmonic functions

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`.

* `eqOn_indicator_convolution_of_weaklyHarmonic`: a continuous weakly harmonic function `u` on
  `U ⊇ closedBall x₀ (2 r)` is reproduced on `ball x₀ r` by convolution with a radial kernel of
  integral one supported in `closedBall 0 r`.
* `exists_norm_fderiv_le_of_weaklyHarmonic`: the interior gradient estimate: there is `C = C(r)`
  with `‖Du(x)‖ ≤ C sup_{B_{2r}(x₀)} |u|` for `x ∈ B_r(x₀)`.
* `weaklyHarmonicOn_of_tendstoLocallyUniformlyOn`: a locally uniform limit of continuous weakly
  harmonic functions is weakly harmonic.
* `harmonicOnNhd_of_tendstoLocallyUniformlyOn`: a locally uniform limit of harmonic functions is
  harmonic, and the gradients converge locally uniformly (Gilbarg–Trudinger Thms 2.8, 2.10).

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001 (reprint of the 1998 edition), Theorems 2.8 and 2.10.

`eqOn_indicator_convolution_of_weaklyHarmonic` extracts, for an arbitrary radial kernel, the
reproduction step of the proof of Weyl's lemma `exists_contDiff_eventuallyEq_laplacian_eq_zero`
(in the Weyl's-lemma file of this directory).
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology ContinuousLinearMap
open scoped ContDiff Laplacian Convolution

@[expose] public noncomputable section

namespace InnerVariational.Vendor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian of a smooth function is continuous. -/
theorem continuous_laplacian_of_contDiff {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) : Continuous (Δ χ) := by
  set b := stdOrthonormalBasis ℝ E
  have h : Δ χ = fun x ↦ ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) :=
    funext (Analysis.laplacian_eq_sum_fderiv_fderiv b (hχ.of_le (by norm_cast)))
  rw [h]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have h1 : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ χ y (b i)) :=
    (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  exact ((h1.continuous_fderiv (by simp)).clm_apply continuous_const)

section Measure

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Reproduction by a radial kernel**. If `u` is continuous and weakly
harmonic on `U ⊇ closedBall x₀ (2 r)` and `g (‖·‖²)` is a smooth radial kernel of integral one
vanishing outside `closedBall 0 r`, then `u = (1_B u) ⋆ g (‖·‖²)` on `ball x₀ r`, where
`B = closedBall x₀ (2 r)`. -/
theorem eqOn_indicator_convolution_of_weaklyHarmonic [Nontrivial E] {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hcont : ContinuousOn u U) (hu : Analysis.WeaklyHarmonicOn μ u U) {x₀ : E}
    {r : ℝ}
    (hr : 0 < r) (hBU : closedBall x₀ (2 * r) ⊆ U) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg0 : ∀ t, r ^ 2 ≤ t → g t = 0) (hg1 : ∫ y, g (‖y‖ ^ 2) ∂μ = 1) :
    EqOn u ((closedBall x₀ (2 * r)).indicator u ⋆[lsmul ℝ ℝ, μ] fun y ↦ g (‖y‖ ^ 2))
      (ball x₀ r) := by
  set B := closedBall x₀ (2 * r)
  set ρ : E → ℝ := fun y ↦ g (‖y‖ ^ 2) with hρ_def
  set f := B.indicator u with hf_def
  intro x hx
  have hxB : closedBall x r ⊆ B := closedBall_subset_closedBall' (by
    rw [mem_ball] at hx
    linarith)
  have hk : Continuous fun s : ℝ ↦ g (s ^ 2) := hg.continuous.comp (continuous_pow 2)
  have hmvp := Analysis.integral_radial_smul_eq_of_weaklyHarmonic hU hcont hu (hxB.trans hBU) hk
    (fun s hs ↦ hg0 _ (pow_le_pow_left₀ hr.le hs.le 2))
  rw [hg1, one_smul] at hmvp
  rw [← hmvp, convolution_def]
  conv_rhs => rw [← integral_add_left_eq_self _ x]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [lsmul_apply, smul_eq_mul, sub_add_cancel_left, norm_neg, hρ_def]
  by_cases hy : ‖y‖ ≤ r
  · rw [hf_def, indicator_of_mem (hxB (by simpa [mem_closedBall, dist_eq_norm] using hy)),
      mul_comm]
  · have := hg0 (‖y‖ ^ 2) (pow_le_pow_left₀ hr.le (not_le.mp hy).le 2)
    simp [this]

variable (μ) in
/-- **Interior gradient estimate.** For `r > 0` there is `C` such that every continuous weakly
harmonic `u` on an open `U ⊇ closedBall x₀ (2 r)` with `|u| ≤ M` on `closedBall x₀ (2 r)`
satisfies `‖Du(x)‖ ≤ C M` for `x ∈ ball x₀ r`. -/
theorem exists_norm_fderiv_le_of_weaklyHarmonic [Nontrivial E] {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set E) (u : E → ℝ) (x₀ : E), IsOpen U → ContinuousOn u U →
      Analysis.WeaklyHarmonicOn μ u U → closedBall x₀ (2 * r) ⊆ U → ∀ M : ℝ,
      (∀ y ∈ closedBall x₀ (2 * r), |u y| ≤ M) → ∀ x ∈ ball x₀ r, ‖fderiv ℝ u x‖ ≤ C * M := by
  obtain ⟨g, hg, hg0, hg1⟩ := Analysis.exists_radial_kernel μ hr
  set ρ : E → ℝ := fun y ↦ g (‖y‖ ^ 2) with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := hg.comp (contDiff_norm_sq ℝ)
  have hρ0 : ∀ y, r < ‖y‖ → ρ y = 0 := fun y hy ↦
    hg0 _ (pow_le_pow_left₀ hr.le hy.le 2)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) r) fun y hy ↦
      hρ0 y (by rwa [mem_closedBall_zero_iff, not_le] at hy)
  have hDρ : Continuous fun y ↦ ‖fderiv ℝ ρ y‖ := (hρ.continuous_fderiv (by simp)).norm
  have hDρi : Integrable (fun y ↦ ‖fderiv ℝ ρ y‖) μ :=
    hDρ.integrable_of_hasCompactSupport (hρc.fderiv (𝕜 := ℝ)).norm
  refine ⟨∫ y, ‖fderiv ℝ ρ y‖ ∂μ, integral_nonneg fun _ ↦ norm_nonneg _,
    fun U u x₀ hU hcont hu hBU M hM x hx ↦ ?_⟩
  set B := closedBall x₀ (2 * r)
  set f := B.indicator u with hf_def
  have hf : LocallyIntegrable f μ :=
    (((hcont.mono hBU).integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator
      measurableSet_closedBall).locallyIntegrable
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ (mem_closedBall_self (by positivity)))
  have hfM : ∀ t, |f t| ≤ M := fun t ↦ by
    by_cases ht : t ∈ B
    · rw [hf_def, indicator_of_mem ht]
      exact hM t ht
    · rw [hf_def, indicator_of_notMem ht, abs_zero]
      exact hM0
  have heq : u =ᶠ[𝓝 x] f ⋆[lsmul ℝ ℝ, μ] ρ :=
    (eqOn_indicator_convolution_of_weaklyHarmonic hU hcont hu hr hBU hg hg0 hg1).eventuallyEq_of_mem
      (isOpen_ball.mem_nhds hx)
  rw [heq.fderiv_eq]
  refine opNorm_le_bound _ (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) hM0) fun v ↦ ?_
  rw [Analysis.fderiv_convolution_apply hf (hρ.of_le (by exact_mod_cast le_top)) hρc x v,
    convolution_def]
  have hbound : Integrable (fun t ↦ M * (‖fderiv ℝ ρ (x - t)‖ * ‖v‖)) μ :=
    ((hDρi.comp_sub_left x).mul_const _).const_mul _
  calc ‖∫ t, (lsmul ℝ ℝ) (f t) (fderiv ℝ ρ (x - t) v) ∂μ‖
      ≤ ∫ t, M * (‖fderiv ℝ ρ (x - t)‖ * ‖v‖) ∂μ := by
        refine norm_integral_le_of_norm_le hbound (Eventually.of_forall fun t ↦ ?_)
        rw [lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hfM t) (le_opNorm _ _) (norm_nonneg _) hM0
    _ = (∫ y, ‖fderiv ℝ ρ y‖ ∂μ) * M * ‖v‖ := by
        rw [integral_const_mul, integral_mul_const,
          integral_sub_left_eq_self (fun y ↦ ‖fderiv ℝ ρ y‖) μ x]
        ring

/-- A locally uniform limit of continuous weakly harmonic functions is weakly harmonic. -/
theorem weaklyHarmonicOn_of_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι} [p.NeBot]
    {U : Set E} (hU : IsOpen U) {F : ι → E → ℝ} {f : E → ℝ}
    (hFc : ∀ k, ContinuousOn (F k) U) (hF : ∀ k, Analysis.WeaklyHarmonicOn μ (F k) U)
    (hconv : TendstoLocallyUniformlyOn F f p U) : Analysis.WeaklyHarmonicOn μ f U := by
  intro χ hχ hχc hχU
  have hfc : ContinuousOn f U := hconv.continuousOn (Frequently.of_forall hFc)
  have hΔc : Continuous (Δ χ) := continuous_laplacian_of_contDiff hχ
  have hΔs : tsupport (Δ χ) ⊆ tsupport χ := Analysis.tsupport_laplacian_subset χ
  have hΔcs : HasCompactSupport (Δ χ) := hχc.mono' (subset_tsupport _ |>.trans hΔs)
  have hint : ∀ g : E → ℝ, ContinuousOn g U → Integrable (fun x ↦ Δ χ x • g x) μ :=
    fun g hg ↦ ((hΔc.continuousOn.smul hg).continuous_of_tsupport_subset hU
      ((tsupport_smul_subset_left _ _).trans (hΔs.trans hχU))).integrable_of_hasCompactSupport
      hΔcs.smul_right
  have hunif : TendstoUniformlyOn F f p (tsupport χ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hχU hχc
  set A := ∫ x, ‖Δ χ x‖ ∂μ
  have hAi : Integrable (fun x ↦ ‖Δ χ x‖) μ := (hΔc.integrable_of_hasCompactSupport hΔcs).norm
  -- `‖∫ Δχ f‖ ≤ ε A` for every `ε > 0`
  have hle : ∀ ε > 0, ‖∫ x, Δ χ x • f x ∂μ‖ ≤ ε * A := by
    intro ε hε
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif ε hε).exists
    have hsub : ∫ x, Δ χ x • f x ∂μ = ∫ x, Δ χ x • (f x - F k x) ∂μ := by
      simp_rw [smul_sub]
      rw [integral_sub (hint f hfc) (hint _ (hFc k)), hF k χ hχ hχc hχU, sub_zero]
    rw [hsub, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hAi.const_mul ε) (Eventually.of_forall fun x ↦ ?_)
    rw [norm_smul]
    by_cases hx : x ∈ tsupport χ
    · rw [mul_comm ε]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← dist_eq_norm]
      exact (hk x hx).le
    · have : Δ χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hΔs h)
      simp [this]
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  rw [zero_add]
  calc ‖∫ x, Δ χ x • f x ∂μ‖ ≤ (ε / (A + 1)) * A := hle _ (by positivity)
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

end Measure

/-- **Limits of harmonic functions** (Gilbarg–Trudinger Thms 2.8, 2.10). A locally uniform limit
of harmonic functions on an open set is harmonic, and the derivatives converge locally
uniformly. -/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι} [p.NeBot]
    {U : Set E} (hU : IsOpen U) {F : ι → E → ℝ} {f : E → ℝ} (hF : ∀ k, HarmonicOnNhd (F k) U)
    (hconv : TendstoLocallyUniformlyOn F f p U) :
    HarmonicOnNhd f U ∧ TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (F k)) (fderiv ℝ f) p U := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hFc : ∀ k, ContinuousOn (F k) U := fun k ↦ (hF k).contDiffOn.continuousOn
  have hfc : ContinuousOn f U := hconv.continuousOn (Frequently.of_forall hFc)
  have hfw : Analysis.WeaklyHarmonicOn μ f U := weaklyHarmonicOn_of_tendstoLocallyUniformlyOn hU hFc
    (fun k ↦ HarmonicOnNhd.weaklyHarmonicOn hU (hF k)) hconv
  obtain ⟨hsmooth, hΔ⟩ := Analysis.weyl_of_weaklyHarmonicOn hU hfc hfw
  have hf : HarmonicOnNhd f U := fun x hx ↦
    ⟨(hsmooth.contDiffAt (hU.mem_nhds hx)).of_le (by norm_cast),
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy ↦ hΔ y hy⟩
  refine ⟨hf, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε x₀ hx₀ ↦ ?_⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero all derivatives vanish
    have h0 : ∀ L : E →L[ℝ] ℝ, L = 0 := fun L ↦ by
      ext v
      rw [Subsingleton.elim v 0, map_zero, zero_apply]
    exact ⟨univ, univ_mem, Eventually.of_forall fun k y _ ↦ by simp [h0 (fderiv ℝ f y),
      h0 (fderiv ℝ (F k) y), hε]⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set r := δ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hBU : closedBall x₀ (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hδU
  obtain ⟨C, hC, hest⟩ := exists_norm_fderiv_le_of_weaklyHarmonic μ hr
  have hunif : TendstoUniformlyOn F f p (closedBall x₀ (2 * r)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hBU (isCompact_closedBall _ _)
  set η := ε / (C + 1) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨ball x₀ r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x₀ hr), ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif η hη0] with k hk y hy
  -- `F k - f` is harmonic, and small on the closed ball
  have hg : HarmonicOnNhd (F k - f) U := fun z hz ↦ (hF k z hz).sub (hf z hz)
  have hyU : y ∈ U := hBU (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith)) hy)
  have hsub : fderiv ℝ (F k - f) y = fderiv ℝ (F k) y - fderiv ℝ f y :=
    fderiv_sub ((hF k y hyU).1.differentiableAt (by norm_num))
      ((hf y hyU).1.differentiableAt (by norm_num))
  have hbound := hest U (F k - f) x₀ hU hg.contDiffOn.continuousOn
    (HarmonicOnNhd.weaklyHarmonicOn hU hg) hBU η
    (fun z hz ↦ by
      rw [Pi.sub_apply, abs_sub_comm, ← Real.dist_eq]
      exact (hk z hz).le) y hy
  rw [hsub] at hbound
  rw [dist_comm, dist_eq_norm]
  calc ‖fderiv ℝ (F k) y - fderiv ℝ f y‖ ≤ C * η := hbound
    _ < ε := by
        rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end InnerVariational.Vendor
