/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import InnerVariational.Vendor.Analysis.Weyl
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import InnerVariational.Vendor.Analysis.MeanValue
import InnerVariational.Vendor.Analysis.PolarCoord

/-!
# Mean-value property on balls and the local Harnack inequality (ported from TauCeti)

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`.

* `integral_laplacian_mul_eq_integral_mul_laplacian`: Green's second identity against a test
  function, `∫ Δχ · u = ∫ χ · Δu` for `u ∈ C²(U)` and `χ ∈ C^∞_c(U)`.
* `HarmonicOnNhd.weaklyHarmonicOn`: a harmonic function on an open set is weakly harmonic there,
  in the sense of `InnerVariational.Vendor.Analysis.WeaklyHarmonicOn`.
* `HarmonicOnNhd.setIntegral_ball_eq`: the mean-value property on balls,
  `∫_{B_R(x₀)} u = |B_R| u(x₀)` for `u` harmonic on a neighbourhood of `closedBall x₀ R`.
* `HarmonicOnNhd.le_div_pow_mul_of_nonneg`: nested balls compare values of a nonnegative
  harmonic function, `u x ≤ (s / r) ^ n * u y` when `r + dist x y ≤ s`.
* `HarmonicOnNhd.le_three_pow_mul_of_nonneg`: the local Harnack inequality `u x ≤ 3 ^ n * u y`
  on `ball c r`, for `u` harmonic and nonnegative on `ball c (4 * r)`.

The sphere mean-value property is the one adapted from TauCeti in `Vendor/Analysis/MeanValue.lean`
(see its `## Provenance`). Here it is
combined with Green's identity (so that classical harmonicity gives weak harmonicity) and
integrated in polar coordinates.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001 (reprint of the 1998 edition), Theorems 2.1 and 2.5.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Amer. Math. Soc., 2010, §2.2.2.

## Provenance

* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti
* Paths: `TauCeti/Analysis/PDE/Harnack/Basic.lean`,
  `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean`,
  `TauCeti/Analysis/Sobolev/WeakDeriv/Laplacian.lean`
* Commit: 90cca67c0c8e91cd30b0d46cb58101f8c5c59236 (2026-09-25)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`;
  upstream authors: The Tau Ceti contributors.
* Extent: `HarmonicOnNhd.le_div_pow_mul_of_nonneg` and `HarmonicOnNhd.le_three_pow_mul_of_nonneg`
  (verbatim up to namespace); `HarmonicOnNhd.setIntegral_ball_eq` (adapted from
  `setIntegral_ball_eq_of_harmonicOnNhd_zero` and `HarmonicOnNhd.setIntegral_ball_eq`);
  `integral_laplacian_mul_eq_integral_mul_laplacian` and `HarmonicOnNhd.weaklyHarmonicOn`
  (adapted from `ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian` and
  `HarmonicOnNhd.integral_laplacian_smul_eq_zero`).
* Changes: ported from Lean v4.34 to Lean/Mathlib v4.30.0; `module`/`public import` removed;
  namespace `TauCeti` → `InnerVariational.Vendor`, and the theorems are no longer stated in the
  root namespace `InnerProductSpace.HarmonicOnNhd`. Green's identity is restated for real-valued
  `u` and smooth compactly supported `χ` (instead of TauCeti's `𝓓(Ω, ℝ)`), and re-proved from
  Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` instead of TauCeti's weak
  derivatives. The ball mean-value property is derived from the sphere mean-value property for
  weakly harmonic functions in `Vendor/Analysis/MeanValue.lean` (adapted from TauCeti's
  `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean` at commit
  `91f66a0514e6523efdccddb9e35fb82c96dd6405`). The global (compact-set) Harnack
  inequality `IsCompact.harnack_inequality` is not ported.
* Module system: converted to a Lean `module` (`public import`, `@[expose] public section`)
  with narrowed Mathlib imports.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology
open scoped ContDiff Laplacian

@[expose] public noncomputable section

namespace InnerVariational.Vendor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Green

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Green's second identity against a test function.** For `u` of class `C²` on an open set
`U` and a smooth `χ` with compact support in `U`, `∫ Δχ · u = ∫ χ · Δu`. -/
theorem integral_laplacian_mul_eq_integral_mul_laplacian {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ x, Δ χ x * u x ∂μ = ∫ x, χ x * Δ u x ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hdu : ∀ v, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y v) U := fun v ↦
    hu1.clm_apply contDiffOn_const
  have hu_diff : ∀ x ∈ U, DifferentiableAt ℝ u x := fun x hx ↦
    (hu.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  have hdu_diff : ∀ v, ∀ x ∈ U, DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y v) x := fun v x hx ↦
    ((hdu v).differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hddu_cont : ∀ v, ContinuousOn (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ u z v) y v) U :=
    fun v ↦ ((hdu v).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hΔu : ∀ x ∈ U, Δ u x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) := by
    intro x hx
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [iteratedFDeriv_two_apply, fderiv_clm_apply
      ((hu1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx))
      (differentiableAt_const _)]
    simp
  have hΔχ : ∀ x, Δ χ x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) :=
    Analysis.laplacian_eq_sum_fderiv_fderiv b (hχ.of_le (by norm_cast))
  -- smooth directional derivatives of `χ`, supported in `tsupport χ`
  have hDχ : ∀ v, ContDiff ℝ ∞ (fun y ↦ fderiv ℝ χ y v) ∧
      tsupport (fun y ↦ fderiv ℝ χ y v) ⊆ tsupport χ := fun v ↦
    ⟨(hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, tsupport_fderiv_apply_subset ℝ v⟩
  have hDDχ : ∀ v, ContDiff ℝ ∞ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ χ z v) y v) ∧
      tsupport (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ χ z v) y v) ⊆ tsupport χ := fun v ↦
    ⟨(((hDχ v).1).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const,
      (tsupport_fderiv_apply_subset ℝ v).trans (hDχ v).2⟩
  -- integrability of the products
  have hint : ∀ φ g : E → ℝ, Continuous φ → tsupport φ ⊆ tsupport χ → ContinuousOn g U →
      Integrable (fun x ↦ φ x * g x) μ := by
    intro φ g hφ hφs hg
    have hφc : HasCompactSupport φ := hχc.mono' (subset_tsupport φ |>.trans hφs)
    exact ((hφ.continuousOn.mul hg).continuous_of_tsupport_subset hU
      ((tsupport_mul_subset_left).trans (hφs.trans hχU))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hucont : ContinuousOn u U := hu.continuousOn
  have hdu_cont : ∀ v, ContinuousOn (fun y ↦ fderiv ℝ u y v) U := fun v ↦ (hdu v).continuousOn
  -- one direction
  have hdir : ∀ v, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y v) x v * u x ∂μ =
      ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ := by
    intro v
    have e1 : ∫ x, fderiv ℝ χ x v * fderiv ℝ u x v ∂μ =
        -∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y v) x v * u x ∂μ :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hint _ _ (hDDχ v).1.continuous (hDDχ v).2 hucont)
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 (hdu_cont v))
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 hucont)
        (fun x _ ↦ ((hDχ v).1.differentiable (by simp)) x)
        (fun x hx ↦ hu_diff x (hχU ((hDχ v).2 hx)))
    have e2 : ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ =
        -∫ x, fderiv ℝ χ x v * fderiv ℝ u x v ∂μ :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 (hdu_cont v))
        (hint _ _ hχ.continuous le_rfl (hddu_cont v))
        (hint _ _ hχ.continuous le_rfl (hdu_cont v))
        (fun x _ ↦ (hχ.differentiable (by simp)) x)
        (fun x hx ↦ hdu_diff v x (hχU hx))
    linarith
  calc ∫ x, Δ χ x * u x ∂μ
      = ∑ i, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) * u x ∂μ := by
        simp_rw [hΔχ, Finset.sum_mul]
        exact integral_finsetSum _ fun i _ ↦
          hint _ _ (hDDχ (b i)).1.continuous (hDDχ (b i)).2 hucont
    _ = ∑ i, ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) ∂μ :=
        Finset.sum_congr rfl fun i _ ↦ hdir (b i)
    _ = ∫ x, χ x * Δ u x ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint _ _ hχ.continuous le_rfl (hddu_cont (b i))]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        by_cases hx : x ∈ U
        · simp only [hΔu x hx, Finset.mul_sum]
        · have : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)
          simp [this]

/-- **A harmonic function is weakly harmonic.** -/
theorem HarmonicOnNhd.weaklyHarmonicOn {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : HarmonicOnNhd u U) : Analysis.WeaklyHarmonicOn μ u U := by
  intro χ hχ hχc hχU
  simp_rw [smul_eq_mul]
  rw [integral_laplacian_mul_eq_integral_mul_laplacian hU hu.contDiffOn hχ hχc hχU]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ U
  · simp [(hu x hx).2.eq_of_nhds]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)]

/-- The mean-value property on balls, for a weakly harmonic function, centred form. -/
private lemma setIntegral_ball_zero_add_eq [Nontrivial E] {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hcont : ContinuousOn u U) (hu : Analysis.WeaklyHarmonicOn μ u U) {x₀ : E} {R : ℝ}
    (hΩ : closedBall x₀ R ⊆ U) (hR : 0 < R) :
    ∫ y in ball (0 : E) R, u (x₀ + y) ∂μ = μ.real (ball (0 : E) R) * u x₀ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  set v : E → ℝ := fun y ↦ u (x₀ + y) with hv
  have hvcont : ContinuousOn v (closedBall (0 : E) R) :=
    (hcont.mono hΩ).comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ by
      rw [mem_closedBall, dist_eq_norm] at hy ⊢
      simpa using hy
  have hint : Integrable ((ball (0 : E) R).indicator v) μ :=
    ((hvcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall).integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,
    Analysis.integral_eq_integral_Ioi_integral_toSphere _ hint]
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, (ball (0 : E) R).indicator v (s • (θ : E)) ∂μ.toSphere =
        (Iio R).indicator (fun s ↦ s ^ (Module.finrank ℝ E - 1) • (μ.toSphere.real univ • u x₀))
          s := by
    intro s hs
    have hs : 0 < s := hs
    have hmem : ∀ θ : sphere (0 : E) 1, s • (θ : E) ∈ ball (0 : E) R ↔ s < R := fun θ ↦ by
      rw [mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    by_cases hsR : s < R
    · rw [indicator_of_mem (mem_Iio.mpr hsR)]
      simp_rw [indicator_of_mem ((hmem _).mpr hsR)]
      rw [hv, Analysis.integral_toSphere_eq_of_weaklyHarmonic hU hcont hu
        ((closedBall_subset_closedBall hsR.le).trans hΩ) hs.le]
    · rw [indicator_of_notMem (by simpa using hsR)]
      simp_rw [indicator_of_notMem ((not_congr (hmem _)).mpr hsR)]
      simp
  have hball : μ.real (ball (0 : E) R) = R ^ (m + 1) * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball μ _ hR.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hm, measureReal_def]
  have hsph : μ.toSphere.real univ = ((m : ℝ) + 1) * μ.real (ball (0 : E) 1) := by
    rw [Measure.toSphere_real_apply_univ, hm]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, integral_smul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le, integral_pow, hball, hsph, smul_smul, hm,
    Nat.add_sub_cancel, zero_pow (Nat.succ_ne_zero m), sub_zero, smul_eq_mul]
  field_simp

/-- **The mean-value property on balls.** If `u` is harmonic on a neighbourhood of the closed
ball `closedBall x₀ R`, then `∫_{B_R(x₀)} u = |B_R| u(x₀)`. (For `R ≤ 0` both sides vanish.) -/
theorem HarmonicOnNhd.setIntegral_ball_eq {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) :
    ∫ x in ball x₀ R, u x ∂μ = μ.real (ball x₀ R) * u x₀ := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.mpr hR]
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [setIntegral_congr_fun measurableSet_ball (g := fun _ ↦ u x₀)
      fun x _ ↦ congrArg u (Subsingleton.elim x x₀), setIntegral_const, smul_eq_mul]
  -- the harmonic points form an open set containing the closed ball
  set U := {x : E | HarmonicAt u x}
  have hU : IsOpen U := isOpen_setOfPred_harmonicAt u
  have hΩ : closedBall x₀ R ⊆ U := fun x hx ↦ hu x hx
  have huU : HarmonicOnNhd u U := fun x hx ↦ hx
  have h := setIntegral_ball_zero_add_eq hU huU.contDiffOn.continuousOn
    (HarmonicOnNhd.weaklyHarmonicOn (μ := μ) hU huU) hΩ hR
  rw [Measure.addHaar_real_ball_center, ← h, ← integral_indicator measurableSet_ball,
    ← integral_indicator measurableSet_ball, ← integral_add_left_eq_self _ x₀]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  classical
  simp only [indicator_apply, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]

end Green

variable {u : E → ℝ} {x y c : E} {r s : ℝ}

/-- **Nested balls compare the values of a nonnegative harmonic function.** If `u` is harmonic
on a neighbourhood of `closedBall y s` and nonnegative on `ball y s`, and `closedBall x r` lies
inside `closedBall y s` in the sense that `r + dist x y ≤ s`, then
`u x ≤ (s / r) ^ n * u y`, where `n` is the dimension of `E`. -/
theorem HarmonicOnNhd.le_div_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (closedBall y s)) (hnonneg : ∀ z ∈ ball y s, 0 ≤ u z) (hr : 0 < r)
    (hxy : r + dist x y ≤ s) :
    u x ≤ (s / r) ^ finrank ℝ E * u y := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hs : 0 < s := hr.trans_le ((le_add_of_nonneg_right dist_nonneg).trans hxy)
  have hint : IntegrableOn u (ball y s) μ :=
    (hu.contDiffOn.continuousOn.integrableOn_compact (isCompact_closedBall y s)).mono_set
      ball_subset_closedBall
  have hle : ∫ z in ball x r, u z ∂μ ≤ ∫ z in ball y s, u z ∂μ :=
    setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hnonneg))
      (ball_subset_ball' hxy).eventuallyLE
  rw [HarmonicOnNhd.setIntegral_ball_eq (hu.mono (closedBall_subset_closedBall' hxy)),
    HarmonicOnNhd.setIntegral_ball_eq hu] at hle
  simp only [measureReal_def, μ.addHaar_ball_of_pos x hr,
    μ.addHaar_ball_of_pos y hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _), ENNReal.toReal_ofReal (pow_nonneg hs.le _)] at hle
  have hB : 0 < (μ (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ hB
  nlinarith [hle]

/-- **The local Harnack inequality.** If `u` is harmonic and nonnegative on `ball c (4 * r)`, then
any two of its values on `ball c r` are within the factor `3 ^ n` of each other, where `n` is the
dimension of `E`. -/
theorem HarmonicOnNhd.le_three_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (ball c (4 * r))) (hnonneg : ∀ z ∈ ball c (4 * r), 0 ≤ u z)
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) :
    u x ≤ 3 ^ finrank ℝ E * u y := by
  have hr : 0 < r := pos_of_mem_ball hx
  rw [mem_ball] at hx hy
  have hsub : closedBall y (3 * r) ⊆ ball c (4 * r) :=
    closedBall_subset_ball' (by linarith)
  have hxy : r + dist x y ≤ 3 * r := by linarith [dist_triangle_right x y c]
  have := HarmonicOnNhd.le_div_pow_mul_of_nonneg (hu.mono hsub)
    (fun z hz ↦ hnonneg z (hsub (ball_subset_closedBall hz))) hr hxy
  rwa [mul_div_cancel_right₀ 3 hr.ne'] at this

end InnerVariational.Vendor
