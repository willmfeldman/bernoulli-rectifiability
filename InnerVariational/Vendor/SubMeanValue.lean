/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import InnerVariational.Vendor.Analysis.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import InnerVariational.Vendor.Analysis.PolarCoord
import InnerVariational.Vendor.Analysis.LaplacianInvariance

/-!
# The sub-mean-value property of continuous weakly subharmonic functions

Let `E` be a nontrivial finite-dimensional real inner product space with an additive Haar measure
`μ`, `U ⊆ E` open, and `u : E → ℝ` continuous on `U` and **weakly subharmonic** in `U`:
`0 ≤ ∫ u Δχ ∂μ` for every nonnegative smooth `χ` with compact support in `U`. If
`closedBall x₀ R ⊆ U`, then

* `integral_toSphere_ge_of_weaklySubharmonic`:
  `μ.toSphere(S) u(x₀) ≤ ∫ θ ∈ S, u (x₀ + R • θ) ∂μ.toSphere`;
* `mul_le_setIntegral_ball_of_weaklySubharmonic`: `μ(B_R(x₀)) u(x₀) ≤ ∫_{B_R(x₀)} u ∂μ`.

## The argument

Write `Φ s = ∫ θ ∈ S, u (s • θ) ∂μ.toSphere`. For a nonnegative test function `ψ` on `(0, R)`,
the radial test function `χ x = ρ (‖x‖²)`, with `ρ t = ∫_t^{R²} ψ (√τ) / (√τ) ^ n dτ ≥ 0`, is
nonnegative, and in polar coordinates `0 ≤ ∫ u Δχ = -2 ∫ ψ' Φ`. So the distributional derivative
of `Φ` on `(0, R)` is nonnegative, and `Φ` is nondecreasing there
(`monotoneOn_of_integral_deriv_mul_nonpos`, by testing against mollified indicators of intervals).
By continuity, `Φ 0 ≤ Φ R`. The ball form follows by integrating in polar coordinates.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001 (reprint of the 1998 edition), Theorem 2.1.

## Provenance

* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti
* Path: `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean`
* Commit: 91f66a0514e6523efdccddb9e35fb82c96dd6405 (2026-09-24)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`;
  upstream authors: The Tau Ceti contributors.
* Extent: `integral_deriv_mul_integral_toSphere_nonpos` and
  `integral_toSphere_ge_of_weaklySubharmonic` are adapted from the weakly harmonic versions
  `integral_deriv_smul_integral_toSphere_eq_zero`, `integral_toSphere_eq_of_weaklyHarmonic_zero`
  and `integral_toSphere_eq_of_weaklyHarmonic` in `Vendor/Analysis/MeanValue.lean`, which are in
  turn
  adapted from the upstream file above (see the `## Provenance` of that file).
  `weaklySubharmonic_comp_add_right` is adapted from `weaklyHarmonic_comp_add_right` there
  (W. M. Feldman).
* Changes: real-valued `u`; weak harmonicity (an equality) is replaced by weak subharmonicity (an
  inequality against nonnegative test functions), the radial test function is taken with the
  opposite sign so that it is nonnegative, and the du Bois-Reymond lemma is replaced by the new
  monotonicity lemma `monotoneOn_of_integral_deriv_mul_nonpos`. The rest of the file is new.
* Module system: converted to a Lean `module` (`public import`, `@[expose] public section`) with
  narrowed Mathlib imports.
-/

open InnerProductSpace MeasureTheory Metric Set Filter Topology
open scoped ContDiff Laplacian

@[expose] public noncomputable section

namespace InnerVariational.Vendor

/-- **A function with nonnegative distributional derivative is nondecreasing.** If `f` is
continuous on `(a, b)` and `∫ ψ' f ≤ 0` for every nonnegative smooth `ψ` with support in `(a, b)`,
then `f` is monotone on `(a, b)`. -/
theorem monotoneOn_of_integral_deriv_mul_nonpos {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → (∀ t, 0 ≤ ψ t) → tsupport ψ ⊆ Ioo a b →
      ∫ t, deriv ψ t * f t ≤ 0) :
    MonotoneOn f (Ioo a b) := by
  intro x hx y hy hxy
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  obtain ⟨δx, hδx, hfx⟩ := Metric.continuousAt_iff.1
    (hf.continuousAt (isOpen_Ioo.mem_nhds hx)) (η / 2) (by positivity)
  obtain ⟨δy, hδy, hfy⟩ := Metric.continuousAt_iff.1
    (hf.continuousAt (isOpen_Ioo.mem_nhds hy)) (η / 2) (by positivity)
  obtain ⟨δ, hδ, hδx', hδy', hxa, hyb⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ < δx ∧ δ < δy ∧ a < x - δ ∧ y + δ < b := by
    have hm := lt_min (lt_min hδx hδy) (lt_min (sub_pos.2 hx.1) (sub_pos.2 hy.2))
    have h1 := min_le_left (min δx δy) (min (x - a) (b - y))
    have h2 := min_le_right (min δx δy) (min (x - a) (b - y))
    have h3 := min_le_left δx δy
    have h4 := min_le_right δx δy
    have h5 := min_le_left (x - a) (b - y)
    have h6 := min_le_right (x - a) (b - y)
    exact ⟨min (min δx δy) (min (x - a) (b - y)) / 2, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩
  -- a normalized bump `ρ` supported in `[-δ, δ]`
  let β : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by linarith, by linarith⟩
  set ρ : ℝ → ℝ := β.normed volume with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := β.contDiff_normed
  have hρc : Continuous ρ := hρ.continuous
  have hρ_nonneg : ∀ t, 0 ≤ ρ t := fun t ↦ β.nonneg_normed t
  have hρ1 : ∫ t, ρ t = 1 := β.integral_normed
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport β.hasCompactSupport_normed
  have hρ0 : ∀ t, δ ≤ |t| → ρ t = 0 := fun t ht ↦ by
    apply Function.notMem_support.1
    rw [hρ_def, β.support_normed_eq, mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact ht
  -- its primitive `G`, a smooth nondecreasing step from `0` to `1`
  set G : ℝ → ℝ := fun t ↦ ∫ s in (-δ)..t, ρ s with hG_def
  have hG : ∀ t, HasDerivAt G (ρ t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hρc.intervalIntegrable _ _)
      (hρc.stronglyMeasurableAtFilter _ _) hρc.continuousAt
  have hGd : deriv G = ρ := funext fun t ↦ (hG t).deriv
  have hGs : ContDiff ℝ ∞ G :=
    contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hG t).differentiableAt, hGd ▸ hρ⟩
  have hGmono : Monotone G := monotone_of_deriv_nonneg (fun t ↦ (hG t).differentiableAt)
    fun t ↦ by rw [hGd]; exact hρ_nonneg t
  have hG0 : ∀ t, t ≤ -δ → G t = 0 := by
    intro t ht
    simp only [hG_def]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge ht] at hs
    exact hρ0 s (by rw [abs_of_neg (by linarith [hs.2])]; linarith [hs.2])
  have hG1 : ∀ t, δ ≤ t → G t = 1 := by
    intro t ht
    have hc : ∀ s, s ∉ Ioc (-δ) t → ρ s = 0 := by
      intro s hs
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
      refine hρ0 s ?_
      rcases hs with hs | hs
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    simp only [hG_def]
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero hc, hρ1]
  -- the test function `ψ = G (· - x) - G (· - y)`, a mollified indicator of `[x, y]`
  set ψ : ℝ → ℝ := fun t ↦ G (t - x) - G (t - y) with hψ_def
  have hψd : ∀ t, HasDerivAt ψ (ρ (t - x) - ρ (t - y)) t := fun t ↦
    ((hG (t - x)).comp_sub_const t x).sub ((hG (t - y)).comp_sub_const t y)
  have hψs : ContDiff ℝ ∞ ψ :=
    (hGs.comp (contDiff_id.sub contDiff_const)).sub (hGs.comp (contDiff_id.sub contDiff_const))
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t ↦ sub_nonneg.2 (hGmono (by linarith))
  have hψsupp : tsupport ψ ⊆ Ioo a b := by
    refine (closure_minimal (fun t ht ↦ ?_) isClosed_Icc).trans (Icc_subset_Ioo hxa hyb)
    rw [Function.mem_support] at ht
    by_contra hti
    rw [mem_Icc, not_and_or, not_le, not_le] at hti
    refine ht ?_
    rcases hti with hti | hti
    · simp only [hψ_def, hG0 _ (by linarith : t - x ≤ -δ), hG0 _ (by linarith : t - y ≤ -δ),
        sub_self]
    · simp only [hψ_def, hG1 _ (by linarith : δ ≤ t - x), hG1 _ (by linarith : δ ≤ t - y),
        sub_self]
  -- integrability of `ρ (· - c) * f`
  have hsuppc : ∀ c, tsupport (fun t ↦ ρ (t - c)) ⊆ Icc (c - δ) (c + δ) := fun c ↦ by
    refine closure_minimal (fun t ht ↦ ?_) isClosed_Icc
    rw [Function.mem_support] at ht
    by_contra hti
    refine ht (hρ0 _ ?_)
    rw [mem_Icc, not_and_or, not_le, not_le] at hti
    rcases hti with hti | hti
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hint : ∀ c, Icc (c - δ) (c + δ) ⊆ Ioo a b → Integrable (fun t ↦ ρ (t - c) * f t) := by
    intro c hc
    have hcont : Continuous fun t ↦ ρ (t - c) := hρc.comp (continuous_id.sub continuous_const)
    have hcs : HasCompactSupport fun t ↦ ρ (t - c) :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hsuppc c)
    exact ((hcont.continuousOn.mul hf).continuous_of_tsupport_subset isOpen_Ioo
      (tsupport_mul_subset_left.trans ((hsuppc c).trans hc))).integrable_of_hasCompactSupport
      hcs.mul_right
  have hIx : Icc (x - δ) (x + δ) ⊆ Ioo a b := Icc_subset_Ioo hxa (by linarith)
  have hIy : Icc (y - δ) (y + δ) ⊆ Ioo a b := Icc_subset_Ioo (by linarith) hyb
  have hmass : ∀ c, ∫ t, ρ (t - c) = 1 := fun c ↦ by
    rw [integral_sub_right_eq_self (fun t ↦ ρ t) c, hρ1]
  -- `∫ ρ (· - x) f ≥ f x - η / 2` and `∫ ρ (· - y) f ≤ f y + η / 2`
  have hlow : f x - η / 2 ≤ ∫ t, ρ (t - x) * f t := by
    calc f x - η / 2 = ∫ t, ρ (t - x) * (f x - η / 2) := by rw [integral_mul_const, hmass, one_mul]
      _ ≤ ∫ t, ρ (t - x) * f t := by
        refine integral_mono ((hρi.comp_sub_right x).mul_const _) (hint x hIx) fun t ↦ ?_
        by_cases ht : |t - x| < δ
        · refine mul_le_mul_of_nonneg_left ?_ (hρ_nonneg _)
          have := hfx (show dist t x < δx by rw [Real.dist_eq]; linarith)
          rw [Real.dist_eq, abs_lt] at this
          linarith
        · simp [hρ0 _ (not_lt.1 ht)]
  have hup : ∫ t, ρ (t - y) * f t ≤ f y + η / 2 := by
    calc ∫ t, ρ (t - y) * f t ≤ ∫ t, ρ (t - y) * (f y + η / 2) := by
          refine integral_mono (hint y hIy) ((hρi.comp_sub_right y).mul_const _) fun t ↦ ?_
          by_cases ht : |t - y| < δ
          · refine mul_le_mul_of_nonneg_left ?_ (hρ_nonneg _)
            have := hfy (show dist t y < δy by rw [Real.dist_eq]; linarith)
            rw [Real.dist_eq, abs_lt] at this
            linarith
          · simp [hρ0 _ (not_lt.1 ht)]
      _ = f y + η / 2 := by rw [integral_mul_const, hmass, one_mul]
  have hmid := h ψ hψs hψ0 hψsupp
  have hdψ : deriv ψ = fun t ↦ ρ (t - x) - ρ (t - y) := funext fun t ↦ (hψd t).deriv
  simp only [hdψ, sub_mul] at hmid
  rw [integral_sub (hint x hIx) (hint y hIy), sub_nonpos] at hmid
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ} {R : ℝ}
  {U : Set E}

/-- `u` is weakly subharmonic in `U` (for the measure `μ`): `0 ≤ ∫ u Δχ ∂μ` for every nonnegative
smooth `χ : E → ℝ` with compact support in `U`. -/
def WeaklySubharmonicOn (μ : Measure E) (u : E → ℝ) (U : Set E) : Prop :=
  ∀ χ : E → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U → (∀ x, 0 ≤ χ x) →
    0 ≤ ∫ x, u x * Δ χ x ∂μ

/-- Weak subharmonicity is translation invariant. -/
theorem weaklySubharmonic_comp_add_right (hu : WeaklySubharmonicOn μ u U) (x₀ : E) :
    WeaklySubharmonicOn μ (fun y ↦ u (y + x₀)) ((· + x₀) ⁻¹' U) := by
  intro χ hχ hχc hχU hχ0
  set χ' : E → ℝ := fun z ↦ χ (z + -x₀) with hχ'_def
  have hχ' : ContDiff ℝ ∞ χ' := hχ.comp (contDiff_id.add contDiff_const)
  have htsupp : tsupport χ' = (· + -x₀) ⁻¹' tsupport χ :=
    tsupport_comp_eq_preimage χ (Homeomorph.addRight (-x₀))
  have hχ'c : HasCompactSupport χ' := hχc.comp_homeomorph (Homeomorph.addRight (-x₀))
  have hχ'U : tsupport χ' ⊆ U := by
    rw [htsupp]
    intro z hz
    simpa using hχU hz
  have h := hu χ' hχ' hχ'c hχ'U fun z ↦ hχ0 _
  rw [hχ'_def, Analysis.laplacian_comp_add_right χ (-x₀)] at h
  rw [← integral_add_right_eq_self _ x₀] at h
  simpa using h

variable [Nontrivial E]

/-- The distributional derivative of the sphere integrals `Φ s = ∫ θ, u (s • θ) ∂μ.toSphere` of a
continuous weakly subharmonic function is nonnegative on `(0, R)`: `∫ ψ' Φ ≤ 0` for every
nonnegative test function `ψ` on `(0, R)`. -/
theorem integral_deriv_mul_integral_toSphere_nonpos (hU : IsOpen U)
    (hcont : ContinuousOn u U) (hu : WeaklySubharmonicOn μ u U) (hΩ : closedBall (0 : E) R ⊆ U)
    (hR : 0 < R) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ∀ s, 0 ≤ ψ s)
    (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∫ s, deriv ψ s * ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere ≤ 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hψz : ∀ r, r ∉ Ioo (0 : ℝ) R → ψ r = 0 := fun r hr ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hr (hψs h)
  -- The radial profile `σ ≥ 0`, chosen so that `ψ s = s ^ n * σ (s ^ 2)` for `s > 0`.
  set σ : ℝ → ℝ := fun t ↦ ψ (√t) / (√t) ^ Module.finrank ℝ E with hσ_def
  have hσ_nonneg : ∀ t, 0 ≤ σ t := fun t ↦
    div_nonneg (hψ0 _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hσ0 : ∀ t, R ^ 2 ≤ t → σ t = 0 := by
    intro t ht
    have : R ≤ √t := by
      rw [← Real.sqrt_sq hR.le]
      exact Real.sqrt_le_sqrt ht
    simp [hσ_def, hψz (√t) fun h ↦ h.2.not_ge this]
  have hσ : ContDiff ℝ ∞ σ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : √t ∈ tsupport ψ
    · have ht0 : 0 < t := Real.sqrt_pos.mp (hψs ht).1
      exact ((hψ.contDiffAt.comp t (Real.contDiffAt_sqrt ht0.ne')).div
        ((Real.contDiffAt_sqrt ht0.ne').pow _) (pow_ne_zero _ (Real.sqrt_pos.mpr ht0).ne'))
    · have hev : ∀ᶠ s in 𝓝 t, σ s = 0 := by
        have : ∀ᶠ s in 𝓝 t, √s ∉ tsupport ψ :=
          Real.continuous_sqrt.continuousAt.preimage_mem_nhds
            ((isClosed_tsupport ψ).isOpen_compl.mem_nhds ht)
        filter_upwards [this] with s hs
        simp [hσ_def, image_eq_zero_of_notMem_tsupport hs]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  have hσc : Continuous σ := hσ.continuous
  -- The nonnegative profile `ρ t = ∫_t^{R²} σ`, vanishing beyond `R ^ 2`.
  set ρ : ℝ → ℝ := fun t ↦ ∫ s in t..R ^ 2, σ s with hρ_def
  have hρderiv : ∀ t, HasDerivAt ρ (-σ t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_left (hσc.intervalIntegrable _ _)
      (hσc.stronglyMeasurableAtFilter _ _) hσc.continuousAt
  have hρ' : deriv ρ = fun t ↦ -σ t := funext fun t ↦ (hρderiv t).deriv
  have hρ : ContDiff ℝ ∞ ρ :=
    contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hρderiv t).differentiableAt, hρ' ▸ hσ.neg⟩
  have hρ0 : ∀ t, R ^ 2 ≤ t → ρ t = 0 := by
    intro t ht
    simp only [hρ_def]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge ht] at hs
    exact hσ0 s hs.1
  have hρ_nonneg : ∀ t, 0 ≤ ρ t := by
    intro t
    by_cases ht : t ≤ R ^ 2
    · exact intervalIntegral.integral_nonneg ht fun s _ ↦ hσ_nonneg s
    · exact (hρ0 t (not_le.mp ht).le).ge
  -- The nonnegative radial test function `χ x = ρ (‖x‖ ^ 2)`, supported in the closed ball.
  set χ : E → ℝ := fun x ↦ ρ (‖x‖ ^ 2) with hχ
  have hχ_supp : tsupport χ ⊆ closedBall (0 : E) R := by
    refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
    rw [mem_ball_zero_iff]
    by_contra h
    exact hx (hρ0 _ (pow_le_pow_left₀ hR.le (not_lt.mp h) 2))
  have hχs : ContDiff ℝ ∞ χ := hρ.comp (contDiff_norm_sq ℝ)
  have hχc : HasCompactSupport χ :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hχ_supp
  have hΔ : Δ χ = fun x ↦
      -(4 * ‖x‖ ^ 2 * deriv σ (‖x‖ ^ 2) + 2 * (Module.finrank ℝ E : ℝ) * σ (‖x‖ ^ 2)) := by
    funext x
    rw [hχ, (hρ.of_le (by norm_cast)).laplacian_comp_norm_sq, hρ', deriv.fun_neg]
    ring
  -- Weak subharmonicity against `χ`, in polar coordinates.
  have hgreen := hu χ hχs hχc (hχ_supp.trans hΩ) fun x ↦ hρ_nonneg _
  have hΔcont : Continuous (Δ χ) := by
    rw [hΔ]
    have hσ' : Continuous (deriv σ) := hσ.continuous_deriv (by simp)
    fun_prop
  have hf_cont : Continuous fun x ↦ u x * Δ χ x :=
    (hcont.mul hΔcont.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans
        ((Analysis.tsupport_laplacian_subset _).trans (hχ_supp.trans hΩ)))
  have hf_supp : HasCompactSupport fun x ↦ u x * Δ χ x :=
    (HasCompactSupport.intro hχc fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (Analysis.tsupport_laplacian_subset _ h)).mul_left
  rw [Analysis.integral_eq_integral_Ioi_integral_toSphere _
    (hf_cont.integrable_of_hasCompactSupport hf_supp)] at hgreen
  -- On the sphere of radius `s`, the weight is `-2 ψ' s`.
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) * Δ χ (s • (θ : E)) ∂μ.toSphere =
        (-2) * (deriv ψ s * ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere) := by
    intro s hs
    have hs : 0 < s := hs
    have hnorm : ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun θ ↦ by
      rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    have hΔs : ∀ θ : sphere (0 : E) 1, Δ χ (s • (θ : E)) =
        -(4 * s ^ 2 * deriv σ (s ^ 2) + 2 * (Module.finrank ℝ E : ℝ) * σ (s ^ 2)) := fun θ ↦ by
      rw [hΔ]
      dsimp only
      rw [hnorm]
    simp_rw [hΔs]
    rw [integral_mul_const, smul_eq_mul]
    have hψeq : ψ =ᶠ[𝓝 s] fun r ↦ r ^ Module.finrank ℝ E * σ (r ^ 2) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      have hr : 0 < r := hr
      simp only [hσ_def, Real.sqrt_sq hr.le]
      rw [mul_div_cancel₀ _ (pow_ne_zero _ hr.ne')]
    have hd : HasDerivAt (fun r ↦ r ^ Module.finrank ℝ E * σ (r ^ 2))
        ((Module.finrank ℝ E : ℝ) * s ^ (Module.finrank ℝ E - 1) * σ (s ^ 2) +
          s ^ Module.finrank ℝ E * (deriv σ (s ^ 2) * ((2 : ℕ) * s ^ (2 - 1)))) s :=
      (hasDerivAt_pow _ s).mul ((hσ.differentiable (by simp) _).hasDerivAt.comp s
        (hasDerivAt_pow 2 s))
    rw [hψeq.deriv_eq, hd.deriv, hm]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_, integral_const_mul] at hgreen
  · linarith
  · have : deriv ψ s = 0 := by
      by_contra h
      exact hs (hψs (support_deriv_subset h)).1
    simp [this]

/-- The sub-mean-value property on spheres about the origin. -/
theorem integral_toSphere_ge_of_weaklySubharmonic_zero (hU : IsOpen U)
    (hcont : ContinuousOn u U) (hu : WeaklySubharmonicOn μ u U) (hΩ : closedBall (0 : E) R ⊆ U)
    (hR : 0 ≤ R) :
    μ.toSphere.real univ * u 0 ≤ ∫ θ : sphere (0 : E) 1, u (R • (θ : E)) ∂μ.toSphere := by
  rcases hR.eq_or_lt with rfl | hR
  · simp [integral_const]
  set Φ : ℝ → ℝ := fun s ↦ ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere with hΦ_def
  have hΦc : ContinuousOn Φ (Icc 0 R) :=
    Analysis.continuousOn_integral_toSphere_smul (hcont.mono hΩ)
  have hmono : MonotoneOn Φ (Ioo 0 R) :=
    monotoneOn_of_integral_deriv_mul_nonpos (hΦc.mono Ioo_subset_Icc_self)
      fun ψ hψ hψ0 hψs ↦ integral_deriv_mul_integral_toSphere_nonpos hU hcont hu hΩ hR hψ hψ0 hψs
  have hc : R / 2 ∈ Ioo 0 R := ⟨by linarith, by linarith⟩
  have h0 : Φ 0 ≤ Φ (R / 2) := by
    refine ContinuousWithinAt.closure_le (s := Ioo 0 (R / 2)) ?_
      ((hΦc 0 ⟨le_rfl, hR.le⟩).mono ?_) continuousWithinAt_const
      fun t ht ↦ hmono ⟨ht.1, by linarith [ht.2]⟩ hc ht.2.le
    · rw [closure_Ioo (by linarith : (0 : ℝ) ≠ R / 2)]
      exact ⟨le_rfl, by linarith⟩
    · exact Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))
  have h1 : Φ (R / 2) ≤ Φ R := by
    refine ContinuousWithinAt.closure_le (s := Ioo (R / 2) R) ?_ continuousWithinAt_const
      ((hΦc R ⟨hR.le, le_rfl⟩).mono ?_) fun t ht ↦ hmono hc ⟨by linarith [ht.1], ht.2⟩ ht.1.le
    · rw [closure_Ioo (by linarith : R / 2 ≠ R)]
      exact ⟨by linarith, le_rfl⟩
    · exact Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl)
  have hΦ0 : Φ 0 = μ.toSphere.real univ * u 0 := by simp [hΦ_def, integral_const]
  change μ.toSphere.real univ * u 0 ≤ Φ R
  linarith

/-- **The sub-mean-value property on spheres** for a continuous weakly subharmonic function: if
`closedBall x₀ R ⊆ U` and `0 ≤ R`, the integral of `u` over the sphere of radius `R` about `x₀`,
parametrized by the unit sphere with the surface measure `μ.toSphere`, is at least the total
surface measure times `u x₀`. -/
theorem integral_toSphere_ge_of_weaklySubharmonic (hU : IsOpen U) (hcont : ContinuousOn u U)
    (hu : WeaklySubharmonicOn μ u U) {x₀ : E} (hΩ : closedBall x₀ R ⊆ U) (hR : 0 ≤ R) :
    μ.toSphere.real univ * u x₀ ≤ ∫ θ : sphere (0 : E) 1, u (x₀ + R • (θ : E)) ∂μ.toSphere := by
  have hU' : IsOpen ((· + x₀) ⁻¹' U) := hU.preimage (continuous_id.add continuous_const)
  have hcont' : ContinuousOn (fun y ↦ u (y + x₀)) ((· + x₀) ⁻¹' U) :=
    hcont.comp (continuous_id.add continuous_const).continuousOn fun y hy ↦ hy
  have hΩ' : closedBall (0 : E) R ⊆ (· + x₀) ⁻¹' U := fun y hy ↦ hΩ (by
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    simpa using hy)
  have h := integral_toSphere_ge_of_weaklySubharmonic_zero hU' hcont'
    (weaklySubharmonic_comp_add_right hu x₀) hΩ' hR
  simpa [add_comm] using h

/-- **The sub-mean-value property on balls** for a continuous weakly subharmonic function: if
`closedBall x₀ R ⊆ U`, then `μ(B_R(x₀)) u(x₀) ≤ ∫_{B_R(x₀)} u ∂μ`. -/
theorem mul_le_setIntegral_ball_of_weaklySubharmonic (hU : IsOpen U) (hcont : ContinuousOn u U)
    (hu : WeaklySubharmonicOn μ u U) {x₀ : E} (hΩ : closedBall x₀ R ⊆ U) :
    μ.real (ball x₀ R) * u x₀ ≤ ∫ y in ball x₀ R, u y ∂μ := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.mpr hR]
  -- recentre at the origin
  have htrans : ∫ y in ball x₀ R, u y ∂μ = ∫ y in ball (0 : E) R, u (x₀ + y) ∂μ := by
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← integral_add_left_eq_self _ x₀]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    classical
    simp only [indicator_apply, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hmem : ∀ y ∈ closedBall (0 : E) R, x₀ + y ∈ closedBall x₀ R := fun y hy ↦ by
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    simpa using hy
  set v : E → ℝ := fun y ↦ u (x₀ + y) with hv
  have hvcont : ContinuousOn v (closedBall (0 : E) R) :=
    (hcont.mono hΩ).comp (continuous_const.add continuous_id).continuousOn hmem
  have hvint : IntegrableOn v (ball (0 : E) R) μ :=
    (hvcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hcint : IntegrableOn (fun _ ↦ u x₀) (ball (0 : E) R) μ :=
    integrableOn_const measure_ball_lt_top.ne
  rw [htrans, Measure.addHaar_real_ball_center, ← smul_eq_mul, ← setIntegral_const, ← sub_nonneg,
    ← integral_sub hvint hcint, ← integral_indicator measurableSet_ball]
  -- in polar coordinates, the integrand is nonnegative on each sphere
  set w : E → ℝ := (ball (0 : E) R).indicator fun y ↦ v y - u x₀ with hw
  have hwint : Integrable w μ := (hvint.sub hcint).integrable_indicator measurableSet_ball
  rw [Analysis.integral_eq_integral_Ioi_integral_toSphere _ hwint]
  refine setIntegral_nonneg measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
  refine smul_nonneg (pow_nonneg hs.le _) ?_
  have hmemb : ∀ θ : sphere (0 : E) 1, s • (θ : E) ∈ ball (0 : E) R ↔ s < R := fun θ ↦ by
    rw [mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
  by_cases hsR : s < R
  · simp_rw [hw, indicator_of_mem ((hmemb _).mpr hsR)]
    have hθc : Continuous fun θ : sphere (0 : E) 1 ↦ v (s • (θ : E)) :=
      hvcont.comp_continuous (continuous_const.smul continuous_subtype_val) fun θ ↦ by
        rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one,
          Real.norm_of_nonneg hs.le]
        exact hsR.le
    rw [integral_sub (hθc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const _), integral_const, smul_eq_mul, sub_nonneg]
    exact integral_toSphere_ge_of_weaklySubharmonic hU hcont hu
      ((closedBall_subset_closedBall hsR.le).trans hΩ) hs.le
  · simp_rw [hw, indicator_of_notMem ((not_congr (hmemb _)).mpr hsR)]
    simp

end InnerVariational.Vendor
