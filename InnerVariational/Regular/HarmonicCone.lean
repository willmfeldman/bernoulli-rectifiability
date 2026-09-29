/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.Harmonic
public import InnerVariational.Registry.Sobolev
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
public import GMTFoundations.Defs.Setup

/-!
# A harmonic cone containing a half-space is the half-space

Let `u₀ ≥ 0` be Lipschitz and one-homogeneous on `ℝⁿ`, and harmonic on a connected component `U`
of `{u₀ > 0}`. If `U` contains the open half-space `H = {⟪y, e⟫ > 0}`, then `U = H`
(`connectedComponentIn_eq_halfSpace`). This is the step "`U` contains a half-sphere, hence is a
half-sphere" in the proof of Lemma 8.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite
Hausdorff measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl.
Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). The
paper obtains this step from domain monotonicity of the first Dirichlet eigenvalue on the
sphere. We give an elementary proof instead.

## Proof

Normalize `|e| = 1` and write `e(y) = ⟪y, e⟫`. It suffices to show `u₀ = 0` on `∂H`: then `U`
lies in `H ∪ {e < 0}`, and it is connected and meets `H`.

`u₀` and `e` are harmonic on `H`, and `u₀` satisfies Euler's identity `⟪∇u₀(y), y⟫ = u₀(y)`. Let
`ψ(y) = η(|y|²)` be a radial cutoff and `σ_ε(y) = θ(e(y)/ε − 1)` with `θ` the smooth step. Testing
`Δu₀ = 0` against `e σ_ε ψ` and integrating `∂_e (u₀ σ_ε ψ)` over `ℝⁿ` gives, after the radial terms
cancel by Euler's identity,
`∫ θ'(e/ε − 1) ψ (u₀ − e ∂_e u₀) = 0` (`integral_deriv_cutoff_mul_eq_zero`).
This is Green's identity for `u₀` and `e` on `H`, with the boundary term written as a limit.
The linear change of variables `y = z + (ε − 1) e(z) e` turns this into
`∫ θ'(e(z) − 1) ψ(T_ε z) F(T_ε z) dz = 0`, and as `ε → 0` dominated convergence gives
`∫ θ'(e(z) − 1) ψ(z') u₀(z') dz = 0` with `z' = z − e(z) e`. The integrand is continuous,
nonnegative, compactly supported, and positive near `y₀ + (1 + c) e` if `u₀(y₀) > 0` at some
`y₀ ∈ ∂H`. So `u₀ = 0` on `∂H`. No surface integrals and no Fubini are needed.
-/

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-! ### Euler's identity and the smooth step -/

/-- **Euler's identity**: a one-homogeneous function differentiable at `y` has
`Df(y) y = f(y)`. -/
theorem fderiv_apply_self_eq_of_homogeneous {f : Rn n → ℝ}
    (hhom : ∀ y (t : ℝ), 0 < t → f (t • y) = t * f y) {y : Rn n}
    (hd : DifferentiableAt ℝ f y) : fderiv ℝ f y y = f y := by
  have hs : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have hd' : HasFDerivAt f (fderiv ℝ f y) ((1 : ℝ) • y) := by
    rw [one_smul]; exact hd.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => f (t • y)) (fderiv ℝ f y y) 1 :=
    hd'.comp_hasDerivAt (1 : ℝ) hs
  have h2 : HasDerivAt (fun t : ℝ => f (t • y)) (f y) 1 := by
    have : HasDerivAt (fun t : ℝ => t * f y) (f y) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (f y)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds one_pos] with t ht using hhom y t ht
  exact h1.unique h2

/-- The smooth step has derivative `1` somewhere in `(0, 1)`. -/
theorem exists_deriv_smoothTransition_eq_one :
    ∃ c ∈ Ioo (0 : ℝ) 1, deriv Real.smoothTransition c = 1 := by
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope Real.smoothTransition zero_lt_one
    Real.smoothTransition.continuous.continuousOn
    fun x _ => (Kernel.hasDerivAt_smoothTransition x).differentiableAt.differentiableWithinAt
  refine ⟨c, hc, ?_⟩
  rw [hdc, Real.smoothTransition.one, Real.smoothTransition.zero]
  norm_num

/-- The derivative of the smooth step is bounded. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ D : ℝ, ∀ s, |deriv Real.smoothTransition s| ≤ D := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨D, fun s => ?_⟩
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · rw [← Real.norm_eq_abs]; exact hD s hs
  · have : s < 0 ∨ 1 < s := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hs; exact hs
    rw [Kernel.deriv_smoothTransition_eq_zero this, abs_zero]
    exact (norm_nonneg _).trans (hD 0 ⟨le_rfl, zero_le_one⟩)

/-! ### A shear along `e` -/

/-- The linear map `z ↦ z + (ε − 1) ⟪z, e⟫ e` for a unit vector `e`, which scales the
`e`-component by `ε`. -/
def stretchEquiv {e : Rn n} (he : ‖e‖ = 1) {ε : ℝ} (hε : ε ≠ 0) : Rn n ≃ₗ[ℝ] Rn n where
  toFun z := z + ((ε - 1) * ⟪z, e⟫) • e
  invFun z := z + ((ε⁻¹ - 1) * ⟪z, e⟫) • e
  map_add' a b := by
    simp only [inner_add_left, mul_add, add_smul]
    abel
  map_smul' c a := by
    simp only [real_inner_smul_left, smul_add, smul_smul, RingHom.id_apply]
    congr 2
    ring
  left_inv z := by
    have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    simp only [inner_add_left, real_inner_smul_left, hee, add_assoc, ← add_smul]
    have : (ε - 1) * ⟪z, e⟫ + (ε⁻¹ - 1) * (⟪z, e⟫ + (ε - 1) * ⟪z, e⟫ * 1) = 0 := by
      field_simp
      ring
    rw [this, zero_smul, add_zero]
  right_inv z := by
    have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    simp only [inner_add_left, real_inner_smul_left, hee, add_assoc, ← add_smul]
    have : (ε⁻¹ - 1) * ⟪z, e⟫ + (ε - 1) * (⟪z, e⟫ + (ε⁻¹ - 1) * ⟪z, e⟫ * 1) = 0 := by
      field_simp
      ring
    rw [this, zero_smul, add_zero]

theorem stretchEquiv_apply {e : Rn n} (he : ‖e‖ = 1) {ε : ℝ} (hε : ε ≠ 0) (z : Rn n) :
    stretchEquiv he hε z = z + ((ε - 1) * ⟪z, e⟫) • e := rfl

theorem inner_stretchEquiv {e : Rn n} (he : ‖e‖ = 1) {ε : ℝ} (hε : ε ≠ 0) (z : Rn n) :
    ⟪stretchEquiv he hε z, e⟫ = ε * ⟪z, e⟫ := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  rw [stretchEquiv_apply, inner_add_left, real_inner_smul_left, hee]
  ring

/-- A linear change of variables preserves vanishing integrals. -/
theorem integral_comp_stretchEquiv_eq_zero {e : Rn n} (he : ‖e‖ = 1) {ε : ℝ} (hε : ε ≠ 0)
    {f : Rn n → ℝ} (hf : ∫ y, f y = 0) : ∫ z, f (stretchEquiv he hε z) = 0 := by
  set T := stretchEquiv he hε
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Rn n)))
    (f := (T : Rn n →ₗ[ℝ] Rn n)) (LinearEquiv.isUnit_det' T).ne_zero
  rw [LinearEquiv.coe_coe] at hmap
  have hemb : MeasurableEmbedding (T : Rn n → Rn n) :=
    T.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have := hemb.integral_map (μ := volume) f
  rw [hmap, integral_smul_measure, hf, smul_zero] at this
  exact this.symm

/-! ### The Green identity with a cutoff -/

/-- **Green's identity for `u₀` and `⟪y, e⟫` on `H = {⟪y, e⟫ > 0}`, cut off at `⟪y, e⟫ ≈ ε`.**
Let `u₀` be `L`-Lipschitz, `C²` and harmonic on `H`, with Euler's identity on `H`, and let
`ψ(y) = η(|y|²)` with `η` smooth and compactly supported. Then
`∫ θ'(ε⁻¹ ⟪y, e⟫ − 1) ψ(y) (u₀(y) − ⟪y, e⟫ ∂_e u₀(y)) dy = 0`, where `θ` is the smooth step. -/
theorem integral_deriv_cutoff_mul_eq_zero {e : Rn n} (he : ‖e‖ = 1) {u₀ : Rn n → ℝ}
    {L : ℝ≥0} (hLip : LipschitzWith L u₀)
    (hC2 : ContDiffOn ℝ 2 u₀ {y | 0 < ⟪y, e⟫})
    (hΔ : ∀ y, 0 < ⟪y, e⟫ → Δ u₀ y = 0)
    (hEuler : ∀ y, 0 < ⟪y, e⟫ → fderiv ℝ u₀ y y = u₀ y)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, deriv Real.smoothTransition (ε⁻¹ * ⟪y, e⟫ - 1) * η (‖y‖ ^ 2) *
      (u₀ y - ⟪y, e⟫ * fderiv ℝ u₀ y e) = 0 := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  set H := {y : Rn n | 0 < ⟪y, e⟫} with hHdef
  have hHo : IsOpen H := isOpen_lt continuous_const (continuous_id.inner continuous_const)
  set s : Rn n → ℝ := fun y => ε⁻¹ * ⟪y, e⟫ - 1 with hsdef
  set ψ : Rn n → ℝ := fun y => η (‖y‖ ^ 2) with hψdef
  set ζ : Rn n → ℝ := fun y => Real.smoothTransition (s y) * ψ y with hζdef
  set g : Rn n → ℝ := fun y => ⟪y, e⟫ * ζ y with hgdef
  -- derivatives
  have hinner : ∀ y, HasFDerivAt (fun y : Rn n => ⟪y, e⟫) (innerSL ℝ e) y := fun y =>
    (innerSL ℝ e).hasFDerivAt.congr_of_eventuallyEq
      (.of_forall fun z => by simp [real_inner_comm])
  have hs : ∀ y, HasFDerivAt s (ε⁻¹ • innerSL ℝ e) y := fun y =>
    ((hinner y).const_mul ε⁻¹).sub_const 1
  have hσ : ∀ y, HasFDerivAt (fun y => Real.smoothTransition (s y))
      (deriv Real.smoothTransition (s y) • ε⁻¹ • innerSL ℝ e) y := fun y =>
    (Kernel.hasDerivAt_smoothTransition (s y)).comp_hasFDerivAt y (hs y)
  have hηd : ∀ t, HasDerivAt η (deriv η t) t := fun t =>
    ((hη.differentiable (by simp)) t).hasDerivAt
  have hψ : ∀ y, HasFDerivAt ψ (deriv η (‖y‖ ^ 2) • (2 : ℝ) • innerSL ℝ y) y := fun y =>
    (hηd _).comp_hasFDerivAt y (by
      simpa only [two_smul, two_nsmul] using (hasStrictFDerivAt_norm_sq y).hasFDerivAt)
  have hζ : ∀ y, HasFDerivAt ζ (Real.smoothTransition (s y) •
      (deriv η (‖y‖ ^ 2) • (2 : ℝ) • innerSL ℝ y) +
      ψ y • (deriv Real.smoothTransition (s y) • ε⁻¹ • innerSL ℝ e)) y := fun y =>
    (hσ y).mul (hψ y)
  have hζapp : ∀ y v, fderiv ℝ ζ y v = Real.smoothTransition (s y) *
      (deriv η (‖y‖ ^ 2) * (2 * ⟪y, v⟫)) +
      ψ y * (deriv Real.smoothTransition (s y) * (ε⁻¹ * ⟪e, v⟫)) := fun y v => by
    rw [(hζ y).fderiv]
    simp [smul_eq_mul]
  have hg : ∀ y, HasFDerivAt g (⟪y, e⟫ • fderiv ℝ ζ y + ζ y • innerSL ℝ e) y := fun y =>
    (hinner y).mul (hζ y).differentiableAt.hasFDerivAt
  have hgapp : ∀ y v, fderiv ℝ g y v = ⟪y, e⟫ * fderiv ℝ ζ y v + ζ y * ⟪e, v⟫ := fun y v => by
    rw [(hg y).fderiv]
    simp [smul_eq_mul]
  -- smoothness and supports
  have hsc : ContDiff ℝ ∞ s := (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).sub
    contDiff_const
  have hψs : ContDiff ℝ ∞ ψ := hη.comp (contDiff_norm_sq ℝ)
  have hζs : ContDiff ℝ ∞ ζ := (Real.smoothTransition.contDiff.comp hsc).mul hψs
  have hgs : ContDiff ℝ ∞ g := (contDiff_id.inner ℝ contDiff_const).mul hζs
  obtain ⟨R, hR⟩ : ∃ R, ∀ t, η t ≠ 0 → |t| ≤ R := by
    obtain ⟨R, hR⟩ := hηc.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun t ht => by
      have := hR (subset_tsupport η ht)
      rwa [mem_closedBall, Real.dist_eq, sub_zero] at this⟩
  have hψc : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (1 + R)) fun y hy => ?_
    by_contra hne
    have h1 := hR _ hne
    rw [mem_closedBall, dist_zero_right] at hy
    rw [abs_of_nonneg (sq_nonneg _)] at h1
    nlinarith [norm_nonneg y]
  have hζ0 : ∀ y, ⟪y, e⟫ < ε → ζ y = 0 := fun y hy => by
    have : s y ≤ 0 := by
      simp only [hsdef]
      have : ε⁻¹ * ⟪y, e⟫ < ε⁻¹ * ε := mul_lt_mul_of_pos_left hy (inv_pos.2 hε)
      rw [inv_mul_cancel₀ hε.ne'] at this
      linarith
    simp only [hζdef, Real.smoothTransition.zero_of_nonpos this, zero_mul]
  have hζH : tsupport ζ ⊆ H := by
    have : Function.support ζ ⊆ {y | ε ≤ ⟪y, e⟫} := fun y hy => by
      by_contra h
      exact hy (hζ0 y (not_le.1 h))
    have hcl : IsClosed {y : Rn n | ε ≤ ⟪y, e⟫} :=
      isClosed_le continuous_const (continuous_id.inner continuous_const)
    exact (closure_minimal this hcl).trans fun y hy => lt_of_lt_of_le hε hy
  have hζc : HasCompactSupport ζ := hψc.mul_left
  have hgc : HasCompactSupport g := hζc.mul_left
  have hgH : tsupport g ⊆ H := (tsupport_mul_subset_right).trans hζH
  have hζL : ∃ C, LipschitzWith C ζ := hζs.lipschitzWith_of_hasCompactSupport hζc (by simp)
  obtain ⟨Cg, hgL⟩ : ∃ C, LipschitzWith C g :=
    hgs.lipschitzWith_of_hasCompactSupport hgc (by simp)
  -- the two integrations by parts
  have hB : ∫ y, u₀ y * fderiv ℝ ζ y e = -∫ y, ζ y * fderiv ℝ u₀ y e :=
    Registry.integral_mul_fderiv_eq_neg isOpen_univ hLip.locallyLipschitz.locallyLipschitzOn hζL
      hζc (subset_univ _) e
  have hA : ∫ y, ⟪gradient u₀ y, gradient g y⟫ = 0 := by
    rw [Kernel.integral_inner_gradient_eq_neg_laplacian hHo hC2 ⟨Cg, hgL⟩ hgc hgH]
    have : ∀ y, g y * Δ u₀ y = 0 := fun y => by
      by_cases hy : y ∈ H
      · rw [hΔ y hy, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (fun h' => hy (hgH h')), zero_mul]
    simp [this]
  -- integrability
  have hIB : Integrable fun y => u₀ y * fderiv ℝ ζ y e :=
    (hLip.continuous.mul ((hζs.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (hζc.fderiv_apply (𝕜 := ℝ) e).mul_left
  have hIJ : Integrable fun y => ζ y * fderiv ℝ u₀ y e := by
    obtain ⟨Z, hZ⟩ := hζs.continuous.bounded_above_of_compact_support hζc
    refine Kernel.integrable_of_bound_of_isCompact hζc
      (hζs.continuous.measurable.mul (measurable_fderiv_apply_const ℝ u₀ e)).aestronglyMeasurable
      (M := Z * L) (fun y _ => ?_)
      (fun y hy => by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    rw [norm_mul]
    refine mul_le_mul (hZ y) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hZ y))
    refine ((fderiv ℝ u₀ y).le_opNorm e).trans ?_
    rw [he, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hLip
  have hIA : Integrable fun y => ⟪gradient u₀ y, gradient g y⟫ :=
    Kernel.integrable_of_bound_of_isCompact hgc
      ((measurable_gradient u₀).inner (measurable_gradient g)).aestronglyMeasurable
      (M := L * Cg) (fun y _ => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul
          (Kernel.norm_gradient_le_of_lipschitz hLip y) (Kernel.norm_gradient_le_of_lipschitz hgL y)
          (norm_nonneg _) L.2))
      (fun y hy => by rw [Kernel.gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right])
  -- the pointwise identity
  have hpt : ∀ y, deriv Real.smoothTransition (ε⁻¹ * ⟪y, e⟫ - 1) * η (‖y‖ ^ 2) *
      (u₀ y - ⟪y, e⟫ * fderiv ℝ u₀ y e) = ε * (u₀ y * fderiv ℝ ζ y e +
        ζ y * fderiv ℝ u₀ y e - ⟪gradient u₀ y, gradient g y⟫) := fun y => by
    have hIA' : ⟪gradient u₀ y, gradient g y⟫ = fderiv ℝ g y (gradient u₀ y) := by
      rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
    have hyu : ⟪y, gradient u₀ y⟫ = fderiv ℝ u₀ y y := by
      rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have heu : ⟪e, gradient u₀ y⟫ = fderiv ℝ u₀ y e := by
      rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rw [hIA', hgapp, hζapp, hζapp, hyu, heu, hee]
    by_cases hy : 0 < ⟪y, e⟫
    · rw [hEuler y hy]
      simp only [hζdef, hψdef, hsdef]
      field_simp
      ring
    · have hs0 : s y < 0 := by
        simp only [hsdef]
        have : ε⁻¹ * ⟪y, e⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hε.le)
          (not_lt.1 hy)
        linarith
      have h1 : Real.smoothTransition (s y) = 0 := Real.smoothTransition.zero_of_nonpos hs0.le
      have h2 : deriv Real.smoothTransition (s y) = 0 :=
        Kernel.deriv_smoothTransition_eq_zero (Or.inl hs0)
      have h2' : deriv Real.smoothTransition (ε⁻¹ * ⟪y, e⟫ - 1) = 0 := h2
      simp only [hζdef, h1, h2, h2', zero_mul, mul_zero, add_zero, sub_zero]
  have hsum : ∫ y, (u₀ y * fderiv ℝ ζ y e + ζ y * fderiv ℝ u₀ y e -
      ⟪gradient u₀ y, gradient g y⟫) = 0 := by
    have hIBJ : Integrable fun y => u₀ y * fderiv ℝ ζ y e + ζ y * fderiv ℝ u₀ y e := hIB.add hIJ
    rw [integral_sub hIBJ hIA, integral_add hIB hIJ, hB, hA]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, hsum, mul_zero]

/-! ### Vanishing on the boundary hyperplane -/

theorem isOpen_halfSpace (e : Rn n) : IsOpen {y : Rn n | 0 < ⟪y, e⟫} :=
  isOpen_lt continuous_const (continuous_id.inner continuous_const)

theorem isOpen_halfSpace_neg (e : Rn n) : IsOpen {y : Rn n | ⟪y, e⟫ < 0} :=
  isOpen_lt (continuous_id.inner continuous_const) continuous_const

/-- Where `θ'(t − 1) ≠ 0`, `1 ≤ t ≤ 2`. -/
theorem mem_Icc_of_deriv_smoothTransition_ne_zero {t : ℝ}
    (ht : deriv Real.smoothTransition (t - 1) ≠ 0) : 1 ≤ t ∧ t ≤ 2 := by
  by_contra h
  apply ht
  refine Kernel.deriv_smoothTransition_eq_zero ?_
  rcases not_and_or.1 h with h | h
  · left; linarith [not_le.1 h]
  · right; linarith [not_le.1 h]

/-- `|w| ≤ 1 + |w|²`. -/
theorem norm_le_one_add_sq (w : Rn n) : ‖w‖ ≤ 1 + ‖w‖ ^ 2 := by
  nlinarith [norm_nonneg w, sq_nonneg (‖w‖ - 1)]

/-- **A nonnegative one-homogeneous function, harmonic on a half-space, vanishes on its boundary
hyperplane.** See the module docstring for the proof. -/
theorem eq_zero_of_inner_eq_zero {e : Rn n} (he : ‖e‖ = 1) {u₀ : Rn n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L u₀) (hnn : ∀ y, 0 ≤ u₀ y)
    (hhom : ∀ y (t : ℝ), 0 < t → u₀ (t • y) = t * u₀ y)
    (hharm : ∀ y, 0 < ⟪y, e⟫ → HarmonicAt u₀ y) {y₀ : Rn n} (hy₀ : ⟪y₀, e⟫ = 0) :
    u₀ y₀ = 0 := by
  by_contra hne
  have hpos : 0 < u₀ y₀ := lt_of_le_of_ne (hnn y₀) (Ne.symm hne)
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hC2 : ContDiffOn ℝ 2 u₀ {y | 0 < ⟪y, e⟫} := fun y hy => (hharm y hy).1.contDiffWithinAt
  have hΔ : ∀ y, 0 < ⟪y, e⟫ → Δ u₀ y = 0 := fun y hy => (hharm y hy).2.self_of_nhds
  have hEuler : ∀ y, 0 < ⟪y, e⟫ → fderiv ℝ u₀ y y = u₀ y := fun y hy =>
    fderiv_apply_self_eq_of_homogeneous hhom ((hharm y hy).1.differentiableAt two_ne_zero)
  have hu0 : u₀ 0 = 0 := by
    have := hhom 0 2 two_pos
    rw [smul_zero] at this
    linarith
  have hu₀b : ∀ w, |u₀ w| ≤ L * ‖w‖ := fun w => by
    have := hLip.dist_le_mul w 0
    rwa [Real.dist_eq, hu0, sub_zero, dist_zero_right] at this
  have hfdb : ∀ w, |fderiv ℝ u₀ w e| ≤ L := fun w => by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ u₀ w).le_opNorm e).trans ?_
    rw [he, mul_one]
    exact norm_fderiv_le_of_lipschitz ℝ hLip
  -- the radial cutoff `η`, equal to `1` at `|y₀|²`
  set s₀ := ‖y₀‖ ^ 2 with hs₀
  set η : ContDiffBump s₀ := ⟨1, 2, one_pos, one_lt_two⟩ with hηdef
  have hηs : ContDiff ℝ ∞ (η : ℝ → ℝ) := η.contDiff
  have hηc : HasCompactSupport (η : ℝ → ℝ) := η.hasCompactSupport
  have hη1 : η s₀ = 1 := η.one_of_mem_closedBall (mem_closedBall_self zero_le_one)
  obtain ⟨R, hR⟩ : ∃ R, ∀ t, η t ≠ 0 → |t| ≤ R := by
    obtain ⟨R, hR⟩ := hηc.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun t ht => by
      have := hR (subset_tsupport _ ht)
      rwa [mem_closedBall, Real.dist_eq, sub_zero] at this⟩
  have hηR : ∀ w : Rn n, η (‖w‖ ^ 2) ≠ 0 → ‖w‖ ≤ 1 + R := fun w hw => by
    have := hR _ hw
    rw [abs_of_nonneg (sq_nonneg _)] at this
    linarith [norm_le_one_add_sq w]
  obtain ⟨D, hD⟩ := exists_abs_deriv_smoothTransition_le
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR s₀ (by rw [hη1]; exact one_ne_zero))
  have hK0 : 0 ≤ D * (2 * L * (1 + R)) :=
    mul_nonneg hD0 (mul_nonneg (mul_nonneg zero_le_two L.2) (by linarith))
  have hdnn : ∀ t, 0 ≤ deriv Real.smoothTransition t := fun t =>
    Real.smoothTransition.monotone.deriv_nonneg
  have hdc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  -- the rescaled identities
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hε1 : ∀ k, ε k ≤ 1 := fun k => by
    simp only [hεdef]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set S : ℕ → Rn n → Rn n := fun k => stretchEquiv he (hε k).ne' with hSdef
  have hSapp : ∀ k z, S k z = z + ((ε k - 1) * ⟪z, e⟫) • e := fun k z => rfl
  have hSinner : ∀ k z, ⟪S k z, e⟫ = ε k * ⟪z, e⟫ := fun k z => inner_stretchEquiv he _ z
  set G : ℕ → Rn n → ℝ := fun k z => deriv Real.smoothTransition (⟪z, e⟫ - 1) *
    η (‖S k z‖ ^ 2) * (u₀ (S k z) - ⟪S k z, e⟫ * fderiv ℝ u₀ (S k z) e) with hGdef
  have hG0 : ∀ k, ∫ z, G k z = 0 := by
    intro k
    have h1 := integral_deriv_cutoff_mul_eq_zero he hLip hC2 hΔ hEuler hηs hηc (hε k)
    have h2 := integral_comp_stretchEquiv_eq_zero he (hε k).ne' h1
    refine Eq.trans ?_ h2
    congr 1
    funext z
    simp only [hGdef]
    rw [hSinner, ← mul_assoc, inv_mul_cancel₀ (hε k).ne', one_mul]
  -- the limit
  set z' : Rn n → Rn n := fun z => z - ⟪z, e⟫ • e with hz'def
  set G₀ : Rn n → ℝ := fun z => deriv Real.smoothTransition (⟪z, e⟫ - 1) *
    η (‖z' z‖ ^ 2) * u₀ (z' z) with hG₀def
  have hSlim : ∀ z, Tendsto (fun k => S k z) atTop (𝓝 (z' z)) := fun z => by
    have h := (((hε0.sub_const 1).mul_const ⟪z, e⟫).smul_const e).const_add z
    have heq : z + ((0 - 1) * ⟪z, e⟫) • e = z' z := by
      rw [zero_sub, neg_one_mul, neg_smul, ← sub_eq_add_neg]
    rw [heq] at h
    exact h.congr fun k => (hSapp k z).symm
  have hGlim : ∀ z, Tendsto (fun k => G k z) atTop (𝓝 (G₀ z)) := fun z => by
    have hη' : Tendsto (fun k => η (‖S k z‖ ^ 2)) atTop (𝓝 (η (‖z' z‖ ^ 2))) :=
      (hηs.continuous.tendsto _).comp ((continuous_norm.pow 2).continuousAt.tendsto.comp
        (hSlim z))
    have hu' : Tendsto (fun k => u₀ (S k z)) atTop (𝓝 (u₀ (z' z))) :=
      (hLip.continuous.tendsto _).comp (hSlim z)
    have hsmall : Tendsto (fun k => ⟪S k z, e⟫ * fderiv ℝ u₀ (S k z) e) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) ((hε0.mul_const (|⟪z, e⟫| * L)).trans_eq ?_)
      · rw [hSinner, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hε k), mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hfdb _) (abs_nonneg _))
          (hε k).le
      · rw [zero_mul]
    have := (tendsto_const_nhds (x := deriv Real.smoothTransition (⟪z, e⟫ - 1))).mul
      (hη'.mul (hu'.sub hsmall))
    simpa [hGdef, hG₀def, mul_assoc] using this
  have hGbd : ∀ k z, ‖G k z‖ ≤ (closedBall (0 : Rn n) (3 + R)).indicator
      (fun _ => D * (2 * L * (1 + R))) z := fun k z => by
    by_cases hGz : G k z = 0
    · rw [hGz, norm_zero]
      exact indicator_nonneg (fun _ _ => hK0) z
    · have hd : deriv Real.smoothTransition (⟪z, e⟫ - 1) ≠ 0 := fun h => hGz (by
        simp only [hGdef, h, zero_mul])
      have hηne : η (‖S k z‖ ^ 2) ≠ 0 := fun h => hGz (by simp only [hGdef, h, mul_zero, zero_mul])
      obtain ⟨h1, h2⟩ := mem_Icc_of_deriv_smoothTransition_ne_zero hd
      have hSz := hηR _ hηne
      have hz : z ∈ closedBall (0 : Rn n) (3 + R) := by
        rw [mem_closedBall, dist_zero_right]
        have : z = S k z - ((ε k - 1) * ⟪z, e⟫) • e := by rw [hSapp]; abel
        rw [this]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul,
          abs_of_nonpos (by linarith [hε1 k] : ε k - 1 ≤ 0), abs_of_pos (by linarith : 0 < ⟪z, e⟫)]
        nlinarith [hε k, hε1 k]
      rw [indicator_of_mem hz, Real.norm_eq_abs]
      simp only [hGdef, abs_mul]
      have hη1' : |η (‖S k z‖ ^ 2)| ≤ 1 := by
        rw [abs_of_nonneg η.nonneg]; exact η.le_one
      have hF : |u₀ (S k z) - ⟪S k z, e⟫ * fderiv ℝ u₀ (S k z) e| ≤ 2 * L * (1 + R) := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul]
        have h3 : |⟪S k z, e⟫| ≤ ‖S k z‖ := by
          have := abs_real_inner_le_norm (S k z) e
          rwa [he, mul_one] at this
        have hL : (0 : ℝ) ≤ L := L.2
        nlinarith [hu₀b (S k z), hfdb (S k z), abs_nonneg ⟪S k z, e⟫,
          abs_nonneg (fderiv ℝ u₀ (S k z) e)]
      calc |deriv Real.smoothTransition (⟪z, e⟫ - 1)| * |η (‖S k z‖ ^ 2)| *
            |u₀ (S k z) - ⟪S k z, e⟫ * fderiv ℝ u₀ (S k z) e|
          ≤ D * 1 * (2 * L * (1 + R)) := by
            refine mul_le_mul (mul_le_mul (hD _) hη1' (abs_nonneg _) hD0) hF (abs_nonneg _)
              (by rw [mul_one]; exact hD0)
        _ = D * (2 * L * (1 + R)) := by ring
  have hGmeas : ∀ k, AEStronglyMeasurable (G k) := fun k => by
    have hSc : Continuous (S k) :=
      LinearMap.continuous_of_finiteDimensional (stretchEquiv he (hε k).ne' : Rn n →ₗ[ℝ] Rn n)
    exact ((hdc.comp ((continuous_id.inner continuous_const).sub continuous_const)).mul
      (hηs.continuous.comp ((continuous_norm.pow 2).comp hSc))).aestronglyMeasurable.mul
      ((hLip.continuous.comp hSc).measurable.sub
        (((continuous_id.inner continuous_const).comp hSc).measurable.mul
          ((measurable_fderiv_apply_const ℝ u₀ e).comp hSc.measurable))).aestronglyMeasurable
  have hint0 : ∫ z, G₀ z = 0 := by
    have hlim := tendsto_integral_of_dominated_convergence _ hGmeas
      ((integrableOn_const (isCompact_closedBall (0 : Rn n) (3 + R)).measure_lt_top.ne
        ).integrable_indicator measurableSet_closedBall)
      (fun k => .of_forall (hGbd k)) (.of_forall hGlim)
    simp only [hG0] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- positivity of the limit integral
  obtain ⟨c, hc, hdc1⟩ := exists_deriv_smoothTransition_eq_one
  have hG₀c : Continuous G₀ := by
    have hz'c : Continuous z' := continuous_id.sub
      ((continuous_id.inner continuous_const).smul continuous_const)
    exact ((hdc.comp ((continuous_id.inner continuous_const).sub continuous_const)).mul
      (hηs.continuous.comp ((continuous_norm.pow 2).comp hz'c))).mul (hLip.continuous.comp hz'c)
  have hG₀cs : HasCompactSupport G₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (3 + R)) fun z hz => ?_
    by_contra hGz
    have hd : deriv Real.smoothTransition (⟪z, e⟫ - 1) ≠ 0 := fun h => hGz (by
      simp only [hG₀def, h, zero_mul])
    have hηne : η (‖z' z‖ ^ 2) ≠ 0 := fun h => hGz (by simp only [hG₀def, h, mul_zero, zero_mul])
    obtain ⟨h1, h2⟩ := mem_Icc_of_deriv_smoothTransition_ne_zero hd
    have hz'R := hηR _ hηne
    apply hz
    rw [mem_closedBall, dist_zero_right]
    have : z = z' z + ⟪z, e⟫ • e := by simp only [hz'def]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < ⟪z, e⟫)]
    linarith
  have hG₀nn : 0 ≤ G₀ := fun z =>
    mul_nonneg (mul_nonneg (hdnn _) η.nonneg) (hnn _)
  set z₁ : Rn n := y₀ + (1 + c) • e with hz₁
  have hz₁e : ⟪z₁, e⟫ = 1 + c := by
    rw [hz₁, inner_add_left, real_inner_smul_left, hy₀, hee]; ring
  have hz₁' : z' z₁ = y₀ := by
    simp only [hz'def, hz₁e]
    rw [hz₁]; abel
  have hG₀z₁ : G₀ z₁ ≠ 0 := by
    simp only [hG₀def, hz₁e, hz₁', add_sub_cancel_left, hdc1, ← hs₀, hη1, one_mul]
    exact hpos.ne'
  have := hG₀c.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hG₀cs hG₀nn hG₀z₁
  rw [hint0] at this
  exact lt_irrefl 0 this

/-- **A harmonic cone containing a half-space is the half-space** (proof of Lemma 8.3). Let
`u₀ ≥ 0` be Lipschitz and one-homogeneous on `ℝⁿ`, and let `U` be the connected component of
`{u₀ > 0}` through `y₀`, with `u₀` harmonic on `U`. If `U` contains the open half-space
`{⟪y, e⟫ > 0}`, `e ≠ 0`, then `U` is that half-space. The paper derives this from the domain
monotonicity of the first Dirichlet eigenvalue on the sphere; see the module docstring for the
elementary proof. -/
theorem connectedComponentIn_eq_halfSpace {u₀ : Rn n → ℝ} (hLip : ∃ L, LipschitzWith L u₀)
    (hnn : ∀ y, 0 ≤ u₀ y) (hhom : ∀ y (t : ℝ), 0 < t → u₀ (t • y) = t * u₀ y) {y₀ : Rn n}
    (hharm : ∀ y ∈ connectedComponentIn {y | 0 < u₀ y} y₀, HarmonicAt u₀ y) {e : Rn n}
    (he : e ≠ 0) (hsub : {y | 0 < ⟪y, e⟫} ⊆ connectedComponentIn {y | 0 < u₀ y} y₀) :
    connectedComponentIn {y | 0 < u₀ y} y₀ = {y | 0 < ⟪y, e⟫} := by
  obtain ⟨L, hL⟩ := hLip
  have hne : 0 < ‖e‖ := norm_pos_iff.2 he
  set ê : Rn n := ‖e‖⁻¹ • e with hêdef
  have hê : ‖ê‖ = 1 := by rw [hêdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne.ne']
  have hêê : ⟪ê, ê⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hê, one_pow]
  have hH : {y : Rn n | 0 < ⟪y, e⟫} = {y : Rn n | 0 < ⟪y, ê⟫} := by
    ext y
    simp only [mem_setOf_eq, hêdef, real_inner_smul_right]
    exact (mul_pos_iff_of_pos_left (inv_pos.2 hne)).symm
  rw [hH] at hsub ⊢
  have hzero : ∀ y, ⟪y, ê⟫ = 0 → u₀ y = 0 := fun y hy =>
    eq_zero_of_inner_eq_zero hê hL hnn hhom (fun z hz => hharm z (hsub hz)) hy
  refine Subset.antisymm ?_ hsub
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (isOpen_halfSpace ê)
    (isOpen_halfSpace_neg ê) ?_ ?_ ⟨ê, hsub (by rw [mem_setOf_eq, hêê]; exact one_pos),
      by rw [mem_setOf_eq, hêê]; exact one_pos⟩
  · rw [Set.disjoint_left]
    intro y hy hy'
    have h1 : 0 < ⟪y, ê⟫ := hy
    have h2 : ⟪y, ê⟫ < 0 := hy'
    linarith
  · intro y hy
    have hy' : y ∈ {y | 0 < u₀ y} := connectedComponentIn_subset {y | 0 < u₀ y} y₀ hy
    have hpos : 0 < u₀ y := hy'
    rcases lt_trichotomy ⟪y, ê⟫ 0 with h | h | h
    · exact Or.inr h
    · exact absurd (hzero y h) hpos.ne'
    · exact Or.inl h

end Regular

end InnerVariational
