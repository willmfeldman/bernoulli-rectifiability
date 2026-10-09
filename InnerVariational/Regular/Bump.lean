/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.HarmonicCone
public import InnerVariational.Kernel.Rescale
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Kernel.Harmonic
import InnerVariational.Kernel.IBP
public import GMTFoundations.Defs.Calculus

/-!
# A radial bump and its rescalings

Auxiliary test functions for the Laplacian identity of Corollary 8.4 of D. Kriventsov and
G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for non-minimizing
Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226;
arXiv:2306.10131 (numbering of arXiv v2); see `Regular/Laplacian.lean`.

* `Regular.bump z = s(2(1 − |z|²))`, with `s = Real.smoothTransition`: smooth, `0 ≤ bump ≤ 1`,
  `bump = 1` on `|z|² ≤ 1/2`, `tsupport bump ⊆ B̄_1`, and radially nonincreasing.
* `Regular.scaledBump x r y = bump ((y − x)/r)`: a test function on `B̄_r(x)`.
* `Regular.halfSpaceFlux v = ∫_{⟪z, v⟫ < 0} ⟪∇bump(z), v⟫ dz`, which is positive for `|v| = 1`.
  It is the common limit of the rescaled Laplacian and perimeter masses at a reduced-boundary
  point (`Regular/Laplacian.lean`).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-- The radial bump `z ↦ s(2(1 − |z|²))`, with `s = Real.smoothTransition`. -/
def bump (z : Rn n) : ℝ :=
  Real.smoothTransition (2 * (1 - ‖z‖ ^ 2))

theorem contDiff_bump : ContDiff ℝ ∞ (bump (n := n)) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ)))

theorem continuous_bump : Continuous (bump (n := n)) :=
  contDiff_bump.continuous

theorem bump_nonneg (z : Rn n) : 0 ≤ bump z :=
  Real.smoothTransition.nonneg _

theorem bump_le_one (z : Rn n) : bump z ≤ 1 :=
  Real.smoothTransition.le_one _

theorem bump_eq_zero_of_one_le_norm {z : Rn n} (hz : 1 ≤ ‖z‖) : bump z = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  nlinarith [norm_nonneg z]

theorem bump_eq_one_of_sq_norm_le {z : Rn n} (hz : ‖z‖ ^ 2 ≤ 1 / 2) : bump z = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  linarith

/-- `∇bump(z) = −4 s'(2(1 − |z|²)) z`. -/
theorem gradient_bump (z : Rn n) :
    gradient bump z = (-4 * deriv Real.smoothTransition (2 * (1 - ‖z‖ ^ 2))) • z := by
  have h1 : HasFDerivAt (fun z : Rn n => ‖z‖ ^ 2) (2 • innerSL ℝ z) z :=
    hasStrictFDerivAt_norm_sq z |>.hasFDerivAt
  have h2 : HasFDerivAt (fun z : Rn n => 2 * (1 - ‖z‖ ^ 2)) (-(2 : ℝ) • (2 • innerSL ℝ z)) z := by
    have := (h1.const_sub 1).const_mul 2
    convert this using 1
    ext w
    simp
  have h3 := (Kernel.hasDerivAt_smoothTransition (2 * (1 - ‖z‖ ^ 2))).comp_hasFDerivAt z h2
  have h4 : HasGradientAt bump ((-4 * deriv Real.smoothTransition (2 * (1 - ‖z‖ ^ 2))) • z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h3 using 1 <;> first
      | rfl
      | (ext w
         simp only [InnerProductSpace.toDual_apply_apply, smul_apply,
           innerSL_apply_apply, smul_eq_mul, real_inner_smul_left, nsmul_eq_mul]
         push_cast
         ring)
  exact h4.gradient

/-- `⟪∇bump(z), v⟫ = −4 s'(2(1 − |z|²)) ⟪z, v⟫`. -/
theorem inner_gradient_bump (z v : Rn n) :
    ⟪gradient bump z, v⟫ = -4 * deriv Real.smoothTransition (2 * (1 - ‖z‖ ^ 2)) * ⟪z, v⟫ := by
  rw [gradient_bump, real_inner_smul_left]

theorem continuous_gradient_bump : Continuous (gradient (bump (n := n))) := by
  have : gradient (bump (n := n)) =
      fun z => (-4 * deriv Real.smoothTransition (2 * (1 - ‖z‖ ^ 2))) • z :=
    funext gradient_bump
  rw [this]
  exact ((continuous_const.mul (Kernel.continuous_deriv_smoothTransition.comp
    (continuous_const.mul (continuous_const.sub (continuous_norm.pow 2)))))).smul continuous_id

theorem gradient_bump_eq_zero_of_one_lt_norm {z : Rn n} (hz : 1 < ‖z‖) : gradient bump z = 0 := by
  rw [gradient_bump, Kernel.deriv_smoothTransition_eq_zero (Or.inl (by nlinarith [norm_nonneg z])),
    mul_zero, zero_smul]

theorem exists_norm_gradient_bump_le : ∃ M, ∀ z : Rn n, ‖gradient bump z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Rn n) 1).exists_bound_of_continuousOn
    continuous_gradient_bump.continuousOn
  refine ⟨max M 0, fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ 1
  · exact (hM z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
  · rw [gradient_bump_eq_zero_of_one_lt_norm (not_le.1 hz), norm_zero]
    exact le_max_right _ _

/-! ### Rescaled bumps -/

/-- `scaledBump x r y = bump ((y − x)/r)`. -/
def scaledBump (x : Rn n) (r : ℝ) (y : Rn n) : ℝ :=
  bump (r⁻¹ • (y - x))

theorem contDiff_scaledBump (x : Rn n) (r : ℝ) : ContDiff ℝ ∞ (scaledBump x r) :=
  contDiff_bump.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

theorem scaledBump_nonneg (x : Rn n) (r : ℝ) (y : Rn n) : 0 ≤ scaledBump x r y :=
  bump_nonneg _

theorem scaledBump_le_one (x : Rn n) (r : ℝ) (y : Rn n) : scaledBump x r y ≤ 1 :=
  bump_le_one _

theorem scaledBump_eq_zero {x : Rn n} {r : ℝ} (hr : 0 < r) {y : Rn n} (hy : y ∉ ball x r) :
    scaledBump x r y = 0 := by
  refine bump_eq_zero_of_one_le_norm ?_
  rw [mem_ball, dist_eq_norm, not_lt] at hy
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, le_inv_mul_iff₀ hr, mul_one]
  exact hy

theorem scaledBump_eq_one {x : Rn n} {r : ℝ} (hr : 0 < r) {y : Rn n} (hy : y ∈ ball x (r / 2)) :
    scaledBump x r y = 1 := by
  refine bump_eq_one_of_sq_norm_le ?_
  rw [mem_ball, dist_eq_norm] at hy
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, mul_pow, inv_pow]
  have h1 : ‖y - x‖ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy.le 2
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

theorem tsupport_scaledBump_subset {x : Rn n} {r : ℝ} (hr : 0 < r) :
    tsupport (scaledBump x r) ⊆ closedBall x r := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra hy'
  exact hy (scaledBump_eq_zero hr fun h => hy' (ball_subset_closedBall h))

theorem hasCompactSupport_scaledBump {x : Rn n} {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledBump x r) :=
  (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_scaledBump_subset hr)

theorem isTestFunction_scaledBump {Ω : Set (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall x r ⊆ Ω) : IsTestFunction Ω (scaledBump x r) :=
  ⟨contDiff_scaledBump x r, hasCompactSupport_scaledBump hr,
    (tsupport_scaledBump_subset hr).trans hΩ⟩

/-- `∇ scaledBump x r (y) = r⁻¹ ∇bump((y − x)/r)`. -/
theorem gradient_scaledBump (x : Rn n) (r : ℝ) (y : Rn n) :
    gradient (scaledBump x r) y = r⁻¹ • gradient bump (r⁻¹ • (y - x)) := by
  have hA : HasFDerivAt (fun y : Rn n => r⁻¹ • (y - x))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Rn n)) y := by
    exact ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x).const_smul r⁻¹
  have hb : HasFDerivAt bump (fderiv ℝ bump (r⁻¹ • (y - x))) (r⁻¹ • (y - x)) :=
    (contDiff_bump.differentiable (by simp) _).hasFDerivAt
  have hc := hb.comp y hA
  refine ext_inner_right ℝ fun w => ?_
  rw [real_inner_smul_left]
  simp only [gradient, InnerProductSpace.toDual_symm_apply]
  rw [show scaledBump x r = bump ∘ fun y => r⁻¹ • (y - x) from rfl, hc.fderiv]
  simp

theorem continuous_gradient_scaledBump (x : Rn n) (r : ℝ) :
    Continuous (gradient (scaledBump x r)) := by
  rw [show gradient (scaledBump x r) = fun y => r⁻¹ • gradient bump (r⁻¹ • (y - x)) from
    funext (gradient_scaledBump x r)]
  exact (continuous_gradient_bump.comp
    (by fun_prop : Continuous fun y : Rn n => r⁻¹ • (y - x))).const_smul r⁻¹

theorem hasCompactSupport_gradient_scaledBump (x : Rn n) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (gradient (scaledBump x r)) :=
  HasCompactSupport.intro (isCompact_closedBall x r) fun _ hy =>
    Kernel.gradient_eq_zero_of_notMem_tsupport fun h' => hy (tsupport_scaledBump_subset hr h')

theorem integrable_norm_gradient_scaledBump (x : Rn n) {r : ℝ} (hr : 0 < r) :
    Integrable fun y => ‖gradient (scaledBump x r) y‖ :=
  (continuous_gradient_scaledBump x r).norm.integrable_of_hasCompactSupport
    (hasCompactSupport_gradient_scaledBump x hr).norm

/-- Change of variables: `∫ F((y − x)/r) dy = rⁿ ∫ F`. -/
theorem integral_comp_rescale (F : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    ∫ y, F (r⁻¹ • (y - x)) = r ^ n * ∫ z, F z := by
  have h := Kernel.integral_comp_similarity (fun y => F (r⁻¹ • (y - x))) x hr
    (LinearIsometryEquiv.refl ℝ (Rn n))
  have e : ∫ y, (fun y => F (r⁻¹ • (y - x))) (x + r • (LinearIsometryEquiv.refl ℝ (Rn n)) y) =
      ∫ z, F z := by
    congr 1
    funext z
    simp only [LinearIsometryEquiv.coe_refl, id, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  rw [e] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_pos hr n).ne', one_mul]

/-! ### The half-space flux of the bump -/

/-- `∫_{⟪z, v⟫ < 0} ⟪∇bump(z), v⟫ dz`. -/
def halfSpaceFlux (v : Rn n) : ℝ :=
  ∫ z in {z : Rn n | ⟪z, v⟫ < 0}, ⟪gradient bump z, v⟫

theorem halfSpaceFlux_pos {v : Rn n} (hv : ‖v‖ = 1) : 0 < halfSpaceFlux v := by
  obtain ⟨t₀, ht₀, hd⟩ := exists_deriv_smoothTransition_eq_one
  set a := Real.sqrt (1 - t₀ / 2) with hadef
  have ha2 : a ^ 2 = 1 - t₀ / 2 := Real.sq_sqrt (by linarith [ht₀.2])
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith [ht₀.2])
  set H := {z : Rn n | ⟪z, v⟫ < 0} with hHdef
  set f : Rn n → ℝ := fun z => ⟪gradient bump z, v⟫ with hfdef
  have hfc : Continuous f := continuous_gradient_bump.inner continuous_const
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  set z₀ : Rn n := (-a) • v with hz₀def
  have hz₀ : f z₀ = 4 * a := by
    simp only [hfdef, inner_gradient_bump, hz₀def, norm_smul, hv, real_inner_smul_left, hvv,
      Real.norm_eq_abs, abs_neg, abs_of_pos ha, mul_one]
    rw [ha2, show 2 * (1 - (1 - t₀ / 2)) = t₀ by ring, hd]
    ring
  have hfcs : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) 1)
    fun z hz => by
      rw [mem_closedBall_zero_iff, not_le] at hz
      change ⟪gradient bump z, v⟫ = 0
      rw [gradient_bump_eq_zero_of_one_lt_norm hz, inner_zero_left]
  have hint : Integrable f := hfc.integrable_of_hasCompactSupport hfcs
  have hnn : 0 ≤ᵐ[volume.restrict H] f := by
    refine (ae_restrict_iff' (isOpen_halfSpace_neg v).measurableSet).2 (.of_forall fun z hz => ?_)
    have hs := Kernel.deriv_smoothTransition_nonneg (2 * (1 - ‖z‖ ^ 2))
    have hz' : ⟪z, v⟫ < 0 := hz
    simp only [Pi.zero_apply, hfdef, inner_gradient_bump]
    nlinarith
  rw [halfSpaceFlux, setIntegral_pos_iff_support_of_nonneg_ae hnn hint.integrableOn]
  have hW : IsOpen ({z | 0 < f z} ∩ H) :=
    (isOpen_lt continuous_const hfc).inter (isOpen_halfSpace_neg v)
  have hz₀H : z₀ ∈ H := by
    simp only [hHdef, hz₀def, mem_ofPred_eq, real_inner_smul_left, hvv]
    linarith
  refine lt_of_lt_of_le (hW.measure_pos volume ⟨z₀, ?_, hz₀H⟩) (measure_mono ?_)
  · change 0 < f z₀
    rw [hz₀]
    positivity
  · rintro z ⟨hz, hzH⟩
    exact ⟨ne_of_gt hz, hzH⟩

end Regular

end InnerVariational
