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

/-!
# Test functions and `L²` limit lemmas for the blow-up profile

Auxiliary results for steps (d) and (e) of the proof of Theorem 5.3 of Kriventsov–Weiss (see
`Blowup/Profile/Normalization.lean` for the overview): the one-dimensional integration by parts
across a hyperplane, the test functions of steps (d) and (e), the annulus integral of `⟪ν, y⟫²`,
and two `L²` limit lemmas.

## Main results

* `integral_indicator_add_max_inner_mul_fderiv`: `∫ ∂_e (max(⟪e, y⟫, 0) η) = 0`, expanded.
* `exists_cutoff_annulus`, `exists_jump_testFunction`: the test functions of steps (d) and (e).
* `integral_annulus_inner_sq`: `∫_A ⟪ν, y⟫² = (∫_{∂B_1} y_1²) ∫_{1/2}^1 s^{n+1} ds`.
* `tendsto_integral_mul_inner_of_tendsto`: strong times weak `L²` convergence.

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

/-- `y ↦ max ⟪e, y⟫ 0` is `1`-Lipschitz for a unit vector `e`. -/
theorem lipschitzWith_max_inner_zero {e : Rn n} (he : ‖e‖ = 1) :
    LipschitzWith 1 (fun y : Rn n => max ⟪e, y⟫ 0) := by
  have h : LipschitzWith 1 (fun y : Rn n => ⟪e, y⟫) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, ← inner_sub_right, NNReal.coe_one, one_mul, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans (by rw [he, one_mul])
  exact h.max_const 0

/-- Off the hyperplane `{⟪e, y⟫ = 0}`, `∂_e max(⟪e, y⟫, 0)` is the indicator of `{⟪e, y⟫ > 0}`. -/
theorem fderiv_max_inner_zero_apply {e y : Rn n} (he : ‖e‖ = 1) (hy : ⟪e, y⟫ ≠ 0) :
    fderiv ℝ (fun z : Rn n => max ⟪e, z⟫ 0) y e = if 0 < ⟪e, y⟫ then 1 else 0 := by
  have hce : Continuous fun z : Rn n => ⟪e, z⟫ := continuous_const.inner continuous_id
  rcases lt_or_gt_of_ne hy with h | h
  · have hev : (fun z : Rn n => max ⟪e, z⟫ 0) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(hce.tendsto y).eventually (gt_mem_nhds h)] with z hz
      exact max_eq_right hz.le
    rw [hev.fderiv_eq, ite_eq_right (not_lt.2 h.le)]
    simp
  · have hev : (fun z : Rn n => max ⟪e, z⟫ 0) =ᶠ[𝓝 y] fun z => ⟪e, z⟫ := by
      filter_upwards [(hce.tendsto y).eventually (lt_mem_nhds h)] with z hz
      exact max_eq_left hz.le
    have hd : HasFDerivAt (fun z : Rn n => ⟪e, z⟫) (innerSL ℝ e) y := (innerSL ℝ e).hasFDerivAt
    rw [hev.fderiv_eq, hd.fderiv, ite_eq_left h, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      he, one_pow]

/-- **Integration by parts across a hyperplane.** For a unit vector `e` and `η ∈ C_c^∞`,
`∫ (1_{⟪e, y⟫ > 0} η + max(⟪e, y⟫, 0) ∂_e η) = 0`. This is `∫ ∂_e (max(⟪e, ·⟫, 0) η) = 0`. -/
theorem integral_indicator_add_max_inner_mul_fderiv {e : Rn n} (he : ‖e‖ = 1) {η : Rn n → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∫ y, ({y | 0 < ⟪e, y⟫}.indicator η y + max ⟪e, y⟫ 0 * fderiv ℝ η y e) = 0 := by
  obtain ⟨D, hD⟩ := hη.lipschitzWith_of_hasCompactSupport hηc (by simp)
  have h := (lipschitzWith_max_inner_zero he).integral_mul_fderiv_eq_neg (μ := volume) hD hηc e
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hS : MeasurableSet {y : Rn n | 0 < ⟪e, y⟫} :=
    measurableSet_lt measurable_const (measurable_const.inner measurable_id)
  have hae : (fun y => η y * fderiv ℝ (fun z : Rn n => max ⟪e, z⟫ 0) y e) =ᵐ[volume]
      {y | 0 < ⟪e, y⟫}.indicator η := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_inner_eq_zero he0)] with y hy
    rw [fderiv_max_inner_zero_apply he hy]
    by_cases hp : 0 < ⟪e, y⟫
    · rw [ite_eq_left hp, indicator_of_mem (show y ∈ {y | 0 < ⟪e, y⟫} from hp), mul_one]
    · rw [ite_eq_right hp, indicator_of_notMem (show y ∉ {y | 0 < ⟪e, y⟫} from hp), mul_zero]
  rw [integral_congr_ae hae] at h
  have hi1 : Integrable ({y : Rn n | 0 < ⟪e, y⟫}.indicator η) :=
    (hη.continuous.integrable_of_hasCompactSupport hηc).indicator hS
  have hc2 : Continuous fun y => max ⟪e, y⟫ 0 * fderiv ℝ η y e :=
    ((continuous_const.inner continuous_id).max continuous_const).mul
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hi2 : Integrable fun y => max ⟪e, y⟫ 0 * fderiv ℝ η y e :=
    hc2.integrable_of_hasCompactSupport (hηc.fderiv_apply (𝕜 := ℝ) e).mul_left
  rw [integral_add hi1 hi2, h]
  ring

/-- `∫ ∂_e φ = 0` for `φ ∈ C_c^∞`. -/
theorem integral_fderiv_apply_eq_zero {φ : Rn n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (e : Rn n) : ∫ y, fderiv ℝ φ y e = 0 := by
  obtain ⟨D, hD⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  have h := (LipschitzWith.const (α := Rn n) (1 : ℝ)).integral_mul_fderiv_eq_neg (μ := volume)
    hD hφc e
  simpa using h

/-- `absProfile ν 0` is `1`-Lipschitz for a unit vector `ν`. -/
theorem lipschitzWith_absProfile {ν : Rn n} (hν : ‖ν‖ = 1) : LipschitzWith 1 (absProfile ν 0) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [absProfile, sub_zero, NNReal.coe_one, one_mul, dist_eq_norm]
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  rw [← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans (by rw [hν, mul_one])

/-- `∇|⟪y, ν⟫| = ν` where `⟪y, ν⟫ > 0`. -/
theorem gradient_absProfile_of_pos {ν y : Rn n} (hy : 0 < ⟪y, ν⟫) :
    gradient (absProfile ν 0) y = ν := by
  have hce : Continuous fun z : Rn n => ⟪z, ν⟫ := continuous_id.inner continuous_const
  have hev : absProfile ν 0 =ᶠ[𝓝 y] fun z => ⟪ν, z⟫ := by
    filter_upwards [(hce.tendsto y).eventually (lt_mem_nhds hy)] with z hz
    simp only [absProfile, sub_zero]
    rw [abs_of_pos hz, real_inner_comm]
  have hd : HasFDerivAt (fun z : Rn n => ⟪ν, z⟫) (InnerProductSpace.toDual ℝ (Rn n) ν) y :=
    (innerSL ℝ ν).hasFDerivAt
  exact (hasGradientAt_iff_hasFDerivAt.2 (hd.congr_of_eventuallyEq hev)).gradient

/-- `∇|⟪y, ν⟫| = -ν` where `⟪y, ν⟫ < 0`. -/
theorem gradient_absProfile_of_neg {ν y : Rn n} (hy : ⟪y, ν⟫ < 0) :
    gradient (absProfile ν 0) y = -ν := by
  have hce : Continuous fun z : Rn n => ⟪z, ν⟫ := continuous_id.inner continuous_const
  have hev : absProfile ν 0 =ᶠ[𝓝 y] fun z => ⟪-ν, z⟫ := by
    filter_upwards [(hce.tendsto y).eventually (gt_mem_nhds hy)] with z hz
    simp only [absProfile, sub_zero]
    rw [abs_of_neg hz, inner_neg_left, real_inner_comm]
  have hd : HasFDerivAt (fun z : Rn n => ⟪-ν, z⟫) (InnerProductSpace.toDual ℝ (Rn n) (-ν)) y :=
    (innerSL ℝ (-ν)).hasFDerivAt
  exact (hasGradientAt_iff_hasFDerivAt.2 (hd.congr_of_eventuallyEq hev)).gradient

/-- A unit vector orthogonal to a given unit vector, in dimension `≥ 2`. -/
theorem exists_unit_inner_eq_zero (hn : 2 ≤ n) {ν : Rn n} (hν : ν ≠ 0) :
    ∃ e : Rn n, ‖e‖ = 1 ∧ ⟪ν, e⟫ = 0 := by
  have : Fact (Module.finrank ℝ (Rn n) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  have hfr : Module.finrank ℝ (ℝ ∙ ν)ᗮ = n - 1 := Submodule.finrank_orthogonal_span_singleton hν
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (show 0 < Module.finrank ℝ (ℝ ∙ ν)ᗮ
    by omega)
  have hw0 : (w : Rn n) ≠ 0 := by simpa using hw
  have hwν : ⟪ν, (w : Rn n)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 w.2
  refine ⟨‖(w : Rn n)‖⁻¹ • (w : Rn n), ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
  · rw [inner_smul_right, hwν, mul_zero]

/-- A smooth cut-off: `0 ≤ η ≤ 1`, `η = 1` on `B_{7/8} \ B̄_{5/8}`, supported in
`B_1 \ B̄_{1/2}`. -/
theorem exists_cutoff_annulus : ∃ η : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
    tsupport η ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) ∧ (∀ y, 0 ≤ η y) ∧ (∀ y, η y ≤ 1) ∧
    ∀ y ∈ ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8), η y = 1 := by
  let b₁ : ContDiffBump (0 : Rn n) := ⟨7 / 8, 15 / 16, by norm_num, by norm_num⟩
  let b₂ : ContDiffBump (0 : Rn n) := ⟨9 / 16, 5 / 8, by norm_num, by norm_num⟩
  have h1 : ∀ y : Rn n, ‖y‖ ≤ 7 / 8 → b₁ y = 1 := fun y hy =>
    b₁.one_of_mem_closedBall (by simpa using hy)
  have h1' : ∀ y : Rn n, 15 / 16 ≤ ‖y‖ → b₁ y = 0 := fun y hy =>
    b₁.zero_of_le_dist (by simpa using hy)
  have h2 : ∀ y : Rn n, ‖y‖ ≤ 9 / 16 → b₂ y = 1 := fun y hy =>
    b₂.one_of_mem_closedBall (by simpa using hy)
  have h2' : ∀ y : Rn n, 5 / 8 ≤ ‖y‖ → b₂ y = 0 := fun y hy =>
    b₂.zero_of_le_dist (by simpa using hy)
  set S : Set (Rn n) := closedBall 0 (15 / 16) \ ball 0 (9 / 16) with hS
  have hSc : IsClosed S := isClosed_closedBall.sdiff isOpen_ball
  have hsupp : tsupport (fun y => b₁ y - b₂ y) ⊆ S := by
    refine closure_minimal (fun y hy => ?_) hSc
    rw [Function.mem_support] at hy
    simp only [hS, Set.mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt]
    constructor
    · by_contra h
      exact hy (by rw [h1' y (by linarith), h2' y (by linarith), sub_zero])
    · by_contra h
      exact hy (by rw [h1 y (by linarith), h2 y (by linarith), sub_self])
  refine ⟨fun y => b₁ y - b₂ y, b₁.contDiff.sub b₂.contDiff, ?_, ?_, fun y => ?_, fun y => ?_,
    fun y hy => ?_⟩
  · exact (isCompact_closedBall (0 : Rn n) (15 / 16)).of_isClosed_subset (isClosed_tsupport _)
      (hsupp.trans sdiff_subset)
  · refine hsupp.trans fun y hy => ⟨?_, ?_⟩
    · have := mem_closedBall_zero_iff.1 hy.1
      rw [mem_ball_zero_iff]; linarith
    · have := hy.2
      rw [mem_ball_zero_iff, not_lt] at this
      rw [mem_closedBall_zero_iff, not_le]; linarith
  · change 0 ≤ b₁ y - b₂ y
    by_cases hy : ‖y‖ < 5 / 8
    · rw [h1 y (by linarith)]; linarith [b₂.le_one (x := y)]
    · rw [h2' y (by linarith)]; linarith [b₁.nonneg (x := y)]
  · change b₁ y - b₂ y ≤ 1
    linarith [b₁.le_one (x := y), b₂.nonneg (x := y)]
  · have hy1 := mem_ball_zero_iff.1 hy.1
    have hy2 := hy.2
    rw [mem_closedBall_zero_iff, not_le] at hy2
    change b₁ y - b₂ y = 1
    rw [h1 y hy1.le, h2' y hy2.le, sub_zero]

/-- **A test function detecting a jump across `{⟪ν, y⟫ = 0}`** (for step (e)).
For `n ≥ 2` and a unit vector `ν` there is `φ ∈ C_c^∞(B_{7/8} \ B̄_{5/8})` with
`∫_{⟪ν, y⟫ > 0} ∂_ν φ < 0`. It is `φ(y) = b(y − ⟪ν, y⟫ ν) θ(⟪ν, y⟫)`, with `b` a bump centred at a
point `x₀ ⊥ ν`, `|x₀| = 3/4` (this uses `n ≥ 2`), and `θ(t) = S(1 − 256 t²)` even and nonincreasing
on `t > 0`. Since `b(y − ⟪ν, y⟫ ν)` does not depend on `⟪ν, y⟫`, `∂_ν φ = b θ'(⟪ν, y⟫) ≤ 0` on
`{⟪ν, y⟫ > 0}`, and it is negative somewhere. -/
theorem exists_jump_testFunction (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1) :
    ∃ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8) ∧
      ∫ y, {y | 0 < ⟪ν, y⟫}.indicator (fun y => fderiv ℝ φ y ν) y < 0 := by
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  obtain ⟨e, he, hνe⟩ := exists_unit_inner_eq_zero hn hν0
  set x₀ : Rn n := (3 / 4 : ℝ) • e with hx₀
  have hx₀ν : ⟪ν, x₀⟫ = 0 := by rw [hx₀, inner_smul_right, hνe, mul_zero]
  have hx₀n : ‖x₀‖ = 3 / 4 := by rw [hx₀, norm_smul, he]; norm_num
  set P := tangentialPart ν with hP
  have hPy : ∀ y, P y = y - ⟪ν, y⟫ • ν := fun y => tangentialPart_apply ν y
  have hPν : P ν = 0 := by rw [hPy, real_inner_self_eq_norm_sq, hν]; simp
  let b : ContDiffBump x₀ := ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩
  set θ : ℝ → ℝ := fun t => Real.smoothTransition (1 - 256 * t ^ 2) with hθ
  set θ' : ℝ → ℝ := fun t => deriv Real.smoothTransition (1 - 256 * t ^ 2) * (-(512 * t))
    with hθ'
  have hθd : ∀ t, HasDerivAt θ (θ' t) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => 1 - 256 * t ^ 2) (-(512 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul 256).const_sub 1
      convert this using 1
      push_cast
      ring
    exact (Kernel.hasDerivAt_smoothTransition _).comp t h1
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ :=
    Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2)))
  set φ : Rn n → ℝ := fun y => b (P y) * θ ⟪ν, y⟫ with hφ
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (b.contDiff.comp P.contDiff).mul (hθs.comp (innerSL ℝ ν).contDiff)
  have hφd : ∀ y, fderiv ℝ φ y ν = b (P y) * θ' ⟪ν, y⟫ := fun y => by
    have hb : HasFDerivAt (fun y => b (P y)) ((fderiv ℝ b (P y)).comp P) y :=
      (((b.contDiff (n := 1)).differentiable one_ne_zero) (P y)).hasFDerivAt.comp y P.hasFDerivAt
    have ht : HasFDerivAt (fun y : Rn n => θ ⟪ν, y⟫) (θ' ⟪ν, y⟫ • innerSL ℝ ν) y :=
      (hθd _).comp_hasFDerivAt y (innerSL ℝ ν).hasFDerivAt
    have hd : HasFDerivAt φ _ y := hb.mul ht
    rw [hd.fderiv]
    simp [hPν, hν]
  -- The support.
  have hsupp : Function.support φ ⊆ closedBall x₀ (1 / 10) := by
    intro y hy
    rw [Function.mem_support] at hy
    have hb0 : b (P y) ≠ 0 := left_ne_zero_of_mul hy
    have hθ0 : θ ⟪ν, y⟫ ≠ 0 := right_ne_zero_of_mul hy
    have h1 : ‖P y - x₀‖ < 1 / 16 := by
      have : P y ∈ Function.support b := hb0
      rw [b.support_eq, mem_ball, dist_eq_norm] at this
      exact this
    have h2 : ⟪ν, y⟫ ^ 2 < 1 / 256 := by
      by_contra h
      push Not at h
      exact hθ0 (Real.smoothTransition.zero_of_nonpos (by linarith))
    have hdec : y - x₀ = (P y - x₀) + ⟪ν, y⟫ • ν := by rw [hPy]; abel
    have horth : ⟪P y - x₀, ν⟫ = 0 := by
      rw [hPy, inner_sub_left, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hν,
        real_inner_comm ν x₀, hx₀ν, real_inner_comm ν y]
      simp
    have hn2 : ‖y - x₀‖ ^ 2 = ‖P y - x₀‖ ^ 2 + ⟪ν, y⟫ ^ 2 := by
      rw [hdec, norm_add_sq_real, inner_smul_right, horth, norm_smul, hν, Real.norm_eq_abs]
      rw [mul_one, mul_zero, mul_zero, add_zero, sq_abs]
    have h3 : ‖P y - x₀‖ ^ 2 < 1 / 256 := by nlinarith [norm_nonneg (P y - x₀)]
    rw [mem_closedBall, dist_eq_norm]
    nlinarith [norm_nonneg (y - x₀)]
  have hts : tsupport φ ⊆ closedBall x₀ (1 / 10) := closure_minimal hsupp isClosed_closedBall
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall x₀ (1 / 10)).of_isClosed_subset (isClosed_tsupport _) hts
  have hA' : closedBall x₀ (1 / 10) ⊆ ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have h1 := norm_sub_norm_le y x₀
    have h2 := norm_sub_norm_le x₀ y
    rw [norm_sub_rev] at h2
    refine ⟨mem_ball_zero_iff.2 (by linarith), fun h => ?_⟩
    rw [mem_closedBall_zero_iff] at h
    linarith
  refine ⟨φ, hφs, hφc, hts.trans hA', ?_⟩
  -- A point where `∂_ν φ < 0`.
  obtain ⟨c, hc, hcθ⟩ := exists_hasDerivAt_eq_slope θ θ' (show (0 : ℝ) < 1 / 16 by norm_num)
    hθs.continuous.continuousOn (fun t _ => hθd t)
  have hθ1 : θ (1 / 16) = 0 := by
    simp only [hθ]
    exact Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hθ0 : θ 0 = 1 := by
    simp only [hθ]
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  rw [hθ1, hθ0] at hcθ
  have hθ'c : θ' c < 0 := by rw [hcθ]; norm_num
  set y₁ : Rn n := x₀ + c • ν with hy₁
  have hy₁ν : ⟪ν, y₁⟫ = c := by
    rw [hy₁, inner_add_right, hx₀ν, inner_smul_right, real_inner_self_eq_norm_sq, hν]
    ring
  have hPy₁ : P y₁ = x₀ := by
    rw [hPy, hy₁ν, hy₁]
    abel
  have hdc : Continuous fun y => fderiv ℝ φ y ν :=
    (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hSm : MeasurableSet {y : Rn n | 0 < ⟪ν, y⟫} :=
    measurableSet_lt measurable_const (measurable_const.inner measurable_id)
  have hgi : Integrable ({y : Rn n | 0 < ⟪ν, y⟫}.indicator fun y => fderiv ℝ φ y ν) :=
    (hdc.integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) ν)).indicator hSm
  have hgnp : ∀ y, {y : Rn n | 0 < ⟪ν, y⟫}.indicator (fun y => fderiv ℝ φ y ν) y ≤ 0 := by
    intro y
    by_cases hy : 0 < ⟪ν, y⟫
    · rw [indicator_of_mem (show y ∈ {y : Rn n | 0 < ⟪ν, y⟫} from hy), hφd]
      refine mul_nonpos_of_nonneg_of_nonpos b.nonneg ?_
      simp only [hθ']
      exact mul_nonpos_of_nonneg_of_nonpos (Kernel.deriv_smoothTransition_nonneg _)
        (by linarith)
    · rw [indicator_of_notMem (show y ∉ {y : Rn n | 0 < ⟪ν, y⟫} from hy)]
  set U : Set (Rn n) := {y | 0 < ⟪ν, y⟫} ∩ {y | fderiv ℝ φ y ν < 0} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_const.inner continuous_id)).inter
      (isOpen_lt hdc continuous_const)
  have hU1 : y₁ ∈ U := by
    refine ⟨show 0 < ⟪ν, y₁⟫ by rw [hy₁ν]; exact hc.1, show fderiv ℝ φ y₁ ν < 0 from ?_⟩
    rw [hφd, hPy₁, hy₁ν, b.one_of_mem_closedBall (mem_closedBall_self (by norm_num)), one_mul]
    exact hθ'c
  have hpos : 0 < ∫ y, -{y : Rn n | 0 < ⟪ν, y⟫}.indicator (fun y => fderiv ℝ φ y ν) y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => neg_nonneg.2 (hgnp y)) hgi.neg]
    refine (hUo.measure_pos volume ⟨y₁, hU1⟩).trans_le (measure_mono fun y hy => ?_)
    rw [Function.mem_support, indicator_of_mem hy.1]
    exact neg_ne_zero.2 hy.2.ne
  rw [integral_neg] at hpos
  linarith

/-- **`∫_A ⟪ν, y⟫² = σ₀ ∫_{1/2}^1 s^{n+1} ds`** on `A = B_1 \ B̄_{1/2}`, where
`σ₀ = ∫_{∂B_1} y_1² = α(n)^{-2}`. The rotation `ν ↦ e_1` is a reflection. -/
theorem integral_annulus_inner_sq [NeZero n] {ν : Rn n} (hν : ‖ν‖ = 1) :
    ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), ⟪ν, y⟫ ^ 2 =
      sphereIntegral (fun y : Rn n => y 0 ^ 2) 0 1 * ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) := by
  set e₀ : Rn n := EuclideanSpace.single 0 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  set R := Submodule.reflection (ℝ ∙ (ν - e₀))ᗮ with hRdef
  have hR : R ν = e₀ := Submodule.reflection_sub (hν.trans he₀n.symm)
  have hinner : ∀ y, ⟪ν, y⟫ = (R y) 0 := fun y => by
    rw [← R.inner_map_map, hR, he₀, EuclideanSpace.inner_single_left]
    simp
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  have hpre : R ⁻¹' A = A := by
    ext y
    simp only [hA, mem_preimage, Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff,
      LinearIsometryEquiv.norm_map]
  have h1 : ∫ y in A, ⟪ν, y⟫ ^ 2 = ∫ y in A, y 0 ^ 2 := by
    have := (R.measurePreserving).setIntegral_preimage_emb
      R.toHomeomorph.measurableEmbedding (fun z : Rn n => z 0 ^ 2) A
    rw [hpre] at this
    simp_rw [hinner]
    exact this
  have hae : A =ᵐ[volume] (ball (0 : Rn n) 1 \ ball 0 (1 / 2)) := by
    refine (EventuallyEqSet.refl _ _).diff ?_
    refine ae_eq_set.2 ⟨?_, by simp [sdiff_eq_empty.2 ball_subset_closedBall]⟩
    rw [closedBall_sdiff_ball]
    exact Measure.addHaar_sphere_of_ne_zero volume 0 (by norm_num)
  have hc : Continuous fun y : Rn n => y 0 ^ 2 :=
    ((EuclideanSpace.proj (0 : Fin n) : Rn n →L[ℝ] ℝ).continuous).pow 2
  have hint : IntegrableOn (fun y : Rn n => y 0 ^ 2) (ball 0 1) :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall
  have h2 := integral_ball_diff_ball (x := (0 : Rn n)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hint
  rw [h1, setIntegral_congr_set hae]
  refine h2.trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [sphereIntegral, zero_add, one_smul, one_pow, one_mul, PiLp.smul_apply, smul_eq_mul,
    mul_pow, integral_const_mul]
  have hs : s ^ (n + 1) = s ^ (n - 1) * s ^ 2 := by
    rw [← pow_add]
    congr 1
    have := NeZero.pos n
    omega
  rw [hs]
  ring

/-! ### Two `L²` limit lemmas -/

section L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The triangle inequality for `L²` convergence to a moving target. -/
theorem tendsto_integral_norm_sub_sq_of_tendsto_of_tendsto {f h : ℕ → α → E} {g : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ) (hh : ∀ k, MemLp (h k) 2 μ)
    (h1 : Tendsto (fun k => ∫ x, ‖f k x - g x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (h2 : Tendsto (fun k => ∫ x, ‖g x - h k x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x - h k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hlim := (h1.const_mul 2).add (h2.const_mul 2)
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) (fun k => ?_) hlim
  have i0 : Integrable (fun x => ‖f k x - h k x‖ ^ 2) μ :=
    MemLp.integrable_norm_sq ((hf k).sub (hh k))
  have i1 : Integrable (fun x => ‖f k x - g x‖ ^ 2) μ := MemLp.integrable_norm_sq ((hf k).sub hg)
  have i2 : Integrable (fun x => ‖g x - h k x‖ ^ 2) μ := MemLp.integrable_norm_sq (hg.sub (hh k))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
  refine integral_mono i0 ((i1.const_mul 2).add (i2.const_mul 2)) fun x => ?_
  have := norm_sub_le_norm_sub_add_norm_sub (f k x) (g x) (h k x)
  have h5 : ‖f k x - h k x‖ ^ 2 ≤ (‖f k x - g x‖ + ‖g x - h k x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) this 2
  nlinarith [sq_nonneg (‖f k x - g x‖ - ‖g x - h k x‖)]

/-- **Strong times weak convergence.** If `f_k → F` strongly in `L²`, `g_k ⇀ G` weakly in `L²` with
`∫ ‖g_k‖² ≤ C`, and `w` is bounded, then `∫ f_k ⟪g_k, w⟫ → ∫ F ⟪G, w⟫`. -/
theorem tendsto_integral_mul_inner_of_tendsto {f : ℕ → α → ℝ} {F : α → ℝ} {g : ℕ → α → E}
    {G : α → E} {w : α → E} (hf : ∀ k, MemLp (f k) 2 μ) (hF : MemLp F 2 μ)
    (hg : ∀ k, MemLp (g k) 2 μ) (hw : AEStronglyMeasurable w μ) {M : ℝ} (hM : 0 ≤ M)
    (hwM : ∀ x, ‖w x‖ ≤ M) {C : ℝ} (hbd : ∀ k, ∫ x, ‖g k x‖ ^ 2 ∂μ ≤ C)
    (hconv : Tendsto (fun k => ∫ x, (f k x - F x) ^ 2 ∂μ) atTop (𝓝 0))
    (hweak : WeakTendstoL2 μ g G) :
    Tendsto (fun k => ∫ x, f k x * ⟪g k x, w x⟫ ∂μ) atTop (𝓝 (∫ x, F x * ⟪G x, w x⟫ ∂μ)) := by
  have hFw : MemLp (fun x => F x • w x) 2 μ := by
    refine (hF.const_mul M).of_le (hF.aestronglyMeasurable.smul hw)
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hwM x) (abs_nonneg _)
  have hgw : ∀ k, MemLp (fun x => ⟪g k x, w x⟫) 2 μ := fun k => by
    refine ((hg k).norm.const_mul M).of_le ((hg k).aestronglyMeasurable.inner hw)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM, abs_norm]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hwM x) (norm_nonneg _)
  have hpt : ∀ k x, f k x * ⟪g k x, w x⟫ = (f k x - F x) * ⟪g k x, w x⟫ + ⟪g k x, F x • w x⟫ :=
    fun k x => by rw [inner_smul_right]; ring
  have i1 : ∀ k, Integrable (fun x => (f k x - F x) * ⟪g k x, w x⟫) μ := fun k =>
    ((hf k).sub hF).integrable_mul (hgw k)
  have i2 : ∀ k, Integrable (fun x => ⟪g k x, F x • w x⟫) μ := fun k =>
    MemLp.integrable_inner_two (hg k) hFw
  have e : ∀ k, ∫ x, f k x * ⟪g k x, w x⟫ ∂μ =
      ∫ x, (f k x - F x) * ⟪g k x, w x⟫ ∂μ + ∫ x, ⟪g k x, F x • w x⟫ ∂μ := fun k => by
    simp_rw [hpt k]
    exact integral_add (i1 k) (i2 k)
  have hcs : ∀ k, ‖∫ x, (f k x - F x) * ⟪g k x, w x⟫ ∂μ‖ ≤
      √(∫ x, (f k x - F x) ^ 2 ∂μ) * √(M ^ 2 * C) := by
    intro k
    have h := abs_integral_inner_le (hgw k) ((hf k).sub hF)
    simp only [RCLike.inner_apply, conj_trivial, Pi.sub_apply, Real.norm_eq_abs, sq_abs] at h
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    calc ∫ x, ⟪g k x, w x⟫ ^ 2 ∂μ ≤ ∫ x, M ^ 2 * ‖g k x‖ ^ 2 ∂μ := by
          refine integral_mono (hgw k).integrable_sq
            ((MemLp.integrable_norm_sq (hg k)).const_mul _) fun x => ?_
          have h1 := abs_real_inner_le_norm (g k x) (w x)
          have h2 : ‖g k x‖ * ‖w x‖ ≤ M * ‖g k x‖ := by
            rw [mul_comm M]
            exact mul_le_mul_of_nonneg_left (hwM x) (norm_nonneg _)
          calc ⟪g k x, w x⟫ ^ 2 = |⟪g k x, w x⟫| ^ 2 := (sq_abs _).symm
            _ ≤ (M * ‖g k x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
            _ = M ^ 2 * ‖g k x‖ ^ 2 := by ring
      _ ≤ M ^ 2 * C := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hbd k) (sq_nonneg M)
  have hlim1 : Tendsto (fun k => ∫ x, (f k x - F x) * ⟪g k x, w x⟫ ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm hcs ?_
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hconv).mul_const √(M ^ 2 * C)
  have hlim2 := hweak (fun x => F x • w x) hFw
  have hval : ∫ x, F x * ⟪G x, w x⟫ ∂μ = 0 + ∫ x, ⟪G x, F x • w x⟫ ∂μ := by
    simp_rw [inner_smul_right, zero_add]
  rw [hval]
  simp_rw [e]
  exact hlim1.add hlim2

end L2

end InnerVariational
