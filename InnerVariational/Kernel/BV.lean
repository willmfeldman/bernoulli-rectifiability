/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.RellichPohozaev
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Hom
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.Energy
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Registry.Sobolev
import InnerVariational.Sobolev.LocalLipschitz

/-!
# Lemma 3.3: the divergence estimate for `χ`

Lemma 3.3 of Kriventsov–Weiss (full reference below): if `(u, χ)` is a variational solution on `Ω`
and `B_{2r}(x) ⋐ Ω`, then `χ ∈ BV(B_r(x))` with `∫_{B_r(x)} |∇χ| ≤ C r^{n-1}`, `C = C(C_V, n)`.

We formalize the estimate that the paper proves:
`|∫ χ div ξ| ≤ C(C_V, n) sup |ξ| r^{n-1}` for `ξ ∈ C^{0,1}_c(B_{3r/2}(x); ℝⁿ)`,
with the explicit constant `C(C_V, n) = 2^{n+1} |B_1| C_V²`. BV membership itself is not
stated here: the structure theorem for functions of bounded variation (Evans–Gariepy, Thm 5.1),
`Registry.exists_isGaussGreenPair_of_integral_divergence_le`, turns the estimate into a perimeter
measure where it is needed.

## Main statements

* `Kernel.gradVariation u ξ = |∇u|² div ξ − 2 ∇u · Dξ ∇u`, the quadratic part of the inner
  variation.
* `IsVariationalSolution.integral_chi_mul_divergence_eq`:
  `∫ χ div ξ = −∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)`.
* `IsVariationalSolution.abs_integral_gradVariation_le`: for a cutoff `η ≥ 0` with `η = 1` on
  `spt ξ`, `|∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)| ≤ C_V sup|ξ| ∫ |∇u · ∇η|`.
* `IsVariationalSolution.chi_divergence_bound`: Lemma 3.3. Variants: `chi_divergence_bound_iSup`
  (with `⨆ y, ‖ξ y‖`) and `abs_setIntegral_divergence_le` (on `Ω ∩ {χ = 1}`, the form taken by the
  BV structure theorem).

## Proof

The paper mollifies `u` and uses that `Δu` is a nonnegative measure. We avoid mollifiers. Let
`F_k(t) = S((k+1)t − 1)`, with `S` a smooth step, so that `F_k(u) → χ_{u>0}` and `F_k(u)` vanishes
near `{u = 0}`. Testing the inner variation with `ζ_k = F_k(u) ξ`, which is supported in
`{u > 0}` where `χ = 1`, gives `∫ (|∇u|² div ζ_k − 2 ∇u·Dζ_k∇u) = −∫ div ζ_k = 0`. The chain rule
turns this into
`∫ F_k(u) (|∇u|² div ξ − 2 ∇u·Dξ∇u) = ∫ F_k'(u) (∇u · ξ) |∇u|²`.
Since `∇u = 0` on `{u = 0}`, the left side tends to `∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u) = −∫ χ div ξ`.
The right side is bounded by `C_V sup|ξ| ∫ F_k'(u) |∇u|² η = −C_V sup|ξ| ∫ F_k(u) ∇u·∇η`
(the energy identity `IsLipHarmonicPos.integral_comp_mul_inner_gradient`). This plays the role
of the paper's bound `Δu(B_{3r/2}(x)) ≤ −∫ ∇u·∇η ≤ C r^{n-1}`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, CRC Press, 2015.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Kernel

/-! ### The quadratic part of the inner variation -/

/-- The quadratic part of the inner variation (3.5): `|∇u|² div ξ − 2 ∇u · Dξ ∇u`. -/
def gradVariation (u : Rn n → ℝ) (ξ : Rn n → Rn n) (y : Rn n) : ℝ :=
  ‖gradient u y‖ ^ 2 * divergence ξ y - 2 * ⟪gradient u y, fderiv ℝ ξ y (gradient u y)⟫

theorem measurable_divergence (ξ : Rn n → Rn n) : Measurable (divergence ξ) := by
  set T : (Rn n →L[ℝ] Rn n) →ₗ[ℝ] ℝ :=
    (LinearMap.trace ℝ (Rn n)).comp (ContinuousLinearMap.coeLM ℝ)
  have hT : Continuous T := T.continuous_of_finiteDimensional
  have e : divergence ξ = fun y => T (fderiv ℝ ξ y) := rfl
  rw [e]
  exact hT.measurable.comp (measurable_fderiv ℝ ξ)

/-- `|div ξ| ≤ n L` for an `L`-Lipschitz field `ξ`. -/
theorem abs_divergence_le {ξ : Rn n → Rn n} {D : ℝ≥0} (hξ : LipschitzWith D ξ) (y : Rn n) :
    |divergence ξ y| ≤ n * D := by
  by_cases hy : DifferentiableAt ℝ ξ y
  · rw [divergence_eq_sum_fderiv hy]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hcomp : ∀ i, LipschitzWith D (fun z => ξ z i) :=
      fun i a b => (PiLp.edist_apply_le _ _ i).trans (hξ a b)
    calc ∑ i, |fderiv ℝ (fun z => ξ z i) y (EuclideanSpace.single i 1)|
        ≤ ∑ _i : Fin n, (D : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [← Real.norm_eq_abs]
          refine ((fderiv ℝ (fun z => ξ z i) y).le_opNorm _).trans ?_
          rw [PiLp.norm_single, norm_one, mul_one]
          exact norm_fderiv_le_of_lipschitz ℝ (hcomp i)
      _ = n * D := by simp
  · rw [show divergence ξ y = 0 by simp [divergence, fderiv_zero_of_not_differentiableAt hy],
      abs_zero]
    positivity

theorem integrable_divergence {ξ : Rn n → Rn n} {D : ℝ≥0} (hξ : LipschitzWith D ξ)
    (hc : HasCompactSupport ξ) : Integrable (divergence ξ) :=
  integrable_of_bound_of_isCompact (K := tsupport ξ) hc
    (measurable_divergence ξ).aestronglyMeasurable (M := n * D)
    (fun y _ => by rw [Real.norm_eq_abs]; exact abs_divergence_le hξ y)
    (fun _ hy => divergence_eq_zero_of_notMem_tsupport hy)

/-- `∫ div ξ = 0` for a Lipschitz test field (Lipschitz integration by parts with `f = 1`). -/
theorem integral_divergence_eq_zero {U : Set (Rn n)} (hU : IsOpen U) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField U ξ) : ∫ y, divergence ξ y = 0 := by
  have := Registry.integral_mul_divergence_eq_neg hU (f := fun _ => (1 : ℝ))
    (fun _ _ => ⟨0, univ, univ_mem, (LipschitzWith.const (1 : ℝ)).lipschitzOnWith⟩) hξ
  simpa [gradient] using this

theorem measurable_gradVariation (u : Rn n → ℝ) (ξ : Rn n → Rn n) :
    Measurable (gradVariation u ξ) := by
  have h1 : Measurable fun y => fderiv ℝ ξ y (gradient u y) :=
    Continuous.measurable2 (c := fun (L : Rn n →L[ℝ] Rn n) (v : Rn n) => L v)
      isBoundedBilinearMap_apply.continuous (measurable_fderiv ℝ ξ) (measurable_gradient u)
  exact (((measurable_gradient u).norm.pow_const 2).mul (measurable_divergence ξ)).sub
    (((measurable_gradient u).inner h1).const_mul 2)

theorem gradVariation_eq_zero_of_notMem_tsupport {u : Rn n → ℝ} {ξ : Rn n → Rn n} {y : Rn n}
    (hy : y ∉ tsupport ξ) : gradVariation u ξ y = 0 := by
  simp [gradVariation, divergence_eq_zero_of_notMem_tsupport hy,
    fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]

theorem gradVariation_eq_zero_of_gradient_eq_zero {u : Rn n → ℝ} {ξ : Rn n → Rn n} {y : Rn n}
    (hy : gradient u y = 0) : gradVariation u ξ y = 0 := by
  simp [gradVariation, hy]

theorem abs_gradVariation_le {u : Rn n → ℝ} {ξ : Rn n → Rn n} {D : ℝ≥0}
    (hξ : LipschitzWith D ξ) {Cg : ℝ} {y : Rn n} (hy : ‖gradient u y‖ ≤ Cg) :
    |gradVariation u ξ y| ≤ Cg ^ 2 * (n * D) + 2 * (Cg ^ 2 * D) := by
  have hsq : ‖gradient u y‖ ^ 2 ≤ Cg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hdiv := abs_divergence_le hξ y
  have hD : ‖fderiv ℝ ξ y‖ ≤ D := norm_fderiv_le_of_lipschitz ℝ hξ
  have hq : |⟪gradient u y, fderiv ℝ ξ y (gradient u y)⟫| ≤ Cg ^ 2 * D := by
    rw [← Real.norm_eq_abs]
    refine (norm_inner_le_norm _ _).trans ?_
    have h1 : ‖fderiv ℝ ξ y (gradient u y)‖ ≤ D * ‖gradient u y‖ :=
      ((fderiv ℝ ξ y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    calc ‖gradient u y‖ * ‖fderiv ℝ ξ y (gradient u y)‖
        ≤ ‖gradient u y‖ * (D * ‖gradient u y‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖gradient u y‖ ^ 2 * D := by ring
      _ ≤ Cg ^ 2 * D := mul_le_mul_of_nonneg_right hsq D.2
  unfold gradVariation
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (sq_nonneg ‖gradient u y‖)]
    exact mul_le_mul hsq hdiv (abs_nonneg _) (sq_nonneg _)
  · rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hq zero_le_two

theorem integrable_gradVariation {U : Set (Rn n)} {u : Rn n → ℝ} {ξ : Rn n → Rn n}
    (hξ : IsLipTestField U ξ) {Cg : ℝ} (hCg : ∀ y ∈ U, ‖gradient u y‖ ≤ Cg) :
    Integrable (gradVariation u ξ) := by
  obtain ⟨⟨D, hD⟩, hc, hU⟩ := hξ
  exact integrable_of_bound_of_isCompact (K := tsupport ξ) hc
    (measurable_gradVariation u ξ).aestronglyMeasurable
    (M := Cg ^ 2 * (n * D) + 2 * (Cg ^ 2 * D))
    (fun y hy => by rw [Real.norm_eq_abs]; exact abs_gradVariation_le hD (hCg y (hU hy)))
    (fun _ hy => gradVariation_eq_zero_of_notMem_tsupport hy)

/-- The product rule for the quadratic part of the inner variation. If `f` has derivative `f'`
at `y` and `ξ` is differentiable at `y`, then at `y`,
`|∇u|² div(fξ) − 2 ∇u·D(fξ)∇u = f (|∇u|² div ξ − 2 ∇u·Dξ∇u) + f'(ξ) |∇u|² − 2 f'(∇u) (∇u·ξ)`. -/
theorem gradVariation_smul_eq {u f : Rn n → ℝ} {ξ : Rn n → Rn n} {f' : Rn n →L[ℝ] ℝ}
    {y : Rn n} (hf : HasFDerivAt f f' y) (hξ : DifferentiableAt ℝ ξ y) :
    gradVariation u (fun z => f z • ξ z) y = f y * gradVariation u ξ y +
      f' (ξ y) * ‖gradient u y‖ ^ 2 - 2 * (f' (gradient u y) * ⟪gradient u y, ξ y⟫) := by
  have hd : HasFDerivAt (fun z => f z • ξ z) (f y • fderiv ℝ ξ y + f'.smulRight (ξ y)) y :=
    hf.smul hξ.hasFDerivAt
  have hdiv : divergence (fun z => f z • ξ z) y = f y * divergence ξ y + f' (ξ y) := by
    rw [divergence, divergence, hd.fderiv, ContinuousLinearMap.coe_add,
      ContinuousLinearMap.coe_smul, map_add, map_smul, ContinuousLinearMap.coe_smulRight,
      LinearMap.trace_smulRight, smul_eq_mul]
    rfl
  have hquad : ⟪gradient u y, fderiv ℝ (fun z => f z • ξ z) y (gradient u y)⟫ =
      f y * ⟪gradient u y, fderiv ℝ ξ y (gradient u y)⟫ +
        f' (gradient u y) * ⟪gradient u y, ξ y⟫ := by
    rw [hd.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, inner_add_right, inner_smul_right, inner_smul_right]
  rw [gradVariation, gradVariation, hdiv, hquad]
  ring

/-! ### Products with a function Lipschitz on the support -/

/-- If `g` is `Lg`-Lipschitz with `‖g‖ ≤ M` and `g = 0` off `K`, and `f` is `Lf`-Lipschitz with
`|f| ≤ A` on `K`, then `f • g` is `(A Lg + M Lf)`-Lipschitz. `f` is only controlled on `K`. -/
theorem lipschitzWith_smul_of_support' {f : Rn n → ℝ} {g : Rn n → Rn n} {K : Set (Rn n)}
    {Lf Lg : ℝ≥0} {A M : ℝ} (hf : LipschitzOnWith Lf f K) (hfA : ∀ y ∈ K, |f y| ≤ A)
    (hg : LipschitzWith Lg g) (hg0 : ∀ y ∉ K, g y = 0) (hgM : ∀ y, ‖g y‖ ≤ M) :
    LipschitzWith (Real.toNNReal (A * Lg + M * Lf)) (fun y => f y • g y) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  have key : ∀ a ∈ K, ∀ b, ‖f a • g a - f b • g b‖ ≤ (A * Lg + M * Lf) * dist a b := by
    intro a ha b
    have hA : 0 ≤ A := (abs_nonneg _).trans (hfA a ha)
    have hgd : ‖g a - g b‖ ≤ Lg * dist a b := by
      rw [← dist_eq_norm]; exact hg.dist_le_mul a b
    have hML : 0 ≤ M * Lf * dist a b := mul_nonneg (mul_nonneg hM Lf.2) dist_nonneg
    by_cases hb : b ∈ K
    · have e : f a • g a - f b • g b = (f a - f b) • g a + f b • (g a - g b) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul]
      have h1 : ‖f a - f b‖ * ‖g a‖ ≤ Lf * dist a b * M := by
        rw [← dist_eq_norm]
        exact mul_le_mul (hf.dist_le_mul a ha b hb) (hgM a) (norm_nonneg _)
          (mul_nonneg Lf.2 dist_nonneg)
      have h2 : ‖f b‖ * ‖g a - g b‖ ≤ A * (Lg * dist a b) := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul (hfA b hb) hgd (norm_nonneg _) hA
      nlinarith
    · have e : f a • g a - f b • g b = f a • (g a - g b) := by
        rw [hg0 b hb]; simp
      rw [e, norm_smul, Real.norm_eq_abs]
      have h2 : |f a| * ‖g a - g b‖ ≤ A * (Lg * dist a b) :=
        mul_le_mul (hfA a ha) hgd (norm_nonneg _) hA
      nlinarith
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm]
  have hK : (A * Lg + M * Lf) ≤ (Real.toNNReal (A * Lg + M * Lf) : ℝ) := Real.le_coe_toNNReal _
  by_cases ha : a ∈ K
  · exact (key a ha b).trans (mul_le_mul_of_nonneg_right hK dist_nonneg)
  · by_cases hb : b ∈ K
    · rw [norm_sub_rev, dist_comm]
      exact (key b hb a).trans (mul_le_mul_of_nonneg_right hK dist_nonneg)
    · simp only [hg0 a ha, hg0 b hb, smul_zero, sub_zero, norm_zero]
      exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg

/-! ### The smooth steps `F_k` -/

/-- The smooth steps `F_k(t) = S((k+1)t − 1)`, with `S = Real.smoothTransition`. `F_k = 0` on
`(−∞, 1/(k+1)]` and `F_k(t) → 1` for `t > 0`. -/
def smoothStep (k : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (((k : ℝ) + 1) * t - 1)

/-- The derivative of `smoothStep k`. -/
def smoothStep' (k : ℕ) (t : ℝ) : ℝ :=
  ((k : ℝ) + 1) * deriv Real.smoothTransition (((k : ℝ) + 1) * t - 1)

theorem hasDerivAt_smoothStep (k : ℕ) (t : ℝ) :
    HasDerivAt (smoothStep k) (smoothStep' k t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((k : ℝ) + 1) * t - 1) ((k : ℝ) + 1) t := by
    simpa using ((hasDerivAt_id' t).const_mul ((k : ℝ) + 1)).sub_const 1
  have h2 := (hasDerivAt_smoothTransition (((k : ℝ) + 1) * t - 1)).comp t h1
  unfold smoothStep smoothStep'
  exact h2.congr_deriv (mul_comm _ _)

theorem continuous_smoothStep (k : ℕ) : Continuous (smoothStep k) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

theorem continuous_smoothStep' (k : ℕ) : Continuous (smoothStep' k) :=
  continuous_const.mul (continuous_deriv_smoothTransition.comp (by fun_prop))

theorem smoothStep_nonneg (k : ℕ) (t : ℝ) : 0 ≤ smoothStep k t :=
  Real.smoothTransition.nonneg _

theorem smoothStep_le_one (k : ℕ) (t : ℝ) : smoothStep k t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem abs_smoothStep_le_one (k : ℕ) (t : ℝ) : |smoothStep k t| ≤ 1 := by
  rw [abs_of_nonneg (smoothStep_nonneg k t)]; exact smoothStep_le_one k t

theorem smoothStep'_nonneg (k : ℕ) (t : ℝ) : 0 ≤ smoothStep' k t :=
  mul_nonneg (by positivity) (deriv_smoothTransition_nonneg _)

theorem smoothStep_eq_zero {k : ℕ} {t : ℝ} (ht : t ≤ ((k : ℝ) + 1)⁻¹) : smoothStep k t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left ht hk.le
  rw [mul_inv_cancel₀ hk.ne'] at this
  linarith

theorem tendsto_smoothStep {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => smoothStep k t) atTop (𝓝 1) :=
  tendsto_smoothTransition ht

theorem exists_bound_deriv_smoothTransition : ∃ B, ∀ s, |deriv Real.smoothTransition s| ≤ B := by
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 1)) fun s hs => ?_
    simp only [mem_Icc, not_and_or, not_le] at hs
    exact deriv_smoothTransition_eq_zero hs
  obtain ⟨B, hB⟩ := continuous_deriv_smoothTransition.bounded_above_of_compact_support hs
  exact ⟨B, fun s => by simpa only [Real.norm_eq_abs] using hB s⟩

theorem exists_bound_smoothStep' (k : ℕ) : ∃ B, ∀ t, |smoothStep' k t| ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_deriv_smoothTransition
  refine ⟨((k : ℝ) + 1) * B, fun t => ?_⟩
  rw [smoothStep', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

theorem exists_lipschitzWith_smoothStep (k : ℕ) : ∃ L, LipschitzWith L (smoothStep k) := by
  obtain ⟨B, hB⟩ := exists_bound_smoothStep' k
  refine ⟨Real.toNNReal B, lipschitzWith_of_nnnorm_deriv_le
    (fun t => (hasDerivAt_smoothStep k t).differentiableAt) fun t => ?_⟩
  rw [(hasDerivAt_smoothStep k t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal',
    Real.norm_eq_abs]
  exact (hB t).trans (le_max_left _ _)

end Kernel

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

open Kernel

/-- `|∇u| ≤ C_V` on `Ω`. -/
theorem norm_gradient_le (h : IsVariationalSolution Ω C u χ) {y : Rn n} (hy : y ∈ Ω) :
    ‖gradient u y‖ ≤ C := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 h.isOpen y hy
  rw [Kernel.norm_gradient_eq]
  exact norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds y hr) (h.lipschitzOnWith y r hrΩ)

/-- The inner variation splits: `∫ χ div ξ = −∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u)` (proof of
Lemma 3.3). -/
theorem integral_chi_mul_divergence_eq (h : IsVariationalSolution Ω C u χ) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) :
    ∫ y, χ y * divergence ξ y = -∫ y, gradVariation u ξ y := by
  have hIV := h.innerVariation_eq_zero ξ hξ
  have hJ := integrable_gradVariation hξ fun y hy => h.norm_gradient_le hy
  obtain ⟨⟨D, hD⟩, hc, hU⟩ := hξ
  have hχ : Integrable fun y => χ y * divergence ξ y := by
    have e : (fun y => χ y * divergence ξ y) = fun y => Ω.indicator χ y * divergence ξ y := by
      funext y
      by_cases hy : y ∈ Ω
      · rw [indicator_of_mem hy]
      · rw [divergence_eq_zero_of_notMem_tsupport (fun h' => hy (hU h')), mul_zero, mul_zero]
    rw [e]
    refine integrable_of_bound_of_isCompact (K := tsupport ξ) hc
      (h.measurable_chi.mul (measurable_divergence ξ)).aestronglyMeasurable (M := 1 * (n * D))
      (fun y hy => ?_) (fun y hy => by rw [divergence_eq_zero_of_notMem_tsupport hy, mul_zero])
    rw [Real.norm_eq_abs, abs_mul, indicator_of_mem (hU hy)]
    exact mul_le_mul (h.abs_chi_le_one (hU hy)) (abs_divergence_le hD y) (abs_nonneg _)
      zero_le_one
  have e2 : (fun y => (‖gradient u y‖ ^ 2 + χ y) * divergence ξ y -
      2 * ⟪gradient u y, fderiv ℝ ξ y (gradient u y)⟫) =
      fun y => gradVariation u ξ y + χ y * divergence ξ y := by
    funext y; simp only [gradVariation]; ring
  rw [innerVariation, e2, integral_add hJ hχ] at hIV
  linarith

/-- **Step 1 of Lemma 3.3.** Testing the inner variation with `ζ_k = F_k(u) ξ`:
`∫ F_k(u) (|∇u|² div ξ − 2 ∇u·Dξ∇u) = ∫ F_k'(u) (∇u · ξ) |∇u|²`. -/
theorem integral_smoothStep_mul_gradVariation (h : IsVariationalSolution Ω C u χ)
    {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) (k : ℕ) :
    ∫ y, smoothStep k (u y) * gradVariation u ξ y =
      ∫ y, smoothStep' k (u y) * (⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2) := by
  have hH := h.isLipHarmonicPos
  obtain ⟨⟨D, hD⟩, hξc, hξΩ⟩ := hξ
  have hK : IsCompact (tsupport ξ) := hξc
  have hξ0 : ∀ y ∉ tsupport ξ, ξ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  obtain ⟨M, hM⟩ := hD.continuous.bounded_above_of_compact_support hξc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC : ∀ y ∈ Ω, ‖gradient u y‖ ≤ C := fun y hy => h.norm_gradient_le hy
  have huK : ContinuousOn u (tsupport ξ) := h.continuousOn.mono hξΩ
  obtain ⟨Lu, hLu⟩ := (hH.locallyLipschitzOn.mono hξΩ).exists_lipschitzOnWith_of_compact hK
  have hδ0 : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
  obtain ⟨LF, hLF⟩ := exists_lipschitzWith_smoothStep k
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : Rn n → Rn n, ζ = fun y => smoothStep k (u y) • ξ y := ⟨_, rfl⟩
  -- `ζ` is a Lipschitz test field supported in `{u > 0}`
  have hK'c : IsClosed (tsupport ξ ∩ u ⁻¹' Ici ((k : ℝ) + 1)⁻¹) :=
    huK.preimage_isClosed_of_isClosed (isClosed_tsupport ξ) isClosed_Ici
  have hsupp : Function.support ζ ⊆ tsupport ξ ∩ u ⁻¹' Ici ((k : ℝ) + 1)⁻¹ := by
    intro y hy
    rw [hζdef] at hy
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hy
    refine ⟨subset_tsupport ξ hy.2, ?_⟩
    by_contra hlt
    exact hy.1 (smoothStep_eq_zero (le_of_lt (not_le.1 hlt)))
  have hts : tsupport ζ ⊆ tsupport ξ ∩ u ⁻¹' Ici ((k : ℝ) + 1)⁻¹ := closure_minimal hsupp hK'c
  have hK'V : tsupport ξ ∩ u ⁻¹' Ici ((k : ℝ) + 1)⁻¹ ⊆ Ω ∩ {x | 0 < u x} :=
    fun y hy => ⟨hξΩ hy.1, hδ0.trans_le hy.2⟩
  have hζL : ∃ L, LipschitzWith L ζ := by
    rw [hζdef]
    exact ⟨_, lipschitzWith_smul_of_support' (f := fun y => smoothStep k (u y))
      (hLF.comp_lipschitzOnWith hLu) (fun y _ => abs_smoothStep_le_one k (u y)) hD hξ0 hM⟩
  have hζ : IsLipTestField Ω ζ :=
    ⟨hζL, hξc.mono' (hsupp.trans inter_subset_left),
      hts.trans (hK'V.trans inter_subset_left)⟩
  -- `∫ (|∇u|² div ζ − 2 ∇u·Dζ∇u) = 0`
  have hζ0 : ∫ y, gradVariation u ζ y = 0 := by
    have h1 := h.integral_chi_mul_divergence_eq hζ
    have h2 : ∫ y, χ y * divergence ζ y = ∫ y, divergence ζ y := by
      refine integral_congr_ae ?_
      filter_upwards [h.ae_chi_eq_one] with y hy
      by_cases hyζ : y ∈ tsupport ζ
      · have := hK'V (hts hyζ)
        rw [hy this.1 this.2, one_mul]
      · rw [divergence_eq_zero_of_notMem_tsupport hyζ, mul_zero]
    rw [h2, integral_divergence_eq_zero h.isOpen hζ] at h1
    linarith
  -- the chain rule, a.e.
  have hpt : ∀ᵐ y, gradVariation u ζ y = smoothStep k (u y) * gradVariation u ξ y -
      smoothStep' k (u y) * (⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2) := by
    filter_upwards [hD.ae_differentiableAt] with y hy
    by_cases hyV : y ∈ Ω ∧ 0 < u y
    · have hu : HasFDerivAt u (fderiv ℝ u y) y :=
        ((hH.contDiffOn.contDiffAt (hH.isOpen_pos.mem_nhds hyV)).differentiableAt
          (by norm_num)).hasFDerivAt
      have hFu : HasFDerivAt (fun z => smoothStep k (u z))
          (smoothStep' k (u y) • fderiv ℝ u y) y :=
        (hasDerivAt_smoothStep k (u y)).comp_hasFDerivAt y hu
      rw [hζdef, gradVariation_smul_eq hFu hy]
      have hsq : fderiv ℝ u y (gradient u y) = ‖gradient u y‖ ^ 2 := by
        rw [← Kernel.inner_gradient_left, real_inner_self_eq_norm_sq]
      have hxi : fderiv ℝ u y (ξ y) = ⟪gradient u y, ξ y⟫ :=
        (Kernel.inner_gradient_left _ _ _).symm
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hsq, hxi, smul_eq_mul,
        smul_eq_mul]
      ring
    · by_cases hyΩ : y ∈ Ω
      · have hu0 : u y = 0 :=
          le_antisymm (not_lt.1 fun hp => hyV ⟨hyΩ, hp⟩) (h.nonneg y hyΩ)
        have hg0 := hH.gradient_eq_zero_of_eq_zero hyΩ hu0
        rw [gradVariation_eq_zero_of_gradient_eq_zero hg0,
          gradVariation_eq_zero_of_gradient_eq_zero hg0, hg0]
        simp
      · have hyK : y ∉ tsupport ξ := fun h' => hyΩ (hξΩ h')
        have hyζ : y ∉ tsupport ζ := fun h' => hyK (hts h').1
        rw [gradVariation_eq_zero_of_notMem_tsupport hyζ,
          gradVariation_eq_zero_of_notMem_tsupport hyK, hξ0 y hyK]
        simp
  -- integrability
  obtain ⟨BF, hBF⟩ := exists_bound_smoothStep' k
  have hI1 : Integrable fun y => smoothStep k (u y) * gradVariation u ξ y :=
    integrable_mul_of_isCompact hK
      (aestronglyMeasurable_comp_mul hK.measurableSet huK (continuous_smoothStep k)
        (measurable_gradVariation u ξ)) (A := 1)
      (fun y _ => by rw [Real.norm_eq_abs]; exact abs_smoothStep_le_one k (u y))
      (B := (C : ℝ) ^ 2 * (n * D) + 2 * ((C : ℝ) ^ 2 * D))
      (fun y hy => by rw [Real.norm_eq_abs]; exact abs_gradVariation_le hD (hC y (hξΩ hy)))
      (fun y hy => gradVariation_eq_zero_of_notMem_tsupport hy)
  have hm : Measurable fun y => ⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2 :=
    ((measurable_gradient u).inner hD.continuous.measurable).mul
      ((measurable_gradient u).norm.pow_const 2)
  have hI2 : Integrable fun y =>
      smoothStep' k (u y) * (⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2) := by
    refine integrable_mul_of_isCompact hK
      (aestronglyMeasurable_comp_mul hK.measurableSet huK (continuous_smoothStep' k) hm)
      (A := BF) (B := C * M * C ^ 2)
      (fun y _ => by rw [Real.norm_eq_abs]; exact hBF (u y)) (fun y hy => ?_)
      (fun y hy => by rw [hξ0 y hy, inner_zero_right, zero_mul])
    have hCy := hC y (hξΩ hy)
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul ((norm_inner_le_norm _ _).trans
      (mul_le_mul hCy (hM y) (norm_nonneg _) C.2)) (pow_le_pow_left₀ (norm_nonneg _) hCy 2)
      (by positivity) (mul_nonneg C.2 hM0)
  rw [integral_congr_ae hpt, integral_sub hI1 hI2] at hζ0
  linarith

/-- **Step 2 of Lemma 3.3.** With `|ξ| ≤ M`, `η ≥ 0` a Lipschitz cutoff with compact support in
`Ω` and `η = 1` on `spt ξ`: `|∫ F_k'(u) (∇u · ξ) |∇u|²| ≤ C_V M ∫ |∇u · ∇η|`. This is the
paper's bound on the Laplacian measure, `Δu(B_{3r/2}(x)) ≤ −∫ ∇u·∇η` (first display in the proof
of Lemma 3.3). -/
theorem abs_integral_smoothStep'_le (h : IsVariationalSolution Ω C u χ) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) {η : Rn n → ℝ}
    (hη : ∃ L, LipschitzWith L η) (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y ∈ tsupport ξ, η y = 1) (k : ℕ) :
    |∫ y, smoothStep' k (u y) * (⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2)| ≤
      C * M * ∫ y, |⟪gradient u y, gradient η y⟫| := by
  have hH := h.isLipHarmonicPos
  obtain ⟨-, -, hξΩ⟩ := hξ
  obtain ⟨Lη, hLη⟩ := hη
  have hKη : IsCompact (tsupport η) := hηc
  have hξ0 : ∀ y ∉ tsupport ξ, ξ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC : ∀ y ∈ Ω, ‖gradient u y‖ ≤ C := fun y hy => h.norm_gradient_le hy
  have huKη : ContinuousOn u (tsupport η) := h.continuousOn.mono hηΩ
  obtain ⟨Aη, hAη⟩ := hLη.continuous.bounded_above_of_compact_support hηc
  have hIg : Integrable fun y => |⟪gradient u y, gradient η y⟫| := by
    refine integrable_of_bound_of_isCompact (K := tsupport η) hKη
      ((measurable_gradient u).inner (measurable_gradient η)).abs.aestronglyMeasurable
      (M := C * Lη) (fun y hy => ?_) (fun y hy => ?_)
    · rw [Real.norm_eq_abs, abs_abs, ← Real.norm_eq_abs]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hC y (hηΩ hy))
        (norm_gradient_le_of_lipschitz hLη y) (norm_nonneg _) C.2)
    · rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right, abs_zero]
  obtain ⟨BF, hBF⟩ := exists_bound_smoothStep' k
  have hE := hH.integral_comp_mul_inner_gradient (hasDerivAt_smoothStep k)
    (continuous_smoothStep' k) (δ := ((k : ℝ) + 1)⁻¹) (by positivity)
    (fun t ht => smoothStep_eq_zero ht) ⟨Lη, hLη⟩ hηc hηΩ
  have hI3 : Integrable fun y => smoothStep' k (u y) * ‖gradient u y‖ ^ 2 * η y := by
    refine integrable_mul_of_isCompact hKη
      ((aestronglyMeasurable_comp_mul hKη.measurableSet huKη (continuous_smoothStep' k)
        ((measurable_gradient u).norm.pow_const 2)).mul
        hLη.continuous.aestronglyMeasurable)
      (A := BF * C ^ 2) (B := Aη) (fun y hy => ?_) (fun y _ => hAη y)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
    exact mul_le_mul (hBF _) (pow_le_pow_left₀ (norm_nonneg _) (hC y (hηΩ hy)) 2)
      (by positivity) ((abs_nonneg _).trans (hBF 0))
  have hpt : ∀ y, ‖smoothStep' k (u y) * (⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2)‖ ≤
      C * M * (smoothStep' k (u y) * ‖gradient u y‖ ^ 2 * η y) := by
    intro y
    have hF0 := smoothStep'_nonneg k (u y)
    by_cases hyK : y ∈ tsupport ξ
    · have hi : |⟪gradient u y, ξ y⟫| ≤ C * M := by
        rw [← Real.norm_eq_abs]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hC y (hξΩ hyK)) (hM y) (norm_nonneg _) C.2)
      rw [hη1 y hyK, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hF0,
        abs_of_nonneg (sq_nonneg ‖gradient u y‖), mul_one]
      calc smoothStep' k (u y) * (|⟪gradient u y, ξ y⟫| * ‖gradient u y‖ ^ 2)
          ≤ smoothStep' k (u y) * ((C * M) * ‖gradient u y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi (sq_nonneg _)) hF0
        _ = C * M * (smoothStep' k (u y) * ‖gradient u y‖ ^ 2) := by ring
    · rw [hξ0 y hyK, inner_zero_right, zero_mul, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg C.2 hM0)
        (mul_nonneg (mul_nonneg hF0 (sq_nonneg _)) (hη0 y))
  have h1 := norm_integral_le_of_norm_le (hI3.const_mul (C * M)) (.of_forall hpt)
  rw [integral_const_mul, ← neg_neg (∫ y, smoothStep' k (u y) * ‖gradient u y‖ ^ 2 * η y),
    ← hE, Real.norm_eq_abs] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg C.2 hM0))
  refine (neg_le_abs _).trans ?_
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hIg (.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_smoothStep_le_one k (u y))

/-- **Step 3 of Lemma 3.3.** `∫ F_k(u) (|∇u|² div ξ − 2 ∇u·Dξ∇u) → ∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)`
by dominated convergence, since `F_k(u) → 1` on `{u > 0}` and `∇u = 0` on `{u = 0}`. -/
theorem tendsto_integral_smoothStep_mul_gradVariation (h : IsVariationalSolution Ω C u χ)
    {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    Tendsto (fun k : ℕ => ∫ y, smoothStep k (u y) * gradVariation u ξ y) atTop
      (𝓝 (∫ y, gradVariation u ξ y)) := by
  have hH := h.isLipHarmonicPos
  obtain ⟨⟨D, hD⟩, hξc, hξΩ⟩ := hξ
  have hK : IsCompact (tsupport ξ) := hξc
  have huK : ContinuousOn u (tsupport ξ) := h.continuousOn.mono hξΩ
  have hJ0 : ∀ y ∉ tsupport ξ, gradVariation u ξ y = 0 := fun y hy =>
    gradVariation_eq_zero_of_notMem_tsupport hy
  refine tendsto_integral_of_isCompact hK (fun k y hy => by rw [hJ0 y hy, mul_zero]) hJ0
    (fun k => aestronglyMeasurable_comp_mul hK.measurableSet huK (continuous_smoothStep k)
      (measurable_gradVariation u ξ)) (B := (C : ℝ) ^ 2 * (n * D) + 2 * ((C : ℝ) ^ 2 * D))
    (fun k y hy => ?_) (fun y hy => ?_)
  · rw [norm_mul, Real.norm_eq_abs (gradVariation u ξ y)]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (by rw [Real.norm_eq_abs]; exact abs_smoothStep_le_one k (u y))).trans
      (abs_gradVariation_le hD (h.norm_gradient_le (hξΩ hy)))
  · rcases (h.nonneg y (hξΩ hy)).lt_or_eq with hpos | h0
    · simpa using (tendsto_smoothStep hpos).mul_const (gradVariation u ξ y)
    · have := gradVariation_eq_zero_of_gradient_eq_zero (ξ := ξ)
        (hH.gradient_eq_zero_of_eq_zero (hξΩ hy) h0.symm)
      simp only [this, mul_zero]
      exact tendsto_const_nhds

/-- **The key estimate of Lemma 3.3.** Let `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)` with `|ξ| ≤ M`, and let `η ≥ 0`
be Lipschitz with compact support in `Ω` and `η = 1` on `spt ξ`. Then
`|∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)| ≤ C_V M ∫ |∇u · ∇η|`. -/
theorem abs_integral_gradVariation_le (h : IsVariationalSolution Ω C u χ) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) {η : Rn n → ℝ}
    (hη : ∃ L, LipschitzWith L η) (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y ∈ tsupport ξ, η y = 1) :
    |∫ y, gradVariation u ξ y| ≤ C * M * ∫ y, |⟪gradient u y, gradient η y⟫| := by
  refine le_of_tendsto (h.tendsto_integral_smoothStep_mul_gradVariation hξ).abs
    (.of_forall fun k => ?_)
  rw [h.integral_smoothStep_mul_gradVariation hξ k]
  exact h.abs_integral_smoothStep'_le hξ hM hη hηc hηΩ hη0 hη1 k

/-- **Lemma 3.3**, the estimate that the paper proves. If `B̄_{2r}(x) ⊆ Ω` and
`ξ ∈ C^{0,1}_c(B_{3r/2}(x); ℝⁿ)` with `|ξ| ≤ M`, then
`|∫ χ div ξ| ≤ 2^{n+1} |B_1| C_V² M r^{n-1}`.

The constant depends only on `C_V` and `n`, as in the paper. The paper then concludes
`χ ∈ BV(B_r(x))` with `∫_{B_r(x)} |∇χ| ≤ C r^{n-1}`. That step is the BV structure theorem
(`Registry.exists_isGaussGreenPair_of_integral_divergence_le`). -/
theorem chi_divergence_bound [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n} {r : ℝ}
    (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField (ball x (3 * r / 2)) ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) :
    |∫ y, χ y * divergence ξ y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * M * r ^ (n - 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hδ : 0 < r / 2 := by positivity
  set η := radialCutoff x (3 * r / 2) (r / 2) with hηdef
  have h2r : 3 * r / 2 + r / 2 = 2 * r := by ring
  have hηt : tsupport η ⊆ closedBall x (2 * r) := by
    rw [← h2r]; exact tsupport_radialCutoff_subset hδ
  have hξΩ : IsLipTestField Ω ξ :=
    hξ.mono ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hΩ)
  have hmain := h.abs_integral_gradVariation_le hξΩ hM ⟨_, lipschitzWith_radialCutoff hδ⟩
    (hasCompactSupport_radialCutoff hδ) (hηt.trans hΩ) radialCutoff_nonneg (fun y hy => by
      have := hξ.2.2 hy
      rw [mem_ball, dist_eq_norm] at this
      exact radialCutoff_eq_one hδ this.le)
  rw [h.integral_chi_mul_divergence_eq hξΩ, abs_neg]
  refine hmain.trans ?_
  -- `∫ |∇u·∇η| ≤ C_V (2/r) |B_{2r}|`
  have hgη : ∀ y, ‖gradient η y‖ ≤ 2 / r := fun y => by
    have := norm_gradient_le_of_lipschitz (lipschitzWith_radialCutoff (x := x)
      (s := 3 * r / 2) hδ) y
    rwa [Real.coe_toNNReal _ (inv_nonneg.2 hδ.le), inv_div] at this
  have hvol : volume.real (closedBall x (2 * r)) =
      (2 * r) ^ n * volume.real (ball (0 : Rn n) 1) := by
    rw [Measure.real, Measure.addHaar_closedBall _ _ (by positivity), finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), Measure.real]
  have hint : ∫ y, |⟪gradient u y, gradient η y⟫| ≤
      C * (2 / r) * volume.real (closedBall x (2 * r)) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall x (2 * r))
      (fun y hy => by
        rw [gradient_eq_zero_of_notMem_tsupport (fun h' => hy (hηt h')), inner_zero_right,
          abs_zero])]
    refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const
      measure_closedBall_lt_top fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_abs, ← Real.norm_eq_abs]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul (h.norm_gradient_le (hΩ hy)) (hgη y) (norm_nonneg _) C.2)
  calc (C : ℝ) * M * ∫ y, |⟪gradient u y, gradient η y⟫|
      ≤ C * M * (C * (2 / r) * volume.real (closedBall x (2 * r))) :=
        mul_le_mul_of_nonneg_left hint (mul_nonneg C.2 hM0)
    _ = 2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * M * r ^ (n - 1) := by
        rw [hvol]
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
          ⟨n - 1, (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm⟩
        simp only [Nat.add_sub_cancel]
        field_simp
        ring

/-- **Lemma 3.3** with `sup |ξ|` written as `⨆ y, ‖ξ y‖`, the form used with the BV structure
theorem. -/
theorem chi_divergence_bound_iSup [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    {r : ℝ} (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField (ball x (3 * r / 2)) ξ) :
    |∫ y, χ y * divergence ξ y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * (⨆ y, ‖ξ y‖) * r ^ (n - 1) := by
  obtain ⟨D, hD⟩ := hξ.1
  exact h.chi_divergence_bound hr hΩ hξ fun y =>
    le_ciSup (hD.continuous.norm.bddAbove_range_of_hasCompactSupport hξ.2.1.norm) y

/-- The set `{χ = 1}` in `Ω` is measurable. -/
theorem measurableSet_chi_eq_one (h : IsVariationalSolution Ω C u χ) :
    MeasurableSet (Ω ∩ {y | χ y = 1}) := by
  have e : Ω ∩ {y | χ y = 1} = Ω ∩ Ω.indicator χ ⁻¹' {1} := by
    ext y
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hy, h1⟩; exact ⟨hy, by rw [indicator_of_mem hy, h1]⟩
    · rintro ⟨hy, h1⟩; exact ⟨hy, by rwa [indicator_of_mem hy] at h1⟩
  rw [e]
  exact h.isOpen.measurableSet.inter (h.measurable_chi (measurableSet_singleton 1))

/-- **Lemma 3.3**, set form: with `E = Ω ∩ {χ = 1}` and `φ ∈ C^∞_c(B_{3r/2}(x); ℝⁿ)`,
`|∫_E div φ| ≤ 2^{n+1} |B_1| C_V² sup|φ| r^{n-1}`. This is the hypothesis of the BV structure
theorem (`Registry.exists_isGaussGreenPair_of_integral_divergence_le`) on `U = B_{3r/2}(x)`. -/
theorem abs_setIntegral_divergence_le [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    {r : ℝ} (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω) {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField (ball x (3 * r / 2)) φ) :
    |∫ y in Ω ∩ {y | χ y = 1}, divergence φ y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * (⨆ y, ‖φ y‖) * r ^ (n - 1) := by
  have hbΩ : ball x (3 * r / 2) ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hΩ
  have e : ∫ y in Ω ∩ {y | χ y = 1}, divergence φ y = ∫ y, χ y * divergence φ y := by
    rw [← integral_indicator h.measurableSet_chi_eq_one]
    refine integral_congr_ae (.of_forall fun y => ?_)
    change (Ω ∩ {y | χ y = 1}).indicator (divergence φ) y = χ y * divergence φ y
    by_cases hy : y ∈ Ω
    · rcases h.chi_mem y hy with h0 | h1
      · rw [indicator_of_notMem (fun h' => by rw [h'.2] at h0; exact zero_ne_one h0.symm), h0,
          zero_mul]
      · rw [indicator_of_mem (show y ∈ Ω ∩ {y | χ y = 1} from ⟨hy, h1⟩), h1, one_mul]
    · rw [indicator_of_notMem (fun h' => hy h'.1),
        divergence_eq_zero_of_notMem_tsupport (fun h' => hy (hbΩ (hφ.2.2 h'))), mul_zero]
  rw [e]
  exact h.chi_divergence_bound_iSup hr hΩ hφ.isLipTestField

end IsVariationalSolution

end InnerVariational
