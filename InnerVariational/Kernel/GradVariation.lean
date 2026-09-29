/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import InnerVariational.Basic.SphereIntegral
public import InnerVariational.Kernel.IBP
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Registry.Sobolev
import InnerVariational.Sobolev.LocalLipschitz

/-!
# The quadratic part of the inner variation

For `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`, the inner variation of the Alt–Caffarelli functional splits as
`∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u) + ∫ χ div ξ`. This file collects the calculus of the first,
quadratic, part and of divergences of Lipschitz test fields.

## Main statements

* `Kernel.gradVariation u ξ = |∇u|² div ξ − 2 ∇u · Dξ ∇u`, with measurability, bounds and
  integrability (`abs_gradVariation_le`, `integrable_gradVariation`).
* `Kernel.integral_divergence_eq_zero`: `∫ div ξ = 0` for a Lipschitz test field.
* `Kernel.divergence_smul_eq`, `Kernel.gradVariation_smul_eq`: the product rules for
  `div (f ξ)` and for the quadratic part along `f ξ`.
* `Kernel.lipschitzWith_smul_of_support'`, `Kernel.isLipTestField_smul`: products of a Lipschitz
  test field with a function that is Lipschitz and bounded on its support.
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

theorem measurable_fderiv_apply (F : Rn n → ℝ) {ξ : Rn n → Rn n} (hξ : Measurable ξ) :
    Measurable fun y => fderiv ℝ F y (ξ y) :=
  Continuous.measurable2 (c := fun (L : Rn n →L[ℝ] ℝ) (v : Rn n) => L v)
    isBoundedBilinearMap_apply.continuous (measurable_fderiv ℝ F) hξ

/-- The product rule for the divergence: if `f` has derivative `f'` at `y` and `ξ` is
differentiable at `y`, then `div (f ξ) = f div ξ + f'(ξ)` at `y`. -/
theorem divergence_smul_eq {f : Rn n → ℝ} {ξ : Rn n → Rn n} {f' : Rn n →L[ℝ] ℝ} {y : Rn n}
    (hf : HasFDerivAt f f' y) (hξ : DifferentiableAt ℝ ξ y) :
    divergence (fun z => f z • ξ z) y = f y * divergence ξ y + f' (ξ y) := by
  have hd : HasFDerivAt (fun z => f z • ξ z) (f y • fderiv ℝ ξ y + f'.smulRight (ξ y)) y :=
    hf.smul hξ.hasFDerivAt
  rw [divergence, divergence, hd.fderiv, ContinuousLinearMap.coe_add,
    ContinuousLinearMap.coe_smul, map_add, map_smul, ContinuousLinearMap.coe_smulRight,
    LinearMap.trace_smulRight, smul_eq_mul]
  rfl

/-- The product rule for the quadratic part of the inner variation. If `f` has derivative `f'`
at `y` and `ξ` is differentiable at `y`, then at `y`,
`|∇u|² div(fξ) − 2 ∇u·D(fξ)∇u = f (|∇u|² div ξ − 2 ∇u·Dξ∇u) + f'(ξ) |∇u|² − 2 f'(∇u) (∇u·ξ)`. -/
theorem gradVariation_smul_eq {u f : Rn n → ℝ} {ξ : Rn n → Rn n} {f' : Rn n →L[ℝ] ℝ}
    {y : Rn n} (hf : HasFDerivAt f f' y) (hξ : DifferentiableAt ℝ ξ y) :
    gradVariation u (fun z => f z • ξ z) y = f y * gradVariation u ξ y +
      f' (ξ y) * ‖gradient u y‖ ^ 2 - 2 * (f' (gradient u y) * ⟪gradient u y, ξ y⟫) := by
  have hd : HasFDerivAt (fun z => f z • ξ z) (f y • fderiv ℝ ξ y + f'.smulRight (ξ y)) y :=
    hf.smul hξ.hasFDerivAt
  have hdiv := divergence_smul_eq hf hξ
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

/-- If `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)` and `f` is Lipschitz and bounded on `Ω`, then
`f ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. -/
theorem isLipTestField_smul {Ω : Set (Rn n)} {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ)
    {f : Rn n → ℝ} {Lf : ℝ≥0} (hf : LipschitzOnWith Lf f Ω) {A : ℝ}
    (hfA : ∀ y ∈ Ω, |f y| ≤ A) : IsLipTestField Ω fun y => f y • ξ y := by
  obtain ⟨⟨D, hD⟩, hc, hΩ⟩ := hξ
  obtain ⟨M, hM⟩ := hD.continuous.bounded_above_of_compact_support hc
  have hL : LipschitzWith _ (fun y => f y • ξ y) :=
    lipschitzWith_smul_of_support' (hf.mono hΩ) (fun y hy => hfA y (hΩ hy)) hD
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hM
  have hsupp : Function.support (fun y => f y • ξ y) ⊆ tsupport ξ := fun y hy =>
    subset_tsupport ξ fun h0 => hy (by simp only [h0, smul_zero])
  have hts : tsupport (fun y => f y • ξ y) ⊆ tsupport ξ :=
    closure_minimal hsupp (isClosed_tsupport ξ)
  exact ⟨⟨_, hL⟩, hc.mono' hsupp, hts.trans hΩ⟩

end Kernel

end InnerVariational
