/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import InnerVariational.Sobolev.Lipschitz
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Hom
public import GMTFoundations.Defs.Calculus

/-!
# Integration by parts for locally Lipschitz functions

This file extends the integration-by-parts formulas of `InnerVariational.Sobolev.Lipschitz`
from Lipschitz functions to functions that are only *locally* Lipschitz on an open set `Ω`, and
adds the divergence form.

## Main results

* `LocallyLipschitzOn.exists_lipschitzWith_eventuallyEq`: a function locally Lipschitz on an open
  set `Ω` agrees, near every point of a compact `K ⊆ Ω`, with a globally Lipschitz function.
* `LocallyLipschitzOn.integral_mul_fderiv_eq_neg`: `∫ f ∂ᵥg = -∫ g ∂ᵥf` for `f` locally Lipschitz
  on `Ω` and `g` Lipschitz with compact support in `Ω`.
* `InnerVariational.integral_mul_divergence_eq_neg_of_locallyLipschitzOn`: `∫ f div ξ = -∫ ⟪∇f, ξ⟫`
  for `f` locally Lipschitz on `Ω` and `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

@[expose] public noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → ℝ} {Ω K : Set E}

/-- A function locally Lipschitz on an open set `Ω` agrees, in a neighbourhood of every point of a
compact set `K ⊆ Ω`, with a single globally Lipschitz function. -/
theorem LocallyLipschitzOn.exists_lipschitzWith_eventuallyEq (hΩ : IsOpen Ω)
    (hf : LocallyLipschitzOn Ω f) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ (C : ℝ≥0) (F : E → ℝ), LipschitzWith C F ∧ ∀ x ∈ K, f =ᶠ[𝓝 x] F := by
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨C, hC⟩ := (hf.mono hLΩ).exists_lipschitzOnWith_of_compact hL
  obtain ⟨F, hF, hfF⟩ := hC.extend_real
  refine ⟨C, F, hF, fun x hx => ?_⟩
  exact Filter.eventually_of_mem (isOpen_interior.mem_nhds (hKL hx))
    fun y hy => hfF (interior_subset hy)

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Integration by parts, locally Lipschitz version.** If `f` is locally Lipschitz on an open set
`Ω`, and `g` is Lipschitz with compact support in `Ω`, then `∫ f ∂ᵥg = -∫ g ∂ᵥf`, with the a.e.
defined derivatives `fderiv ℝ · x v`. -/
theorem LocallyLipschitzOn.integral_mul_fderiv_eq_neg (hΩ : IsOpen Ω)
    (hf : LocallyLipschitzOn Ω f) {D : ℝ≥0} (hg : LipschitzWith D g)
    (hg_supp : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω) (v : E) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = -∫ x, g x * fderiv ℝ f x v ∂μ := by
  obtain ⟨C, F, hF, hfF⟩ := hf.exists_lipschitzWith_eventuallyEq hΩ hg_supp hgΩ
  have h1 : (fun x => f x * fderiv ℝ g x v) = fun x => F x * fderiv ℝ g x v := by
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [(hfF x hx).eq_of_nhds]
    · rw [fderiv_apply_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have h2 : (fun x => g x * fderiv ℝ f x v) = fun x => g x * fderiv ℝ F x v := by
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [(hfF x hx).fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  rw [h1, h2]
  exact hF.integral_mul_fderiv_eq_neg hg hg_supp v

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A product `F * h` with `F` continuous and `h` bounded and measurable is integrable when it
vanishes outside a compact set. -/
theorem integrable_mul_of_continuous_of_bdd {F h : E → ℝ} (hF : Continuous F) (hh : Measurable h)
    {c : ℝ} (hc : ∀ x, ‖h x‖ ≤ c) (hK : IsCompact K) (hvan : ∀ x ∉ K, F x * h x = 0) :
    Integrable (fun x => F x * h x) μ := by
  have hon : IntegrableOn (fun x => F x * h x) K μ :=
    (hF.continuousOn.integrableOn_compact hK).mul_bdd hh.aestronglyMeasurable (ae_of_all _ hc)
  exact hon.integrable_of_forall_notMem_eq_zero hvan

end General

namespace InnerVariational

variable {n : ℕ} {f : Rn n → ℝ} {ξ : Rn n → Rn n} {Ω : Set (Rn n)}

/-- At a point where `ξ` is differentiable, `div ξ = ∑ᵢ ∂ᵢ ξᵢ`. -/
theorem divergence_eq_sum_fderiv {x : Rn n} (hx : DifferentiableAt ℝ ξ x) :
    divergence ξ x =
      ∑ i, fderiv ℝ (fun y => ξ y i) x (EuclideanSpace.single i 1) := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := hasFDerivWithinAt_univ.1
    ((hasFDerivWithinAt_piLp 2).1 (hasFDerivWithinAt_univ.2 hx.hasFDerivAt) i)
  rw [hi.fderiv]
  simp [EuclideanSpace.inner_single_left]

/-- `⟪∇f, ξ⟫ = ∑ᵢ ξᵢ ∂ᵢ f` on `ℝⁿ`. -/
theorem inner_gradient_eq_sum_fderiv (x : Rn n) :
    ⟪gradient f x, ξ x⟫ = ∑ i, ξ x i * fderiv ℝ f x (EuclideanSpace.single i 1) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gradient_apply_eq_fderiv]
  simp

/-- **Integration by parts, divergence form, globally Lipschitz version.** -/
theorem integral_mul_divergence_eq_neg_of_lipschitzWith {C D : ℝ≥0} {F : Rn n → ℝ}
    (hF : LipschitzWith C F) (hξ : LipschitzWith D ξ) (hξc : HasCompactSupport ξ) :
    ∫ x, F x * divergence ξ x = -∫ x, ⟪gradient F x, ξ x⟫ := by
  set e : Fin n → Rn n := fun i => EuclideanSpace.single i 1
  -- the components of `ξ`
  have hcomp : ∀ i, LipschitzWith D (fun y => ξ y i) :=
    fun i x y => (PiLp.edist_apply_le _ _ i).trans (hξ x y)
  have hcompc : ∀ i, HasCompactSupport (fun y => ξ y i) := fun i =>
    hξc.comp_left (g := fun v : Rn n => v i) rfl
  have hcompt : ∀ i, tsupport (fun y => ξ y i) ⊆ tsupport ξ := fun i =>
    tsupport_comp_subset (g := fun v : Rn n => v i) rfl ξ
  -- pointwise identities
  have hdiv : (fun x => F x * divergence ξ x) =ᵐ[volume]
      fun x => ∑ i, F x * fderiv ℝ (fun y => ξ y i) x (e i) := by
    filter_upwards [hξ.ae_differentiableAt (μ := volume)] with x hx
    rw [divergence_eq_sum_fderiv hx, Finset.mul_sum]
  have hgrad : (fun x => ⟪gradient F x, ξ x⟫) =
      fun x => ∑ i, ξ x i * fderiv ℝ F x (e i) := by
    funext x; exact inner_gradient_eq_sum_fderiv x
  -- integrability
  have hint1 : ∀ i, Integrable (fun x => F x * fderiv ℝ (fun y => ξ y i) x (e i)) := by
    intro i
    refine integrable_mul_of_continuous_of_bdd hF.continuous
      (measurable_fderiv_apply_const ℝ _ _) (c := D * ‖e i‖) (fun x => ?_) hξc fun x hx => ?_
    · exact ((fderiv ℝ (fun y => ξ y i) x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hcomp i)) (norm_nonneg _))
    · rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun h => hx (hcompt i h)), mul_zero]
  have hint2 : ∀ i, Integrable (fun x => ξ x i * fderiv ℝ F x (e i)) := by
    intro i
    refine integrable_mul_of_continuous_of_bdd (hcomp i).continuous
      (measurable_fderiv_apply_const ℝ _ _) (c := C * ‖e i‖) (fun x => ?_) hξc fun x hx => ?_
    · exact ((fderiv ℝ F x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hcompt i h)), zero_mul]
  rw [integral_congr_ae hdiv, hgrad, integral_finsetSum _ fun i _ => hint1 i,
    integral_finsetSum _ fun i _ => hint2 i, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hF.integral_mul_fderiv_eq_neg (hcomp i) (hcompc i) (e i)

/-- **Integration by parts, divergence form.** If `f` is locally Lipschitz on an open set `Ω` and
`ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`, then `∫ f div ξ = -∫ ⟪∇f, ξ⟫`. -/
theorem integral_mul_divergence_eq_neg_of_locallyLipschitzOn (hΩ : IsOpen Ω)
    (hf : LocallyLipschitzOn Ω f) (hξ : IsLipTestField Ω ξ) :
    ∫ x, f x * divergence ξ x = -∫ x, ⟪gradient f x, ξ x⟫ := by
  obtain ⟨⟨D, hD⟩, hξc, hξΩ⟩ := hξ
  obtain ⟨C, F, hF, hfF⟩ := hf.exists_lipschitzWith_eventuallyEq hΩ hξc hξΩ
  have h1 : (fun x => f x * divergence ξ x) = fun x => F x * divergence ξ x := by
    funext x
    by_cases hx : x ∈ tsupport ξ
    · rw [(hfF x hx).eq_of_nhds]
    · rw [divergence_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have h2 : (fun x => ⟪gradient f x, ξ x⟫) = fun x => ⟪gradient F x, ξ x⟫ := by
    funext x
    by_cases hx : x ∈ tsupport ξ
    · rw [(hfF x hx).gradient_eq]
    · rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right, inner_zero_right]
  rw [h1, h2]
  exact integral_mul_divergence_eq_neg_of_lipschitzWith hF hD hξc

end InnerVariational
