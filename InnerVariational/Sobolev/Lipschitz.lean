/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
public import GMTFoundations.Sobolev.Lipschitz
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Hom
public import GMTFoundations.Defs.Sobolev

/-!
# Lipschitz functions are Sobolev

This file bridges Mathlib's Rademacher theorem (`Mathlib/Analysis/Calculus/Rademacher.lean`) and
gmt-foundations' Sobolev layer (`GMTFoundations.HasWeakGradient`, `GMTFoundations.MemH1`).

## Main results

* `LipschitzWith.integral_mul_fderiv_eq_neg`: integration by parts for two Lipschitz functions on a
  finite-dimensional real space, one of them compactly supported:
  `∫ f ∂ᵥg = -∫ g ∂ᵥf`, where `∂ᵥ` is the a.e. defined derivative `fderiv ℝ · x v`.
* `LipschitzOnWith.integral_mul_fderiv_eq_neg`: the same with `f` only Lipschitz on an open set
  `Ω ⊇ tsupport g`, and `InnerVariational.integral_mul_partial_eq_neg`, its coordinate version on
  `ℝⁿ` (with `integral_mul_inner_gradient_eq_neg`, the directional form with gradients).
  This is the classical integration by parts for Lipschitz functions (Evans–Gariepy, Chapter 4:
  Lipschitz functions are locally `W^{1,∞}` with weak gradient the a.e. gradient).
* `InnerVariational.hasWeakGradient_gradient_of_lipschitzOnWith`: a function Lipschitz on an open
  set `Ω ⊆ ℝⁿ` has weak gradient `gradient f` on `Ω`.
* `InnerVariational.memH1_gradient_of_lipschitzOnWith`: on a bounded open set, a Lipschitz
  function is in `H¹(Ω)` with weak gradient `gradient f`.

The derivative `fderiv ℝ f x` is Mathlib's Fréchet derivative, which is `0` where `f` is not
differentiable. By Rademacher's theorem that set is Lebesgue-null for Lipschitz `f`
(`LipschitzWith.ae_differentiableAt`), so these are the a.e. partial derivatives.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, CRC Press, 2015.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

@[expose] public noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {C D : ℝ≥0} {f g : E → ℝ}

/-- **Integration by parts for Lipschitz functions.** If `f` and `g` are Lipschitz and `g` has
compact support, then `∫ f ∂ᵥg = -∫ g ∂ᵥf`, with the a.e. defined derivatives
`fderiv ℝ · x v` (Rademacher). -/
theorem LipschitzWith.integral_mul_fderiv_eq_neg (hf : LipschitzWith C f)
    (hg : LipschitzWith D g) (hg_supp : HasCompactSupport g) (v : E) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = -∫ x, g x * fderiv ℝ f x v ∂μ := by
  have h := hf.integral_lineDeriv_mul_eq (μ := μ) hg hg_supp v
  have hf' : (fun x => lineDeriv ℝ f x v * g x) =ᵐ[μ] fun x => g x * fderiv ℝ f x v := by
    filter_upwards [hf.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv, mul_comm]
  have hg' : (fun x => lineDeriv ℝ g x (-v) * f x) =ᵐ[μ] fun x => -(f x * fderiv ℝ g x v) := by
    filter_upwards [hg.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv, map_neg]
    ring
  rw [integral_congr_ae hf', integral_congr_ae hg', integral_neg] at h
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Outside the topological support of `g`, the derivative of `g` vanishes. -/
theorem fderiv_apply_eq_zero_of_notMem_tsupport {x : E} (hx : x ∉ tsupport g) (v : E) :
    fderiv ℝ g x v = 0 := by
  have : fderiv ℝ g x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  simp [this]

/-- **Integration by parts, local version.** If `f` is Lipschitz on an open set `Ω`, and `g` is
Lipschitz with compact support in `Ω`, then `∫ f ∂ᵥg = -∫ g ∂ᵥf`, with the a.e. defined
derivatives `fderiv ℝ · x v`. -/
theorem LipschitzOnWith.integral_mul_fderiv_eq_neg {Ω : Set E} (hΩ : IsOpen Ω)
    (hf : LipschitzOnWith C f Ω) (hg : LipschitzWith D g) (hg_supp : HasCompactSupport g)
    (hgΩ : tsupport g ⊆ Ω) (v : E) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = -∫ x, g x * fderiv ℝ f x v ∂μ := by
  obtain ⟨F, hF, hfF⟩ := hf.extend_real
  have h1 : (fun x => f x * fderiv ℝ g x v) = fun x => F x * fderiv ℝ g x v := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [hfF hx]
    · rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun h => hx (hgΩ h)), mul_zero, mul_zero]
  have h2 : (fun x => g x * fderiv ℝ f x v) = fun x => g x * fderiv ℝ F x v := by
    funext x
    by_cases hx : x ∈ Ω
    · have : f =ᶠ[𝓝 x] F := Filter.eventually_of_mem (hΩ.mem_nhds hx) fun y hy => hfF hy
      rw [this.fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hgΩ h)), zero_mul, zero_mul]
  rw [h1, h2]
  exact hF.integral_mul_fderiv_eq_neg hg hg_supp v

end General

namespace InnerVariational

variable {n : ℕ} {C D : ℝ≥0} {f g : Rn n → ℝ} {Ω : Set (Rn n)}

/-- On `ℝⁿ`, the `i`-th coordinate of the gradient is the `i`-th partial derivative. -/
theorem gradient_apply_eq_fderiv (f : Rn n → ℝ) (x : Rn n) (i : Fin n) :
    gradient f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  rw [gradient, ← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ), real_inner_comm,
    EuclideanSpace.inner_single_left]
  simp

/-- **Integration by parts for Lipschitz functions.** If `f` is Lipschitz on an open set
`Ω ⊆ ℝⁿ` and `g` is Lipschitz with compact support in `Ω`, then
`∫_Ω f ∂ᵢg = -∫_Ω g ∂ᵢf`, with the a.e. partial derivatives `∂ᵢ = fderiv ℝ · x eᵢ`.
(Cf. Evans–Gariepy, Chapter 4.) -/
theorem integral_mul_partial_eq_neg (hΩ : IsOpen Ω) (hf : LipschitzOnWith C f Ω)
    (hg : LipschitzWith D g) (hg_supp : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω)
    (i : Fin n) :
    ∫ x in Ω, f x * fderiv ℝ g x (EuclideanSpace.single i 1) =
      -∫ x in Ω, g x * fderiv ℝ f x (EuclideanSpace.single i 1) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hf.integral_mul_fderiv_eq_neg hΩ hg hg_supp hgΩ _
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hgΩ h)), zero_mul]
  · intro x hx
    rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun h => hx (hgΩ h)), mul_zero]

/-- Directional form of `integral_mul_partial_eq_neg`, with gradients:
`∫_Ω f ⟪∇g, v⟫ = -∫_Ω g ⟪∇f, v⟫`. -/
theorem integral_mul_inner_gradient_eq_neg (hΩ : IsOpen Ω) (hf : LipschitzOnWith C f Ω)
    (hg : LipschitzWith D g) (hg_supp : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω)
    (v : Rn n) :
    ∫ x in Ω, f x * ⟪gradient g x, v⟫_ℝ = -∫ x in Ω, g x * ⟪gradient f x, v⟫_ℝ := by
  simp only [gradient, InnerProductSpace.toDual_symm_apply]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hf.integral_mul_fderiv_eq_neg hΩ hg hg_supp hgΩ v
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hgΩ h)), zero_mul]
  · intro x hx
    rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun h => hx (hgΩ h)), mul_zero]

/-- A function Lipschitz on an open set `Ω ⊆ ℝⁿ` has weak gradient `gradient f` on `Ω`. -/
theorem hasWeakGradient_gradient_of_lipschitzOnWith (hΩ : IsOpen Ω) (hf : LipschitzOnWith C f Ω) :
    GMTFoundations.HasWeakGradient Ω f (gradient f) :=
  (GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn hΩ
    fun _ _ => ⟨C, Ω, self_mem_nhdsWithin, hf⟩).1

/-- The gradient of a function Lipschitz on an open set `Ω` is bounded by the Lipschitz constant
on `Ω`, hence lies in `L^∞(Ω)`. -/
theorem memLp_top_gradient_of_lipschitzOnWith (hΩ : IsOpen Ω) (hf : LipschitzOnWith C f Ω) :
    MemLp (gradient f) ⊤ (volume.restrict Ω) := by
  refine memLp_top_of_bound (GMTFoundations.measurable_gradient f).aestronglyMeasurable C ?_
  filter_upwards [self_mem_ae_restrict hΩ.measurableSet] with x hx
  rw [GMTFoundations.norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hf

/-- A function Lipschitz on a bounded set is bounded there, hence in `L^∞`. -/
theorem memLp_top_of_lipschitzOnWith (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hf : LipschitzOnWith C f Ω) :
    MemLp f ⊤ (volume.restrict Ω) := by
  obtain ⟨F, hF, hfF⟩ := hf.extend_real
  obtain ⟨M, hM⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hF.continuous.continuousOn
  refine memLp_top_of_bound (hf.continuousOn.aestronglyMeasurable hΩ.measurableSet) M ?_
  filter_upwards [self_mem_ae_restrict hΩ.measurableSet] with x hx
  rw [hfF hx]
  exact hM x (subset_closure hx)

/-- **Lipschitz functions are `H¹` on bounded sets.** A function that is Lipschitz on a bounded
open set `Ω ⊆ ℝⁿ` is in `H¹(Ω)` with weak gradient `gradient f`. -/
theorem memH1_gradient_of_lipschitzOnWith (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hf : LipschitzOnWith C f Ω) : GMTFoundations.MemH1 Ω f (gradient f) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  exact ⟨(memLp_top_of_lipschitzOnWith hΩ hΩb hf).mono_exponent le_top,
    (memLp_top_gradient_of_lipschitzOnWith hΩ hf).mono_exponent le_top,
    hasWeakGradient_gradient_of_lipschitzOnWith hΩ hf⟩

end InnerVariational
