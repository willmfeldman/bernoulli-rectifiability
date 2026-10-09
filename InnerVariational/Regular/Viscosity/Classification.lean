/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Perimeter
public import InnerVariational.Regular.HarmonicCone
public import InnerVariational.Blowup.ExplicitForm
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Regular.Density
import InnerVariational.Registry.BV
import InnerVariational.Monotonicity.Limits
import InnerVariational.Regular.ChiInteriorQ
import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Monotonicity.Density
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Registry.Harmonic
public import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.Solutions
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral

/-!
# Half-spaces and the classification of blow-ups (proof of Lemma 8.3)

Auxiliary results for the proof of Lemma 8.3 of Kriventsov–Weiss (see
`Regular/Viscosity/Main.lean` for the overview): facts about half-spaces, the half-space
computation (step 5, `eq_one_of_halfSpace`), passing the inner variation to the limit along a
blow-up sequence, and the classification of the blow-up (step 4, `eq_mul_max_of_le_max`,
`eq_mul_max_of_le`).

## Deviations from the paper's argument

* **Two-plane solutions.** The paper classifies `u₀ = α₊ (y_n)₊ + α₋ (y_n)₋` and
  then excludes `α₊ α₋ ≠ 0` by the density bound. We exclude a second component directly in the
  classification (step 4), so the half-space computation only sees `a ⟪y, e⟫₊`.
* **The half-space computation** is done without surface integrals. On
  `{⟪y, e⟫ < 0} ∩ B_1` the limit identity says `∫ χ₀ div ξ = 0`, so `χ₀ = c ∈ {0, 1}` there. For
  every `ξ ∈ C^∞_c(B_1)` the identity becomes `a² (A(ξ) − 2 B(ξ)) + (1 − c) A(ξ) = 0` with
  `A(ξ) = ∫_H div ξ` and `B(ξ) = ∫_H ⟪e, Dξ e⟫`. Testing with the tangential part
  `ξ − ⟪ξ, e⟫ e` gives `A = B`, so `(1 − c − a²) A(ξ) = 0`. If `1 − c ≠ a²`, then `A ≡ 0`, and
  `1_H` would be constant on `B_1`, which is false. So `a² = 1 − c`, and `a > 0` forces `c = 0`,
  `a = 1`.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-! ### Half-spaces -/

theorem convex_halfSpace (e : Rn n) : Convex ℝ {y : Rn n | 0 < ⟪y, e⟫} := by
  intro y hy z hz a b ha hb hab
  simp only [mem_ofPred_eq, inner_add_left, real_inner_smul_left] at hy hz ⊢
  rcases ha.lt_or_eq with ha' | rfl
  · nlinarith [mul_pos ha' hy, mul_nonneg hb hz.le]
  · rw [zero_add] at hab; subst hab; simpa using hz

theorem convex_halfSpace_neg (e : Rn n) : Convex ℝ {y : Rn n | ⟪y, e⟫ < 0} := by
  intro y hy z hz a b ha hb hab
  simp only [mem_ofPred_eq, inner_add_left, real_inner_smul_left] at hy hz ⊢
  rcases ha.lt_or_eq with ha' | rfl
  · nlinarith [mul_pos ha' (neg_pos.2 hy), mul_nonneg hb (neg_pos.2 hz).le]
  · rw [zero_add] at hab; subst hab; simpa using hz

/-- A hyperplane through the origin is Lebesgue-null. -/
theorem volume_hyperplane {e : Rn n} (he : e ≠ 0) : volume {y : Rn n | ⟪y, e⟫ = 0} = 0 := by
  have := volume_inner_eq_zero he
  simpa only [real_inner_comm] using this

/-- Almost every point lies off a hyperplane through the origin. -/
theorem ae_inner_ne_zero {e : Rn n} (he : e ≠ 0) : ∀ᵐ y : Rn n, ⟪y, e⟫ ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (volume_hyperplane he)

/-- A half-ball has half the volume of the ball. -/
theorem volume_halfSpace_inter_ball {e : Rn n} (he : e ≠ 0) :
    volume.real ({y : Rn n | 0 < ⟪y, e⟫} ∩ ball 0 1) = unitBallVolume n / 2 := by
  set H := {y : Rn n | 0 < ⟪y, e⟫} with hHdef
  set L := {y : Rn n | ⟪y, e⟫ < 0} with hLdef
  set B := ball (0 : Rn n) 1 with hBdef
  have hneg : -(H ∩ B) = L ∩ B := by
    ext y
    simp [hHdef, hLdef, hBdef, inner_neg_left]
  have hLH : volume (L ∩ B) = volume (H ∩ B) := by rw [← hneg, Measure.measure_neg]
  have hdisj : Disjoint (H ∩ B) (L ∩ B) := by
    rw [Set.disjoint_left]
    rintro y ⟨hy, -⟩ ⟨hy', -⟩
    simp only [hHdef, hLdef, mem_ofPred_eq] at hy hy'
    linarith
  have hLm : MeasurableSet (L ∩ B) := (isOpen_halfSpace_neg e).measurableSet.inter
    measurableSet_ball
  have hunion : volume (H ∩ B) + volume (L ∩ B) = volume B := by
    rw [← measure_union hdisj hLm]
    refine le_antisymm (measure_mono (union_subset inter_subset_right inter_subset_right)) ?_
    calc volume B ≤ volume ((H ∩ B) ∪ (L ∩ B) ∪ {y : Rn n | ⟪y, e⟫ = 0}) := measure_mono
          fun y hy => by
            rcases lt_trichotomy ⟪y, e⟫ 0 with h | h | h
            · exact Or.inl (Or.inr ⟨h, hy⟩)
            · exact Or.inr h
            · exact Or.inl (Or.inl ⟨h, hy⟩)
      _ ≤ volume ((H ∩ B) ∪ (L ∩ B)) + volume {y : Rn n | ⟪y, e⟫ = 0} := measure_union_le _ _
      _ = volume ((H ∩ B) ∪ (L ∩ B)) := by rw [volume_hyperplane he, add_zero]
  rw [hLH] at hunion
  have hfin : volume (H ∩ B) ≠ ⊤ := ((measure_mono inter_subset_right).trans_lt
    measure_ball_lt_top).ne
  rw [unitBallVolume, ← hunion, ENNReal.toReal_add hfin hfin, Measure.real]
  ring

/-- If an open half-space `{⟪y, e'⟫ > 0}` lies in another one `{⟪y, e⟫ > 0}` (unit normals), the
two coincide. -/
theorem eq_of_halfSpace_subset {e e' : Rn n} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (h : {y : Rn n | 0 < ⟪y, e'⟫} ⊆ {y : Rn n | 0 < ⟪y, e⟫}) : e' = e := by
  set c := ⟪e', e⟫ with hc
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have he'e' : ⟪e', e'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he', one_pow]
  have hc1 : |c| ≤ 1 := by
    have := abs_real_inner_le_norm e' e
    rwa [he, he', one_mul] at this
  -- `y = e' − c e` has `⟪y, e⟫ = 0`, so `⟪y, e'⟫ = 1 − c² ≤ 0`
  have hy : ¬ (0 < ⟪e' - c • e, e'⟫) := fun hpos => by
    have := h hpos
    simp only [mem_ofPred_eq, inner_sub_left, real_inner_smul_left, hee, ← hc] at this
    linarith
  simp only [inner_sub_left, real_inner_smul_left, he'e', real_inner_comm e' e, ← hc] at hy
  have hcpos : 0 < c := h (show 0 < ⟪e', e'⟫ by rw [he'e']; exact one_pos)
  have hc1' : c = 1 := by nlinarith [abs_le.1 hc1]
  have hsq : ‖e' - e‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right, he'e',
      hee, real_inner_comm e' e, ← hc, hc1']
    ring
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq))

/-- A property that holds a.e. on a nonempty open set holds at some point of it. -/
theorem exists_mem_of_ae_restrict {U : Set (Rn n)} (hU : IsOpen U) (hne : U.Nonempty)
    {p : Rn n → Prop} (h : ∀ᵐ y ∂(volume.restrict U), p y) : ∃ y ∈ U, p y := by
  have : (ae (volume.restrict U)).NeBot :=
    ae_neBot.2 fun h0 => (hU.measure_pos volume hne).ne' (Measure.restrict_eq_zero.1 h0)
  obtain ⟨y, hy, hyU⟩ := (h.and (ae_restrict_mem hU.measurableSet)).exists
  exact ⟨y, hyU, hy⟩

/-! ### The half-space computation (end of the proof of Lemma 8.3) -/

/-- The gradient of `a ⟪y, ν⟫₊` on the open half-space `{⟪y, ν⟫ > 0}` is `a ν`. -/
theorem gradient_mul_max_of_pos {ν y : Rn n} (a : ℝ) (hy : 0 < ⟪y, ν⟫) :
    gradient (fun z => a * max ⟪z, ν⟫ 0) y = a • ν := by
  have h1 : HasFDerivAt (fun z : Rn n => ⟪z, ν⟫) (innerSL ℝ ν) y :=
    (innerSL ℝ ν).hasFDerivAt.congr_of_eventuallyEq
      (.of_forall fun z => by simp [real_inner_comm])
  have hlin : HasGradientAt (fun z : Rn n => a * ⟪z, ν⟫) (a • ν) y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h1.const_mul a using 1
    ext v
    simp
  have hev : (fun z : Rn n => a * max ⟪z, ν⟫ 0) =ᶠ[𝓝 y] fun z => a * ⟪z, ν⟫ := by
    filter_upwards [(isOpen_halfSpace ν).mem_nhds hy] with z hz
    rw [max_eq_left (le_of_lt hz)]
  exact (hlin.congr_of_eventuallyEq hev).gradient

/-- The gradient of `a ⟪y, ν⟫₊` vanishes on the open half-space `{⟪y, ν⟫ < 0}`. -/
theorem gradient_mul_max_of_neg {ν y : Rn n} (a : ℝ) (hy : ⟪y, ν⟫ < 0) :
    gradient (fun z => a * max ⟪z, ν⟫ 0) y = 0 :=
  gradient_eq_zero_of_eventuallyEq (by
    filter_upwards [(isOpen_halfSpace_neg ν).mem_nhds hy] with z hz
    rw [max_eq_right (le_of_lt hz), mul_zero])

/-- On `{⟪y, ν⟫ > 0}`: `|∇u₀|² div ξ − 2 ∇u₀·Dξ ∇u₀ = a² (div ξ − 2 ⟪ν, Dξ ν⟫)` for
`u₀ = a ⟪y, ν⟫₊`, `|ν| = 1`. -/
theorem gradVariation_mul_max_of_pos {ν y : Rn n} (hν : ‖ν‖ = 1) (a : ℝ) (ξ : Rn n → Rn n)
    (hy : 0 < ⟪y, ν⟫) :
    Kernel.gradVariation (fun z => a * max ⟪z, ν⟫ 0) ξ y =
      a ^ 2 * (divergence ξ y - 2 * ⟪ν, fderiv ℝ ξ y ν⟫) := by
  rw [Kernel.gradVariation, gradient_mul_max_of_pos a hy, norm_smul, Real.norm_eq_abs, hν,
    mul_one, sq_abs, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- `∫ Q_ξ(∇u₀) = a² (∫_H div ξ − 2 ∫_H ⟪ν, Dξ ν⟫)` for `u₀ = a ⟪y, ν⟫₊`, where
`H = {⟪y, ν⟫ > 0}` and `Q_ξ(p) = |p|² div ξ − 2 p·Dξ p`. -/
theorem integral_gradVariation_mul_max {ν : Rn n} (hν : ‖ν‖ = 1) (a : ℝ) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField univ ξ) :
    ∫ y, Kernel.gradVariation (fun z => a * max ⟪z, ν⟫ 0) ξ y =
      a ^ 2 * ((∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y) -
        2 * ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) := by
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  set H := {y : Rn n | 0 < ⟪y, ν⟫} with hHdef
  have hHm : MeasurableSet H := (isOpen_halfSpace ν).measurableSet
  obtain ⟨⟨D, hD⟩, hc, -⟩ := hξ
  have hDint : Integrable (divergence ξ) := Kernel.integrable_divergence hD hc
  have hEint : Integrable fun y => ⟪ν, fderiv ℝ ξ y ν⟫ :=
    Kernel.integrable_of_bound_of_isCompact hc
      (measurable_const.inner (measurable_fderiv_apply_const ℝ ξ ν)).aestronglyMeasurable
      (M := D) (fun y _ => by
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hν, one_mul]
        refine ((fderiv ℝ ξ y).le_opNorm ν).trans ?_
        rw [hν, mul_one]
        exact norm_fderiv_le_of_lipschitz ℝ hD)
      (fun y hy => by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy])
  have hae : Kernel.gradVariation (fun z => a * max ⟪z, ν⟫ 0) ξ =ᵐ[volume] fun y => a ^ 2 *
      (H.indicator (divergence ξ) y - 2 * H.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) := by
    filter_upwards [ae_inner_ne_zero hν0] with y hy
    rcases hy.lt_or_gt with hneg | hpos
    · have hyH : y ∉ H := fun h' => lt_asymm hneg h'
      rw [Kernel.gradVariation_eq_zero_of_gradient_eq_zero (gradient_mul_max_of_neg a hneg),
        indicator_of_notMem hyH, indicator_of_notMem hyH]
      ring
    · have hyH : y ∈ H := hpos
      rw [gradVariation_mul_max_of_pos hν a ξ hpos, indicator_of_mem hyH, indicator_of_mem hyH]
  calc ∫ y, Kernel.gradVariation (fun z => a * max ⟪z, ν⟫ 0) ξ y
      = ∫ y, a ^ 2 * (H.indicator (divergence ξ) y -
          2 * H.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) := integral_congr_ae hae
    _ = a ^ 2 * ∫ y, (H.indicator (divergence ξ) y -
          2 * H.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) := integral_const_mul _ _
    _ = a ^ 2 * ((∫ y, H.indicator (divergence ξ) y) -
          ∫ y, 2 * H.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) := by
        rw [integral_sub (hDint.indicator hHm) ((hEint.indicator hHm).const_mul 2)]
    _ = _ := by rw [integral_const_mul]

/-- If `f₀ = 1` a.e. on `B_1 ∩ {⟪y, ν⟫ > 0}` and `f₀ = c` a.e. on `B_1 ∩ {⟪y, ν⟫ < 0}`, then
`∫ f₀ div ξ = (1 − c) ∫_H div ξ` for `ξ ∈ C^{0,1}_c(B_1)`. -/
theorem integral_mul_divergence_eq_of_ae {ν : Rn n} (hν0 : ν ≠ 0) {f₀ : Rn n → ℝ} {c : ℝ}
    (h1 : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < ⟪y, ν⟫ → f₀ y = 1)
    (hc : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1 ∩ {y | ⟪y, ν⟫ < 0})), f₀ y = c)
    {ξ : Rn n → Rn n} (hξ : IsLipTestField (ball (0 : Rn n) 1) ξ) :
    ∫ y, f₀ y * divergence ξ y =
      (1 - c) * ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y := by
  set H := {y : Rn n | 0 < ⟪y, ν⟫} with hHdef
  have hHm : MeasurableSet H := (isOpen_halfSpace ν).measurableSet
  have hLm : MeasurableSet {y : Rn n | ⟪y, ν⟫ < 0} := (isOpen_halfSpace_neg ν).measurableSet
  obtain ⟨⟨D, hD⟩, hcpt, hsub⟩ := hξ
  have hDint : Integrable (divergence ξ) := Kernel.integrable_divergence hD hcpt
  have h1' := (ae_restrict_iff' measurableSet_ball).1 h1
  have h2' := (ae_restrict_iff' (measurableSet_ball.inter hLm)).1 hc
  have hae : (fun y => f₀ y * divergence ξ y) =ᵐ[volume]
      fun y => (1 - c) * H.indicator (divergence ξ) y + c * divergence ξ y := by
    filter_upwards [h1', h2', ae_inner_ne_zero hν0] with y hy1 hy2 hy0
    by_cases hyB : y ∈ ball (0 : Rn n) 1
    · rcases hy0.lt_or_gt with hneg | hpos
      · have hyH : y ∉ H := fun h' => lt_asymm hneg h'
        rw [hy2 ⟨hyB, hneg⟩, indicator_of_notMem hyH]
        ring
      · have hyH : y ∈ H := hpos
        rw [hy1 hyB hpos, indicator_of_mem hyH]
        ring
    · have hy : divergence ξ y = 0 :=
        divergence_eq_zero_of_notMem_tsupport fun h' => hyB (hsub h')
      simp [hy]
  have hdiv0 : ∫ y, divergence ξ y = 0 :=
    Kernel.integral_divergence_eq_zero isOpen_ball ⟨⟨D, hD⟩, hcpt, hsub⟩
  calc ∫ y, f₀ y * divergence ξ y
      = ∫ y, ((1 - c) * H.indicator (divergence ξ) y + c * divergence ξ y) := integral_congr_ae hae
    _ = (∫ y, (1 - c) * H.indicator (divergence ξ) y) + ∫ y, c * divergence ξ y :=
        integral_add ((hDint.indicator hHm).const_mul _) (hDint.const_mul _)
    _ = _ := by rw [integral_const_mul, integral_const_mul, hdiv0, mul_zero, add_zero]

/-- The tangential part `ξ − ⟪ξ, ν⟫ ν` of a test field: it is a test field, `⟪ν, D ξ_T ν⟫ = 0`,
and `div ξ_T = div ξ − ⟪ν, Dξ ν⟫`. -/
theorem exists_tangentialField {ν : Rn n} (hν : ‖ν‖ = 1) {U : Set (Rn n)} {ξ : Rn n → Rn n}
    (hξ : IsSmoothTestField U ξ) : ∃ ξT : Rn n → Rn n, IsSmoothTestField U ξT ∧
      (∀ y, ⟪ν, fderiv ℝ ξT y ν⟫ = 0) ∧
      ∀ y, divergence ξT y = divergence ξ y - ⟪ν, fderiv ℝ ξ y ν⟫ := by
  have hνν : ⟪ν, ν⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hν, one_pow]
  set Q : Rn n →L[ℝ] Rn n := (innerSL ℝ ν).smulRight ν with hQdef
  have hQ : ∀ v, Q v = ⟪ν, v⟫ • ν := fun v => by simp [hQdef]
  set ξT : Rn n → Rn n := fun y => ξ y - Q (ξ y) with hξTdef
  have hsupp : tsupport ξT ⊆ tsupport ξ := closure_mono fun y hy h0 => hy (by
    simp only [hξTdef, h0, map_zero, sub_zero])
  have hd : ∀ y, HasFDerivAt ξT (fderiv ℝ ξ y - Q.comp (fderiv ℝ ξ y)) y := fun y => by
    have hy : DifferentiableAt ℝ ξ y := hξ.1.differentiable (by simp) y
    exact hy.hasFDerivAt.sub (Q.hasFDerivAt.comp y hy.hasFDerivAt)
  refine ⟨ξT, ⟨hξ.1.sub (Q.contDiff.comp hξ.1),
    hξ.2.1.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hξ.2.2⟩,
    fun y => ?_, fun y => ?_⟩
  · rw [(hd y).fderiv, sub_apply, ContinuousLinearMap.comp_apply, hQ,
      inner_sub_right, real_inner_smul_right, hνν, mul_one, sub_self]
  · have hcomp : Q.comp (fderiv ℝ ξ y) = ((innerSL ℝ ν).comp (fderiv ℝ ξ y)).smulRight ν := by
      ext v
      simp [hQ]
    rw [divergence, (hd y).fderiv, ContinuousLinearMap.toLinearMap_sub, map_sub, hcomp,
      ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight, divergence]
    simp

/-- `1_H` is not a.e. constant on `B_1`: some `ξ ∈ C^∞_c(B_1)` has `∫_H div ξ ≠ 0`. -/
theorem exists_integral_indicator_divergence_ne_zero {ν : Rn n} (hν : ‖ν‖ = 1) :
    ∃ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ ∧
      ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y ≠ 0 := by
  have hνν : ⟪ν, ν⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hν, one_pow]
  set H := {y : Rn n | 0 < ⟪y, ν⟫} with hHdef
  have hHm : MeasurableSet H := (isOpen_halfSpace ν).measurableSet
  by_contra hall
  push Not at hall
  have hA : ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
      ∫ y, H.indicator (1 : Rn n → ℝ) y * divergence ξ y = 0 := by
    intro ξ hξ
    rw [← hall ξ hξ]
    congr 1
    funext y
    by_cases hy : y ∈ H
    · rw [indicator_of_mem hy, indicator_of_mem hy, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
  have hbd : ∀ y, ‖H.indicator (1 : Rn n → ℝ) y‖ ≤ 1 := fun y => by
    by_cases hy : y ∈ H
    · rw [indicator_of_mem hy, Pi.one_apply, norm_one]
    · rw [indicator_of_notMem hy, norm_zero]; exact zero_le_one
  have hloc : LocallyIntegrableOn (H.indicator (1 : Rn n → ℝ)) (ball (0 : Rn n) 1) :=
    (IntegrableOn.of_bound measure_ball_lt_top
      (measurable_one.indicator hHm).aestronglyMeasurable 1 (.of_forall hbd)).locallyIntegrableOn
  obtain ⟨c', hc'⟩ := exists_ae_eq_const_of_integral_mul_divergence_eq_zero isOpen_ball
    (convex_ball (0 : Rn n) 1).isPreconnected hloc hA
  have hB1 : (1 / 2 : ℝ) • ν ∈ ball (0 : Rn n) 1 := by
    rw [mem_ball_zero_iff, norm_smul, hν]; norm_num
  have hB2 : (-(1 / 2) : ℝ) • ν ∈ ball (0 : Rn n) 1 := by
    rw [mem_ball_zero_iff, norm_smul, hν]; norm_num
  obtain ⟨y₁, hy₁, hy₁c⟩ := exists_mem_of_ae_restrict (isOpen_ball.inter (isOpen_halfSpace ν))
    ⟨_, hB1, show 0 < ⟪(1 / 2 : ℝ) • ν, ν⟫ by rw [real_inner_smul_left, hνν]; norm_num⟩
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hc')
  obtain ⟨y₂, hy₂, hy₂c⟩ := exists_mem_of_ae_restrict
    (isOpen_ball.inter (isOpen_halfSpace_neg ν))
    ⟨_, hB2, show ⟪(-(1 / 2) : ℝ) • ν, ν⟫ < 0 by rw [real_inner_smul_left, hνν]; norm_num⟩
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hc')
  have hy₂H : y₂ ∉ H := by
    simp only [hHdef, mem_ofPred_eq, not_lt]
    exact (hy₂.2 : ⟪y₂, ν⟫ < 0).le
  rw [indicator_of_mem (show y₁ ∈ H from hy₁.2), Pi.one_apply] at hy₁c
  rw [indicator_of_notMem hy₂H] at hy₂c
  rw [← hy₁c] at hy₂c
  exact one_ne_zero hy₂c.symm

/-- **The half-space computation** (end of the proof of Lemma 8.3). Let `|ν| = 1`, `a > 0`, and
let `f₀` take
values in `{0, 1}` a.e. on `B_1`, with `f₀ = 1` a.e. on `B_1 ∩ {⟪y, ν⟫ > 0}`. If the limit
domain variation identity `∫ Q_ξ(∇u₀) + ∫ f₀ div ξ = 0` holds for `u₀ = a ⟪y, ν⟫₊` and all
`ξ ∈ C^∞_c(B_1; ℝⁿ)`, then `a = 1`.

The paper computes both sides as surface integrals over `{y_n = 0}`. We avoid them; see the module
docstring. -/
theorem eq_one_of_halfSpace {ν : Rn n} (hν : ‖ν‖ = 1) {a : ℝ} (ha : 0 < a) {f₀ : Rn n → ℝ}
    (hf₀m : Measurable f₀)
    (h01 : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1)
    (hpos : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < ⟪y, ν⟫ → f₀ y = 1)
    (hid : ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
      (∫ y, Kernel.gradVariation (fun z => a * max ⟪z, ν⟫ 0) ξ y) +
        ∫ y, f₀ y * divergence ξ y = 0) :
    a = 1 := by
  have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
  have hνν : ⟪ν, ν⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hν, one_pow]
  set B := ball (0 : Rn n) 1 with hBdef
  set L := {y : Rn n | ⟪y, ν⟫ < 0} with hLdef
  have hBLo : IsOpen (B ∩ L) := isOpen_ball.inter (isOpen_halfSpace_neg ν)
  have hBL : (B ∩ L).Nonempty := ⟨(-(1 / 2) : ℝ) • ν, by
    rw [hBdef, mem_ball_zero_iff, norm_smul, hν]; norm_num, by
    simp only [hLdef, mem_ofPred_eq, real_inner_smul_left, hνν]; norm_num⟩
  have hf₀B : IntegrableOn f₀ B := IntegrableOn.of_bound measure_ball_lt_top
    hf₀m.aestronglyMeasurable 1 (by
      filter_upwards [h01] with y hy
      rcases hy with h | h <;> simp [h])
  -- Step 1: `f₀ = c` a.e. on `B ∩ L`
  obtain ⟨c, hc⟩ : ∃ c, ∀ᵐ y ∂(volume.restrict (B ∩ L)), f₀ y = c := by
    refine exists_ae_eq_const_of_integral_mul_divergence_eq_zero hBLo
      ((convex_ball (0 : Rn n) 1).inter (convex_halfSpace_neg ν)).isPreconnected
      (hf₀B.mono_set inter_subset_left).locallyIntegrableOn (fun ξ hξ => ?_)
    have h0 : ∀ y, Kernel.gradVariation (fun z => a * max ⟪z, ν⟫ 0) ξ y = 0 := fun y => by
      by_cases hy : y ∈ tsupport ξ
      · exact Kernel.gradVariation_eq_zero_of_gradient_eq_zero
          (gradient_mul_max_of_neg a (hξ.2.2 hy).2)
      · exact Kernel.gradVariation_eq_zero_of_notMem_tsupport hy
    have hz : ∫ y, Kernel.gradVariation (fun z => a * max ⟪z, ν⟫ 0) ξ y = 0 :=
      integral_eq_zero_of_ae (.of_forall h0)
    have := hid ξ ⟨hξ.1, hξ.2.1, hξ.2.2.trans inter_subset_left⟩
    rwa [hz, zero_add] at this
  have hc01 : c = 0 ∨ c = 1 := by
    obtain ⟨y, -, hyc, hy01⟩ := exists_mem_of_ae_restrict hBLo hBL
      (hc.and (ae_restrict_of_ae_restrict_of_subset inter_subset_left h01))
    rw [← hyc]; exact hy01
  -- Step 2: `a² (A − 2B) + (1 − c) A = 0` for every test field
  have hkey : ∀ ξ, IsSmoothTestField B ξ →
      a ^ 2 * ((∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y) -
          2 * ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) +
        (1 - c) * ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y = 0 := by
    intro ξ hξ
    have h1 := hid ξ hξ
    rw [integral_gradVariation_mul_max hν a (hξ.isLipTestField.mono (subset_univ _)),
      integral_mul_divergence_eq_of_ae hν0 hpos hc hξ.isLipTestField] at h1
    exact h1
  -- Step 3: the tangential part gives `A = B`
  have hAB : ∀ ξ, IsSmoothTestField B ξ →
      ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y =
        ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y := by
    intro ξ hξ
    obtain ⟨⟨D, hD⟩, -, -⟩ := hξ.isLipTestField
    have hHm : MeasurableSet {y : Rn n | 0 < ⟪y, ν⟫} := (isOpen_halfSpace ν).measurableSet
    have hDint : Integrable (divergence ξ) := Kernel.integrable_divergence hD hξ.2.1
    have hEint : Integrable fun y => ⟪ν, fderiv ℝ ξ y ν⟫ :=
      Kernel.integrable_of_bound_of_isCompact hξ.2.1
        (measurable_const.inner (measurable_fderiv_apply_const ℝ ξ ν)).aestronglyMeasurable
        (M := D) (fun y _ => by
          rw [Real.norm_eq_abs]
          refine (abs_real_inner_le_norm _ _).trans ?_
          rw [hν, one_mul]
          refine ((fderiv ℝ ξ y).le_opNorm ν).trans ?_
          rw [hν, mul_one]
          exact norm_fderiv_le_of_lipschitz ℝ hD)
        (fun y hy => by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy])
    obtain ⟨ξT, hξT, hT1, hT2⟩ := exists_tangentialField hν hξ
    have h1 := hkey ξT hξT
    have hE0 : (fun y => {y : Rn n | 0 < ⟪y, ν⟫}.indicator (fun y => ⟪ν, fderiv ℝ ξT y ν⟫) y) =
        fun _ => 0 := funext fun y => by simp [hT1]
    have hsplit : ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξT) y =
        (∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y) -
          ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y := by
      calc ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξT) y
          = ∫ y, ({y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y -
              {y : Rn n | 0 < ⟪y, ν⟫}.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) := by
            congr 1
            funext y
            by_cases hy : y ∈ {y : Rn n | 0 < ⟪y, ν⟫}
            · rw [indicator_of_mem hy, indicator_of_mem hy, indicator_of_mem hy, hT2]
            · rw [indicator_of_notMem hy, indicator_of_notMem hy, indicator_of_notMem hy,
                sub_zero]
        _ = _ := integral_sub (hDint.indicator hHm) (hEint.indicator hHm)
    rw [hE0, integral_zero, mul_zero, sub_zero, hsplit] at h1
    have hpos2 : 0 < a ^ 2 + (1 - c) := by
      rcases hc01 with h | h <;> rw [h] <;> positivity
    have h3 : (a ^ 2 + (1 - c)) *
        ((∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ) y) -
          ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (fun y => ⟪ν, fderiv ℝ ξ y ν⟫) y) = 0 := by
      linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hpos2.ne')
  -- Step 4: `a² = 1 − c`, hence `c = 0` and `a = 1`
  obtain ⟨ξ₀, hξ₀, hne⟩ := exists_integral_indicator_divergence_ne_zero hν
  have h1 := hkey ξ₀ hξ₀
  rw [← hAB ξ₀ hξ₀] at h1
  have h2 : (1 - c - a ^ 2) * ∫ y, {y : Rn n | 0 < ⟪y, ν⟫}.indicator (divergence ξ₀) y = 0 := by
    linear_combination h1
  have hac : 1 - c - a ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_right hne
  rcases hc01 with h | h
  · rw [h] at hac
    nlinarith
  · rw [h] at hac
    nlinarith

/-! ### Passing the inner variation to the limit -/

/-- `|Q_ξ(∇u) − Q_ξ(∇v)| ≤ 2 L (n D + 2 D) |∇u − ∇v|` at a point where `|∇u|, |∇v| ≤ L`, for a
`D`-Lipschitz `ξ`. Here `Q_ξ(p) = |p|² div ξ − 2 p·Dξ p`. -/
theorem abs_gradVariation_sub_le {u v : Rn n → ℝ} {ξ : Rn n → Rn n} {D : ℝ≥0}
    (hξ : LipschitzWith D ξ) {L : ℝ} {y : Rn n} (hu : ‖gradient u y‖ ≤ L)
    (hv : ‖gradient v y‖ ≤ L) :
    |Kernel.gradVariation u ξ y - Kernel.gradVariation v ξ y| ≤
      2 * L * (n * D + 2 * D) * ‖gradient u y - gradient v y‖ := by
  set a := gradient u y with hadef
  set b := gradient v y with hbdef
  set A := fderiv ℝ ξ y with hAdef
  have hA : ‖A‖ ≤ D := norm_fderiv_le_of_lipschitz ℝ hξ
  have hdiv := Kernel.abs_divergence_le hξ y
  have hL : 0 ≤ L := (norm_nonneg _).trans hu
  have e : Kernel.gradVariation u ξ y - Kernel.gradVariation v ξ y =
      (‖a‖ ^ 2 - ‖b‖ ^ 2) * divergence ξ y - 2 * (⟪a - b, A a⟫ + ⟪b, A (a - b)⟫) := by
    simp only [Kernel.gradVariation, inner_sub_left, map_sub, inner_sub_right, ← hadef, ← hbdef,
      ← hAdef]
    ring
  have h1 : |(‖a‖ ^ 2 - ‖b‖ ^ 2) * divergence ξ y| ≤ 2 * L * ‖a - b‖ * (n * D) := by
    rw [abs_mul]
    exact mul_le_mul (abs_sq_norm_sub_sq_norm_le hu hv) hdiv (abs_nonneg _) (by positivity)
  have h2 : |⟪a - b, A a⟫| ≤ ‖a - b‖ * (D * L) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((A.le_opNorm a).trans (mul_le_mul hA hu (norm_nonneg _) D.2)) (norm_nonneg _))
  have h3 : |⟪b, A (a - b)⟫| ≤ L * (D * ‖a - b‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hv ((A.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) (norm_nonneg _) hL)
  rw [e]
  obtain ⟨h1l, h1r⟩ := abs_le.1 h1
  obtain ⟨h2l, h2r⟩ := abs_le.1 h2
  obtain ⟨h3l, h3r⟩ := abs_le.1 h3
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith

/-- `L²` convergence implies `L¹` convergence on a set of finite measure (Cauchy–Schwarz). -/
theorem tendsto_setIntegral_norm_sub_of_sq {S : Set (Rn n)} (hS : MeasurableSet S)
    (hSf : volume S < ⊤) {g : ℕ → Rn n → Rn n} {g₀ : Rn n → Rn n} {L : ℝ}
    (hgm : ∀ k, Measurable (g k)) (hg0m : Measurable g₀) (hgb : ∀ k, ∀ y ∈ S, ‖g k y‖ ≤ L)
    (hg0b : ∀ y ∈ S, ‖g₀ y‖ ≤ L)
    (hlim : Tendsto (fun k => ∫ y in S, ‖g k y - g₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y in S, ‖g k y - g₀ y‖) atTop (𝓝 0) := by
  have hint : ∀ f : Rn n → ℝ, Measurable f → ∀ M, (∀ y ∈ S, |f y| ≤ M) → IntegrableOn f S :=
    fun f hf M hM => IntegrableOn.of_bound hSf hf.aestronglyMeasurable M
      ((ae_restrict_iff' hS).2 (.of_forall fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy))
  have hsq : ∀ k, IntegrableOn (fun y => ‖g k y - g₀ y‖ ^ 2) S := fun k =>
    hint _ (((hgm k).sub hg0m).norm.pow_const 2) ((2 * L) ^ 2) fun y hy => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by
        linarith [hgb k y hy, hg0b y hy])) 2
  have hlin : ∀ k, IntegrableOn (fun y => ‖g k y - g₀ y‖) S := fun k =>
    hint _ ((hgm k).sub hg0m).norm (2 * L) fun y hy => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by linarith [hgb k y hy, hg0b y hy])
  have hone : IntegrableOn (fun _ : Rn n => (1 : ℝ)) S := integrableOn_const hSf.ne
  have hCS : ∀ k, (∫ y in S, ‖g k y - g₀ y‖) ^ 2 ≤
      (∫ y in S, ‖g k y - g₀ y‖ ^ 2) * volume.real S := by
    intro k
    have := sq_integral_mul_le (μ := volume.restrict S) (F := fun y => ‖g k y - g₀ y‖)
      (G := fun _ => (1 : ℝ)) (hsq k) (by simp only [one_pow]; exact hone)
      (by simp only [mul_one]; exact hlin k)
    simpa [Measure.real, Measure.restrict_apply MeasurableSet.univ] using this
  have h1 : Tendsto (fun k => √((∫ y in S, ‖g k y - g₀ y‖ ^ 2) * volume.real S)) atTop
      (𝓝 0) := by
    simpa using (hlim.mul_const (volume.real S)).sqrt
  refine squeeze_zero (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) h1
  exact (le_abs_self _).trans (Real.abs_le_sqrt (hCS k))

/-- **Convergence of the quadratic part of the inner variation** under strong `L²` convergence
of uniformly bounded gradients on `supp ξ`. -/
theorem tendsto_integral_gradVariation {w : ℕ → Rn n → ℝ} {w₀ : Rn n → ℝ} {ξ : Rn n → Rn n}
    {D : ℝ≥0} (hD : LipschitzWith D ξ) (hc : HasCompactSupport ξ) {L : ℝ}
    (hwb : ∀ k, ∀ y ∈ tsupport ξ, ‖gradient (w k) y‖ ≤ L)
    (hw0b : ∀ y ∈ tsupport ξ, ‖gradient w₀ y‖ ≤ L)
    (hlim : Tendsto (fun k => ∫ y in tsupport ξ, ‖gradient (w k) y - gradient w₀ y‖ ^ 2) atTop
      (𝓝 0)) :
    Tendsto (fun k => ∫ y, Kernel.gradVariation (w k) ξ y) atTop
      (𝓝 (∫ y, Kernel.gradVariation w₀ ξ y)) := by
  have hK : IsCompact (tsupport ξ) := hc
  have hL1 := tendsto_setIntegral_norm_sub_of_sq hK.measurableSet hK.measure_lt_top
    (fun k => measurable_gradient (w k)) (measurable_gradient w₀) hwb hw0b hlim
  have hint : ∀ v : Rn n → ℝ, (∀ y ∈ tsupport ξ, ‖gradient v y‖ ≤ L) →
      Integrable (Kernel.gradVariation v ξ) := fun v hv =>
    Kernel.integrable_gradVariation ⟨⟨D, hD⟩, hc, subset_rfl⟩ hv
  set c := 2 * L * (n * D + 2 * D) with hcdef
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) (by simpa using hL1.const_mul c)
  rw [← integral_sub (hint _ (hwb k)) (hint _ hw0b),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport ξ) (fun y hy => by
      simp [Kernel.gradVariation_eq_zero_of_notMem_tsupport hy]),
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((IntegrableOn.of_bound hK.measure_lt_top
    (((measurable_gradient _).sub (measurable_gradient _)).norm.const_mul c).aestronglyMeasurable
    (c * (2 * L)) ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => ?_))))
    ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => ?_))
  · have hc0 : 0 ≤ c := by
      have hL : 0 ≤ L := (norm_nonneg _).trans (hw0b y hy)
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by
      linarith [hwb k y hy, hw0b y hy])) hc0
  · rw [Real.norm_eq_abs]
    exact abs_gradVariation_sub_le hD (hwb k y hy) (hw0b y hy)

/-! ### Classification of the blow-up (proof of Lemma 8.3) -/

/-- **Classification from above.** A nonzero Lipschitz, one-homogeneous `u₀ ≥ 0`, harmonic on
`{u₀ > 0}`, with `u₀ ≤ (β ⟪y, e⟫)₊` (`β > 0`, `|e| = 1`) is `a ⟪y, e⟫₊` for some `a > 0`.
Each component of `{u₀ > 0}` lies in the half-space, so it has volume `≤ |B_1|/2` in `B_1`, and
the equality case of Sperner's inequality applies. -/
theorem eq_mul_max_of_le_max (hn : 2 ≤ n) {u₀ : Rn n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u₀)
    (hnn : ∀ y, 0 ≤ u₀ y) (hhom : ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y)
    (hharm : ∀ y, 0 < u₀ y → HarmonicAt u₀ y) {y₀ : Rn n} (hy₀ : 0 < u₀ y₀) {e : Rn n}
    (he : ‖e‖ = 1) {β : ℝ} (hβ : 0 < β) (hle : ∀ y, u₀ y ≤ max (β * ⟪y, e⟫) 0) :
    ∃ a, 0 < a ∧ ∀ y, u₀ y = a * max ⟪y, e⟫ 0 := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hPH : {y | 0 < u₀ y} ⊆ {y : Rn n | 0 < ⟪y, e⟫} := fun y hy => by
    have h1 : 0 < max (β * ⟪y, e⟫) 0 := lt_of_lt_of_le hy (hle y)
    rcases max_choice (β * ⟪y, e⟫) 0 with h | h <;> rw [h] at h1
    · exact pos_of_mul_pos_right h1 hβ.le
    · exact absurd h1 (lt_irrefl 0)
  have hUH := (connectedComponentIn_subset {y | 0 < u₀ y} y₀).trans hPH
  have hR07 := Registry.sperner_half_volume hn ⟨L, hLip⟩ hnn (fun y t ht => hhom t ht y) hy₀
    (fun y hy => hharm y (connectedComponentIn_subset _ _ hy : y ∈ {y | 0 < u₀ y}))
  have hHvol := volume_halfSpace_inter_ball he0
  rw [measureReal_def] at hHvol
  have hUle : (volume (connectedComponentIn {y | 0 < u₀ y} y₀ ∩ ball 0 1)).toReal ≤
      unitBallVolume n / 2 := by
    rw [← hHvol]
    exact ENNReal.toReal_mono ((measure_mono inter_subset_right).trans_lt
      measure_ball_lt_top).ne (measure_mono (inter_subset_inter_left _ hUH))
  obtain ⟨e', he', hUe', a, ha, hua⟩ := hR07.2 (le_antisymm hUle hR07.1)
  have hee : e' = e := eq_of_halfSpace_subset he he' (by rw [← hUe']; exact hUH)
  subst hee
  refine ⟨a, ha, fun y => ?_⟩
  by_cases hy : 0 < ⟪y, e'⟫
  · rw [max_eq_left hy.le, hua y (by rw [hUe']; exact hy)]
  · rw [max_eq_right (not_lt.1 hy), mul_zero]
    refine le_antisymm ?_ (hnn y)
    have := hle y
    rwa [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hβ.le (not_lt.1 hy))] at this

/-- **Classification from below** (proof of Lemma 8.3). A Lipschitz, one-homogeneous `u₀ ≥ 0`,
harmonic on `{u₀ > 0}`, with `β ⟪y, e⟫ ≤ u₀` (`β > 0`, `|e| = 1`) and
`|{u₀ > 0} ∩ B_1| < |B_1|` is `a ⟪y, e⟫₊` for some `a > 0`. The component through `e` contains the
half-space, so it is the half-space (`connectedComponentIn_eq_halfSpace`); a second component
would add `|B_1|/2` (Sperner's inequality). -/
theorem eq_mul_max_of_le (hn : 2 ≤ n) {u₀ : Rn n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u₀)
    (hnn : ∀ y, 0 ≤ u₀ y) (hhom : ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y)
    (hharm : ∀ y, 0 < u₀ y → HarmonicAt u₀ y)
    (hvol : volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) < unitBallVolume n) {e : Rn n}
    (he : ‖e‖ = 1) {β : ℝ} (hβ : 0 < β) (hle : ∀ y, β * ⟪y, e⟫ ≤ u₀ y) :
    ∃ a, 0 < a ∧ ∀ y, u₀ y = a * max ⟪y, e⟫ 0 := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  set P := {y | 0 < u₀ y} with hPdef
  have hPo : IsOpen P := isOpen_lt continuous_const hLip.continuous
  have heP : 0 < u₀ e := by
    have := hle e
    rw [hee, mul_one] at this
    linarith
  have hHP : {y : Rn n | 0 < ⟪y, e⟫} ⊆ P := fun y hy => (mul_pos hβ hy).trans_le (hle y)
  have hHU : {y : Rn n | 0 < ⟪y, e⟫} ⊆ connectedComponentIn P e :=
    (convex_halfSpace e).isPreconnected.subset_connectedComponentIn
      (show 0 < ⟪e, e⟫ by rw [hee]; exact one_pos) hHP
  have hharmU : ∀ y ∈ connectedComponentIn P e, HarmonicAt u₀ y := fun y hy =>
    hharm y (connectedComponentIn_subset _ _ hy : y ∈ {y | 0 < u₀ y})
  have hUH : connectedComponentIn P e = {y | 0 < ⟪y, e⟫} :=
    connectedComponentIn_eq_halfSpace ⟨L, hLip⟩ hnn (fun y t ht => hhom t ht y) hharmU he0 hHU
  have hR07 := Registry.sperner_half_volume hn ⟨L, hLip⟩ hnn (fun y t ht => hhom t ht y) heP hharmU
  have hHvol := volume_halfSpace_inter_ball he0
  rw [measureReal_def] at hHvol
  obtain ⟨e', he', hUe', a, ha, hua⟩ := hR07.2 (by rw [hUH]; exact hHvol)
  have he'e : e' = e := eq_of_halfSpace_subset he he' (by rw [← hUe', hUH])
  subst he'e
  refine ⟨a, ha, fun y => ?_⟩
  by_cases hy : 0 < ⟪y, e'⟫
  · rw [max_eq_left hy.le, hua y (by rw [hUe']; exact hy)]
  · rw [max_eq_right (not_lt.1 hy), mul_zero]
    by_contra hne
    have hy₁ : 0 < u₀ y := lt_of_le_of_ne (hnn y) (Ne.symm hne)
    have hdisj : Disjoint (connectedComponentIn P e') (connectedComponentIn P y) := by
      rw [Set.disjoint_left]
      intro z hzU hzU₁
      have hyU : y ∈ connectedComponentIn P e' := by
        rw [connectedComponentIn_eq hzU, ← connectedComponentIn_eq hzU₁]
        exact mem_connectedComponentIn hy₁
      rw [hUH] at hyU
      exact hy hyU
    have hR07' := Registry.sperner_half_volume hn ⟨L, hLip⟩ hnn (fun y t ht => hhom t ht y) hy₁
      (fun z hz => hharm z (connectedComponentIn_subset _ _ hz : z ∈ {y | 0 < u₀ y}))
    have hfin : ∀ s : Set (Rn n), volume (s ∩ ball (0 : Rn n) 1) ≠ ⊤ := fun s =>
      ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
    have hsum : volume (connectedComponentIn P e' ∩ ball 0 1) +
        volume (connectedComponentIn P y ∩ ball 0 1) ≤ volume (P ∩ ball (0 : Rn n) 1) := by
      rw [← measure_union (hdisj.mono inter_subset_left inter_subset_left)
        (hPo.connectedComponentIn.measurableSet.inter measurableSet_ball)]
      exact measure_mono (union_subset (inter_subset_inter_left _ (connectedComponentIn_subset _ _))
        (inter_subset_inter_left _ (connectedComponentIn_subset _ _)))
    have h1 := ENNReal.toReal_mono (hfin P) hsum
    rw [ENNReal.toReal_add (hfin _) (hfin _)] at h1
    rw [measureReal_def] at hvol
    linarith [hR07.1, hR07'.1]

end Regular

end InnerVariational
