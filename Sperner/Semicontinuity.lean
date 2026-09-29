/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.GaussIBP
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Lower semicontinuity of the Gaussian Dirichlet energy

If `L`-Lipschitz functions `w k` converge pointwise to `w₀` and `∫ |D w k|² dγ ≤ D` for all `k`,
then `∫ |D w₀|² dγ ≤ D`.

Proof by duality. Write `∂ᵢ` for the partial derivative along the `i`-th standard basis vector,
so that `|Dw|² = ∑ᵢ (∂ᵢ w)²`. For `C¹` compactly supported `ψᵢ`, pointwise
`(∂ᵢ w)² ≥ 2 ∂ᵢ w ψᵢ - ψᵢ²`, and `∫ ∂ᵢ w_k ψᵢ dγ = -∫ w_k ∂ᵢ(ψᵢ e^{-|x|²/2}) dx` passes to the
limit by dominated convergence (integration by parts for Lipschitz functions). Hence
`∑ᵢ (2 ∫ ∂ᵢ w₀ ψᵢ dγ - ∫ ψᵢ² dγ) ≤ D`, and it remains to let `ψᵢ → ∂ᵢ w₀` in `L²(γ)`: we use
`ψᵢ = χ_j · (ρ_j ⋆ ∂ᵢ w₀)` with a mollifier `ρ_j` and a cutoff `χ_j` (Lebesgue differentiation
gives almost-everywhere convergence, and everything is bounded).
-/

open MeasureTheory Set Filter Topology Metric
open scoped NNReal RealInnerProductSpace Convolution

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- The squared operator norm of a linear functional on `ℝⁿ` is the sum of the squares of its
values on the standard basis. -/
lemma norm_sq_eq_sum_apply_single (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖ℓ‖ ^ 2 = ∑ i, (ℓ (EuclideanSpace.single i 1)) ^ 2 := by
  set v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ℓ
  have hv : ‖v‖ = ‖ℓ‖ := LinearIsometryEquiv.norm_map _ _
  have hℓ : ∀ y, ℓ y = ⟪v, y⟫ := fun y => (InnerProductSpace.toDual_symm_apply).symm
  rw [← hv, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hℓ, EuclideanSpace.inner_single_right]
  simp

/-- Integration by parts for a Lipschitz `w` against a `C¹` compactly supported `Ψ`. -/
lemma integral_fderiv_mul_eq_neg_of_hasCompactSupport {w Ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ≥0} (hw : LipschitzWith L w) (a : EuclideanSpace ℝ (Fin n)) (hΨ : ContDiff ℝ 1 Ψ)
    (hΨc : HasCompactSupport Ψ) :
    ∫ x, fderiv ℝ w x a * Ψ x = -∫ x, w x * fderiv ℝ Ψ x a := by
  obtain ⟨R₀, hR₀⟩ := hΨc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C₁, hC₁⟩ := hΨ.continuous.bounded_above_of_compact_support hΨc
  obtain ⟨C₂, hC₂⟩ := (hΨ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hΨc.fderiv (𝕜 := ℝ))
  set R := R₀ + ‖a‖
  set C := max C₁ C₂
  set B : EuclideanSpace ℝ (Fin n) → ℝ := fun x => C * (closedBall 0 R).indicator 1 x
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable one_ne_zero
  have hB : Integrable fun x => (1 + ‖x‖) * B x := by
    have hint : Integrable ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R).indicator
        fun x => (1 + ‖x‖) * C) :=
      ((by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * C)
        |>.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).integrable_indicator
        measurableSet_closedBall
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R
    · simp [B, indicator_of_mem hx]
    · simp [B, indicator_of_notMem hx]
  have hout : ∀ y, R₀ < ‖y‖ → y ∉ tsupport Ψ := fun y hy hmem => by
    have := hR₀ hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  refine integral_fderiv_mul_eq_neg_integral_mul_fderiv hw a hΨd hB (fun x => ?_) fun x t ht => ?_
  · by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R
    · simp only [B, indicator_of_mem hx, Pi.one_apply, mul_one]
      exact (Real.norm_eq_abs _ ▸ hC₁ x).trans (le_max_left _ _)
    · simp only [B, indicator_of_notMem hx, mul_zero]
      rw [mem_closedBall, dist_zero_right, not_le] at hx
      rw [image_eq_zero_of_notMem_tsupport (hout x (by linarith [norm_nonneg a])), abs_zero]
  · by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R
    · simp only [B, indicator_of_mem hx, Pi.one_apply, mul_one]
      exact (hC₂ _).trans (le_max_right _ _)
    · simp only [B, indicator_of_notMem hx, mul_zero]
      rw [mem_closedBall, dist_zero_right, not_le] at hx
      have hta : ‖t • a‖ ≤ ‖a‖ := by
        rw [norm_smul, Real.norm_eq_abs]; nlinarith [norm_nonneg a, abs_nonneg t]
      have hy : R₀ < ‖x + t • a‖ := by
        have := norm_sub_norm_le x (-(t • a))
        rw [sub_neg_eq_add, norm_neg] at this
        linarith
      have h0 : fderiv ℝ Ψ (x + t • a) = 0 := by
        by_contra hne
        exact hout _ hy (support_fderiv_subset ℝ hne)
      rw [h0, norm_zero]

/-- Weak convergence of the derivatives of pointwise convergent equi-Lipschitz functions. -/
lemma tendsto_integral_fderiv_mul {L : ℝ≥0} {w : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {w₀ : EuclideanSpace ℝ (Fin n) → ℝ} (hw : ∀ k, LipschitzWith L (w k))
    (hw₀ : LipschitzWith L w₀) (h0 : ∀ k, w k 0 = 0)
    (hconv : ∀ x, Tendsto (fun k => w k x) atTop (𝓝 (w₀ x)))
    (a : EuclideanSpace ℝ (Fin n)) {Ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨc : HasCompactSupport Ψ) :
    Tendsto (fun k => ∫ x, fderiv ℝ (w k) x a * Ψ x) atTop
      (𝓝 (∫ x, fderiv ℝ w₀ x a * Ψ x)) := by
  simp_rw [integral_fderiv_mul_eq_neg_of_hasCompactSupport (hw _) a hΨ hΨc,
    integral_fderiv_mul_eq_neg_of_hasCompactSupport hw₀ a hΨ hΨc]
  refine Tendsto.neg ?_
  have hDΨ : Continuous fun x => fderiv ℝ Ψ x a :=
    (hΨ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hbc : HasCompactSupport fun x => L * ‖x‖ * |fderiv ℝ Ψ x a| :=
    (hΨc.fderiv_apply (𝕜 := ℝ) a).abs.mul_left
  refine tendsto_integral_of_dominated_convergence (fun x => L * ‖x‖ * |fderiv ℝ Ψ x a|)
    (fun k => ((hw k).continuous.mul hDΨ).aestronglyMeasurable)
    ((by fun_prop : Continuous fun x => (L : ℝ) * ‖x‖ * |fderiv ℝ Ψ x a|)
      |>.integrable_of_hasCompactSupport hbc) (fun k => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => (hconv x).mul_const _)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have := (hw k).dist_le_mul x 0
  rwa [Real.dist_eq, h0, sub_zero, dist_zero_right] at this

lemma contDiff_gaussWeight : ContDiff ℝ 1 (gaussWeight (n := n)) := by
  unfold gaussWeight
  exact Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).neg.div_const 2)

/-- Smooth compactly supported functions approximate bounded measurable functions in `L²(γ)`. -/
lemma exists_seq_contDiff_tendsto_integral_sq {a : EuclideanSpace ℝ (Fin n) → ℝ}
    (ha : Measurable a) {C : ℝ} (hC : ∀ x, |a x| ≤ C) :
    ∃ ψ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ, (∀ j, ContDiff ℝ 1 (ψ j) ∧ HasCompactSupport (ψ j)) ∧
      Tendsto (fun j => ∫ x, (a x - ψ j x) ^ 2 ∂gaussMeasure n) atTop (𝓝 0) := by
  -- mollifiers and cutoffs
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun j =>
    ⟨1 / ((j : ℝ) + 2), 2 / ((j : ℝ) + 2), by positivity,
      by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  let χ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun j =>
    ⟨(j : ℝ) + 1, (j : ℝ) + 2, by positivity, by linarith⟩
  have hloc : LocallyIntegrable a volume :=
    (memLp_top_of_bound ha.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hC x))).locallyIntegrable
      le_top
  set conv : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun j =>
    (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a
  have hconvC : ∀ j x, |conv j x| ≤ C := by
    intro j x
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    simp only [conv, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le ((φ j).integrable_normed.mul_const C)
      (Filter.Eventually.of_forall fun t => ?_)).trans_eq ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((φ j).nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hC _) ((φ j).nonneg_normed t)
    · rw [integral_mul_const, (φ j).integral_normed, one_mul]
  refine ⟨fun j x => χ j x * conv j x, fun j => ⟨?_, ?_⟩, ?_⟩
  · exact (χ j).contDiff.mul
      ((φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed hloc)
  · exact (χ j).hasCompactSupport.mul_right
  · have hae : ∀ᵐ x ∂volume, Tendsto (fun j => conv j x) atTop (𝓝 (a x)) := by
      refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2) ?_
        (Filter.Eventually.of_forall fun j => ?_) hloc
      · have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).const_mul
          (2 : ℝ)
        refine (this.congr fun j => ?_).trans (by simp)
        simp only [Function.comp, φ, Nat.cast_add, Nat.cast_one]; ring
      · simp only [φ]; ring_nf; rfl
    have hae' : ∀ᵐ x ∂gaussMeasure n, Tendsto (fun j => conv j x) atTop (𝓝 (a x)) :=
      (withDensity_absolutelyContinuous _ _).ae_le hae
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have : Tendsto (fun j => ∫ x, (a x - χ j x * conv j x) ^ 2 ∂gaussMeasure n) atTop
        (𝓝 (∫ x, (0 : ℝ) ∂gaussMeasure n)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2)
        (fun j => ?_) (integrable_const _) (fun j => Filter.Eventually.of_forall fun x => ?_) ?_
      · have hcc : Continuous (conv j) :=
          ((φ j).hasCompactSupport_normed.contDiff_convolution_left _
            ((φ j).contDiff_normed (n := 0)) hloc).continuous
        exact ((ha.sub ((χ j).continuous.mul hcc).measurable).pow_const 2).aestronglyMeasurable
      · have h1 : |χ j x * conv j x| ≤ C := by
          rw [abs_mul, abs_of_nonneg (χ j).nonneg]
          calc χ j x * |conv j x| ≤ 1 * C :=
                mul_le_mul (χ j).le_one (hconvC j x) (abs_nonneg _) zero_le_one
            _ = C := one_mul C
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h2 : |a x - χ j x * conv j x| ≤ 2 * C := by
          have := abs_sub (a x) (χ j x * conv j x)
          linarith [hC x]
        calc (a x - χ j x * conv j x) ^ 2 = |a x - χ j x * conv j x| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      · filter_upwards [hae'] with x hx
        have hχ : Tendsto (fun j => χ j x) atTop (𝓝 1) := by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with j hj
          refine ((χ j).one_of_mem_closedBall ?_).symm
          rw [mem_closedBall, dist_zero_right]
          have := Nat.le_ceil ‖x‖
          have : (⌈‖x‖⌉₊ : ℝ) ≤ j := by exact_mod_cast hj
          simp only [χ]; linarith
        have := ((tendsto_const_nhds (x := a x)).sub (hχ.mul hx)).pow 2
        simpa using this
    simpa using this

/-- **Lower semicontinuity of the Dirichlet energy** under pointwise convergence of
equi-Lipschitz functions. -/
theorem dirichletEnergy_le_of_tendsto {L : ℝ≥0} {w : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {w₀ : EuclideanSpace ℝ (Fin n) → ℝ} (hw : ∀ k, LipschitzWith L (w k))
    (hw₀ : LipschitzWith L w₀) (h0 : ∀ k, w k 0 = 0)
    (hconv : ∀ x, Tendsto (fun k => w k x) atTop (𝓝 (w₀ x))) {D : ℝ}
    (hD : ∀ k, dirichletEnergy (w k) ≤ D) : dirichletEnergy w₀ ≤ D := by
  set e : Fin n → EuclideanSpace ℝ (Fin n) := fun i => EuclideanSpace.single i 1
  have he : ∀ i, ‖e i‖ = 1 := fun i => by simp [e]
  -- partial derivatives are bounded and measurable
  have hbd : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), LipschitzWith L f →
      ∀ i x, |fderiv ℝ f x (e i)| ≤ L := fun f hf i x => by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ f x).le_opNorm _).trans
      (by rw [he, mul_one]; exact norm_fderiv_le_of_lipschitz ℝ hf)
  have hmeas : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) i, Measurable fun x => fderiv ℝ f x (e i) :=
    fun f i => measurable_fderiv_apply_const ℝ f (e i)
  have hsum : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, dirichletEnergy f =
      ∫ x, ∑ i, (fderiv ℝ f x (e i)) ^ 2 ∂gaussMeasure n := fun f => by
    unfold dirichletEnergy
    congr 1; funext x; exact norm_sq_eq_sum_apply_single _
  -- integrability of bounded measurable functions
  have ibd : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ), Measurable g → (∀ x, |g x| ≤ C) →
      Integrable g (gaussMeasure n) := fun g C hg hC =>
    (integrable_const C).mono' hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hC x))
  -- Step 1: the dual bound for fixed test functions
  have step1 : ∀ ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i, ContDiff ℝ 1 (ψ i) ∧ HasCompactSupport (ψ i)) →
      ∑ i, (2 * ∫ x, fderiv ℝ w₀ x (e i) * ψ i x ∂gaussMeasure n -
        ∫ x, ψ i x ^ 2 ∂gaussMeasure n) ≤ D := by
    intro ψ hψ
    have hψb : ∀ i, ∃ C, ∀ x, |ψ i x| ≤ C := fun i => by
      obtain ⟨C, hC⟩ := (hψ i).1.continuous.bounded_above_of_compact_support (hψ i).2
      exact ⟨C, fun x => (Real.norm_eq_abs _).symm.trans_le (hC x)⟩
    choose Cψ hCψ using hψb
    have iprod : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), LipschitzWith L f → ∀ i,
        Integrable (fun x => fderiv ℝ f x (e i) * ψ i x) (gaussMeasure n) := fun f hf i =>
      ibd _ (L * Cψ i) ((hmeas f i).mul (hψ i).1.continuous.measurable) fun x => by
        rw [abs_mul]; exact mul_le_mul (hbd f hf i x) (hCψ i x) (abs_nonneg _) L.2
    have isq : ∀ i, Integrable (fun x => ψ i x ^ 2) (gaussMeasure n) := fun i =>
      ibd _ (Cψ i ^ 2) ((hψ i).1.continuous.measurable.pow_const 2) fun x => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hCψ i x) 2
    -- lower bound for each `w k`
    have hk : ∀ k, ∑ i, (2 * ∫ x, fderiv ℝ (w k) x (e i) * ψ i x ∂gaussMeasure n -
        ∫ x, ψ i x ^ 2 ∂gaussMeasure n) ≤ D := by
      intro k
      refine le_trans ?_ (hD k)
      rw [hsum]
      have hint : ∀ i, Integrable (fun x => 2 * (fderiv ℝ (w k) x (e i) * ψ i x) - ψ i x ^ 2)
          (gaussMeasure n) := fun i => ((iprod _ (hw k) i).const_mul 2).sub (isq i)
      calc ∑ i, (2 * ∫ x, fderiv ℝ (w k) x (e i) * ψ i x ∂gaussMeasure n -
            ∫ x, ψ i x ^ 2 ∂gaussMeasure n)
          = ∫ x, ∑ i, (2 * (fderiv ℝ (w k) x (e i) * ψ i x) - ψ i x ^ 2) ∂gaussMeasure n := by
            rw [integral_finsetSum _ fun i _ => hint i]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [integral_sub ((iprod _ (hw k) i).const_mul 2) (isq i), integral_const_mul]
        _ ≤ ∫ x, ∑ i, (fderiv ℝ (w k) x (e i)) ^ 2 ∂gaussMeasure n := by
            refine integral_mono (integrable_finsetSum _ fun i _ => hint i)
              (integrable_finsetSum _ fun i _ => ibd _ ((L : ℝ) ^ 2)
                ((hmeas _ i).pow_const 2) fun x => by
                  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
                  exact pow_le_pow_left₀ (abs_nonneg _) (hbd _ (hw k) i x) 2) fun x => ?_
            refine Finset.sum_le_sum fun i _ => ?_
            nlinarith [sq_nonneg (fderiv ℝ (w k) x (e i) - ψ i x)]
    -- pass to the limit
    refine le_of_tendsto' (x := atTop) (tendsto_finsetSum _ fun i _ => ?_) hk
    refine ((Tendsto.const_mul 2 ?_).sub tendsto_const_nhds)
    simp_rw [integral_gaussMeasure]
    have hΨ : ContDiff ℝ 1 fun x => ψ i x * gaussWeight x := (hψ i).1.mul contDiff_gaussWeight
    have hΨc : HasCompactSupport fun x => ψ i x * gaussWeight x := (hψ i).2.mul_right
    have := tendsto_integral_fderiv_mul hw hw₀ h0 hconv (e i) hΨ hΨc
    refine (this.congr fun k => ?_).trans (le_of_eq ?_)
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
    · congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  -- Step 2: approximate the partial derivatives of `w₀`
  have happrox : ∀ i, ∃ ψ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ 1 (ψ j) ∧ HasCompactSupport (ψ j)) ∧
      Tendsto (fun j => ∫ x, (fderiv ℝ w₀ x (e i) - ψ j x) ^ 2 ∂gaussMeasure n) atTop (𝓝 0) :=
    fun i => exists_seq_contDiff_tendsto_integral_sq (hmeas w₀ i) (hbd w₀ hw₀ i)
  choose ψ hψ hψlim using happrox
  have hψj : ∀ j, ∑ i, (2 * ∫ x, fderiv ℝ w₀ x (e i) * ψ i j x ∂gaussMeasure n -
      ∫ x, ψ i j x ^ 2 ∂gaussMeasure n) ≤ D := fun j => step1 (fun i => ψ i j) fun i => hψ i j
  refine le_of_tendsto' (x := atTop) ?_ hψj
  rw [hsum, integral_finsetSum _ fun i _ => ibd _ ((L : ℝ) ^ 2) ((hmeas _ i).pow_const 2)
    fun x => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbd _ hw₀ i x) 2]
  refine tendsto_finsetSum _ fun i _ => ?_
  -- `2 ∫ a ψ - ∫ ψ² = ∫ a² - ∫ (a - ψ)²`
  have hψB : ∀ j, ∃ C, ∀ x, |ψ i j x| ≤ C := fun j => by
    obtain ⟨C, hC⟩ := (hψ i j).1.continuous.bounded_above_of_compact_support (hψ i j).2
    exact ⟨C, fun x => (Real.norm_eq_abs _).symm.trans_le (hC x)⟩
  have ha2 : Integrable (fun x => fderiv ℝ w₀ x (e i) ^ 2) (gaussMeasure n) :=
    ibd _ ((L : ℝ) ^ 2) ((hmeas _ i).pow_const 2) fun x => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbd _ hw₀ i x) 2
  have heq : ∀ j, 2 * ∫ x, fderiv ℝ w₀ x (e i) * ψ i j x ∂gaussMeasure n -
      ∫ x, ψ i j x ^ 2 ∂gaussMeasure n = ∫ x, fderiv ℝ w₀ x (e i) ^ 2 ∂gaussMeasure n -
      ∫ x, (fderiv ℝ w₀ x (e i) - ψ i j x) ^ 2 ∂gaussMeasure n := by
    intro j
    obtain ⟨C, hC⟩ := hψB j
    have hcont := (hψ i j).1.continuous
    have i1 : Integrable (fun x => fderiv ℝ w₀ x (e i) * ψ i j x) (gaussMeasure n) :=
      ibd _ (L * C) ((hmeas _ i).mul hcont.measurable) fun x => by
        rw [abs_mul]; exact mul_le_mul (hbd _ hw₀ i x) (hC x) (abs_nonneg _) L.2
    have i2 : Integrable (fun x => ψ i j x ^ 2) (gaussMeasure n) :=
      ibd _ (C ^ 2) (hcont.measurable.pow_const 2) fun x => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
    have i3 : Integrable (fun x => (fderiv ℝ w₀ x (e i) - ψ i j x) ^ 2) (gaussMeasure n) := by
      have := (ha2.sub (i1.const_mul 2)).add i2
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [← integral_const_mul, ← integral_sub (i1.const_mul 2) i2, ← integral_sub ha2 i3]
    congr 1; funext x; ring
  simp_rw [heq]
  simpa using (tendsto_const_nhds (x := ∫ x, fderiv ℝ w₀ x (e i) ^ 2 ∂gaussMeasure n)).sub
    (hψlim i)

end Sperner
