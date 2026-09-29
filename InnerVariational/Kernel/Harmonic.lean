/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.IBP
public import InnerVariational.Defs.Solutions
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Basic.SphereIntegral
public import InnerVariational.Defs.Calculus

/-!
# Lipschitz functions harmonic on their positivity set

Kriventsov–Weiss (full reference below) use two facts about a nonnegative Lipschitz `u` that is
harmonic on `{u > 0}`: the energy identity `∫ |∇u|² η = −∫ u ∇u·∇η` (in the proofs of
Proposition 3.5 and Theorem 5.3) and the subharmonicity of `u` and `u²` (Proposition 3.2).
Blow-up limits of variational solutions have these properties without being variational
solutions, so we state them for the predicate `IsLipHarmonicPos U u`.

## Main definitions

* `IsLipHarmonicPos U u`: `U` open, `u ≥ 0` on `U`, `u` Lipschitz on the balls of `U` with a
  uniform constant, `u` harmonic (`C²` with `Δu = 0`) near each point of `U ∩ {u > 0}`.

## Main results

* `IsLipHarmonicPos.integral_inner_gradient_eq_zero`: `∫ ∇u·∇g = 0` for `g` Lipschitz with
  compact support in `U ∩ {u > 0}`.
* `IsLipHarmonicPos.integral_comp_mul_inner_gradient`: `∫ F(u) ∇u·∇η = −∫ F'(u) |∇u|² η` for `F`
  `C¹` vanishing on `(−∞, δ]`, `δ > 0`, and `η` Lipschitz with compact support in `U`.
* `IsLipHarmonicPos.integral_norm_gradient_sq_mul`: the energy identity with a cutoff,
  `∫ |∇u|² η = −∫ u ∇u·∇η`.
* `IsLipHarmonicPos.weaklySubharmonic`, `IsLipHarmonicPos.weaklySubharmonic_sq`: `u` and `u²` are
  weakly subharmonic on `U` (in the sense of `IsWeaklySubharmonicOn`).

## Proof notes

The paper tests with `(u − ε)₊ η` and uses smoothness of `∂{u > ε}` for a.e. `ε`. We test with
`F_k(u) η`, `F_k` smooth and vanishing on `(−∞, 1/(k+1)]` (built from `Real.smoothTransition`).
Then `F_k(u) η` is Lipschitz with compact support in `{u > 0}`, and dominated convergence as
`k → ∞` gives the identities. On `U ∩ {u = 0}` the gradient vanishes, since `u` has a local
minimum there, so no level-set argument is needed.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped NNReal ENNReal ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- `u` is a nonnegative function on the open set `U`, Lipschitz on the balls of `U` with a
uniform constant, and harmonic on `U ∩ {u > 0}`. Variational solutions have this
property (`IsVariationalSolution.isLipHarmonicPos`), and so do their blow-up limits. -/
structure IsLipHarmonicPos (U : Set (Rn n)) (u : Rn n → ℝ) : Prop where
  /-- `U` is open. -/
  isOpen : IsOpen U
  /-- `u ≥ 0` on `U`. -/
  nonneg : ∀ x ∈ U, 0 ≤ u x
  /-- `u` is Lipschitz on each ball in `U`, with a constant independent of the ball. -/
  lipschitzOnWith : ∃ C : ℝ≥0, ∀ x r, ball x r ⊆ U → LipschitzOnWith C u (ball x r)
  /-- `u` is harmonic near each point of `U ∩ {u > 0}`. -/
  harmonicAt : ∀ x ∈ U, 0 < u x → HarmonicAt u x

namespace Kernel

/-! ### The smooth step `Real.smoothTransition` -/

theorem deriv_smoothTransition_eq_zero {s : ℝ} (hs : s < 0 ∨ 1 < s) :
    deriv Real.smoothTransition s = 0 := by
  rcases hs with hs | hs
  · have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs] with t ht using Real.smoothTransition.zero_of_nonpos ht.le
    rw [this.deriv_eq, deriv_const]
  · have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hs] with t ht using Real.smoothTransition.one_of_one_le ht.le
    rw [this.deriv_eq, deriv_const]

theorem hasDerivAt_smoothTransition (s : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero s).hasDerivAt

theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem deriv_smoothTransition_nonneg (s : ℝ) : 0 ≤ deriv Real.smoothTransition s :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem exists_bound_mul_deriv_smoothTransition :
    ∃ B, ∀ s, |(s + 1) * deriv Real.smoothTransition s| ≤ B := by
  have hc : Continuous fun s => (s + 1) * deriv Real.smoothTransition s :=
    (continuous_id.add continuous_const).mul continuous_deriv_smoothTransition
  have hs : HasCompactSupport fun s => (s + 1) * deriv Real.smoothTransition s := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 1)) fun s hs => ?_
    simp only [mem_Icc, not_and_or, not_le] at hs
    rw [deriv_smoothTransition_eq_zero hs, mul_zero]
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨B, fun s => by simpa only [Real.norm_eq_abs] using hB s⟩

theorem eventually_lt_mul {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ∀ᶠ k : ℕ in atTop, a < ((k : ℝ) + 1) * t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (a / t)
  refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
  have h1 : (N : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : a < N * t := (div_lt_iff₀ ht).1 hN
  nlinarith

/-- For `t > 0`, `S((k+1)t − 1) → 1`. -/
theorem tendsto_smoothTransition {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => Real.smoothTransition (((k : ℝ) + 1) * t - 1)) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_lt_mul ht 2] with k hk
  exact (Real.smoothTransition.one_of_one_le (by linarith)).symm

/-- For `t > 0`, `S'((k+1)t − 1) = 0` eventually. -/
theorem eventually_deriv_smoothTransition_eq_zero {t : ℝ} (ht : 0 < t) :
    ∀ᶠ k : ℕ in atTop, deriv Real.smoothTransition (((k : ℝ) + 1) * t - 1) = 0 := by
  filter_upwards [eventually_lt_mul ht 2] with k hk
  exact deriv_smoothTransition_eq_zero (Or.inr (by linarith))

end Kernel

namespace IsLipHarmonicPos

variable {U : Set (Rn n)} {u : Rn n → ℝ}

theorem locallyLipschitzOn (h : IsLipHarmonicPos U u) : LocallyLipschitzOn U u := by
  obtain ⟨C, hC⟩ := h.lipschitzOnWith
  intro y hy
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 h.isOpen y hy
  exact ⟨C, ball y r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hr), hC y r hrU⟩

theorem continuousOn (h : IsLipHarmonicPos U u) : ContinuousOn u U :=
  h.locallyLipschitzOn.continuousOn

theorem isOpen_pos (h : IsLipHarmonicPos U u) : IsOpen (U ∩ {x | 0 < u x}) :=
  h.continuousOn.isOpen_inter_preimage h.isOpen isOpen_Ioi

theorem contDiffOn (h : IsLipHarmonicPos U u) : ContDiffOn ℝ 2 u (U ∩ {x | 0 < u x}) :=
  fun x hx => (h.harmonicAt x hx.1 hx.2).1.contDiffWithinAt

theorem laplacian_eq_zero (h : IsLipHarmonicPos U u) {x : Rn n} (hx : x ∈ U) (hpos : 0 < u x) :
    Δ u x = 0 :=
  (h.harmonicAt x hx hpos).2.self_of_nhds

/-- At a zero of `u` in `U`, `u` has a local minimum, so `Du = 0`. -/
theorem fderiv_eq_zero_of_eq_zero (h : IsLipHarmonicPos U u) {x : Rn n} (hx : x ∈ U)
    (h0 : u x = 0) : fderiv ℝ u x = 0 := by
  have hmin : IsLocalMin u x :=
    Filter.mem_of_superset (h.isOpen.mem_nhds hx) fun y hy => by
      simp only [mem_setOf_eq, h0]; exact h.nonneg y hy
  exact hmin.fderiv_eq_zero

theorem gradient_eq_zero_of_eq_zero (h : IsLipHarmonicPos U u) {x : Rn n} (hx : x ∈ U)
    (h0 : u x = 0) : gradient u x = 0 := by
  simp [gradient, h.fderiv_eq_zero_of_eq_zero hx h0]

/-- `|∇u| ≤ C` on `U`. -/
theorem exists_norm_gradient_le (h : IsLipHarmonicPos U u) :
    ∃ C : ℝ≥0, ∀ x ∈ U, ‖gradient u x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.lipschitzOnWith
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  rw [Kernel.norm_gradient_eq]
  exact norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x hr) (hC x r hrU)

/-- Harmonicity tested against Lipschitz functions: `∫ ∇u·∇g = 0` for `g` Lipschitz with compact
support in `U ∩ {u > 0}`. -/
theorem integral_inner_gradient_eq_zero (h : IsLipHarmonicPos U u) {g : Rn n → ℝ}
    (hg : ∃ C, LipschitzWith C g) (hgc : HasCompactSupport g)
    (hgV : tsupport g ⊆ U ∩ {x | 0 < u x}) :
    ∫ y, ⟪gradient u y, gradient g y⟫ = 0 := by
  rw [Kernel.integral_inner_gradient_eq_neg_laplacian h.isOpen_pos h.contDiffOn hg hgc hgV]
  have : ∀ y, g y * Δ u y = 0 := by
    intro y
    by_cases hy : y ∈ tsupport g
    · rw [h.laplacian_eq_zero (hgV hy).1 (hgV hy).2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  simp [this]

/-- **Testing harmonicity with `F(u) η`.** Let `F` be `C¹` with `F = 0` on `(−∞, δ]`, `δ > 0`,
and `η` Lipschitz with compact support in `U`. Then `∫ F(u) ∇u·∇η = −∫ F'(u) |∇u|² η`. -/
theorem integral_comp_mul_inner_gradient (h : IsLipHarmonicPos U u) {F F' : ℝ → ℝ}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F') {δ : ℝ} (hδ : 0 < δ)
    (hF0 : ∀ t ≤ δ, F t = 0) {η : Rn n → ℝ} (hη : ∃ C, LipschitzWith C η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ y, F (u y) * ⟪gradient u y, gradient η y⟫ =
      -∫ y, F' (u y) * ‖gradient u y‖ ^ 2 * η y := by
  obtain ⟨Cη, hCη⟩ := hη
  set K := tsupport η with hKdef
  have hK : IsCompact K := hηc
  have hη0 : ∀ y ∉ K, η y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have huK : ContinuousOn u K := h.continuousOn.mono hηU
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  obtain ⟨Cu, hCu⟩ := h.exists_norm_gradient_le
  obtain ⟨Lu, hLu⟩ := (h.locallyLipschitzOn.mono hηU).exists_lipschitzOnWith_of_compact hK
  obtain ⟨Mu, hMu⟩ := hK.exists_bound_of_continuousOn huK
  obtain ⟨BF, hBF⟩ :=
    (isCompact_Icc (a := -Mu) (b := Mu)).exists_bound_of_continuousOn hF'.continuousOn
  obtain ⟨BF0, hBF0⟩ :=
    (isCompact_Icc (a := -Mu) (b := Mu)).exists_bound_of_continuousOn hFc.continuousOn
  have huI : ∀ y ∈ K, u y ∈ Icc (-Mu) Mu := fun y hy =>
    abs_le.1 (by simpa only [Real.norm_eq_abs] using hMu y hy)
  have hLF : LipschitzOnWith (Real.toNNReal BF) F (Icc (-Mu) Mu) :=
    (convex_Icc _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t _ => (hF t).hasDerivWithinAt) (fun t ht => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
        exact (hBF t ht).trans (le_max_left _ _))
  have hFuL : LipschitzOnWith (Real.toNNReal BF * Lu) (fun y => F (u y)) K :=
    hLF.comp hLu huI
  obtain ⟨Aη, hAη⟩ := hCη.continuous.bounded_above_of_compact_support hηc
  set g : Rn n → ℝ := fun y => η y • F (u y) with hg
  have hgL := Kernel.lipschitzWith_smul_of_support hCη
    (fun y => by simpa only [Real.norm_eq_abs] using hAη y) hη0 hFuL
    (fun y hy => hBF0 (u y) (huI y hy))
  -- the support of `g` is a compact subset of `U ∩ {u > 0}`
  set K' := K ∩ u ⁻¹' Ici δ
  have hK'c : IsClosed K' := huK.preimage_isClosed_of_isClosed (isClosed_tsupport η) isClosed_Ici
  have hsupp : Function.support g ⊆ K' := by
    intro y hy
    simp only [Function.mem_support, hg, smul_eq_mul, ne_eq, mul_eq_zero, not_or] at hy
    refine ⟨subset_tsupport η hy.1, ?_⟩
    by_contra hlt
    exact hy.2 (hF0 _ (le_of_lt (not_le.1 hlt)))
  have hts : tsupport g ⊆ K' := closure_minimal hsupp hK'c
  have hgc : HasCompactSupport g :=
    (hK.of_isClosed_subset hK'c inter_subset_left).of_isClosed_subset (isClosed_tsupport g) hts
  have hK'V : K' ⊆ U ∩ {x | 0 < u x} := fun y hy => ⟨hηU hy.1, hδ.trans_le hy.2⟩
  have hmain := h.integral_inner_gradient_eq_zero ⟨_, hgL⟩ hgc (hts.trans hK'V)
  -- the chain rule, a.e.
  have hpt : ∀ᵐ y, ⟪gradient u y, gradient g y⟫ =
      F (u y) * ⟪gradient u y, gradient η y⟫ + F' (u y) * ‖gradient u y‖ ^ 2 * η y := by
    filter_upwards [hCη.ae_differentiableAt] with y hy
    rw [Kernel.inner_gradient_right g, Kernel.inner_gradient_right η]
    by_cases hyV : y ∈ U ∧ 0 < u y
    · have hu : HasFDerivAt u (fderiv ℝ u y) y :=
        ((h.contDiffOn.contDiffAt (h.isOpen_pos.mem_nhds hyV)).differentiableAt
          (by norm_num)).hasFDerivAt
      have hFu := (hF (u y)).comp_hasFDerivAt y hu
      have hgd : HasFDerivAt g _ y := hy.hasFDerivAt.smul hFu
      have hsq : fderiv ℝ u y (gradient u y) = ‖gradient u y‖ ^ 2 := by
        rw [← Kernel.inner_gradient_left, real_inner_self_eq_norm_sq]
      rw [hgd.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, hsq]
      ring
    · have hyK' : y ∉ tsupport g := fun hy' => hyV (hK'V (hts hy'))
      rw [Kernel.fderiv_eq_zero_of_notMem_tsupport hyK', ContinuousLinearMap.zero_apply]
      by_cases hyK : y ∈ K
      · have hu0 : u y = 0 :=
          le_antisymm (not_lt.1 fun hp => hyV ⟨hηU hyK, hp⟩) (h.nonneg y (hηU hyK))
        rw [h.gradient_eq_zero_of_eq_zero (hηU hyK) hu0]
        simp
      · rw [Kernel.fderiv_eq_zero_of_notMem_tsupport hyK, hη0 y hyK]
        simp
  -- integrability
  have hgradη : ∀ y, ‖gradient η y‖ ≤ Cη := Kernel.norm_gradient_le_of_lipschitz hCη
  have hI1 : Integrable fun y => F (u y) * ⟪gradient u y, gradient η y⟫ := by
    refine Kernel.integrable_mul_of_isCompact hK
      (Kernel.aestronglyMeasurable_comp_mul hK.measurableSet huK hFc
        ((measurable_gradient u).inner (measurable_gradient η)))
      (fun y hy => hBF0 _ (huI y hy)) (B := Cu * Cη) (fun y hy => ?_) (fun y hy => ?_)
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hCu y (hηU hy)) (hgradη y) (norm_nonneg _) Cu.2)
    · rw [Kernel.gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right]
  have hI2 : Integrable fun y => F' (u y) * ‖gradient u y‖ ^ 2 * η y := by
    refine Kernel.integrable_mul_of_isCompact hK
      (((Kernel.aestronglyMeasurable_comp_mul hK.measurableSet huK hF'
        ((measurable_gradient u).norm.pow_const 2))).mul
        hCη.continuous.aestronglyMeasurable)
      (A := BF * Cu ^ 2) (fun y hy => ?_) (fun y _ => hAη y) hη0
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (hBF _ (huI y hy)) (pow_le_pow_left₀ (norm_nonneg _) (hCu y (hηU hy)) 2)
      (by positivity) ((norm_nonneg _).trans (hBF _ (huI y hy)))
  rw [integral_congr_ae hpt, integral_add hI1 hI2] at hmain
  linarith

/-- **Energy identity with a cutoff** (as in the proof of Proposition 3.5). For `η` Lipschitz
with compact support in `U`, `∫ |∇u|² η = −∫ u ∇u·∇η`. -/
theorem integral_norm_gradient_sq_mul (h : IsLipHarmonicPos U u) {η : Rn n → ℝ}
    (hη : ∃ C, LipschitzWith C η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∫ y, ‖gradient u y‖ ^ 2 * η y = -∫ y, u y * ⟪gradient u y, gradient η y⟫ := by
  set S := Real.smoothTransition
  set S' := deriv Real.smoothTransition
  obtain ⟨Cη, hCη⟩ := hη
  set K := tsupport η
  have hK : IsCompact K := hηc
  have hη0 : ∀ y ∉ K, η y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have huK : ContinuousOn u K := h.continuousOn.mono hηU
  have hSc : Continuous S := Real.smoothTransition.continuous
  have hS'c : Continuous S' := Kernel.continuous_deriv_smoothTransition
  obtain ⟨Cu, hCu⟩ := h.exists_norm_gradient_le
  obtain ⟨Mu, hMu⟩ := hK.exists_bound_of_continuousOn huK
  obtain ⟨Aη, hAη⟩ := hCη.continuous.bounded_above_of_compact_support hηc
  obtain ⟨B', hB'⟩ := Kernel.exists_bound_mul_deriv_smoothTransition
  have hgradη : ∀ y, ‖gradient η y‖ ≤ Cη := Kernel.norm_gradient_le_of_lipschitz hCη
  have hI0 : ∀ y ∉ K, ⟪gradient u y, gradient η y⟫ = 0 := fun y hy => by
    rw [Kernel.gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right]
  have hIb : ∀ y ∈ K, ‖⟪gradient u y, gradient η y⟫‖ ≤ Cu * Cη := fun y hy =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hCu y (hηU hy)) (hgradη y) (norm_nonneg _) Cu.2)
  have hnn : ∀ y ∈ K, 0 ≤ u y := fun y hy => h.nonneg y (hηU hy)
  -- the identities for `F_k(t) = t S((k+1)t − 1)`
  have hk : ∀ k : ℕ, ∫ y, u y * S (((k : ℝ) + 1) * u y - 1) * ⟪gradient u y, gradient η y⟫ =
      -∫ y, (S (((k : ℝ) + 1) * u y - 1) + u y * (((k : ℝ) + 1) * S' (((k : ℝ) + 1) * u y - 1)))
        * ‖gradient u y‖ ^ 2 * η y := by
    intro k
    have hc : (0 : ℝ) < k + 1 := by positivity
    refine h.integral_comp_mul_inner_gradient
      (F := fun t => t * S (((k : ℝ) + 1) * t - 1))
      (F' := fun t => S (((k : ℝ) + 1) * t - 1) + t * (((k : ℝ) + 1) * S' (((k : ℝ) + 1) * t - 1)))
      (fun t => ?_) (by fun_prop) (δ := 1 / ((k : ℝ) + 1)) (by positivity) (fun t ht => ?_)
      ⟨Cη, hCη⟩ hηc hηU
    · have h1 : HasDerivAt (fun t : ℝ => ((k : ℝ) + 1) * t - 1) ((k : ℝ) + 1) t := by
        simpa using ((hasDerivAt_id t).const_mul ((k : ℝ) + 1)).sub_const 1
      have h2 := (Kernel.hasDerivAt_smoothTransition (((k : ℝ) + 1) * t - 1)).comp t h1
      convert (hasDerivAt_id t).mul h2 using 1
      simp only [id, one_mul, S', S, Function.comp_apply]
      ring
    · have : ((k : ℝ) + 1) * t - 1 ≤ 0 := by
        rw [le_div_iff₀ hc] at ht; linarith
      simp only [S, Real.smoothTransition.zero_of_nonpos this, mul_zero]
  -- limits
  have hL : Tendsto (fun k : ℕ => ∫ y, u y * S (((k : ℝ) + 1) * u y - 1) *
      ⟪gradient u y, gradient η y⟫) atTop (𝓝 (∫ y, u y * ⟪gradient u y, gradient η y⟫)) := by
    refine Kernel.tendsto_integral_of_isCompact hK (fun k y hy => by rw [hI0 y hy, mul_zero])
      (fun y hy => by rw [hI0 y hy, mul_zero]) (fun k => ?_) (B := Mu * 1 * (Cu * Cη))
      (fun k y hy => ?_) (fun y hy => ?_)
    · exact Kernel.aestronglyMeasurable_comp_mul hK.measurableSet huK
        (Φ := fun t => t * S (((k : ℝ) + 1) * t - 1)) (by fun_prop)
        ((measurable_gradient u).inner (measurable_gradient η))
    · rw [norm_mul, norm_mul]
      have hM0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu y hy)
      refine mul_le_mul (mul_le_mul (hMu y hy) ?_ (norm_nonneg _) hM0) (hIb y hy)
        (norm_nonneg _) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · rcases (hnn y hy).lt_or_eq with hpos | hzero
      · simpa using ((Kernel.tendsto_smoothTransition hpos).const_mul (u y)).mul_const
          ⟪gradient u y, gradient η y⟫
      · simp [← hzero]
  have hR : Tendsto (fun k : ℕ => ∫ y, (S (((k : ℝ) + 1) * u y - 1) +
      u y * (((k : ℝ) + 1) * S' (((k : ℝ) + 1) * u y - 1))) * ‖gradient u y‖ ^ 2 * η y) atTop
      (𝓝 (∫ y, ‖gradient u y‖ ^ 2 * η y)) := by
    refine Kernel.tendsto_integral_of_isCompact hK (fun k y hy => by rw [hη0 y hy, mul_zero])
      (fun y hy => by rw [hη0 y hy, mul_zero]) (fun k => ?_) (B := (1 + B') * Cu ^ 2 * Aη)
      (fun k y hy => ?_) (fun y hy => ?_)
    · exact (Kernel.aestronglyMeasurable_comp_mul hK.measurableSet huK
        (Φ := fun t => S (((k : ℝ) + 1) * t - 1) +
          t * (((k : ℝ) + 1) * S' (((k : ℝ) + 1) * t - 1))) (by fun_prop)
        ((measurable_gradient u).norm.pow_const 2)).mul hCη.continuous.aestronglyMeasurable
    · have hS1 : |S (((k : ℝ) + 1) * u y - 1)| ≤ 1 := by
        rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      have hS2 : |u y * (((k : ℝ) + 1) * S' (((k : ℝ) + 1) * u y - 1))| ≤ B' := by
        have := hB' (((k : ℝ) + 1) * u y - 1)
        rw [show ((k : ℝ) + 1) * u y - 1 + 1 = ((k : ℝ) + 1) * u y by ring] at this
        rwa [show u y * (((k : ℝ) + 1) * S' (((k : ℝ) + 1) * u y - 1)) =
          ((k : ℝ) + 1) * u y * S' (((k : ℝ) + 1) * u y - 1) by ring]
      have hsum := (abs_add_le _ _).trans (add_le_add hS1 hS2)
      rw [norm_mul, norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
      have hg2 : ‖gradient u y‖ ^ 2 ≤ (Cu : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hCu y (hηU hy)) 2
      have hB0 : 0 ≤ 1 + B' := (abs_nonneg _).trans hsum
      exact mul_le_mul (mul_le_mul hsum hg2 (by positivity) hB0) (hAη y) (norm_nonneg _)
        (by positivity)
    · rcases (hnn y hy).lt_or_eq with hpos | hzero
      · have h1 := Kernel.tendsto_smoothTransition hpos
        have h2 : Tendsto (fun k : ℕ => u y * (((k : ℝ) + 1) *
            S' (((k : ℝ) + 1) * u y - 1))) atTop (𝓝 0) := by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [Kernel.eventually_deriv_smoothTransition_eq_zero hpos] with k hk
          simp only [S'] at hk ⊢
          rw [hk, mul_zero, mul_zero]
        simpa using ((h1.add h2).mul_const (‖gradient u y‖ ^ 2)).mul_const (η y)
      · have hg : gradient u y = 0 := h.gradient_eq_zero_of_eq_zero (hηU hy) hzero.symm
        simp [hg]
  have := tendsto_nhds_unique (hL.congr hk) hR.neg
  linarith

/-- `∫ ∇u·∇φ ≤ 0` for `0 ≤ φ ∈ C^∞_c(U)`. -/
theorem integral_inner_gradient_nonpos (h : IsLipHarmonicPos U u) {φ : Rn n → ℝ}
    (hφ : IsTestFunction U φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫ y, ⟪gradient u y, gradient φ y⟫ ≤ 0 := by
  set S := Real.smoothTransition
  set S' := deriv Real.smoothTransition
  obtain ⟨hφs, hφc, hφU⟩ := hφ
  obtain ⟨Cφ, hCφ⟩ := hφs.lipschitzWith_of_hasCompactSupport hφc (by simp)
  set K := tsupport φ
  have hK : IsCompact K := hφc
  have huK : ContinuousOn u K := h.continuousOn.mono hφU
  obtain ⟨Cu, hCu⟩ := h.exists_norm_gradient_le
  have hI0 : ∀ y ∉ K, ⟪gradient u y, gradient φ y⟫ = 0 := fun y hy => by
    rw [Kernel.gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right]
  have hIb : ∀ y ∈ K, ‖⟪gradient u y, gradient φ y⟫‖ ≤ Cu * Cφ := fun y hy =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hCu y (hφU hy))
      (Kernel.norm_gradient_le_of_lipschitz hCφ y) (norm_nonneg _) Cu.2)
  have hk : ∀ k : ℕ, ∫ y, S (((k : ℝ) + 1) * u y - 1) * ⟪gradient u y, gradient φ y⟫ ≤ 0 := by
    intro k
    have hc : (0 : ℝ) < k + 1 := by positivity
    rw [h.integral_comp_mul_inner_gradient (F := fun t => S (((k : ℝ) + 1) * t - 1))
      (F' := fun t => ((k : ℝ) + 1) * S' (((k : ℝ) + 1) * t - 1))
      (fun t => ?_) (by fun_prop) (δ := 1 / ((k : ℝ) + 1)) (by positivity) (fun t ht => ?_)
      ⟨Cφ, hCφ⟩ hφc hφU, neg_nonpos]
    · refine integral_nonneg fun y => ?_
      have := Kernel.deriv_smoothTransition_nonneg (((k : ℝ) + 1) * u y - 1)
      have := hφ0 y
      positivity
    · have h1 : HasDerivAt (fun t : ℝ => ((k : ℝ) + 1) * t - 1) ((k : ℝ) + 1) t := by
        simpa using ((hasDerivAt_id t).const_mul ((k : ℝ) + 1)).sub_const 1
      convert (Kernel.hasDerivAt_smoothTransition (((k : ℝ) + 1) * t - 1)).comp t h1 using 1
      simp only [S']
      ring
    · have : ((k : ℝ) + 1) * t - 1 ≤ 0 := by
        rw [le_div_iff₀ hc] at ht; linarith
      exact Real.smoothTransition.zero_of_nonpos this
  have hL : Tendsto (fun k : ℕ => ∫ y, S (((k : ℝ) + 1) * u y - 1) *
      ⟪gradient u y, gradient φ y⟫) atTop (𝓝 (∫ y, ⟪gradient u y, gradient φ y⟫)) := by
    refine Kernel.tendsto_integral_of_isCompact hK (fun k y hy => by rw [hI0 y hy, mul_zero])
      hI0 (fun k => ?_) (B := 1 * (Cu * Cφ)) (fun k y hy => ?_) (fun y hy => ?_)
    · exact Kernel.aestronglyMeasurable_comp_mul hK.measurableSet huK
        (Φ := fun t => S (((k : ℝ) + 1) * t - 1)) (by fun_prop)
        ((measurable_gradient u).inner (measurable_gradient φ))
    · rw [norm_mul]
      refine mul_le_mul ?_ (hIb y hy) (norm_nonneg _) zero_le_one
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · rcases (h.nonneg y (hφU hy)).lt_or_eq with hpos | hzero
      · simpa using (Kernel.tendsto_smoothTransition hpos).mul_const
          ⟪gradient u y, gradient φ y⟫
      · have hg : gradient u y = 0 := h.gradient_eq_zero_of_eq_zero (hφU hy) hzero.symm
        simp [hg]
  exact le_of_tendsto' hL hk

/-- **Proposition 3.2, subharmonicity**: `u` is weakly subharmonic on `U`. -/
theorem weaklySubharmonic (h : IsLipHarmonicPos U u) : IsWeaklySubharmonicOn U u := by
  intro φ hφ hφ0
  rw [Kernel.integral_mul_laplacian_eq_neg h.isOpen h.locallyLipschitzOn hφ]
  linarith [h.integral_inner_gradient_nonpos hφ hφ0]

/-- At a zero of `u`, `u²` is differentiable with derivative `0`. -/
theorem hasFDerivAt_sq_of_eq_zero (h : IsLipHarmonicPos U u) {y : Rn n} (hy : y ∈ U)
    (h0 : u y = 0) : HasFDerivAt (fun z => u z ^ 2) (0 : Rn n →L[ℝ] ℝ) y := by
  obtain ⟨C, hC⟩ := h.lipschitzOnWith
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 h.isOpen y hy
  rw [hasFDerivAt_iff_isLittleO]
  simp only [h0, ContinuousLinearMap.zero_apply, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hδ : 0 < min r (c / ((C : ℝ) ^ 2 + 1)) := lt_min hr (by positivity)
  filter_upwards [ball_mem_nhds y hδ] with z hz
  have hzr : z ∈ ball y r := mem_ball.2 ((mem_ball.1 hz).trans_le (min_le_left _ _))
  have hd : ‖z - y‖ < c / ((C : ℝ) ^ 2 + 1) := by
    rw [← dist_eq_norm]; exact (mem_ball.1 hz).trans_le (min_le_right _ _)
  have hL := (hC y r hrU).dist_le_mul z hzr y (mem_ball_self hr)
  rw [Real.dist_eq, h0, sub_zero, dist_eq_norm] at hL
  rw [norm_pow, Real.norm_eq_abs]
  have hC2 : (C : ℝ) ^ 2 * ‖z - y‖ ≤ c := by
    have h1 : (C : ℝ) ^ 2 * ‖z - y‖ ≤ ((C : ℝ) ^ 2 + 1) * ‖z - y‖ := by
      nlinarith [norm_nonneg (z - y)]
    have h2 : ((C : ℝ) ^ 2 + 1) * ‖z - y‖ ≤ c := by
      rw [lt_div_iff₀ (by positivity)] at hd; linarith
    linarith
  have habs : |u z| ≤ C * ‖z - y‖ := hL
  calc |u z| ^ 2 ≤ (C * ‖z - y‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = (C : ℝ) ^ 2 * ‖z - y‖ * ‖z - y‖ := by ring
    _ ≤ c * ‖z - y‖ := mul_le_mul_of_nonneg_right hC2 (norm_nonneg _)

/-- `D(u²) = 2u Du` on `U`. -/
theorem fderiv_sq (h : IsLipHarmonicPos U u) {y : Rn n} (hy : y ∈ U) :
    fderiv ℝ (fun z => u z ^ 2) y = (2 * u y) • fderiv ℝ u y := by
  rcases (h.nonneg y hy).lt_or_eq with hpos | hzero
  · have hu : DifferentiableAt ℝ u y :=
      (h.contDiffOn.contDiffAt (h.isOpen_pos.mem_nhds ⟨hy, hpos⟩)).differentiableAt
        (by norm_num)
    rw [(hu.hasFDerivAt.pow 2).fderiv]
    simp
  · rw [(h.hasFDerivAt_sq_of_eq_zero hy hzero.symm).fderiv, ← hzero]
    simp

theorem locallyLipschitzOn_sq (h : IsLipHarmonicPos U u) :
    LocallyLipschitzOn U fun z => u z ^ 2 := by
  obtain ⟨C, hC⟩ := h.lipschitzOnWith
  intro y hy
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 h.isOpen y hy
  have hL := hC y r hrU
  set M := |u y| + C * r
  have hM : ∀ z ∈ ball y r, |u z| ≤ M := fun z hz => by
    have := hL.dist_le_mul z hz y (mem_ball_self hr)
    rw [Real.dist_eq] at this
    have h2 : dist z y ≤ r := (mem_ball.1 hz).le
    have := abs_sub_abs_le_abs_sub (u z) (u y)
    nlinarith [C.coe_nonneg]
  refine ⟨Real.toNNReal (2 * M * C), ball y r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hr),
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  rw [Real.dist_eq, show u a ^ 2 - u b ^ 2 = (u a + u b) * (u a - u b) by ring, abs_mul]
  have h1 : |u a + u b| ≤ 2 * M := (abs_add_le _ _).trans (by linarith [hM a ha, hM b hb])
  have h2 : |u a - u b| ≤ C * dist a b := by
    rw [← Real.dist_eq]; exact hL.dist_le_mul a ha b hb
  calc |u a + u b| * |u a - u b| ≤ 2 * M * (C * dist a b) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by linarith [abs_nonneg (u a + u b)])
    _ = 2 * M * C * dist a b := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg

/-- **Prop 3.2 for `u²`**: `u²` is weakly subharmonic on `U`, since
`∫ u² Δφ = −2 ∫ u ∇u·∇φ = 2 ∫ |∇u|² φ ≥ 0` by the energy identity. -/
theorem weaklySubharmonic_sq (h : IsLipHarmonicPos U u) :
    IsWeaklySubharmonicOn U fun z => u z ^ 2 := by
  intro φ hφ hφ0
  rw [Kernel.integral_mul_laplacian_eq_neg h.isOpen h.locallyLipschitzOn_sq hφ]
  obtain ⟨hφs, hφc, hφU⟩ := hφ
  have hpt : ∀ y, ⟪gradient (fun z => u z ^ 2) y, gradient φ y⟫ =
      2 * (u y * ⟪gradient u y, gradient φ y⟫) := by
    intro y
    by_cases hy : y ∈ tsupport φ
    · rw [Kernel.inner_gradient_left, Kernel.inner_gradient_left, h.fderiv_sq (hφU hy)]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    · rw [Kernel.gradient_eq_zero_of_notMem_tsupport hy]
      simp
  simp_rw [hpt]
  rw [integral_const_mul]
  have hE := h.integral_norm_gradient_sq_mul
    (hφs.lipschitzWith_of_hasCompactSupport hφc (by simp)) hφc hφU
  have : 0 ≤ ∫ y, ‖gradient u y‖ ^ 2 * φ y :=
    integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hφ0 y)
  linarith

end IsLipHarmonicPos

end InnerVariational
