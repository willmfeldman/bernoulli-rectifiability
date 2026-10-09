/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Kernel.GradVariation
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
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
  variation (in `Kernel/GradVariation.lean`).
* `IsVariationalSolution.integral_chi_mul_divergence_eq`:
  `∫ χ div ξ = −∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)`.
* `IsVariationalSolutionQ.abs_integral_gradVariation_le`: for a cutoff `η ≥ 0` with `η = 1` on
  `spt ξ`, `|∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)| ≤ C_V sup|ξ| ∫ |∇u · ∇η|`.
* `IsVariationalSolutionQ.abs_integral_chi_mul_divergence_sq_smul_le`:
  `|∫ χ div (Q² ξ)| ≤ 2^{n+1} |B_1| C_V² sup|ξ| r^{n-1}`.
* `IsVariationalSolutionQ.chi_divergence_bound`: Lemma 3.3 with a Lipschitz coefficient
  `0 < c ≤ Q`, `|∫ χ div ξ| ≤ 2^{n+1} |B_1| C_V² sup|ξ| r^{n-1} / c²`. Variants:
  `chi_divergence_bound_iSup` (with `⨆ y, ‖ξ y‖`) and `abs_setIntegral_divergence_le` (on
  `Ω ∩ {χ = 1}`, the form taken by the BV structure theorem).
* The `IsVariationalSolution` versions (the coefficient `Q ≡ 1`, with constant
  `2^{n+1} |B_1| C_V²`) are specializations.

## Proof

The paper mollifies `u` and uses that `Δu` is a nonnegative measure. We avoid mollifiers. Let
`F_k(t) = S((k+1)t − 1)`, with `S` a smooth step, so that `F_k(u) → χ_{u>0}` and `F_k(u)` vanishes
near `{u = 0}`. Testing the inner variation with `ζ_k = F_k(u) ξ`, which is supported in
`{u > 0}` where `χ = 1`, gives `∫ (|∇u|² div ζ_k − 2 ∇u·Dζ_k∇u) = −∫ div (Q² ζ_k) = 0`. The
chain rule turns this into
`∫ F_k(u) (|∇u|² div ξ − 2 ∇u·Dξ∇u) = ∫ F_k'(u) (∇u · ξ) |∇u|²`.
Since `∇u = 0` on `{u = 0}`, the left side tends to
`∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u) = −∫ χ div (Q² ξ)`.
The right side is bounded by `C_V sup|ξ| ∫ F_k'(u) |∇u|² η = −C_V sup|ξ| ∫ F_k(u) ∇u·∇η`
(the energy identity `IsLipHarmonicPos.integral_comp_mul_inner_gradient`). This plays the role
of the paper's bound `Δu(B_{3r/2}(x)) ≤ −∫ ∇u·∇η ≤ C r^{n-1}`. Replacing `ξ` by the test field
`Q⁻² ξ` bounds `∫ χ div ξ`, at the cost of the factor `c⁻²`. The paper treats `Q ≡ 1`.

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

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

open Kernel

/-- **Step 1 of Lemma 3.3.** Testing the inner variation with `ζ_k = F_k(u) ξ`:
`∫ F_k(u) (|∇u|² div ξ − 2 ∇u·Dξ∇u) = ∫ F_k'(u) (∇u · ξ) |∇u|²`. -/
theorem integral_smoothStep_mul_gradVariation (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C')
    {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) (k : ℕ) :
    ∫ y, smoothStep k (u y) * gradVariation u ξ y =
      ∫ y, smoothStep' k (u y) * (⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2) := by
  have hH := h.isLipHarmonicPos hQ
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
  have hζ0 : ∫ y, gradVariation u ζ y = 0 :=
    h.integral_gradVariation_eq_zero_of_pos hQ ⟨hζL, hξc.mono' (hsupp.trans inter_subset_left),
      hts.trans hK'V⟩
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
      rw [smul_apply, smul_apply, hsq, hxi, smul_eq_mul,
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
theorem abs_integral_smoothStep'_le (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) {η : Rn n → ℝ}
    (hη : ∃ L, LipschitzWith L η) (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y ∈ tsupport ξ, η y = 1) (k : ℕ) :
    |∫ y, smoothStep' k (u y) * (⟪gradient u y, ξ y⟫ * ‖gradient u y‖ ^ 2)| ≤
      C * M * ∫ y, |⟪gradient u y, gradient η y⟫| := by
  have hH := h.isLipHarmonicPos hQ
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
theorem tendsto_integral_smoothStep_mul_gradVariation (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C')
    {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    Tendsto (fun k : ℕ => ∫ y, smoothStep k (u y) * gradVariation u ξ y) atTop
      (𝓝 (∫ y, gradVariation u ξ y)) := by
  have hH := h.isLipHarmonicPos hQ
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
theorem abs_integral_gradVariation_le (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) {η : Rn n → ℝ}
    (hη : ∃ L, LipschitzWith L η) (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y ∈ tsupport ξ, η y = 1) :
    |∫ y, gradVariation u ξ y| ≤ C * M * ∫ y, |⟪gradient u y, gradient η y⟫| := by
  refine le_of_tendsto (h.tendsto_integral_smoothStep_mul_gradVariation hQ hξ).abs
    (.of_forall fun k => ?_)
  rw [h.integral_smoothStep_mul_gradVariation hQ hξ k]
  exact h.abs_integral_smoothStep'_le hQ hξ hM hη hηc hηΩ hη0 hη1 k

/-- **Lemma 3.3 for the field `Q² ξ`.** If `B̄_{2r}(x) ⊆ Ω` and
`ξ ∈ C^{0,1}_c(B_{3r/2}(x); ℝⁿ)` with `|ξ| ≤ M`, then
`|∫ χ div (Q² ξ)| ≤ 2^{n+1} |B_1| C_V² M r^{n-1}`. The constant does not depend on `Q`. -/
theorem abs_integral_chi_mul_divergence_sq_smul_le [NeZero n]
    (h : IsVariationalSolutionQ Ω C Q u χ) (hQ : QBounds Ω Q L c C') {x : Rn n} {r : ℝ}
    (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField (ball x (3 * r / 2)) ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) :
    |∫ y, χ y * divergence (fun z => Q z ^ 2 • ξ z) y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * M * r ^ (n - 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hδ : 0 < r / 2 := by positivity
  set η := radialCutoff x (3 * r / 2) (r / 2) with hηdef
  have h2r : 3 * r / 2 + r / 2 = 2 * r := by ring
  have hηt : tsupport η ⊆ closedBall x (2 * r) := by
    rw [← h2r]; exact tsupport_radialCutoff_subset hδ
  have hξΩ : IsLipTestField Ω ξ :=
    hξ.mono ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hΩ)
  have hmain := h.abs_integral_gradVariation_le hQ hξΩ hM ⟨_, lipschitzWith_radialCutoff hδ⟩
    (hasCompactSupport_radialCutoff hδ) (hηt.trans hΩ) radialCutoff_nonneg (fun y hy => by
      have := hξ.2.2 hy
      rw [mem_ball, dist_eq_norm] at this
      exact radialCutoff_eq_one hδ this.le)
  rw [h.integral_chi_mul_divergence_sq_smul_eq hQ hξΩ, abs_neg]
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

/-- **Lemma 3.3**, the estimate that the paper proves, with a Lipschitz coefficient. If
`B̄_{2r}(x) ⊆ Ω` and `ξ ∈ C^{0,1}_c(B_{3r/2}(x); ℝⁿ)` with `|ξ| ≤ M`, then
`|∫ χ div ξ| ≤ 2^{n+1} |B_1| C_V² M r^{n-1} / c²`, where `c > 0` is the lower bound of `Q`.

The proof applies `abs_integral_chi_mul_divergence_sq_smul_le` to the test field `Q⁻² ξ`. For
`Q ≡ 1` the constant `2^{n+1} |B_1| C_V²` depends only on `C_V` and `n`, as in the paper. The
paper then concludes `χ ∈ BV(B_r(x))` with `∫_{B_r(x)} |∇χ| ≤ C r^{n-1}`. That step is the BV
structure theorem (`Registry.exists_isGaussGreenPair_of_integral_divergence_le`). -/
theorem chi_divergence_bound [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {x : Rn n} {r : ℝ} (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω)
    {ξ : Rn n → Rn n} (hξ : IsLipTestField (ball x (3 * r / 2)) ξ) {M : ℝ}
    (hM : ∀ y, ‖ξ y‖ ≤ M) :
    |∫ y, χ y * divergence ξ y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * M * r ^ (n - 1) / c ^ 2 := by
  have hbΩ : ball x (3 * r / 2) ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hΩ
  have hc2 : 0 < c ^ 2 := pow_pos hQ.pos 2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hξ' := (hQ.mono hbΩ).isLipTestField_inv_sq_smul hξ
  have hM' : ∀ y, ‖(Q y ^ 2)⁻¹ • ξ y‖ ≤ M / c ^ 2 := by
    intro y
    by_cases hy : y ∈ tsupport ξ
    · have hq := hQ.sq_le_sq (hbΩ (hξ.2.2 hy))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hc2.trans_le hq)), div_eq_inv_mul]
      exact mul_le_mul (inv_anti₀ hc2 hq) (hM y) (norm_nonneg _) (inv_nonneg.2 hc2.le)
    · rw [image_eq_zero_of_notMem_tsupport hy, smul_zero, norm_zero]
      positivity
  have hbound := h.abs_integral_chi_mul_divergence_sq_smul_le hQ hr hΩ hξ' hM'
  rw [(hQ.mono hbΩ).sq_smul_inv_sq_smul hξ.2.2] at hbound
  refine hbound.trans_eq ?_
  ring

/-- **Lemma 3.3** with `sup |ξ|` written as `⨆ y, ‖ξ y‖`, the form used with the BV structure
theorem, with a Lipschitz coefficient. -/
theorem chi_divergence_bound_iSup [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {x : Rn n}
    {r : ℝ} (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField (ball x (3 * r / 2)) ξ) :
    |∫ y, χ y * divergence ξ y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * (⨆ y, ‖ξ y‖) * r ^ (n - 1) /
        c ^ 2 := by
  obtain ⟨D, hD⟩ := hξ.1
  exact h.chi_divergence_bound hQ hr hΩ hξ fun y =>
    le_ciSup (hD.continuous.norm.bddAbove_range_of_hasCompactSupport hξ.2.1.norm) y

/-- **Lemma 3.3**, set form, with a Lipschitz coefficient: with `E = Ω ∩ {χ = 1}` and
`φ ∈ C^∞_c(B_{3r/2}(x); ℝⁿ)`, `|∫_E div φ| ≤ 2^{n+1} |B_1| C_V² sup|φ| r^{n-1} / c²`. This is
the hypothesis of the BV structure theorem
(`Registry.exists_isGaussGreenPair_of_integral_divergence_le`) on `U = B_{3r/2}(x)`. -/
theorem abs_setIntegral_divergence_le [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {x : Rn n}
    {r : ℝ} (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω) {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField (ball x (3 * r / 2)) φ) :
    |∫ y in Ω ∩ {y | χ y = 1}, divergence φ y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * (⨆ y, ‖φ y‖) * r ^ (n - 1) /
        c ^ 2 := by
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
  exact h.chi_divergence_bound_iSup hQ hr hΩ hφ.isLipTestField

end IsVariationalSolutionQ

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

open Kernel

/-- `|∇u| ≤ C_V` on `Ω`. -/
theorem norm_gradient_le (h : IsVariationalSolution Ω C u χ) {y : Rn n} (hy : y ∈ Ω) :
    ‖gradient u y‖ ≤ C :=
  h.toQ.norm_gradient_le hy

/-- The inner variation splits: `∫ χ div ξ = −∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u)` (proof of
Lemma 3.3). -/
theorem integral_chi_mul_divergence_eq (h : IsVariationalSolution Ω C u χ) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) :
    ∫ y, χ y * divergence ξ y = -∫ y, gradVariation u ξ y := by
  simpa using h.toQ.integral_chi_mul_divergence_sq_smul_eq (QBounds.one Ω) hξ

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
  simpa using h.toQ.chi_divergence_bound (QBounds.one Ω) hr hΩ hξ hM

/-- The set `{χ = 1}` in `Ω` is measurable. -/
theorem measurableSet_chi_eq_one (h : IsVariationalSolution Ω C u χ) :
    MeasurableSet (Ω ∩ {y | χ y = 1}) :=
  h.toQ.measurableSet_chi_eq_one

/-- **Lemma 3.3**, set form: with `E = Ω ∩ {χ = 1}` and `φ ∈ C^∞_c(B_{3r/2}(x); ℝⁿ)`,
`|∫_E div φ| ≤ 2^{n+1} |B_1| C_V² sup|φ| r^{n-1}`. This is the hypothesis of the BV structure
theorem (`Registry.exists_isGaussGreenPair_of_integral_divergence_le`) on `U = B_{3r/2}(x)`. -/
theorem abs_setIntegral_divergence_le [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    {r : ℝ} (hr : 0 < r) (hΩ : closedBall x (2 * r) ⊆ Ω) {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField (ball x (3 * r / 2)) φ) :
    |∫ y in Ω ∩ {y | χ y = 1}, divergence φ y| ≤
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * (⨆ y, ‖φ y‖) * r ^ (n - 1) := by
  simpa using h.toQ.abs_setIntegral_divergence_le (QBounds.one Ω) hr hΩ hφ

end IsVariationalSolution

end InnerVariational
