/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.GradVariation
public import InnerVariational.Defs.VariationalSolutionQ
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star

/-!
# Variational solutions with a Lipschitz coefficient: basic facts and the key identity

Let `Q` be `L`-Lipschitz on the open set `Ω` with `0 < c ≤ Q ≤ C` there (`QBounds Ω Q L c C`), and
let `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. By Rademacher's theorem `Q²` is differentiable a.e. in `Ω`, with
`|∇(Q²)| ≤ 2 C L`, and a.e. `div (Q² ξ) = Q² div ξ + ∇(Q²) · ξ`. Since `Q² ξ` is again a Lipschitz
test field, `∫ div (Q² ξ) = 0`. Hence the inner variation of `∫ (|∇u|² + Q² χ)` splits as

`∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u) = −∫ χ div (Q² ξ) = ∫ (1 − χ) div (Q² ξ)`.

In particular, for `ξ` supported in `Ω ∩ {u > 0}`, where `χ = 1` a.e., the quadratic part
`∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u)` vanishes, exactly as for the constant coefficient `1`.

## Main statements

* `QBounds.one`, `QBounds.mono`, `QBounds.lipschitzOnWith_sq`, `QBounds.norm_fderiv_sq_le`: the
  constant coefficient, restriction, and the bound `|∇(Q²)| ≤ 2 C L`.
* `QBounds.ae_divergence_sq_smul_eq`: `div (Q² ξ) = Q² div ξ + ∇(Q²) · ξ` a.e.
* `QBounds.integral_sq_mul_divergence_add_eq_zero`: `∫ (Q² div ξ + ∇(Q²) · ξ) = 0`.
* `IsVariationalSolutionQ.integral_gradVariation_eq`: the key identity
  `∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u) = ∫ (1 − χ) (Q² div ξ + ∇(Q²) · ξ)`, and its variants
  `integral_gradVariation_eq_neg`, `integral_chi_mul_divergence_sq_smul_eq`.
* `IsVariationalSolutionQ.integral_gradVariation_eq_zero_of_pos`: the quadratic part vanishes
  for test fields supported in `Ω ∩ {u > 0}`.
* `IsVariationalSolutionQ.mono`, `of_le`, `ae_chi_eq_one`, `norm_gradient_le`, and measurability
  helpers.
* `IsVariationalSolution.toQ`: a variational solution is one for the coefficient `Q ≡ 1`.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

open Kernel

/-- A variational solution is a variational solution for the constant coefficient `1`. -/
theorem IsVariationalSolution.toQ {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution Ω C u χ) : IsVariationalSolutionQ Ω C (fun _ => 1) u χ :=
  isVariationalSolutionQ_one_iff.2 h

namespace QBounds

variable {Ω Ω' : Set (Rn n)} {Q : Rn n → ℝ} {L : ℝ≥0} {c C : ℝ}

/-- The constant coefficient `1` satisfies the bounds with `L = 0` and `c = C = 1`. -/
theorem one (Ω : Set (Rn n)) : QBounds Ω (fun _ => (1 : ℝ)) 0 1 1 where
  lipschitzOnWith := (LipschitzWith.const (1 : ℝ)).lipschitzOnWith
  pos := one_pos
  le _ _ := le_rfl
  le' _ _ := le_rfl

theorem mono (hQ : QBounds Ω Q L c C) (hsub : Ω' ⊆ Ω) : QBounds Ω' Q L c C :=
  ⟨hQ.lipschitzOnWith.mono hsub, hQ.pos, fun x hx => hQ.le x (hsub hx),
    fun x hx => hQ.le' x (hsub hx)⟩

theorem pos_of_mem (hQ : QBounds Ω Q L c C) {x : Rn n} (hx : x ∈ Ω) : 0 < Q x :=
  hQ.pos.trans_le (hQ.le x hx)

theorem nonneg_of_mem (hQ : QBounds Ω Q L c C) {x : Rn n} (hx : x ∈ Ω) : 0 ≤ C :=
  (hQ.pos_of_mem hx).le.trans (hQ.le' x hx)

theorem abs_le (hQ : QBounds Ω Q L c C) {x : Rn n} (hx : x ∈ Ω) : |Q x| ≤ C := by
  rw [abs_of_pos (hQ.pos_of_mem hx)]; exact hQ.le' x hx

theorem sq_le (hQ : QBounds Ω Q L c C) {x : Rn n} (hx : x ∈ Ω) : Q x ^ 2 ≤ C ^ 2 :=
  pow_le_pow_left₀ (hQ.pos_of_mem hx).le (hQ.le' x hx) 2

theorem sq_le_sq (hQ : QBounds Ω Q L c C) {x : Rn n} (hx : x ∈ Ω) : c ^ 2 ≤ Q x ^ 2 :=
  pow_le_pow_left₀ hQ.pos.le (hQ.le x hx) 2

theorem continuousOn (hQ : QBounds Ω Q L c C) : ContinuousOn Q Ω :=
  hQ.lipschitzOnWith.continuousOn

/-- `Q²` is `2 C L`-Lipschitz on `Ω`. -/
theorem lipschitzOnWith_sq (hQ : QBounds Ω Q L c C) :
    LipschitzOnWith (Real.toNNReal (2 * C) * L) (fun y => Q y ^ 2) Ω := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  have hC : 0 ≤ C := hQ.nonneg_of_mem ha
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), Real.dist_eq,
    show Q a ^ 2 - Q b ^ 2 = (Q a + Q b) * (Q a - Q b) by ring, abs_mul]
  have h1 : |Q a + Q b| ≤ 2 * C := by
    rw [abs_of_pos (add_pos (hQ.pos_of_mem ha) (hQ.pos_of_mem hb))]
    linarith [hQ.le' a ha, hQ.le' b hb]
  have h2 : |Q a - Q b| ≤ L * dist a b := by
    rw [← Real.dist_eq]; exact hQ.lipschitzOnWith.dist_le_mul a ha b hb
  calc |Q a + Q b| * |Q a - Q b| ≤ 2 * C * (L * dist a b) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 2 * C * L * dist a b := by ring

/-- `Q⁻²` is `2 C L / c⁴`-Lipschitz on `Ω`. -/
theorem lipschitzOnWith_inv_sq (hQ : QBounds Ω Q L c C) :
    LipschitzOnWith (Real.toNNReal (2 * C / c ^ 4) * L) (fun y => (Q y ^ 2)⁻¹) Ω := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  have hC : 0 ≤ C := hQ.nonneg_of_mem ha
  have hc := hQ.pos
  have ha2 := hQ.sq_le_sq ha
  have hb2 := hQ.sq_le_sq hb
  have hpa : 0 < Q a ^ 2 := (pow_pos hc 2).trans_le ha2
  have hpb : 0 < Q b ^ 2 := (pow_pos hc 2).trans_le hb2
  have hsq := hQ.lipschitzOnWith_sq.dist_le_mul a ha b hb
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)] at hsq ⊢
  rw [Real.dist_eq, inv_sub_inv hpa.ne' hpb.ne', abs_div, abs_of_pos (mul_pos hpa hpb),
    abs_sub_comm, ← Real.dist_eq]
  have hc4 : c ^ 4 ≤ Q a ^ 2 * Q b ^ 2 := by
    rw [show c ^ 4 = c ^ 2 * c ^ 2 by ring]
    exact mul_le_mul ha2 hb2 (by positivity) hpa.le
  rw [div_le_iff₀ (mul_pos hpa hpb)]
  calc dist (Q a ^ 2) (Q b ^ 2) ≤ 2 * C * L * dist a b := hsq
    _ = 2 * C / c ^ 4 * L * dist a b * c ^ 4 := by field_simp
    _ ≤ 2 * C / c ^ 4 * L * dist a b * (Q a ^ 2 * Q b ^ 2) :=
        mul_le_mul_of_nonneg_left hc4 (by positivity)

/-- `|∇(Q²)| ≤ 2 C L` on `Ω`. -/
theorem norm_fderiv_sq_le (hQ : QBounds Ω Q L c C) (hΩ : IsOpen Ω) {x : Rn n} (hx : x ∈ Ω) :
    ‖fderiv ℝ (fun y => Q y ^ 2) x‖ ≤ 2 * C * L := by
  have := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hx) hQ.lipschitzOnWith_sq
  rwa [NNReal.coe_mul, Real.coe_toNNReal _ (by linarith [hQ.nonneg_of_mem hx])] at this

theorem abs_fderiv_sq_apply_le (hQ : QBounds Ω Q L c C) (hΩ : IsOpen Ω) {x : Rn n} (hx : x ∈ Ω)
    (v : Rn n) : |fderiv ℝ (fun y => Q y ^ 2) x v| ≤ 2 * C * L * ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact ((fderiv ℝ _ x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hQ.norm_fderiv_sq_le hΩ hx) (norm_nonneg _))

/-- Rademacher: `Q²` is differentiable a.e. in `Ω`. -/
theorem ae_differentiableAt_sq (hQ : QBounds Ω Q L c C) (hΩ : IsOpen Ω) :
    ∀ᵐ y, y ∈ Ω → DifferentiableAt ℝ (fun y => Q y ^ 2) y := by
  filter_upwards [hQ.lipschitzOnWith_sq.ae_differentiableWithinAt_of_mem (μ := volume)]
    with y hy hyΩ
  exact (hy hyΩ).differentiableAt (hΩ.mem_nhds hyΩ)

/-- `Q² ξ` is a Lipschitz test field. -/
theorem isLipTestField_sq_smul (hQ : QBounds Ω Q L c C) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) : IsLipTestField Ω fun y => Q y ^ 2 • ξ y :=
  isLipTestField_smul hξ hQ.lipschitzOnWith_sq (A := C ^ 2) fun y hy => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact hQ.sq_le hy

/-- `Q⁻² ξ` is a Lipschitz test field. -/
theorem isLipTestField_inv_sq_smul (hQ : QBounds Ω Q L c C) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) : IsLipTestField Ω fun y => (Q y ^ 2)⁻¹ • ξ y :=
  isLipTestField_smul hξ hQ.lipschitzOnWith_inv_sq (A := (c ^ 2)⁻¹) fun y hy => by
    have hc2 : 0 < c ^ 2 := pow_pos hQ.pos 2
    rw [abs_of_pos (inv_pos.2 (hc2.trans_le (hQ.sq_le_sq hy)))]
    exact inv_anti₀ hc2 (hQ.sq_le_sq hy)

/-- `Q² (Q⁻² ξ) = ξ` for `ξ` supported in `Ω`. -/
theorem sq_smul_inv_sq_smul (hQ : QBounds Ω Q L c C) {ξ : Rn n → Rn n} (hξ : tsupport ξ ⊆ Ω) :
    (fun y => Q y ^ 2 • (fun z => (Q z ^ 2)⁻¹ • ξ z) y) = ξ := by
  funext y
  by_cases hy : y ∈ tsupport ξ
  · rw [smul_smul, mul_inv_cancel₀ (pow_pos (hQ.pos_of_mem (hξ hy)) 2).ne', one_smul]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- The product rule `div (Q² ξ) = Q² div ξ + ∇(Q²) · ξ`, a.e. -/
theorem ae_divergence_sq_smul_eq (hQ : QBounds Ω Q L c C) (hΩ : IsOpen Ω) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField Ω ξ) :
    ∀ᵐ y, divergence (fun z => Q z ^ 2 • ξ z) y =
      Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y) := by
  obtain ⟨⟨D, hD⟩, -, hξΩ⟩ := hξ
  filter_upwards [hQ.ae_differentiableAt_sq hΩ, hD.ae_differentiableAt] with y hQy hξy
  by_cases hy : y ∈ tsupport ξ
  · exact divergence_smul_eq (hQy (hξΩ hy)).hasFDerivAt hξy
  · have hy' : y ∉ tsupport fun z => Q z ^ 2 • ξ z :=
      fun h' => hy (tsupport_smul_subset_right _ _ h')
    rw [divergence_eq_zero_of_notMem_tsupport hy', divergence_eq_zero_of_notMem_tsupport hy,
      image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero, add_zero]

theorem sq_mul_divergence_add_eq_zero_of_notMem (ξ : Rn n → Rn n) {y : Rn n}
    (hy : y ∉ tsupport ξ) :
    Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y) = 0 := by
  rw [divergence_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy, map_zero,
    mul_zero, add_zero]

/-- `|Q² div ξ + ∇(Q²) · ξ| ≤ C² n D + 2 C L M` on `Ω` for `ξ` `D`-Lipschitz with `|ξ| ≤ M`. -/
theorem abs_sq_mul_divergence_add_le (hQ : QBounds Ω Q L c C) (hΩ : IsOpen Ω) {ξ : Rn n → Rn n}
    {D : ℝ≥0} (hD : LipschitzWith D ξ) {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) {y : Rn n} (hy : y ∈ Ω) :
    |Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y)| ≤
      C ^ 2 * (n * D) + 2 * C * L * M := by
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (hQ.sq_le hy) (abs_divergence_le hD y) (abs_nonneg _) (sq_nonneg _)
  · refine (hQ.abs_fderiv_sq_apply_le hΩ hy _).trans ?_
    have := hQ.nonneg_of_mem hy
    exact mul_le_mul_of_nonneg_left (hM y) (by positivity)

theorem aestronglyMeasurable_sq_mul_divergence_add (hQ : QBounds Ω Q L c C) {K : Set (Rn n)}
    (hK : MeasurableSet K) (hKΩ : K ⊆ Ω) {ξ : Rn n → Rn n} (hξ : Continuous ξ) :
    AEStronglyMeasurable (fun y => Q y ^ 2 * divergence ξ y +
      fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) (volume.restrict K) :=
  ((((hQ.continuousOn.mono hKΩ).pow 2).aestronglyMeasurable hK).mul
    (measurable_divergence ξ).aestronglyMeasurable).add
    (measurable_fderiv_apply _ hξ.measurable).aestronglyMeasurable

theorem integrable_sq_mul_divergence_add (hQ : QBounds Ω Q L c C) (hΩ : IsOpen Ω)
    {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    Integrable fun y => Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y) := by
  obtain ⟨⟨D, hD⟩, hc, hξΩ⟩ := hξ
  obtain ⟨M, hM⟩ := hD.continuous.bounded_above_of_compact_support hc
  exact integrable_of_bound_of_isCompact hc
    (hQ.aestronglyMeasurable_sq_mul_divergence_add (isClosed_tsupport ξ).measurableSet hξΩ
      hD.continuous)
    (fun y hy => by rw [Real.norm_eq_abs]; exact hQ.abs_sq_mul_divergence_add_le hΩ hD hM (hξΩ hy))
    (fun y hy => sq_mul_divergence_add_eq_zero_of_notMem ξ hy)

/-- `∫ (Q² div ξ + ∇(Q²) · ξ) = ∫ div (Q² ξ) = 0` for `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. -/
theorem integral_sq_mul_divergence_add_eq_zero (hQ : QBounds Ω Q L c C) (hΩ : IsOpen Ω)
    {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    ∫ y, (Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) = 0 := by
  rw [← integral_congr_ae (hQ.ae_divergence_sq_smul_eq hΩ hξ)]
  exact integral_divergence_eq_zero hΩ (hQ.isLipTestField_sq_smul hξ)

end QBounds

namespace IsVariationalSolutionQ

variable {Ω Ω' : Set (Rn n)} {C C₁ : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- A variational solution on `Ω` is one on every open subset of `Ω`. -/
theorem mono (h : IsVariationalSolutionQ Ω C Q u χ) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) :
    IsVariationalSolutionQ Ω' C Q u χ where
  isOpen := hΩ'
  nonneg x hx := h.nonneg x (hsub hx)
  continuousOn := h.continuousOn.mono hsub
  contDiffOn := h.contDiffOn.mono (inter_subset_inter_left _ hsub)
  lipschitzOnWith x r hr := h.lipschitzOnWith x r (hr.trans hsub)
  measurable_chi := by
    have : Ω'.indicator χ = Ω'.indicator (Ω.indicator χ) := by
      rw [indicator_indicator, inter_eq_left.2 hsub]
    rw [this]
    exact h.measurable_chi.indicator hΩ'.measurableSet
  chi_mem x hx := h.chi_mem x (hsub hx)
  posIndicator_le_chi := ae_restrict_of_ae_restrict_of_subset hsub h.posIndicator_le_chi
  innerVariationQ_eq_zero ξ hξ := h.innerVariationQ_eq_zero ξ (hξ.mono hsub)

/-- The gradient constant of a variational solution can be increased. -/
theorem of_le (h : IsVariationalSolutionQ Ω C Q u χ) (hC : C ≤ C₁) :
    IsVariationalSolutionQ Ω C₁ Q u χ where
  isOpen := h.isOpen
  nonneg := h.nonneg
  continuousOn := h.continuousOn
  contDiffOn := h.contDiffOn
  lipschitzOnWith x r hr := (h.lipschitzOnWith x r hr).weaken hC
  measurable_chi := h.measurable_chi
  chi_mem := h.chi_mem
  posIndicator_le_chi := h.posIndicator_le_chi
  innerVariationQ_eq_zero := h.innerVariationQ_eq_zero

theorem isOpen_pos (h : IsVariationalSolutionQ Ω C Q u χ) : IsOpen (Ω ∩ {x | 0 < u x}) :=
  h.continuousOn.isOpen_inter_preimage h.isOpen isOpen_Ioi

/-- `χ = 1` a.e. on `Ω ∩ {u > 0}`. -/
theorem ae_chi_eq_one (h : IsVariationalSolutionQ Ω C Q u χ) :
    ∀ᵐ y, y ∈ Ω → 0 < u y → χ y = 1 := by
  filter_upwards [(ae_restrict_iff' h.isOpen.measurableSet).1 h.posIndicator_le_chi]
    with y hy hyΩ hpos
  have h1 := hy hyΩ
  rw [posIndicator_of_pos hpos] at h1
  rcases h.chi_mem y hyΩ with h0 | h1'
  · rw [h0] at h1; norm_num at h1
  · exact h1'

theorem abs_chi_le_one (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    |χ y| ≤ 1 := by
  rcases h.chi_mem y hy with h0 | h1 <;> simp [*]

theorem chi_nonneg (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    0 ≤ χ y := by
  rcases h.chi_mem y hy with h0 | h1 <;> simp [*]

theorem chi_le_one (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    χ y ≤ 1 := by
  rcases h.chi_mem y hy with h0 | h1 <;> simp [*]

theorem aestronglyMeasurable_chi (h : IsVariationalSolutionQ Ω C Q u χ) {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) : AEStronglyMeasurable χ (volume.restrict S) :=
  h.measurable_chi.aestronglyMeasurable.congr
    ((ae_restrict_iff' hS).2 (.of_forall fun _ hy => indicator_of_mem (hSΩ hy) χ))

/-- The set `{χ = 1}` in `Ω` is measurable. -/
theorem measurableSet_chi_eq_one (h : IsVariationalSolutionQ Ω C Q u χ) :
    MeasurableSet (Ω ∩ {y | χ y = 1}) := by
  have e : Ω ∩ {y | χ y = 1} = Ω ∩ Ω.indicator χ ⁻¹' {1} := by
    ext y
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hy, h1⟩; exact ⟨hy, by rw [indicator_of_mem hy, h1]⟩
    · rintro ⟨hy, h1⟩; exact ⟨hy, by rwa [indicator_of_mem hy] at h1⟩
  rw [e]
  exact h.isOpen.measurableSet.inter (h.measurable_chi (measurableSet_singleton 1))

/-- `|∇u| ≤ C_V` on `Ω`. -/
theorem norm_gradient_le (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    ‖gradient u y‖ ≤ C := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 h.isOpen y hy
  rw [Kernel.norm_gradient_eq]
  exact norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds y hr) (h.lipschitzOnWith y r hrΩ)

/-- `χ (Q² div ξ + ∇(Q²) · ξ)` is integrable for `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. -/
theorem integrable_chi_mul_sq_mul_divergence_add (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    Integrable fun y => χ y * (Q y ^ 2 * divergence ξ y +
      fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) := by
  have hI := hQ.integrable_sq_mul_divergence_add h.isOpen hξ
  obtain ⟨-, -, hξΩ⟩ := hξ
  have e : (fun y => χ y * (Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y))) =
      fun y => Ω.indicator χ y * (Q y ^ 2 * divergence ξ y +
        fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [indicator_of_mem hy]
    · rw [QBounds.sq_mul_divergence_add_eq_zero_of_notMem ξ (fun h' => hy (hξΩ h')), mul_zero,
        mul_zero]
  rw [e]
  refine hI.bdd_mul h.measurable_chi.aestronglyMeasurable (c := 1) (.of_forall fun y => ?_)
  by_cases hy : y ∈ Ω
  · rw [indicator_of_mem hy, Real.norm_eq_abs]; exact h.abs_chi_le_one hy
  · rw [indicator_of_notMem hy, norm_zero]; exact zero_le_one

/-- **The key identity.** For `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`,
`∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u) = −∫ χ (Q² div ξ + ∇(Q²) · ξ)`. -/
theorem integral_gradVariation_eq_neg (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    ∫ y, gradVariation u ξ y = -∫ y, χ y * (Q y ^ 2 * divergence ξ y +
      fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) := by
  have hIV := h.innerVariationQ_eq_zero ξ hξ
  have hJ := integrable_gradVariation hξ fun y hy => h.norm_gradient_le hy
  have hχ := h.integrable_chi_mul_sq_mul_divergence_add hQ hξ
  have e : (fun x => (‖gradient u x‖ ^ 2 + Q x ^ 2 * χ x) * divergence ξ x -
      2 * ⟪gradient u x, fderiv ℝ ξ x (gradient u x)⟫ +
      fderiv ℝ (fun y => Q y ^ 2) x (ξ x) * χ x) =
      fun y => gradVariation u ξ y + χ y * (Q y ^ 2 * divergence ξ y +
        fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) := by
    funext y; simp only [gradVariation]; ring
  rw [innerVariationQ, e, integral_add hJ hχ] at hIV
  linarith

/-- **The key identity**, in the form with `1 − χ`: for `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`,
`∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u) = ∫ (1 − χ) (Q² div ξ + ∇(Q²) · ξ)`. -/
theorem integral_gradVariation_eq (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    ∫ y, gradVariation u ξ y = ∫ y, (1 - χ y) * (Q y ^ 2 * divergence ξ y +
      fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) := by
  have hI := hQ.integrable_sq_mul_divergence_add h.isOpen hξ
  have hχ := h.integrable_chi_mul_sq_mul_divergence_add hQ hξ
  simp_rw [sub_mul, one_mul]
  rw [integral_sub hI hχ, hQ.integral_sq_mul_divergence_add_eq_zero h.isOpen hξ, zero_sub]
  exact h.integral_gradVariation_eq_neg hQ hξ

/-- **The key identity**, divergence form: `∫ χ div (Q² ξ) = −∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u)`
for `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. For `Q ≡ 1` this is `∫ χ div ξ = −∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)`. -/
theorem integral_chi_mul_divergence_sq_smul_eq (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    ∫ y, χ y * divergence (fun z => Q z ^ 2 • ξ z) y = -∫ y, gradVariation u ξ y := by
  rw [h.integral_gradVariation_eq_neg hQ hξ, neg_neg]
  refine integral_congr_ae ?_
  filter_upwards [hQ.ae_divergence_sq_smul_eq h.isOpen hξ] with y hy
  rw [hy]

/-- For `ξ ∈ C^{0,1}_c(Ω ∩ {u > 0}; ℝⁿ)`, where `χ = 1` a.e., the quadratic part of the inner
variation vanishes: `∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u) = 0`. -/
theorem integral_gradVariation_eq_zero_of_pos (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {ξ : Rn n → Rn n} (hξ : IsLipTestField (Ω ∩ {x | 0 < u x}) ξ) :
    ∫ y, gradVariation u ξ y = 0 := by
  have hξΩ : IsLipTestField Ω ξ := hξ.mono inter_subset_left
  rw [h.integral_gradVariation_eq_neg hQ hξΩ, neg_eq_zero,
    ← hQ.integral_sq_mul_divergence_add_eq_zero h.isOpen hξΩ]
  refine integral_congr_ae ?_
  filter_upwards [h.ae_chi_eq_one] with y hy
  by_cases hyK : y ∈ tsupport ξ
  · have := hξ.2.2 hyK
    rw [hy this.1 this.2, one_mul]
  · rw [QBounds.sq_mul_divergence_add_eq_zero_of_notMem ξ hyK, mul_zero]

end IsVariationalSolutionQ

end InnerVariational
