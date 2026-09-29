/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Density
public import InnerVariational.Blowup.DomainVariation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Hom
import Mathlib.Topology.EMetricSpace.Paracompact
import InnerVariational.Registry.BV
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral

/-!
# Compactness of variational solutions on a fixed domain

The first paragraph of the proof of Theorem 9.3 of Kriventsov–Weiss (full reference below), for
arbitrary variational solutions with a uniform constant (Remark 9.4 of the paper notes that this
part does not use that the `u_k` are classical). Let `(u_k, χ_k)` be variational solutions on an
open `U` with constant `C_V`, and `u_k → v` locally uniformly on `U`. Then:

* `∇u_k → ∇v` in `L²_loc(U)` (along the full sequence);
* along a subsequence, `χ_k → χ₀` in `L¹_loc(U)` and a.e. on `U`, with `χ₀ ∈ {0, 1}`;
* `(v, χ₀)` is a variational solution on `U` with constant `C_V`.

This is `IsVariationalSolution.exists_subseq_limit`. We also record
`IsVariationalSolution.posIndicator_of_ae_eq` (replacing `χ` by `χ_{u>0}` when they agree a.e.) and
`IsVariationalSolution.posIndicator_of_eq_zero` (the case `u ≡ 0`), which Theorem 9.3 combines with
Theorem 8.6.

## Proof

* Gradients: the strong convergence of gradients from the proof of Proposition 3.5
  (`tendsto_setIntegral_norm_gradient_sub_sq`), which uses only the Lipschitz bound, harmonicity on
  `{u_k > 0}`, and interior estimates for harmonic functions.
* `χ_k`: Lemma 3.3, in the form of the key estimate `abs_integral_gradVariation_le` with one fixed
  Lipschitz cutoff, gives a bound on `∫ χ_k div ψ` uniform in `k` on a neighbourhood of each
  compact set (`exists_abs_integral_chi_mul_divergence_le`); then BV compactness
  (`Registry.exists_subseq_tendsto_of_integral_mul_divergence_le`) gives a subsequence converging
  in `L¹_loc` and a.e. to some `f₀`. Since each `χ_k` is `{0, 1}`-valued on `U`, so is `f₀` a.e.,
  and `χ₀ := if f₀ = 1 then 1 else 0` is a `{0, 1}`-valued representative.
* The domain variation passes to the limit: its quadratic part by strong `L²` convergence of the
  gradients (`tendsto_integral_gradVariation`), its `χ` part by dominated convergence.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

open Kernel

variable {U : Set (Rn n)} {C : ℝ≥0}

/-- **Uniform local BV bound for `χ`** (Lemma 3.3, uniform version). Every compact
`K ⊆ U` has an open neighbourhood `W ⊆ U` and a bound `P` such that `|∫ χ div ψ| ≤ P` for every
variational solution `(u, χ)` on `U` with constant `C` and every `ψ ∈ C^{0,1}_c(W; ℝⁿ)` with
`|ψ| ≤ 1`. The bound depends only on `C`, `K` and `U`. -/
theorem exists_abs_integral_chi_mul_divergence_le (hU : IsOpen U) {K : Set (Rn n)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ ∃ P : ℝ, ∀ u χ : Rn n → ℝ, IsVariationalSolution U C u χ →
      ∀ ψ : Rn n → Rn n, IsLipTestField W ψ → (∀ y, ‖ψ y‖ ≤ 1) →
        |∫ y, χ y * divergence ψ y| ≤ P := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening (δ / 2) K) := hK.cthickening
  have hK'U : cthickening (δ / 2) K ⊆ U :=
    (cthickening_mono (by linarith) K).trans hδU
  obtain ⟨η, ⟨Lη, hLη⟩, hηc, hηU, hη0, -, hη1⟩ := exists_lipschitz_cutoff hU hK' hK'U
  refine ⟨thickening (δ / 2) K, isOpen_thickening, self_subset_thickening (by linarith) K,
    (thickening_subset_cthickening _ _).trans hK'U,
    C * ((C : ℝ) * Lη * volume.real (tsupport η)), fun u χ h ψ hψ hψ1 => ?_⟩
  have hψU : IsLipTestField U ψ := hψ.mono ((thickening_subset_cthickening _ _).trans hK'U)
  have hmain := h.abs_integral_gradVariation_le hψU hψ1 ⟨Lη, hLη⟩ hηc hηU hη0 (fun y hy =>
    hη1 y (thickening_subset_cthickening _ _ (hψ.2.2 hy)))
  rw [h.integral_chi_mul_divergence_eq hψU, abs_neg]
  refine hmain.trans ?_
  rw [mul_one]
  refine mul_le_mul_of_nonneg_left ?_ C.2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport η) (fun y hy => by
      rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right, abs_zero])]
  refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const
    hηc.isCompact.measure_lt_top fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_abs, ← Real.norm_eq_abs]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (h.norm_gradient_le (hηU hy))
    (norm_gradient_le_of_lipschitz hLη y) (norm_nonneg _) C.2)

/-- `(u, χ_{u>0})` is a variational solution as soon as `(u, χ)` is one and the domain variation
of `(u, χ_{u>0})` vanishes. -/
theorem posIndicator_of_innerVariation {Ω : Set (Rn n)} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution Ω C u χ)
    (hIV : ∀ ξ, IsLipTestField Ω ξ → innerVariation u (posIndicator u) ξ = 0) :
    IsVariationalSolution Ω C u (posIndicator u) where
  isOpen := h.isOpen
  nonneg := h.nonneg
  continuousOn := h.continuousOn
  contDiffOn := h.contDiffOn
  lipschitzOnWith := h.lipschitzOnWith
  measurable_chi := by
    have e : Ω.indicator (posIndicator u) = (Ω ∩ {y | 0 < u y}).indicator 1 := by
      rw [posIndicator, indicator_indicator]
    rw [e]
    exact measurable_one.indicator h.isOpen_pos.measurableSet
  chi_mem x _ := by
    by_cases hx : 0 < u x
    · exact Or.inr (posIndicator_of_pos hx)
    · exact Or.inl (posIndicator_of_nonpos (not_lt.1 hx))
  posIndicator_le_chi := .of_forall fun _ => le_rfl
  innerVariation_eq_zero := hIV

/-- Replacing `χ` by `χ_{u>0}` when the two agree a.e. on `Ω`. -/
theorem posIndicator_of_ae_eq {Ω : Set (Rn n)} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution Ω C u χ) (hχ : χ =ᵐ[volume.restrict Ω] posIndicator u) :
    IsVariationalSolution Ω C u (posIndicator u) :=
  h.posIndicator_of_innerVariation fun ξ hξ => by
    rw [← h.innerVariation_eq_zero ξ hξ, innerVariation, innerVariation]
    refine integral_congr_ae ?_
    have hΩ : ∀ᵐ y, y ∈ Ω → χ y = posIndicator u y :=
      (ae_restrict_iff' h.isOpen.measurableSet).1 hχ
    filter_upwards [hΩ] with y hy
    by_cases hyΩ : y ∈ Ω
    · rw [hy hyΩ]
    · have hyξ : y ∉ tsupport ξ := fun h' => hyΩ (hξ.2.2 h')
      simp [divergence_eq_zero_of_notMem_tsupport hyξ, fderiv_of_notMem_tsupport (𝕜 := ℝ) hyξ]

/-- If `u ≡ 0` on `Ω` and `(u, χ)` is a variational solution, then so is `(u, χ_{u>0})`: the
integrand of the domain variation of `(0, 0)` vanishes. -/
theorem posIndicator_of_eq_zero {Ω : Set (Rn n)} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution Ω C u χ) (hu : ∀ x ∈ Ω, u x = 0) :
    IsVariationalSolution Ω C u (posIndicator u) :=
  h.posIndicator_of_innerVariation fun ξ hξ => by
    rw [innerVariation]
    refine integral_eq_zero_of_ae (.of_forall fun y => ?_)
    by_cases hyΩ : y ∈ Ω
    · have hev : u =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
        Filter.mem_of_superset (h.isOpen.mem_nhds hyΩ) fun z hz => hu z hz
      have hg : gradient u y = 0 := by simp [gradient, hev.fderiv_eq]
      simp [hg, posIndicator_of_nonpos (hu y hyΩ).le]
    · have hyξ : y ∉ tsupport ξ := fun h' => hyΩ (hξ.2.2 h')
      simp [divergence_eq_zero_of_notMem_tsupport hyξ, fderiv_of_notMem_tsupport (𝕜 := ℝ) hyξ]

/-- **Compactness of variational solutions on a fixed domain** (first paragraph of the proof of
Theorem 9.3). Let `(u_k, χ_k)` be variational solutions on the open
set `U` with a common constant `C_V`, and `u_k → v` locally uniformly on `U`. Then
`∇u_k → ∇v` in `L²_loc(U)`, and along a subsequence `χ_k → χ₀` in `L¹_loc(U)` and a.e. on `U`,
where `(v, χ₀)` is a variational solution on `U` with constant `C_V`. -/
theorem exists_subseq_limit {u χ : ℕ → Rn n → ℝ} {v : Rn n → ℝ}
    (h : ∀ k, IsVariationalSolution U C (u k) (χ k))
    (hconv : TendstoLocallyUniformlyOn u v atTop U) :
    (∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun k => ∫ y in K, ‖gradient (u k) y - gradient v y‖ ^ 2) atTop (𝓝 0)) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : Rn n → ℝ, IsVariationalSolution U C v χ₀ ∧
      (∀ K, IsCompact K → K ⊆ U →
        Tendsto (fun k => ∫ y in K, |χ (φ k) y - χ₀ y|) atTop (𝓝 0)) ∧
      ∀ᵐ y ∂(volume.restrict U), Tendsto (fun k => χ (φ k) y) atTop (𝓝 (χ₀ y)) := by
  have hU : IsOpen U := (h 0).isOpen
  have hH : ∀ k, IsLipHarmonicPos U (u k) := fun k => (h k).isLipHarmonicPos
  have hL : ∀ k x r, ball x r ⊆ U → LipschitzOnWith C (u k) (ball x r) :=
    fun k => (h k).lipschitzOnWith
  have hvH : IsLipHarmonicPos U v := IsLipHarmonicPos.of_tendstoLocallyUniformlyOn hH hL hconv
  have hvL : ∀ x r, ball x r ⊆ U → LipschitzOnWith C v (ball x r) :=
    fun _ _ hr => lipschitzOnWith_of_tendstoLocallyUniformlyOn hL hconv hr
  have hvg : ∀ y ∈ U, ‖gradient v y‖ ≤ C := fun y hy =>
    norm_gradient_le_of_lipschitzOnWith_ball hU hvL hy
  -- (1) strong `L²_loc` convergence of the gradients (proof of Proposition 3.5)
  have hgrad : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun k => ∫ y in K, ‖gradient (u k) y - gradient v y‖ ^ 2) atTop (𝓝 0) :=
    fun K hK hKU => tendsto_setIntegral_norm_gradient_sub_sq hH hL hconv hK hKU
  refine ⟨hgrad, ?_⟩
  -- (2) BV compactness of `χ_k` (Lemma 3.3 and BV compactness)
  set f : ℕ → Rn n → ℝ := fun k => U.indicator (χ k) with hfdef
  have hfm : ∀ k, Measurable (f k) := fun k => (h k).measurable_chi
  have hf01 : ∀ k, ∀ y ∈ U, f k y = 0 ∨ f k y = 1 := fun k y hy => by
    simp only [hfdef, indicator_of_mem hy]
    exact (h k).chi_mem y hy
  have hfb : ∀ k, ∀ y ∈ U, |f k y| ≤ 1 := fun k y hy => by
    rcases hf01 k y hy with h0 | h0 <;> simp [h0]
  have hfχ : ∀ k (ξ : Rn n → Rn n), tsupport ξ ⊆ U →
      ∫ y, f k y * divergence ξ y = ∫ y, χ k y * divergence ξ y := by
    intro k ξ hξ
    congr 1
    funext y
    by_cases hy : y ∈ U
    · simp only [hfdef, indicator_of_mem hy]
    · simp only [hfdef, indicator_of_notMem hy,
        divergence_eq_zero_of_notMem_tsupport fun h' => hy (hξ h'), mul_zero]
  have hTV : ∀ K, IsCompact K → K ⊆ U → ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ ∃ P : ℝ, ∀ k,
      ∀ ψ : Rn n → Rn n, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
        (∀ y, ‖ψ y‖ ≤ 1) → ∫ y, f k y * divergence ψ y ≤ P := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, P, hP⟩ :=
      exists_abs_integral_chi_mul_divergence_le (C := C) hU hK hKU
    refine ⟨W, hWo, hKW, hWU, P, fun k ψ hψ hψc hψW hψ1 => ?_⟩
    have hψL : IsLipTestField W ψ :=
      ⟨ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero, hψc, hψW⟩
    rw [hfχ k ψ (hψW.trans hWU)]
    exact (le_abs_self _).trans (hP _ _ (h k) ψ hψL hψ1)
  obtain ⟨φ, hφ, f₀, hf₀m, hf₀L, hf₀ae⟩ :=
    Registry.exists_subseq_tendsto_of_integral_mul_divergence_le hU f hfm hfb hTV
  -- `f₀ ∈ {0, 1}` a.e. on `U`; the `{0, 1}`-valued representative `χ₀`
  have h01 : ∀ᵐ y ∂(volume.restrict U), f₀ y = 0 ∨ f₀ y = 1 := by
    filter_upwards [hf₀ae, ae_restrict_mem hU.measurableSet] with y hy hyU
    have hcl01 : IsClosed ({0, 1} : Set ℝ) := (Set.toFinite _).isClosed
    exact hcl01.mem_of_tendsto hy (.of_forall fun k => hf01 (φ k) y hyU)
  set χ₀ : Rn n → ℝ := fun y => if f₀ y = 1 then 1 else 0 with hχ₀def
  have hχ₀m : Measurable χ₀ :=
    Measurable.ite (measurableSet_eq_fun hf₀m measurable_const) measurable_const measurable_const
  have hχ₀01 : ∀ y, χ₀ y = 0 ∨ χ₀ y = 1 := fun y => by
    by_cases hy : f₀ y = 1 <;> simp [χ₀, hy]
  have hχ₀b : ∀ y, |χ₀ y| ≤ 1 := fun y => by
    rcases hχ₀01 y with h0 | h0 <;> simp [h0]
  have hfχ₀ : ∀ᵐ y ∂(volume.restrict U), f₀ y = χ₀ y := by
    filter_upwards [h01] with y hy
    rcases hy with h0 | h1
    · simp [χ₀, h0]
    · simp [χ₀, h1]
  -- the convergence statements for `χ (φ k)`
  have hχae : ∀ᵐ y ∂(volume.restrict U), Tendsto (fun k => χ (φ k) y) atTop (𝓝 (χ₀ y)) := by
    filter_upwards [hf₀ae, hfχ₀, ae_restrict_mem hU.measurableSet] with y hy hy' hyU
    rw [← hy']
    refine hy.congr fun k => ?_
    simp only [hfdef, indicator_of_mem hyU]
  have hχL : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun k => ∫ y in K, |χ (φ k) y - χ₀ y|) atTop (𝓝 0) := by
    intro K hK hKU
    refine (hf₀L K hK hKU).congr fun k => ?_
    refine setIntegral_congr_ae hK.measurableSet ?_
    filter_upwards [(ae_restrict_iff' hU.measurableSet).1 hfχ₀] with y hy hyK
    rw [hy (hKU hyK)]
    simp only [hfdef, indicator_of_mem (hKU hyK)]
  -- (3) the limit is a variational solution
  have hlimχ : ∀ ξ, IsLipTestField U ξ → Tendsto (fun k => ∫ y, χ (φ k) y * divergence ξ y)
      atTop (𝓝 (∫ y, χ₀ y * divergence ξ y)) := by
    intro ξ hξ
    obtain ⟨⟨D, hD⟩, hξc, hξU⟩ := hξ
    refine tendsto_integral_of_dominated_convergence
      (fun y => (tsupport ξ).indicator (fun _ => (n : ℝ) * D) y)
      (fun k => ?_)
      ((integrableOn_const hξc.isCompact.measure_lt_top.ne).integrable_indicator
        (isClosed_tsupport ξ).measurableSet) (fun k => .of_forall fun y => ?_) ?_
    · refine (((hfm (φ k)).mul (Kernel.measurable_divergence ξ)).aestronglyMeasurable).congr
        (.of_forall fun y => ?_)
      by_cases hy : y ∈ U
      · simp only [hfdef, indicator_of_mem hy]
      · simp only [hfdef, indicator_of_notMem hy,
          divergence_eq_zero_of_notMem_tsupport fun h' => hy (hξU h'), mul_zero]
    · dsimp only
      by_cases hy : y ∈ tsupport ξ
      · rw [indicator_of_mem hy, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |χ (φ k) y| * |divergence ξ y| ≤ 1 * ((n : ℝ) * D) :=
              mul_le_mul ((h (φ k)).abs_chi_le_one (hξU hy)) (Kernel.abs_divergence_le hD y)
                (abs_nonneg _) zero_le_one
          _ = (n : ℝ) * D := one_mul _
      · rw [indicator_of_notMem hy, divergence_eq_zero_of_notMem_tsupport hy, mul_zero,
          norm_zero]
    · filter_upwards [(ae_restrict_iff' hU.measurableSet).1 hχae] with y hy
      by_cases hyU : y ∈ U
      · exact (hy hyU).mul_const _
      · have : y ∉ tsupport ξ := fun h' => hyU (hξU h')
        simp [divergence_eq_zero_of_notMem_tsupport this]
  have hlimG : ∀ ξ, IsLipTestField U ξ → Tendsto (fun k => ∫ y, gradVariation (u (φ k)) ξ y)
      atTop (𝓝 (∫ y, gradVariation v ξ y)) := by
    intro ξ hξ
    obtain ⟨⟨D, hD⟩, hξc, hξU⟩ := hξ
    have hK : IsCompact (tsupport ξ) := hξc.isCompact
    have hmem : ∀ w : Rn n → ℝ, (∀ y ∈ U, ‖gradient w y‖ ≤ C) →
        MemLp (gradient w) 2 (volume.restrict (tsupport ξ)) := fun w hw => by
      haveI : IsFiniteMeasure (volume.restrict (tsupport ξ)) :=
        isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
      exact MemLp.of_bound (measurable_gradient w).aestronglyMeasurable C
        ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => hw y (hξU hy)))
    have := tendsto_integral_gradVariation hD subset_rfl
      (fun k => hmem _ fun y hy => (h (φ k)).norm_gradient_le hy) (hmem v hvg)
      ((hgrad _ hK hξU).comp hφ.tendsto_atTop)
    refine this.congr' (.of_forall fun k => rfl) |>.trans (le_of_eq ?_)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport ξ)
      fun y hy => gradVariation_eq_zero_of_notMem_tsupport hy]
    rfl
  have hIV : ∀ ξ, IsLipTestField U ξ → innerVariation v χ₀ ξ = 0 := by
    intro ξ hξ
    have e1 : ∫ y, χ₀ y * divergence ξ y = -∫ y, gradVariation v ξ y :=
      tendsto_nhds_unique (hlimχ ξ hξ) (((hlimG ξ hξ).neg).congr fun k =>
        ((h (φ k)).integral_chi_mul_divergence_eq hξ).symm)
    have hJ := integrable_gradVariation hξ hvg
    obtain ⟨⟨D, hD⟩, hξc, hξU⟩ := hξ
    have hχint : Integrable fun y => χ₀ y * divergence ξ y :=
      integrable_of_bound_of_isCompact (K := tsupport ξ) hξc
        (hχ₀m.mul (measurable_divergence ξ)).aestronglyMeasurable (M := 1 * (n * D))
        (fun y _ => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hχ₀b y) (abs_divergence_le hD y) (abs_nonneg _) zero_le_one)
        (fun y hy => by rw [divergence_eq_zero_of_notMem_tsupport hy, mul_zero])
    have e2 : (fun y => (‖gradient v y‖ ^ 2 + χ₀ y) * divergence ξ y -
        2 * ⟪gradient v y, fderiv ℝ ξ y (gradient v y)⟫) =
        fun y => gradVariation v ξ y + χ₀ y * divergence ξ y := by
      funext y; simp only [gradVariation]; ring
    rw [innerVariation, e2, integral_add hJ hχint, e1]
    ring
  refine ⟨φ, hφ, χ₀, ?_, hχL, hχae⟩
  exact
    { isOpen := hU
      nonneg := hvH.nonneg
      continuousOn := hvH.continuousOn
      contDiffOn := hvH.contDiffOn
      lipschitzOnWith := hvL
      measurable_chi := hχ₀m.indicator hU.measurableSet
      chi_mem := fun y _ => hχ₀01 y
      posIndicator_le_chi := by
        have hall : ∀ᵐ y ∂(volume.restrict U), ∀ k, posIndicator (u k) y ≤ χ k y :=
          ae_all_iff.2 fun k => (h k).posIndicator_le_chi
        filter_upwards [hχae, hall, ae_restrict_mem hU.measurableSet] with y hy hle hyU
        by_cases hpos : 0 < v y
        · rw [posIndicator_of_pos hpos]
          have hev : ∀ᶠ k in atTop, χ (φ k) y = 1 := by
            filter_upwards [(hφ.tendsto_atTop).eventually
              ((hconv.tendsto_at hyU).eventually (lt_mem_nhds hpos))] with k hk
            have h1 := hle (φ k)
            rw [posIndicator_of_pos hk] at h1
            rcases (h (φ k)).chi_mem y hyU with h0 | h0
            · rw [h0] at h1; norm_num at h1
            · exact h0
          exact (tendsto_nhds_unique hy (tendsto_const_nhds.congr' (hev.mono fun k hk =>
            hk.symm))).ge
        · rw [posIndicator_of_nonpos (not_lt.1 hpos)]
          rcases hχ₀01 y with h0 | h0 <;> simp [h0]
      innerVariation_eq_zero := hIV }

end IsVariationalSolution

end InnerVariational
