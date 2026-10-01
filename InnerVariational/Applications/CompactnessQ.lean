/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import InnerVariational.Kernel.VariationalQ
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Registry.BV
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Blowup.DomainVariation
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic

/-!
# Compactness of variational solutions with Lipschitz coefficients

The first paragraph of the proof of Theorem 9.3 of Kriventsov–Weiss (full reference below), for
variational solutions with coefficients `Q_k` whose Lipschitz constants tend to zero. Let
`(u_k, χ_k)` be variational solutions on an open `U` for coefficients `Q_k`, with a common
gradient constant `C_V`, with `QBounds U Q_k L_k c C'` for common bounds `c, C'`, `L_k → 0`, and
`Q_k → q` pointwise on `U`. If `u_k → v` locally uniformly on `U`, then:

* `∇u_k → ∇v` in `L²_loc(U)` (along the full sequence);
* along a subsequence, `χ_k → χ₀` in `L¹_loc(U)` and a.e. on `U`, with `χ₀ ∈ {0, 1}`;
* `(v, χ₀)` is a variational solution on `U` for the constant coefficient `q`, with constant
  `C_V`.

This is `IsVariationalSolutionQ.exists_subseq_limit`. The case `Q_k ≡ 1` is the compactness of
variational solutions (`IsVariationalSolution.exists_subseq_limit`). The typical application is
to blow-ups `Q_k(y) = Q(x + r_k y)`, whose Lipschitz constants are `r_k L → 0`.

## Proof

* Gradients: the strong convergence of gradients from the proof of Proposition 3.5
  (`tendsto_setIntegral_norm_gradient_sub_sq`), which uses only the Lipschitz bound, harmonicity on
  `{u_k > 0}` (Proposition 3.2) and interior estimates for harmonic functions.
* `χ_k`: Lemma 3.3 in the form of the key estimate `abs_integral_gradVariation_le`, applied to the
  test field `Q_k⁻² ψ` and one fixed Lipschitz cutoff, bounds `∫ χ_k div ψ` uniformly in `k` on a
  neighbourhood of each compact set (`exists_abs_integral_chi_mul_divergence_le`); the bound
  depends on `c` but not on `L_k`. BV compactness then gives a subsequence converging in
  `L¹_loc` and a.e.
* The domain variation passes to the limit: its quadratic part by strong `L²` convergence of the
  gradients, its `χ` part `χ_k (Q_k² div ξ + ∇(Q_k²) · ξ)` by dominated convergence, since
  `Q_k → q` and `|∇(Q_k²)| ≤ 2 C' L_k → 0`.

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

namespace IsVariationalSolutionQ

open Kernel

variable {U : Set (Rn n)} {C : ℝ≥0}

/-- **Uniform local BV bound for `χ`** (Lemma 3.3, uniform version). Every compact `K ⊆ U` has
an open neighbourhood `W ⊆ U` and a bound `P` such that `|∫ χ div ψ| ≤ P` for every coefficient
`Q` with `QBounds U Q L c C'`, every variational solution `(u, χ)` on `U` for `Q` with constant
`C`, and every `ψ ∈ C^{0,1}_c(W; ℝⁿ)` with `|ψ| ≤ 1`. The bound depends only on `C`, `c`, `K`
and `U`; not on `L` or `C'`. -/
theorem exists_abs_integral_chi_mul_divergence_le (hU : IsOpen U) {K : Set (Rn n)}
    (hK : IsCompact K) (hKU : K ⊆ U) (c : ℝ) :
    ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ ∃ P : ℝ, ∀ (Q u χ : Rn n → ℝ) (L : ℝ≥0) (C' : ℝ),
      QBounds U Q L c C' → IsVariationalSolutionQ U C Q u χ →
      ∀ ψ : Rn n → Rn n, IsLipTestField W ψ → (∀ y, ‖ψ y‖ ≤ 1) →
        |∫ y, χ y * divergence ψ y| ≤ P := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening (δ / 2) K) := hK.cthickening
  have hK'U : cthickening (δ / 2) K ⊆ U :=
    (cthickening_mono (by linarith) K).trans hδU
  obtain ⟨η, ⟨Lη, hLη⟩, hηc, hηU, hη0, -, hη1⟩ := exists_lipschitz_cutoff hU hK' hK'U
  refine ⟨thickening (δ / 2) K, isOpen_thickening, self_subset_thickening (by linarith) K,
    (thickening_subset_cthickening _ _).trans hK'U,
    C * (c ^ 2)⁻¹ * ((C : ℝ) * Lη * volume.real (tsupport η)),
    fun Q u χ L C' hQ h ψ hψ hψ1 => ?_⟩
  have hc2 : 0 < c ^ 2 := pow_pos hQ.pos 2
  have hψU : IsLipTestField U ψ := hψ.mono ((thickening_subset_cthickening _ _).trans hK'U)
  have hξ := hQ.isLipTestField_inv_sq_smul hψU
  have hM : ∀ y, ‖(Q y ^ 2)⁻¹ • ψ y‖ ≤ (c ^ 2)⁻¹ := by
    intro y
    by_cases hy : y ∈ tsupport ψ
    · have hq := hQ.sq_le_sq (hψU.2.2 hy)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hc2.trans_le hq)), ← mul_one
        (c ^ 2)⁻¹]
      exact mul_le_mul (inv_anti₀ hc2 hq) (hψ1 y) (norm_nonneg _) (inv_nonneg.2 hc2.le)
    · rw [image_eq_zero_of_notMem_tsupport hy, smul_zero, norm_zero]
      positivity
  have hmain := h.abs_integral_gradVariation_le hQ hξ hM ⟨Lη, hLη⟩ hηc hηU hη0 (fun y hy =>
    hη1 y (thickening_subset_cthickening _ _ (hψ.2.2 (tsupport_smul_subset_right _ _ hy))))
  have e := h.integral_chi_mul_divergence_sq_smul_eq hQ hξ
  rw [hQ.sq_smul_inv_sq_smul hψU.2.2] at e
  rw [e, abs_neg]
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg C.2 (inv_nonneg.2 hc2.le))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport η) (fun y hy => by
      rw [gradient_eq_zero_of_notMem_tsupport hy, inner_zero_right, abs_zero])]
  refine (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const
    hηc.isCompact.measure_lt_top fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_abs, ← Real.norm_eq_abs]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (h.norm_gradient_le (hηU hy))
    (norm_gradient_le_of_lipschitz hLη y) (norm_nonneg _) C.2)

/-- **Compactness of variational solutions with Lipschitz coefficients** (first paragraph of the
proof of Theorem 9.3). Let `(u_k, χ_k)` be variational solutions on the open set `U` for
coefficients `Q_k`, with a common constant `C_V`, `QBounds U Q_k L_k c C'`, `L_k → 0` and
`Q_k → q` pointwise on `U`. If `u_k → v` locally uniformly on `U`, then `∇u_k → ∇v` in
`L²_loc(U)`, and along a subsequence `χ_k → χ₀` in `L¹_loc(U)` and a.e. on `U`, where `(v, χ₀)`
is a variational solution on `U` for the constant coefficient `q`, with constant `C_V`. -/
theorem exists_subseq_limit {Q u χ : ℕ → Rn n → ℝ} {L : ℕ → ℝ≥0} {c C' q : ℝ}
    {v : Rn n → ℝ} (hQ : ∀ k, QBounds U (Q k) (L k) c C')
    (hL : Tendsto (fun k => (L k : ℝ)) atTop (𝓝 0))
    (hq : ∀ y ∈ U, Tendsto (fun k => Q k y) atTop (𝓝 q))
    (h : ∀ k, IsVariationalSolutionQ U C (Q k) (u k) (χ k))
    (hconv : TendstoLocallyUniformlyOn u v atTop U) :
    (∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun k => ∫ y in K, ‖gradient (u k) y - gradient v y‖ ^ 2) atTop (𝓝 0)) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : Rn n → ℝ,
      IsVariationalSolutionQ U C (fun _ => q) v χ₀ ∧
      (∀ K, IsCompact K → K ⊆ U →
        Tendsto (fun k => ∫ y in K, |χ (φ k) y - χ₀ y|) atTop (𝓝 0)) ∧
      ∀ᵐ y ∂(volume.restrict U), Tendsto (fun k => χ (φ k) y) atTop (𝓝 (χ₀ y)) := by
  have hU : IsOpen U := (h 0).isOpen
  have hH : ∀ k, IsLipHarmonicPos U (u k) := fun k => (h k).isLipHarmonicPos (hQ k)
  have hLu : ∀ k x r, ball x r ⊆ U → LipschitzOnWith C (u k) (ball x r) :=
    fun k => (h k).lipschitzOnWith
  have hvH : IsLipHarmonicPos U v := IsLipHarmonicPos.of_tendstoLocallyUniformlyOn hH hLu hconv
  have hvL : ∀ x r, ball x r ⊆ U → LipschitzOnWith C v (ball x r) :=
    fun _ _ hr => lipschitzOnWith_of_tendstoLocallyUniformlyOn hLu hconv hr
  have hvg : ∀ y ∈ U, ‖gradient v y‖ ≤ C := fun y hy =>
    norm_gradient_le_of_lipschitzOnWith_ball hU hvL hy
  -- (1) strong `L²_loc` convergence of the gradients (proof of Proposition 3.5)
  have hgrad : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun k => ∫ y in K, ‖gradient (u k) y - gradient v y‖ ^ 2) atTop (𝓝 0) :=
    fun K hK hKU => tendsto_setIntegral_norm_gradient_sub_sq hH hLu hconv hK hKU
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
      exists_abs_integral_chi_mul_divergence_le (C := C) hU hK hKU c
    refine ⟨W, hWo, hKW, hWU, P, fun k ψ hψ hψc hψW hψ1 => ?_⟩
    have hψL : IsLipTestField W ψ :=
      ⟨ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero, hψc, hψW⟩
    rw [hfχ k ψ (hψW.trans hWU)]
    exact (le_abs_self _).trans (hP _ _ _ _ _ (hQ k) (h k) ψ hψL hψ1)
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
  -- (3) the limit is a variational solution for the constant coefficient `q`
  have hlimχ : ∀ ξ, IsLipTestField U ξ → Tendsto (fun k => ∫ y, χ (φ k) y *
      (Q (φ k) y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q (φ k) z ^ 2) y (ξ y)))
      atTop (𝓝 (∫ y, χ₀ y * (q ^ 2 * divergence ξ y))) := by
    intro ξ hξ
    obtain ⟨⟨D, hD⟩, hξc, hξU⟩ := hξ
    obtain ⟨M, hM⟩ := hD.continuous.bounded_above_of_compact_support hξc
    have hLφ : ∀ᶠ k in atTop, (L (φ k) : ℝ) ≤ 1 :=
      (hL.comp hφ.tendsto_atTop).eventually (ge_mem_nhds one_pos)
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => (tsupport ξ).indicator (fun _ => C' ^ 2 * (n * D) + 2 * C' * 1 * M) y)
      (.of_forall fun k => ((h (φ k)).integrable_chi_mul_sq_mul_divergence_add (hQ (φ k))
        ⟨⟨D, hD⟩, hξc, hξU⟩).aestronglyMeasurable) ?_
      ((integrableOn_const hξc.isCompact.measure_lt_top.ne).integrable_indicator
        (isClosed_tsupport ξ).measurableSet) ?_
    · filter_upwards [hLφ] with k hk
      refine .of_forall fun y => ?_
      by_cases hy : y ∈ tsupport ξ
      · have hyU := hξU hy
        have hC' := (hQ (φ k)).nonneg_of_mem hyU
        rw [indicator_of_mem hy, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |χ (φ k) y| * |Q (φ k) y ^ 2 * divergence ξ y +
              fderiv ℝ (fun z => Q (φ k) z ^ 2) y (ξ y)|
            ≤ 1 * (C' ^ 2 * (n * D) + 2 * C' * L (φ k) * M) :=
              mul_le_mul ((h (φ k)).abs_chi_le_one hyU)
                ((hQ (φ k)).abs_sq_mul_divergence_add_le hU hD hM hyU) (abs_nonneg _)
                zero_le_one
          _ ≤ C' ^ 2 * (n * D) + 2 * C' * 1 * M := by
              have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y)
              rw [one_mul]
              gcongr
      · rw [indicator_of_notMem hy, QBounds.sq_mul_divergence_add_eq_zero_of_notMem ξ hy,
          mul_zero, norm_zero]
    · filter_upwards [(ae_restrict_iff' hU.measurableSet).1 hχae] with y hy
      by_cases hyU : y ∈ U
      · have h1 : Tendsto (fun k => Q (φ k) y ^ 2 * divergence ξ y) atTop
            (𝓝 (q ^ 2 * divergence ξ y)) :=
          (((hq y hyU).comp hφ.tendsto_atTop).pow 2).mul_const _
        have h2 : Tendsto (fun k => fderiv ℝ (fun z => Q (φ k) z ^ 2) y (ξ y)) atTop (𝓝 0) := by
          refine squeeze_zero_norm (fun k => ?_) (by
            simpa using ((hL.comp hφ.tendsto_atTop).const_mul (2 * C')).mul_const ‖ξ y‖)
          rw [Real.norm_eq_abs]
          exact (hQ (φ k)).abs_fderiv_sq_apply_le hU hyU _
        have h3 := h1.add h2
        rw [add_zero] at h3
        exact (hy hyU).mul h3
      · have : y ∉ tsupport ξ := fun h' => hyU (hξU h')
        have e : ∀ k, χ (φ k) y * (Q (φ k) y ^ 2 * divergence ξ y +
            fderiv ℝ (fun z => Q (φ k) z ^ 2) y (ξ y)) = 0 := fun k => by
          rw [QBounds.sq_mul_divergence_add_eq_zero_of_notMem ξ this, mul_zero]
        change Tendsto (fun k => χ (φ k) y * (Q (φ k) y ^ 2 * divergence ξ y +
          fderiv ℝ (fun z => Q (φ k) z ^ 2) y (ξ y))) atTop
          (𝓝 (χ₀ y * (q ^ 2 * divergence ξ y)))
        rw [show (fun k => χ (φ k) y * (Q (φ k) y ^ 2 * divergence ξ y +
          fderiv ℝ (fun z => Q (φ k) z ^ 2) y (ξ y))) = fun _ => 0 from funext e,
          divergence_eq_zero_of_notMem_tsupport this, mul_zero, mul_zero]
        exact tendsto_const_nhds
  have hlimG : ∀ ξ, IsLipTestField U ξ → Tendsto (fun k => ∫ y, gradVariation (u (φ k)) ξ y)
      atTop (𝓝 (∫ y, gradVariation v ξ y)) := by
    intro ξ hξ
    obtain ⟨⟨D, hD⟩, hξc, hξU⟩ := hξ
    have hK : IsCompact (tsupport ξ) := hξc.isCompact
    have hmem : ∀ w : Rn n → ℝ, (∀ y ∈ U, ‖gradient w y‖ ≤ C) →
        MemLp (gradient w) 2 (volume.restrict (tsupport ξ)) := fun w hw => by
      have : IsFiniteMeasure (volume.restrict (tsupport ξ)) :=
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
  have hIV : ∀ ξ, IsLipTestField U ξ → innerVariationQ (fun _ => q) v χ₀ ξ = 0 := by
    intro ξ hξ
    have e1 : ∫ y, χ₀ y * (q ^ 2 * divergence ξ y) = -∫ y, gradVariation v ξ y :=
      tendsto_nhds_unique (hlimχ ξ hξ) (((hlimG ξ hξ).neg).congr fun k =>
        by rw [(h (φ k)).integral_gradVariation_eq_neg (hQ (φ k)) hξ, neg_neg])
    have hJ := integrable_gradVariation hξ hvg
    obtain ⟨⟨D, hD⟩, hξc, hξU⟩ := hξ
    have hχint : Integrable fun y => χ₀ y * (q ^ 2 * divergence ξ y) :=
      integrable_of_bound_of_isCompact (K := tsupport ξ) hξc
        (hχ₀m.mul (measurable_const.mul (measurable_divergence ξ))).aestronglyMeasurable
        (M := 1 * (q ^ 2 * (n * D)))
        (fun y _ => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg q)]
          exact mul_le_mul (hχ₀b y) (mul_le_mul_of_nonneg_left (abs_divergence_le hD y)
            (sq_nonneg q)) (by positivity) zero_le_one)
        (fun y hy => by rw [divergence_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero])
    have e2 : (fun y => (‖gradient v y‖ ^ 2 + q ^ 2 * χ₀ y) * divergence ξ y -
        2 * ⟪gradient v y, fderiv ℝ ξ y (gradient v y)⟫ +
        fderiv ℝ (fun _ : Rn n => q ^ 2) y (ξ y) * χ₀ y) =
        fun y => gradVariation v ξ y + χ₀ y * (q ^ 2 * divergence ξ y) := by
      funext y
      simp only [gradVariation, fderiv_fun_const, Pi.zero_apply, zero_apply,
        zero_mul, add_zero]
      ring
    rw [innerVariationQ, e2, integral_add hJ hχint, e1]
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
      innerVariationQ_eq_zero := hIV }

end IsVariationalSolutionQ

end InnerVariational
