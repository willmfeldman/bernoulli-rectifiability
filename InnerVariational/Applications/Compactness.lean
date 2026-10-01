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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.EMetricSpace.Paracompact
import InnerVariational.Registry.BV
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Applications.CompactnessQ

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

Both results are the case `Q ≡ 1` of their versions for Lipschitz coefficients
(`IsVariationalSolutionQ.exists_abs_integral_chi_mul_divergence_le`,
`IsVariationalSolutionQ.exists_subseq_limit`, `Applications/CompactnessQ.lean`). The argument:

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
  obtain ⟨W, hWo, hKW, hWU, P, hP⟩ :=
    IsVariationalSolutionQ.exists_abs_integral_chi_mul_divergence_le (C := C) hU hK hKU 1
  exact ⟨W, hWo, hKW, hWU, P, fun u χ h ψ hψ hψ1 =>
    hP _ u χ 0 1 (QBounds.one U) h.toQ ψ hψ hψ1⟩

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
  obtain ⟨hgrad, φ, hφ, χ₀, hsol, hL, hae⟩ :=
    IsVariationalSolutionQ.exists_subseq_limit (Q := fun _ _ => 1) (L := fun _ => 0) (c := 1)
      (C' := 1) (q := 1) (fun _ => QBounds.one U) (by simp) (fun _ _ => tendsto_const_nhds)
      (fun k => (h k).toQ) hconv
  exact ⟨hgrad, φ, hφ, χ₀, isVariationalSolutionQ_one_iff.1 hsol, hL, hae⟩

end IsVariationalSolution

end InnerVariational
