/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weak sequential compactness in `L²`

A bounded sequence in `L²(μ; E)` has a weakly convergent subsequence (the Hilbert-space case of
Brezis, Theorem 3.18), with no extra hypotheses on `μ`. The statement
`Registry.exists_weakly_convergent_subseq` is this theorem.

## Proof

Lift the sequence to `f k ∈ Lp E 2 μ` and let `K` be the closure of the span of `{f k}`. `K` is a
complete, separable Hilbert space. The functionals `⟪f k, ·⟫` on `K` are bounded by `√C`, so
sequential Banach–Alaoglu (`WeakDual.isSeqCompact_closedBall`) gives a weak-* convergent
subsequence. Its limit is `⟪G, ·⟫` for some `G ∈ K` (Riesz, `InnerProductSpace.toDual`). A test
function `h ∈ L²` enters only through its orthogonal projection onto `K`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 3.18.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

/-- **Weak sequential compactness of bounded sets in `L²`** (Brezis, Theorem 3.18).
A sequence bounded in `L²(μ; E)`, with `E` a finite-dimensional real inner product space, has a
subsequence converging weakly in `L²(μ; E)`. The statement is the one of
`Registry.exists_weakly_convergent_subseq`. -/
theorem exists_weakly_convergent_subseq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g : ℕ → α → E) (C : ℝ) (hg : ∀ k, MemLp (g k) 2 μ) (hbd : ∀ k, ∫ x, ‖g k x‖ ^ 2 ∂μ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : α → E, MemLp G 2 μ ∧
      ∀ h : α → E, MemLp h 2 μ →
        Tendsto (fun k => ∫ x, ⟪g (φ k) x, h x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪G x, h x⟫ ∂μ)) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- `∫ ⟪f, g⟫` is the `L²` inner product.
  have hinner : ∀ {f₁ f₂ : α → E} (h₁ : MemLp f₁ 2 μ) (h₂ : MemLp f₂ 2 μ),
      ∫ x, ⟪f₁ x, f₂ x⟫ ∂μ = ⟪h₁.toLp f₁, h₂.toLp f₂⟫ := by
    intro f₁ f₂ h₁ h₂
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [h₁.coeFn_toLp, h₂.coeFn_toLp] with x e₁ e₂
    rw [e₁, e₂]
  set f : ℕ → Lp E 2 μ := fun k => (hg k).toLp (g k) with hf_def
  set K : Submodule ℝ (Lp E 2 μ) := (Submodule.span ℝ (range f)).topologicalClosure with hK
  haveI : CompleteSpace K :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  haveI : TopologicalSpace.SeparableSpace K := by
    have hsep : TopologicalSpace.IsSeparable (K : Set (Lp E 2 μ)) := by
      rw [hK, Submodule.topologicalClosure_coe]
      exact ((countable_range f).isSeparable.span (R := ℝ)).closure
    exact hsep.separableSpace
  have hfK : ∀ k, f k ∈ K := fun k =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, rfl⟩)
  set x : ℕ → K := fun k => ⟨f k, hfK k⟩ with hx_def
  -- The bound `‖f k‖ ≤ √C`.
  have hnorm : ∀ k, ‖x k‖ ≤ √C := by
    intro k
    have h1 : ‖x k‖ ^ 2 = ∫ y, ‖g k y‖ ^ 2 ∂μ := by
      have : ‖x k‖ = ‖f k‖ := rfl
      rw [this, ← real_inner_self_eq_norm_sq, ← hinner (hg k) (hg k)]
      simp only [real_inner_self_eq_norm_sq]
    exact Real.le_sqrt_of_sq_le (h1 ▸ hbd k)
  set ℓ : ℕ → WeakDual ℝ K := fun k => StrongDual.toWeakDual (innerSL ℝ (x k)) with hℓ_def
  have hmem : ∀ k, ℓ k ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ K) √C := by
    intro k
    have h1 : ‖(innerSL ℝ (x k) : StrongDual ℝ K)‖ ≤ √C :=
      (innerSL_apply_norm ℝ (x k)).le.trans (hnorm k)
    exact (mem_closedBall_zero_iff (E := StrongDual ℝ K)).2 h1
  obtain ⟨ℓlim, -, φ, hφ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := K) 0 √C hmem
  set GK : K := (InnerProductSpace.toDual ℝ K).symm (WeakDual.toStrongDual ℓlim) with hGK
  refine ⟨φ, hφ, ((GK : Lp E 2 μ) : α → E), Lp.memLp _, fun h hh => ?_⟩
  set P : K := K.orthogonalProjection (hh.toLp h)
  -- Evaluation at `P` is weak-* continuous.
  have hev : Tendsto (fun k => ℓ (φ k) P) atTop (𝓝 (ℓlim P)) :=
    ((WeakDual.eval_continuous P).tendsto ℓlim).comp hlim
  have hk : ∀ k, ∫ y, ⟪g (φ k) y, h y⟫ ∂μ = ℓ (φ k) P := by
    intro k
    rw [hinner (hg (φ k)) hh]
    change _ = ⟪x (φ k), P⟫
    rw [K.inner_orthogonalProjection_eq_of_mem_left]
  have hGint : ∫ y, ⟪((GK : Lp E 2 μ) : α → E) y, h y⟫ ∂μ = ℓlim P := by
    have e : ∫ y, ⟪((GK : Lp E 2 μ) : α → E) y, h y⟫ ∂μ = ⟪(GK : Lp E 2 μ), hh.toLp h⟫ := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hh.coeFn_toLp] with y e₁
      rw [e₁]
    rw [e, ← K.inner_orthogonalProjection_eq_of_mem_left, hGK, InnerProductSpace.toDual_symm_apply]
    rfl
  rw [hGint]
  simpa only [hk] using hev

end InnerVariational
