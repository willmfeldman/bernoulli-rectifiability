/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Smooth cut-offs and compactly supported integrands

Helpers on a finite-dimensional real normed space `V`, used for the local compactness criterion
in `LocalCompactness.lean`.

## Main results

* `exists_smooth_cutoff`: a `C^∞` cut-off `0 ≤ ζ ≤ 1`, `ζ = 1` on a compact `K`, compactly
  supported in an open `U ⊇ K`.
* `integrable_of_continuousOn_of_zero`: a function continuous on a compact `K` and vanishing off
  `K` is integrable.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

namespace InnerVariational.Vendor.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A smooth cut-off `0 ≤ ζ ≤ 1`, `ζ = 1` on a compact `K`, with compact support in an open `U`
(smooth Urysohn lemma, `exists_contMDiffMap_one_nhds_of_subset_interior`). -/
theorem exists_smooth_cutoff {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ζ : V → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ U ∧
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ ∀ x ∈ K, ζ x = 1 := by
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, V)) (n := ⊤) hK.isClosed hKK'
  have hts : tsupport f ⊆ K' :=
    closure_minimal (fun p hp ↦ by_contra fun h ↦ (Function.mem_support.1 hp) (hf0 p h))
      hK'.isClosed
  refine ⟨f, f.contMDiff.contDiff, IsCompact.of_isClosed_subset hK' (isClosed_tsupport _) hts,
    hts.trans hK'U, fun p ↦ hf01 p, fun p hp ↦ hf1.self_of_nhdsSet p hp⟩

/-- A function continuous on a compact set `K` and vanishing off `K` is integrable. -/
theorem integrable_of_continuousOn_of_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) {g : X → ℝ} (hg : ContinuousOn g K)
    (h0 : ∀ x ∉ K, g x = 0) : Integrable g μ := by
  refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1
    (hg.integrableOn_compact hK)
  by_contra h
  exact hx (h0 x h)

end InnerVariational.Vendor.Analysis
