/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import InnerVariational.Vendor.Analysis.BVCompactness
import InnerVariational.Vendor.Analysis.LocalCompactness
public import GMTFoundations.Defs.Calculus

/-!
# Background: BV compactness

A classical result used by the proof, proved here: compactness in `L¹_loc` of sequences with
locally bounded total variation (Evans–Gariepy, §5.2; Ambrosio–Fusco–Pallara, Thm 3.23). The
total variation is written in duality form:
`|Df|(W) = sup {∫ f div ψ : ψ ∈ C¹_c(W; ℝⁿ), |ψ| ≤ 1}`.

## Faithfulness

The textbook statement assumes `sup_k ‖f_k‖_{BV(W)} < ∞` on each `W ⋐ V`. Here `|f_k| ≤ 1` on `V`
bounds `‖f_k‖_{L¹(W)}` on bounded `W` (a neighbourhood of a compact set can be shrunk to a bounded
one), and `hTV` bounds `|Df_k|(W)`. The integrand `f_k · div ψ` is integrable (bounded measurable
times a continuous compactly supported function), so Lean's junk value `∫ = 0` for non-integrable
functions never weakens `hTV`.

## Proof

The `L¹_loc` subsequence comes from the BV compactness theorem `exists_tendstoLpLoc_subseq_of_TV` of
the `Vendor` layer (Fréchet–Kolmogorov via ball averages, applied to cut-offs `ζ f_k`). For the a.e.
convergence we pass to a further subsequence with `‖f_{k_j} - f₀‖_{L¹(K_j)} ≤ 2^{-j}` along the
compact exhaustion `K_j = exhaust V j`. On each `K_m` the tail sum `∑_j |f_{k_{j+m}} - f₀|` then has
finite integral, hence is finite a.e. (Borel–Cantelli).

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
  CRC Press, 2015.
* L. Ambrosio, N. Fusco and D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Oxford Univ. Press, 2000.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

@[expose] public noncomputable section

namespace InnerVariational.Registry

variable {n : ℕ}

/-- **BV compactness in `L¹_loc`.** Let `V ⊆ ℝⁿ` be open and let `f_k : ℝⁿ → ℝ` be
measurable with `|f_k| ≤ 1` on `V`. Suppose that every compact `K ⊆ V` has an open neighbourhood
`W ⊆ V` with `∫ f_k div ψ ≤ P` for all `k` and all `ψ ∈ C¹_c(W; ℝⁿ)` with `|ψ| ≤ 1`. Then a
subsequence converges in `L¹_loc(V)` and a.e. on `V` to a measurable `f₀`. -/
theorem exists_subseq_tendsto_of_integral_mul_divergence_le {V : Set (Rn n)} (hV : IsOpen V)
    (f : ℕ → Rn n → ℝ) (hf : ∀ k, Measurable (f k)) (hb : ∀ k, ∀ y ∈ V, |f k y| ≤ 1)
    (hTV : ∀ K, IsCompact K → K ⊆ V → ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧ ∃ P : ℝ, ∀ k,
      ∀ ψ : Rn n → Rn n, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
        (∀ y, ‖ψ y‖ ≤ 1) → ∫ y, f k y * divergence ψ y ≤ P) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : Rn n → ℝ, Measurable f₀ ∧
      (∀ K, IsCompact K → K ⊆ V →
        Tendsto (fun k => ∫ y in K, |f (φ k) y - f₀ y|) atTop (𝓝 0)) ∧
      ∀ᵐ y ∂(volume.restrict V), Tendsto (fun k => f (φ k) y) atTop (𝓝 (f₀ y)) := by
  classical
  -- the duality bound on fields supported in a compact `K ⊆ V`
  have hTVK : ∀ K, IsCompact K → K ⊆ V → ∃ P : ℝ, ∀ k, ∀ ψ : Rn n → Rn n, ContDiff ℝ 1 ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ K → (∀ y, ‖ψ y‖ ≤ 1) →
        ∫ y, f k y * divergence ψ y ≤ P := by
    intro K hK hKV
    obtain ⟨W, -, hKW, -, P, hP⟩ := hTV K hK hKV
    exact ⟨P, fun k ψ hψ hψc hψK hψ1 ↦ hP k ψ hψ hψc (hψK.trans hKW) hψ1⟩
  -- `L¹_loc` convergence along a subsequence
  obtain ⟨φ, hφ, f₀, hf₀, hL⟩ := Vendor.Analysis.exists_tendstoLpLoc_subseq_of_TV hV f
    (fun k ↦ (hf k).aestronglyMeasurable) ⟨1, hb⟩ hTVK
  -- a fast subsequence along the compact exhaustion `K_j` of `V`
  set Kx := Vendor.Analysis.exhaust V
  have hev : ∀ j, ∀ᶠ k in atTop,
      eLpNorm (f (φ k) - f₀) 1 (volume.restrict (Kx j)) ≤ (1 / 2 : ℝ≥0∞) ^ j := fun j ↦
    (hL _ (Vendor.Analysis.exhaust_subset V j) (Vendor.Analysis.isCompact_exhaust V j)).eventually
      (ge_mem_nhds (ENNReal.pow_pos (by norm_num) j))
  obtain ⟨ψ, hψ, hψle⟩ := extraction_forall_of_eventually hev
  refine ⟨φ ∘ ψ, hφ.comp hψ, f₀, hf₀, fun K hK hKV ↦ ?_, ?_⟩
  · -- `L¹(K)` convergence: rewrite the `L¹` seminorm as an integral
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      ((hL K hKV hK).comp hψ.tendsto_atTop)
    rw [ENNReal.toReal_zero] at h1
    refine h1.congr fun k ↦ ?_
    have e : ∫ y in K, |f (φ (ψ k)) y - f₀ y| = ∫ y in K, ‖(f (φ (ψ k)) - f₀) y‖ := by
      simp only [Pi.sub_apply, Real.norm_eq_abs]
    simp only [Function.comp_apply]
    rw [e, integral_norm_eq_lintegral_enorm (μ := volume.restrict K) (f := f (φ (ψ k)) - f₀)
      ((hf _).sub hf₀).aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm ((hf _).sub hf₀).aestronglyMeasurable]
  · -- a.e. convergence on each `K_m` by summability of the `L¹(K_m)` norms
    have hVK : V = ⋃ j, Kx j := by
      refine Subset.antisymm (fun y hy ↦ ?_) (iUnion_subset (Vendor.Analysis.exhaust_subset V))
      obtain ⟨j, hj⟩ := Vendor.Analysis.exists_subset_exhaust hV isCompact_singleton
        (singleton_subset_iff.2 hy)
      exact mem_iUnion.2 ⟨j, hj rfl⟩
    rw [hVK, ae_restrict_iUnion_iff]
    intro m
    set g : ℕ → Rn n → ℝ≥0∞ := fun j y ↦ ‖f (φ (ψ (j + m))) y - f₀ y‖ₑ with hg
    have hgm : ∀ j, Measurable (g j) := fun j ↦ ((hf _).sub hf₀).enorm
    have hgj : ∀ j, ∫⁻ y in Kx m, g j y ≤ (1 / 2 : ℝ≥0∞) ^ j := by
      intro j
      calc ∫⁻ y in Kx m, g j y
          = eLpNorm (f (φ (ψ (j + m))) - f₀) 1 (volume.restrict (Kx m)) := by
            rw [eLpNorm_one_eq_lintegral_enorm ((hf _).sub hf₀).aestronglyMeasurable]; rfl
        _ ≤ eLpNorm (f (φ (ψ (j + m))) - f₀) 1 (volume.restrict (Kx (j + m))) :=
            eLpNorm_mono_measure _
              (Measure.restrict_mono (Vendor.Analysis.exhaust_mono V (Nat.le_add_left m j)) le_rfl)
        _ ≤ (1 / 2 : ℝ≥0∞) ^ (j + m) := hψle (j + m)
        _ ≤ (1 / 2 : ℝ≥0∞) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (Nat.le_add_right j m)
    have hsum : ∫⁻ y in Kx m, ∑' j, g j y ≠ ⊤ := by
      rw [lintegral_tsum fun j ↦ (hgm j).aemeasurable]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hgj)
      rw [ENNReal.tsum_geometric]
      exact ENNReal.inv_ne_top.2 (by norm_num)
    filter_upwards [ae_lt_top' (Measurable.aemeasurable (Measurable.tsum hgm)) hsum]
      with y hy
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hy.ne)
    rw [ENNReal.toReal_zero] at h1
    have h2 : Tendsto (fun j ↦ f (φ (ψ (j + m))) y) atTop (𝓝 (f₀ y)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 (h1.congr fun j ↦ ?_)
      simp only [Function.comp_apply, hg, toReal_enorm]
    exact (tendsto_add_atTop_iff_nat m).1 h2

end InnerVariational.Registry
