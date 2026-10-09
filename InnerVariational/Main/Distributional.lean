/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Main.Covering
public import InnerVariational.Singular.Density
public import InnerVariational.Defs.LaplacianMeasure
public import InnerVariational.Singular.HeightLimit
public import InnerVariational.Singular.Chi
import InnerVariational.NaberValtorta.Hausdorff
import InnerVariational.Regular.Perimeter
import InnerVariational.Registry.GMT
import GMTFoundations.GMT.ApproxTangent
import InnerVariational.Monotonicity.HighestDensity
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution

/-!
# Theorem 8.7: rectifiability and local finiteness of `∂{u > 0}`

Theorem 8.7 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), first part. Let `(u, χ)`
be a variational solution on an open `Ω`. Then `S = Ω ∩ ∂{u > 0}` is countably
`ℋ^{n-1}`-rectifiable and has locally finite `ℋ^{n-1}` measure in `Ω`
(`rectifiable_and_locallyFinite_frontier_pos`). This is also Theorem 1.2 (ii).

## Proof

Write `E = Ω ∩ {χ = 1}`. Then `S ⊆ (Ω ∩ ∂ᵉE) ∪ Σ^H`:

* **Off `Σ^H`** (`frontier_pos_diff_sigmaH_subset_essentialBoundary`). On `Ω \ Σ^H`, which is open
  and has empty `Σ^H`, `∂{u > 0} ⊆ ∂ᵉ{χ = 1}` (proof of Lemma 8.2: the density
  `M_x(0+)/|B_1|` of `{χ = 1}` lies in `[1/2, 1)`). Densities are local, so `∂ᵉ` may be taken
  for `E`.
* **`∂ᵉE` is rectifiable and locally finite** (`isCountablyRectifiable_inter_essentialBoundary_chi`,
  `hausdorffN_inter_essentialBoundary_chi_lt_top`). On each ball `B_{3r/2}(x)` with
  `B̄_{2r}(x) ⊆ Ω`, `E` has a Gauss–Green pair of mass `≤ C r^{n-1}` (Lemma 3.3 and the BV
  structure theorem, `exists_isGaussGreenPair_chi`); Federer's theorem
  `|Dχ_E| = ℋ^{n-1}⌊∂ᵉE` identifies the pair's measure, and the De Giorgi–Federer structure
  theorem makes `∂ᵉE` rectifiable there (H. Federer, *Geometric Measure Theory*, Springer, 1969,
  4.5.6; L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*,
  rev. ed., CRC Press, 2015, Chapter 5; both proved in gmt-foundations,
  https://github.com/willmfeldman/gmt-foundations, v0.1.0). The covering lemmas of
  `Main/Covering.lean` globalize. The paper's proof of Theorem 8.7 instead uses the bound on
  `Δu(B_r(x))` and Corollary 8.4; the route through `∂ᵉ{χ = 1}` needs neither the Laplacian
  measure nor a Gauss–Green pair on all of `Ω`.
* **On `Σ^H`**: Theorem 7.2 (2) near each point (`Main/Covering.lean`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational.Main

variable {n : ℕ} {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-! ### The free boundary off `Σ^H` lies in the essential boundary of `{χ = 1}` -/

/-- `(Ω ∩ ∂{u > 0}) \ Σ^H ⊆ ∂ᵉ(Ω ∩ {χ = 1})` (proof of Lemma 8.2, applied on the open
set `Ω \ Σ^H`, whose `Σ^H` is empty). -/
theorem frontier_pos_diff_sigmaH_subset_essentialBoundary (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) :
    (Ω ∩ frontier {y | 0 < u y}) \ sigmaH Ω u χ ⊆ essentialBoundary (Ω ∩ {y | χ y = 1}) := by
  have : NeZero n := ⟨by omega⟩
  rintro x ⟨⟨hxΩ, hxf⟩, hxS⟩
  have hx' : x ∈ Ω \ sigmaH Ω u χ := ⟨hxΩ, hxS⟩
  have hU : Ω \ sigmaH Ω u χ ∈ 𝓝 x := h.isOpen_diff_sigmaH.mem_nhds hx'
  have hmem := h.diff_sigmaH.frontier_pos_inter_subset_essentialBoundary hn
    h.sigmaH_diff_sigmaH_eq_empty ⟨hx', hxf⟩
  have e : (Ω \ sigmaH Ω u χ) ∩ {y | χ y = 1} =
      (Ω \ sigmaH Ω u χ) ∩ (Ω ∩ {y | χ y = 1}) := by
    rw [← inter_assoc, inter_eq_left.2 sdiff_subset]
  rw [e] at hmem
  exact ⟨fun h0 => hmem.1 ((Singular.hasDensity_inter_iff hU).2 h0),
    fun h1 => hmem.2 ((Singular.hasDensity_inter_iff hU).2 h1)⟩

/-- `Ω ∩ ∂{u > 0} ⊆ (Ω ∩ ∂ᵉ(Ω ∩ {χ = 1})) ∪ Σ^H`. -/
theorem inter_frontier_pos_subset (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    Ω ∩ frontier {y | 0 < u y} ⊆
      (Ω ∩ essentialBoundary (Ω ∩ {y | χ y = 1})) ∪ sigmaH Ω u χ := by
  intro x hx
  by_cases hxS : x ∈ sigmaH Ω u χ
  · exact Or.inr hxS
  · exact Or.inl ⟨hx.1, frontier_pos_diff_sigmaH_subset_essentialBoundary hn h ⟨hx, hxS⟩⟩

/-! ### Local bounds for `∂ᵉ{χ = 1}` (Lemma 3.3 and the structure theory of `BV`) -/

/-- `ℋ^{n-1}(∂ᵉ(Ω ∩ {χ = 1}) ∩ B_r(x)) ≤ 2^{n+1} |B_1| C_V² r^{n-1}` whenever `B̄_{2r}(x) ⊆ Ω`
(Lemma 3.3 through the `BV` structure theorem and `|Dχ_E| = ℋ^{n-1}⌊∂ᵉE`; no assumption on
`Σ^H`). -/
theorem hausdorffN_essentialBoundary_chi_inter_ball_le (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    hausdorffN n (n - 1) (essentialBoundary (Ω ∩ {y | χ y = 1}) ∩ ball x r) ≤
      ENNReal.ofReal (2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * r ^ (n - 1)) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨μ, ν, hpair, hμ⟩ := h.exists_isGaussGreenPair_chi hn hr hball
  have hμeq := Registry.IsGaussGreenPair.eq_hausdorffN_restrict hn isOpen_ball
    h.measurableSet_chi_eq_one hpair
  calc hausdorffN n (n - 1) (essentialBoundary (Ω ∩ {y | χ y = 1}) ∩ ball x r)
      ≤ hausdorffN n (n - 1) (ball x (3 * r / 2) ∩
          (ball x (3 * r / 2) ∩ essentialBoundary (Ω ∩ {y | χ y = 1}))) := by
        refine measure_mono fun y hy => ?_
        have hyU : y ∈ ball x (3 * r / 2) := ball_subset_ball (by linarith) hy.2
        exact ⟨hyU, hyU, hy.1⟩
    _ = μ (ball x (3 * r / 2)) := by
        rw [hμeq, Measure.restrict_apply isOpen_ball.measurableSet]
    _ ≤ _ := hμ

/-- `∂ᵉ(Ω ∩ {χ = 1}) ∩ B_r(x)` is countably `ℋ^{n-1}`-rectifiable whenever `B̄_{2r}(x) ⊆ Ω`
(De Giorgi–Federer on `B_{3r/2}(x)`, where `{χ = 1}` has a Gauss–Green pair by Lemma 3.3 and
the `BV` structure theorem). -/
theorem isCountablyRectifiable_essentialBoundary_chi_inter_ball (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    IsCountablyRectifiable n (n - 1) (essentialBoundary (Ω ∩ {y | χ y = 1}) ∩ ball x r) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨μ, ν, hpair, -⟩ := h.exists_isGaussGreenPair_chi hn hr hball
  have hrect := (Registry.HasLocallyFinitePerimeter.rectifiable_essentialBoundary hn isOpen_ball
    h.measurableSet_chi_eq_one ⟨μ, ν, hpair⟩).1
  exact hrect.mono fun y hy => ⟨ball_subset_ball (by linarith) hy.2, hy.1⟩

/-- `Ω ∩ ∂ᵉ(Ω ∩ {χ = 1})` is countably `ℋ^{n-1}`-rectifiable. -/
theorem isCountablyRectifiable_inter_essentialBoundary_chi (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ essentialBoundary (Ω ∩ {y | χ y = 1})) := by
  refine isCountablyRectifiable_of_forall_mem_nhds fun x hx => ?_
  obtain ⟨r, hr, hB⟩ := exists_closedBall_two_mul_subset h.isOpen hx.1
  exact ⟨ball x r, ball_mem_nhds x hr,
    (isCountablyRectifiable_essentialBoundary_chi_inter_ball hn h hr hB).mono
      fun y hy => ⟨hy.1.2, hy.2⟩⟩

/-- `ℋ^{n-1}(K ∩ ∂ᵉ(Ω ∩ {χ = 1})) < ∞` for every compact `K ⊆ Ω`. -/
theorem hausdorffN_inter_essentialBoundary_chi_lt_top (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) {K : Set (Rn n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    hausdorffN n (n - 1) (K ∩ essentialBoundary (Ω ∩ {y | χ y = 1})) < ∞ := by
  refine measure_inter_lt_top_of_forall_mem_nhds _ hK fun x hx => ?_
  obtain ⟨r, hr, hB⟩ := exists_closedBall_two_mul_subset h.isOpen (hKΩ hx)
  exact ⟨ball x r, ball_mem_nhds x hr,
    (hausdorffN_essentialBoundary_chi_inter_ball_le hn h hr hB).trans_lt ENNReal.ofReal_lt_top⟩

/-! ### Theorem 8.7, first part (= Theorem 1.2 (ii)) -/

/-- **Theorem 8.7**, first part: `Ω ∩ ∂{u > 0}` is countably
`ℋ^{n-1}`-rectifiable. -/
theorem isCountablyRectifiable_frontier_pos (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) :=
  (NaberValtorta.IsCountablyRectifiable.union
    (isCountablyRectifiable_inter_essentialBoundary_chi hn h)
    (isCountablyRectifiable_sigmaH hn h)).mono (inter_frontier_pos_subset hn h)

/-- **Theorem 8.7**, first part: `∂{u > 0}` has locally finite
`ℋ^{n-1}` measure in `Ω`. -/
theorem hausdorffN_inter_frontier_pos_lt_top (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    {K : Set (Rn n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞ := by
  have hsub : K ∩ frontier {x | 0 < u x} ⊆
      (K ∩ essentialBoundary (Ω ∩ {y | χ y = 1})) ∪ (K ∩ sigmaH Ω u χ) := by
    intro x hx
    rcases inter_frontier_pos_subset hn h ⟨hKΩ hx.1, hx.2⟩ with hE | hS
    · exact Or.inl ⟨hx.1, hE.2⟩
    · exact Or.inr ⟨hx.1, hS⟩
  exact (measure_mono hsub).trans_lt ((measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.2 ⟨hausdorffN_inter_essentialBoundary_chi_lt_top hn h hK hKΩ,
      hausdorffN_inter_sigmaH_lt_top hn h hK hKΩ⟩))

/-- **Theorem 8.7**, first part, in the form of the first two
conjuncts of `Statements.laplacian_measure_eq` and of `Statements.main_theorem_ii`
(Theorem 1.2 (ii)). No connectedness is needed. -/
theorem rectifiable_and_locallyFinite_frontier_pos (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞ :=
  ⟨isCountablyRectifiable_frontier_pos hn h,
    fun _ hK hKΩ => hausdorffN_inter_frontier_pos_lt_top hn h hK hKΩ⟩

/-! ### Gauss–Green pairs up to null sets -/

/-- Set integrals of functions vanishing off a measurable `Ω` only see `Ω ∩ F`. -/
theorem setIntegral_eq_setIntegral_inter_of_eq_zero {Ω F : Set (Rn n)} (hΩ : MeasurableSet Ω)
    {f : Rn n → ℝ} (hf : ∀ y ∉ Ω, f y = 0) :
    ∫ y in F, f y = ∫ y in Ω ∩ F, f y := by
  have e : f = Ω.indicator f := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, hf y hy]
  conv_lhs => rw [e]
  rw [integral_indicator hΩ, Measure.restrict_restrict hΩ]

/-- **Gauss–Green pairs only see `E ∩ Ω` up to null sets**. -/
theorem isGaussGreenPair_congr_ae {Ω E E' : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}
    (hΩ : MeasurableSet Ω) (h : IsGaussGreenPair Ω E μ ν)
    (hEE' : (Ω ∩ E : Set (Rn n)) =ᵐ[volume] (Ω ∩ E' : Set (Rn n))) :
    IsGaussGreenPair Ω E' μ ν :=
  { h with
    integral_divergence := fun φ hφ => by
      have hz : ∀ y ∉ Ω, divergence φ y = 0 := fun y hy =>
        divergence_eq_zero_of_notMem_tsupport fun h' => hy (hφ.2.2 h')
      rw [setIntegral_eq_setIntegral_inter_of_eq_zero hΩ hz, ← setIntegral_congr_set hEE',
        ← setIntegral_eq_setIntegral_inter_of_eq_zero hΩ hz]
      exact h.integral_divergence φ hφ }

/-- The reduced boundary only sees `E ∩ Ω` up to null sets. -/
theorem reducedBoundary_subset_of_ae_eq {Ω E E' : Set (Rn n)} (hΩ : MeasurableSet Ω)
    (hEE' : (Ω ∩ E : Set (Rn n)) =ᵐ[volume] (Ω ∩ E' : Set (Rn n))) :
    reducedBoundary Ω E ⊆ reducedBoundary Ω E' := by
  rintro x ⟨hx, μ, ν, hpair, hpos, v, hv, hlim⟩
  exact ⟨hx, μ, ν, isGaussGreenPair_congr_ae hΩ hpair hEE', hpos, v, hv, hlim⟩

/-! ### Local finiteness of the Laplacian measure -/

/-- `∂ᵉE ⊆ ∂E`: interior points have density `1`, exterior points density `0`. -/
theorem essentialBoundary_subset_frontier (E : Set (Rn n)) : essentialBoundary E ⊆ frontier E := by
  intro y hy
  by_contra hf
  rw [frontier, Set.mem_sdiff, not_and_or, not_not] at hf
  rcases hf with hc | hi
  · exact hy.1 (Singular.hasDensity_zero_of_notMem_closure hc)
  · exact hy.2 (Singular.hasDensity_one_of_mem_nhds (mem_interior_iff_mem_nhds.1 hi))

/-- `∂*{u > 0} ⊆ Ω ∩ ∂{u > 0}`: the Gauss–Green measure of `{u > 0}` is `ℋ^{n-1}⌊∂ᵉ`
(Federer 4.5.6), which vanishes near points off the topological boundary. -/
theorem reducedBoundary_pos_subset (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    reducedBoundary Ω {y | 0 < u y} ⊆ Ω ∩ frontier {y | 0 < u y} := by
  rintro x ⟨hx, μ, ν, hpair, hpos, -⟩
  refine ⟨hx, ?_⟩
  by_contra hxf
  have hpair' : IsGaussGreenPair Ω (Ω ∩ {y | 0 < u y}) μ ν :=
    isGaussGreenPair_congr_ae h.isOpen.measurableSet hpair
      (Filter.EventuallyEq.of_eq (by rw [← inter_assoc, inter_self]))
  have hμ := Registry.IsGaussGreenPair.eq_hausdorffN_restrict hn h.isOpen
    h.isOpen_pos.measurableSet hpair'
  have hxf' : x ∉ frontier (Ω ∩ {y | 0 < u y}) := fun h' =>
    hxf ((h.mem_frontier_pos_inter_iff hx).1 h')
  obtain ⟨r, hr, hrf⟩ := Metric.isOpen_iff.1 isClosed_frontier.isOpen_compl x hxf'
  have hμr := hpos r hr
  rw [hμ, Measure.restrict_apply isOpen_ball.measurableSet] at hμr
  exact hμr.ne' (measure_mono_null
    (fun y hy => hrf hy.1 (essentialBoundary_subset_frontier _ hy.2.2)) measure_empty)

/-- `Σ^H` is Borel: it is relatively closed in the open set `Ω` (Proposition 3.5). -/
theorem measurableSet_sigmaH (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    MeasurableSet (sigmaH Ω u χ) := by
  have : NeZero n := ⟨by omega⟩
  have e : sigmaH Ω u χ = closure (sigmaH Ω u χ) ∩ Ω :=
    Subset.antisymm (fun x hx => ⟨subset_closure hx, hx.1⟩) h.closure_sigmaH_inter_subset
  rw [e]
  exact isClosed_closure.measurableSet.inter h.isOpen.measurableSet

end InnerVariational.Main
