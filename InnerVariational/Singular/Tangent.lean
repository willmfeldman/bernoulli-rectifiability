/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Singular.FlatPoint
public import InnerVariational.NaberValtorta.MainFrequency
public import InnerVariational.Registry.GMT
public import InnerVariational.Monotonicity.HighestDensity
import Mathlib.Topology.UniformSpace.Uniformizable
import InnerVariational.NaberValtorta.Main
import InnerVariational.NaberValtorta.Reifenberg
import InnerVariational.Defs.GMT
import InnerVariational.Kernel.Rescale
public import GMTFoundations.Defs.GMT

/-!
# `Σ^H` is flat at `ℋ^{n-1}`-a.e. of its points

First sentence of the proof of Lemma 8.5 of D. Kriventsov and G. S. Weiss, *Rectifiability,
finite Hausdorff measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm.
Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of
arXiv v2): by Theorem 7.2, `Σ^H` has an approximate tangent plane at `ℋ^{n-1}`-a.e. of its
points. We derive the consequence used in the proof, `IsFlatAt` (`Singular/FlatPoint.lean`), from
the existence of approximate tangent planes a.e. on countably rectifiable sets of locally finite
measure (P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Cambridge Univ. Press,
1995, Theorem 15.19; `Registry.hausdorffN_not_approxTangent_eq_zero`, proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0).

## Main results

* `measurableSet_sigmaH`: `Σ^H` is Borel (it is relatively closed in `Ω`, Proposition 3.5).
* `sigmaH_inter_ball_structure`: localization of Theorem 7.2 (1)–(2). For `x₀ ∈ Σ^H` and
  `B̄_ρ(x₀) ⊆ Ω`, `Σ^H ∩ B_{ρ/100}(x₀)` has finite `ℋ^{n-1}` measure and is countably
  `ℋ^{n-1}`-rectifiable. Proof: `NaberValtorta.sigmaH_main` for the rescaling `u_{x₀,ρ}`, as in
  `NaberValtorta.hausdorffN_not_tendsto_frequencyN_inter_ball_eq_zero`.
* `isFlatAt_of_tendsto`: an approximate tangent plane `ν^⊥` (weak-* convergence of the blow-ups
  of `ℋ^{n-1}⌊S` to `ℋ^{n-1}⌊ν^⊥`) gives `IsFlatAt`. The limit measure charges every ball centred
  on `ν^⊥`, since `ℋ^{n-1}` on a hyperplane is `(n−1)`-dimensional Lebesgue measure
  (H. Federer, *Geometric Measure Theory*, Springer, 1969, 2.10.35; proved in gmt-foundations).
* `hausdorffN_not_isFlatAt_eq_zero`: `Σ^H` is flat in some direction at `ℋ^{n-1}`-a.e. point.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

namespace Singular

variable {n : ℕ} {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-! ### Rectifiability under similarities -/

/-- The image of a countably `ℋ^k`-rectifiable set under `z ↦ p + σ z`, `σ > 0`, is countably
`ℋ^k`-rectifiable. -/
theorem IsCountablyRectifiable.image_affine {k : ℕ} {A : Set (Rn n)}
    (hA : IsCountablyRectifiable n k A) (p : Rn n) {σ : ℝ} (hσ : 0 < σ) :
    IsCountablyRectifiable n k ((fun z => p + σ • z) '' A) := by
  obtain ⟨f, hf, hnull⟩ := hA
  set T : Rn n → Rn n := fun z => p + σ • z with hT
  have hTinj : Function.Injective T := fun a b hab => by
    have : σ • a = σ • b := add_left_cancel hab
    exact smul_right_injective _ hσ.ne' this
  have hTlip : LipschitzWith (Real.toNNReal σ) T := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.coe_toNNReal _ hσ.le, hT, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub,
      ← smul_sub, norm_smul, Real.norm_of_nonneg hσ.le]
  refine ⟨fun i => T ∘ f i, fun i => ?_, ?_⟩
  · obtain ⟨Ci, hCi⟩ := hf i
    exact ⟨_, hTlip.comp hCi⟩
  · have hsub : T '' A \ ⋃ i, range (T ∘ f i) ⊆ T '' (A \ ⋃ i, range (f i)) := by
      rintro _ ⟨⟨a, ha, rfl⟩, hna⟩
      refine ⟨a, ⟨ha, fun hmem => hna ?_⟩, rfl⟩
      obtain ⟨i, b, rfl⟩ := mem_iUnion.1 hmem
      exact mem_iUnion.2 ⟨i, b, rfl⟩
    refine measure_mono_null hsub ?_
    rw [NaberValtorta.hausdorffN_eq_mul_preimage_affine (p := p) hσ k,
      Set.preimage_image_eq _ hTinj, hnull, mul_zero]

/-! ### Measurability and local structure of `Σ^H` -/

/-- `Σ^H` is Borel: it is relatively closed in the open set `Ω` (Prop 3.5). -/
theorem measurableSet_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    MeasurableSet (sigmaH Ω u χ) := by
  have heq : sigmaH Ω u χ = closure (sigmaH Ω u χ) ∩ Ω :=
    Subset.antisymm (fun y hy => ⟨subset_closure hy, hy.1⟩) h.closure_sigmaH_inter_subset
  rw [heq]
  exact isClosed_closure.measurableSet.inter h.isOpen.measurableSet

/-- **Theorem 7.2 (1)–(2), localized.** For `x₀ ∈ Σ^H` and `B̄_ρ(x₀) ⊆ Ω`, the set
`Σ^H ∩ B_{ρ/100}(x₀)` has finite `ℋ^{n-1}` measure and is countably `ℋ^{n-1}`-rectifiable. -/
theorem sigmaH_inter_ball_structure (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    {x₀ : Rn n} (hx₀ : x₀ ∈ sigmaH Ω u χ) {ρ : ℝ} (hρ : 0 < ρ) (hB : closedBall x₀ ρ ⊆ Ω) :
    hausdorffN n (n - 1) (sigmaH Ω u χ ∩ ball x₀ (ρ / 100)) < ∞ ∧
      IsCountablyRectifiable n (n - 1) (sigmaH Ω u χ ∩ ball x₀ (ρ / 100)) := by
  haveI : NeZero n := ⟨by omega⟩
  have hsol := h.rescale x₀ hρ
  set v := oneHomRescale u x₀ ρ
  set η := chiRescale χ x₀ ρ
  have hΩ' : closedBall (0 : Rn n) 1 ⊆ (fun y => x₀ + ρ • y) ⁻¹' Ω := by
    intro y hy
    refine hB ?_
    rw [mem_closedBall, dist_zero_right] at hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
    calc ρ * ‖y‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hy hρ.le
      _ = ρ := mul_one ρ
  have hmem : ∀ y : Rn n, x₀ + ρ • y ∈ sigmaH Ω u χ → ‖y‖ < 1 → y ∈ sigmaH (ball 0 1) v η := by
    intro y hy hy1
    refine ⟨mem_ball_zero_iff.2 hy1,
      (NaberValtorta.mem_closure_oneHomRescale_iff u x₀ y hρ).2 hy.2.1, fun r hr hrB => ?_⟩
    rw [NaberValtorta.monotonicityM_oneHomRescale_apply u χ x₀ y hρ]
    exact hy.2.2 (ρ * r) (mul_pos hρ hr)
      ((NaberValtorta.closedBall_add_smul_subset_ball hρ hrB).trans
        (ball_subset_closedBall.trans hB))
  have h0 : (0 : Rn n) ∈ sigmaH (ball 0 1) v η := hmem 0 (by simpa using hx₀) (by simp)
  obtain ⟨Cm, hCm⟩ := NaberValtorta.sigmaH_main hn (frequencyN v η 0 1)
  obtain ⟨-, H⟩ := hCm _ C v η hsol hΩ' le_rfl
  obtain ⟨-, hfin, hrect⟩ := H h0
  -- the preimage of our set lies in `Σ^H(v) ∩ B_{1/100}`
  have hpre : (fun y : Rn n => x₀ + ρ • y) ⁻¹' (sigmaH Ω u χ ∩ ball x₀ (ρ / 100)) ⊆
      sigmaH (ball 0 1) v η ∩ ball 0 (1 / 100) := by
    rintro y ⟨hyH, hyB⟩
    have hy : ‖y‖ < 1 / 100 := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
        at hyB
      have h1 : ρ * ‖y‖ < ρ * (1 / 100) := by linarith
      exact lt_of_mul_lt_mul_left h1 hρ.le
    exact ⟨hmem y hyH (by linarith), mem_ball_zero_iff.2 hy⟩
  constructor
  · rw [NaberValtorta.hausdorffN_eq_mul_preimage_affine (p := x₀) hρ (n - 1)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono hpre).trans_lt (hfin.trans_lt ENNReal.ofReal_lt_top))
  · have himg : sigmaH Ω u χ ∩ ball x₀ (ρ / 100) ⊆
        (fun z => x₀ + ρ • z) '' (sigmaH (ball 0 1) v η ∩ ball 0 (1 / 100)) := by
      intro y hy
      refine ⟨ρ⁻¹ • (y - x₀), hpre ?_, ?_⟩
      · rw [mem_preimage]
        rwa [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
      · change x₀ + ρ • (ρ⁻¹ • (y - x₀)) = y
        rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
    exact IsCountablyRectifiable.mono (IsCountablyRectifiable.image_affine hrect x₀ hρ) himg

/-! ### From approximate tangent planes to flatness -/

/-- The limit measure `ℋ^{n-1}⌊ν^⊥` charges every ball centred on `ν^⊥`:
`∫_{ν^⊥} (τ − |y − p|)₊ dℋ^{n-1} > 0` for `p ⊥ ν`, `τ > 0`. Uses that `ℋ^{n-1}` on a
hyperplane is the image of `(n−1)`-dimensional Lebesgue measure. -/
theorem integral_hyperplane_pos (hn : 2 ≤ n) {ν p : Rn n} (hν : ‖ν‖ = 1) (hp : ⟪p, ν⟫ = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    0 < ∫ y in {y : Rn n | ⟪y, ν⟫ = 0}, max 0 (τ - ‖y - p‖) ∂hausdorffN n (n - 1) := by
  have hν0 : ν ≠ 0 := fun h0 => by rw [h0, norm_zero] at hν; exact zero_ne_one hν
  haveI : Fact (Module.finrank ℝ (Rn n) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  set K : Submodule ℝ (Rn n) := (ℝ ∙ ν)ᗮ with hK
  have hfr : Module.finrank ℝ K = n - 1 := Submodule.finrank_orthogonal_span_singleton hν0
  set b : OrthonormalBasis (Fin (n - 1)) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hfr)
  set L : Rn (n - 1) →ₗᵢ[ℝ] Rn n := K.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry with hL
  have hmemK : ∀ y : Rn n, y ∈ K ↔ ⟪y, ν⟫ = 0 := fun y => by
    rw [hK, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
  have hrange : range (fun y => (0 : Rn n) + L y) = {y : Rn n | ⟪y, ν⟫ = 0} := by
    ext y
    simp only [zero_add, mem_range, mem_setOf_eq]
    constructor
    · rintro ⟨z, rfl⟩
      exact (hmemK _).1 (b.repr.symm z).2
    · intro hy
      refine ⟨b.repr ⟨y, (hmemK y).2 hy⟩, ?_⟩
      simp [hL]
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, L z₀ = p := by
    have : p ∈ range (fun y => (0 : Rn n) + L y) := by rw [hrange]; exact hp
    obtain ⟨z₀, hz₀⟩ := this
    exact ⟨z₀, by simpa using hz₀⟩
  have hmap := Registry.map_volume_affineIsometry_eq_hausdorffN L (0 : Rn n)
  rw [hrange] at hmap
  have hφc : Continuous fun y : Rn n => max 0 (τ - ‖y - p‖) := by fun_prop
  rw [← hmap, integral_map (by fun_prop) hφc.aestronglyMeasurable]
  have hψ : (fun z : Rn (n - 1) => max 0 (τ - ‖(0 + L z) - p‖)) =
      fun z => max 0 (τ - ‖z - z₀‖) := by
    funext z
    rw [zero_add, ← hz₀, ← map_sub, LinearIsometry.norm_map]
  rw [hψ]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := z₀) (by fun_prop)
    ?_ (fun z => le_max_left _ _) ?_
  · refine HasCompactSupport.intro (isCompact_closedBall z₀ τ) fun z hz => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    exact max_eq_left (by linarith)
  · rw [sub_self, norm_zero, sub_zero, max_eq_right hτ.le]
    exact hτ.ne'

/-- **Approximate tangent plane ⇒ flatness** (proof of Lemma 8.5). If `S ⊆ Σ^H` and the
blow-ups of `ℋ^{n-1}⌊S` at `x` converge to `ℋ^{n-1}⌊ν^⊥` (as in
`Registry.hausdorffN_not_approxTangent_eq_zero`), then `Σ^H` is flat at `x` in direction `ν`. -/
theorem isFlatAt_of_tendsto (hn : 2 ≤ n) {S : Set (Rn n)} (hS : S ⊆ sigmaH Ω u χ) {x ν : Rn n}
    (hν : ‖ν‖ = 1)
    (hT : ∀ φ : Rn n → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r => (r ^ (n - 1))⁻¹ * ∫ y in S, φ (r⁻¹ • (y - x)) ∂hausdorffN n (n - 1))
        (𝓝[>] 0) (𝓝 (∫ y in {y | ⟪y, ν⟫ = 0}, φ y ∂hausdorffN n (n - 1)))) :
    IsFlatAt Ω u χ x ν := by
  intro p hp τ hτ
  set φ : Rn n → ℝ := fun y => max 0 (τ - ‖y - p‖) with hφ
  have hφc : Continuous φ := by rw [hφ]; fun_prop
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall p τ) fun z hz => ?_
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    exact max_eq_left (by linarith)
  have hpos := integral_hyperplane_pos hn hν hp hτ
  filter_upwards [(hT φ hφc hφs).eventually (lt_mem_nhds hpos), self_mem_nhdsWithin]
    with r hr (hr0 : 0 < r)
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hzero : ∫ y in S, φ (r⁻¹ • (y - x)) ∂hausdorffN n (n - 1) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    by_contra hφy
    have hlt : ‖r⁻¹ • (y - x) - p‖ < τ := by
      by_contra hge
      exact hφy (max_eq_left (by linarith [not_lt.1 hge]))
    have hyB : y ∈ ball (x + r • p) (τ * r) := by
      rw [mem_ball, dist_eq_norm]
      have e : y - (x + r • p) = r • (r⁻¹ • (y - x) - p) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]; abel
      rw [e, norm_smul, Real.norm_of_nonneg hr0.le, mul_comm τ r]
      exact mul_lt_mul_of_pos_left hlt hr0
    have : y ∈ sigmaH Ω u χ ∩ ball (x + r • p) (τ * r) := ⟨hS hy, hyB⟩
    rw [hne] at this
    exact this
  rw [hzero, mul_zero] at hr
  exact lt_irrefl _ hr

/-- **`Σ^H` is flat at `ℋ^{n-1}`-a.e. of its points** (proof of Lemma 8.5), from the localized
Theorem 7.2 and the existence of approximate tangent planes a.e. on rectifiable sets. -/
theorem hausdorffN_not_isFlatAt_eq_zero (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    hausdorffN n (n - 1)
      {x | x ∈ sigmaH Ω u χ ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧ IsFlatAt Ω u χ x ν} = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have hρ : ∀ x ∈ Ω, ∃ ρ, 0 < ρ ∧ closedBall x ρ ⊆ Ω := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hx
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεΩ⟩
  choose! ρ hρpos hρsub using hρ
  set E := {x | x ∈ sigmaH Ω u χ ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧ IsFlatAt Ω u χ x ν} with hE
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : sigmaH Ω u χ => ball (i : Rn n) (ρ i / 100)) fun _ => isOpen_ball
  have hcov : E ⊆ ⋃ i ∈ T, E ∩ ball (i : Rn n) (ρ i / 100) := by
    intro x hx
    have hx' : x ∈ ⋃ i : sigmaH Ω u χ, ball (i : Rn n) (ρ i / 100) := by
      have := hρpos x hx.1.1
      exact mem_iUnion.2 ⟨⟨x, hx.1⟩, mem_ball_self (by positivity)⟩
    rw [← hTU] at hx'
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx'
    exact mem_iUnion₂.2 ⟨i, hi, hx, hxi⟩
  refine measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
  -- one ball of the cover
  set B := ball (i : Rn n) (ρ i / 100) with hB
  set S := sigmaH Ω u χ ∩ B with hS
  obtain ⟨hfin, hrect⟩ := sigmaH_inter_ball_structure hn h i.2 (hρpos i i.2.1) (hρsub i i.2.1)
  have hSm : MeasurableSet S := (measurableSet_sigmaH h).inter measurableSet_ball
  have hR13 := Registry.hausdorffN_not_approxTangent_eq_zero hn isOpen_ball hSm
    inter_subset_right hrect fun K _ _ => (measure_mono inter_subset_right).trans_lt hfin
  refine measure_mono_null ?_ hR13
  rintro x ⟨⟨hxH, hxnot⟩, hxB⟩
  refine ⟨⟨hxH, hxB⟩, fun ⟨ν, hν, hT⟩ => hxnot ⟨ν, hν, ?_⟩⟩
  exact isFlatAt_of_tendsto hn inter_subset_left hν hT

end Singular

end InnerVariational
