/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.MainFrequency
public import InnerVariational.Regular.Perimeter
import InnerVariational.NaberValtorta.Main
import InnerVariational.NaberValtorta.Hausdorff
import InnerVariational.NaberValtorta.Reifenberg
import GMTFoundations.GMT.ApproxTangent
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Kernel.Rescale
public import InnerVariational.Defs.VariationalSolution
public import GMTFoundations.Defs.GMT

/-!
# Local-to-global covering for `Σ^H` (Theorem 7.2 (2) on a general open set)

The proof of Theorem 8.7 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), uses: "by
Theorem 7.2, `ℋ^{n-1}(Σ^H ∩ Ω') < ∞` … `Σ^H` is countably `ℋ^{n-1}`-rectifiable". Theorem 7.2
is stated on `B_1` around a point `0 ∈ Σ^H`, and concludes only for `Σ^H ∩ B_{1/100}`.
This file globalizes it.

* **Generic covering lemmas.** `isCountablyRectifiable_of_forall_mem_nhds` (a set that is
  rectifiable near each of its points is rectifiable; Lindelöf) and
  `measure_inter_lt_top_of_forall_mem_nhds` (a set of locally finite measure near each point of a
  compact `K` has finite measure in `K`).
* **Affine invariance.** `isCountablyRectifiable_of_preimage_affine`: rectifiability of
  `T⁻¹ A`, `T z = p + σ z`, gives rectifiability of `A`.
* **`Σ^H` near one of its points** (`sigmaH_inter_ball_rectifiable_and_lt_top`). For `x₀ ∈ Σ^H(Ω)`
  and `B̄_ρ(x₀) ⊆ Ω`, the set `Σ^H(Ω) ∩ B_{ρ/100}(x₀)` is countably rectifiable and has finite
  `ℋ^{n-1}` measure: Theorem 7.2 (2) for the rescaling `u_{x₀,ρ}`, with `N₊ := N_0(u_{x₀,ρ}; 1)`.
  Only finiteness is needed here, so the constant of Theorem 7.2 may depend on the point and no
  uniform frequency bound (Lemma 4.6) enters.
* **`Σ^H` globally** (`isCountablyRectifiable_sigmaH`, `hausdorffN_inter_sigmaH_lt_top`):
  `Σ^H(Ω)` is countably `ℋ^{n-1}`-rectifiable, and `ℋ^{n-1}(K ∩ Σ^H) < ∞` for compact
  `K ⊆ Ω`. The second uses the relative closedness of `Σ^H` (upper semicontinuity of
  `x ↦ M_x(u; 0+)`, Proposition 3.5): a point of `K \ Σ^H` has a neighbourhood missing `Σ^H`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational.Main

variable {n : ℕ}

/-! ### Generic covering lemmas -/

/-- **Local-to-global rectifiability.** If every point of `S` has a neighbourhood `V` with
`S ∩ V` countably `ℋ^k`-rectifiable, then `S` is countably `ℋ^k`-rectifiable (Lindelöf). -/
theorem isCountablyRectifiable_of_forall_mem_nhds {k : ℕ} {S : Set (Rn n)}
    (h : ∀ x ∈ S, ∃ V ∈ 𝓝 x, IsCountablyRectifiable n k (S ∩ V)) :
    IsCountablyRectifiable n k S := by
  choose! V hV hrect using h
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : S => interior (V i)) fun _ => isOpen_interior
  have hcov : S ⊆ ⋃ i ∈ T, S ∩ V (i : Rn n) := by
    intro x hx
    have hx' : x ∈ ⋃ i : S, interior (V i) :=
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hV x hx)⟩
    rw [← hTU] at hx'
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx'
    exact mem_iUnion₂.2 ⟨i, hi, hx, interior_subset hxi⟩
  exact (NaberValtorta.isCountablyRectifiable_biUnion hTc fun i _ => hrect i i.2).mono hcov

/-- **Local-to-global finiteness on compact sets.** If every point of a compact `K` has a
neighbourhood `V` with `μ (S ∩ V) < ∞`, then `μ (K ∩ S) < ∞`. -/
theorem measure_inter_lt_top_of_forall_mem_nhds (μ : Measure (Rn n)) {K S : Set (Rn n)}
    (hK : IsCompact K) (h : ∀ x ∈ K, ∃ V ∈ 𝓝 x, μ (S ∩ V) < ∞) : μ (K ∩ S) < ∞ := by
  have hfin := hK.measure_lt_top_of_nhdsWithin (μ := μ.restrict S) fun x hx => by
    obtain ⟨V, hV, hVfin⟩ := h x hx
    refine ⟨interior V, mem_nhdsWithin_of_mem_nhds (interior_mem_nhds.2 hV), ?_⟩
    rw [Measure.restrict_apply isOpen_interior.measurableSet]
    exact (measure_mono (show interior V ∩ S ⊆ S ∩ V from
      fun y hy => ⟨hy.2, interior_subset hy.1⟩)).trans_lt hVfin
  rwa [Measure.restrict_apply hK.isClosed.measurableSet] at hfin

/-- Every point of an open set is the centre of a closed ball of positive radius `2 r` inside it. -/
theorem exists_closedBall_two_mul_subset {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {x : Rn n}
    (hx : x ∈ Ω) : ∃ r > 0, closedBall x (2 * r) ⊆ Ω := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  refine ⟨ε / 4, by positivity, (closedBall_subset_ball ?_).trans hεΩ⟩
  linarith

/-! ### Affine invariance of rectifiability -/

/-- **Rectifiability pulls back along homotheties.** If `T⁻¹ A` is countably `ℋ^k`-rectifiable,
`T z = p + σ z` with `σ > 0`, then so is `A`: compose the Lipschitz parametrizations with `T`, and
use `ℋ^k(B) = σ^k ℋ^k(T⁻¹ B)` for the exceptional set. -/
theorem isCountablyRectifiable_of_preimage_affine {k : ℕ} {p : Rn n} {σ : ℝ} (hσ : 0 < σ)
    {A : Set (Rn n)} (h : IsCountablyRectifiable n k ((fun z : Rn n => p + σ • z) ⁻¹' A)) :
    IsCountablyRectifiable n k A := by
  obtain ⟨f, hf, hnull⟩ := h
  set T : Rn n → Rn n := fun z => p + σ • z with hT
  have hTL : LipschitzWith (1 * ‖σ‖₊) T :=
    (IsometryEquiv.addLeft p).isometry.lipschitzWith.comp (lipschitzWith_smul σ)
  refine ⟨fun i => T ∘ f i, fun i => ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hf i
    exact ⟨_, hTL.comp hC⟩
  · rw [NaberValtorta.hausdorffN_eq_mul_preimage_affine (p := p) hσ k]
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ hnull)
    rintro y ⟨hyA, hy⟩
    refine ⟨hyA, fun hy' => hy ?_⟩
    obtain ⟨i, w, hw⟩ := mem_iUnion.1 hy'
    exact mem_iUnion.2 ⟨i, w, show T (f i w) = T y by rw [hw]⟩

/-! ### `Σ^H` near one of its points: Theorem 7.2 (2) after rescaling -/

/-- `B̄_1 ⊆ T⁻¹ Ω` for `T y = x₀ + ρ y` when `B̄_ρ(x₀) ⊆ Ω`. -/
theorem closedBall_zero_one_subset_preimage {Ω : Set (Rn n)} {x₀ : Rn n} {ρ : ℝ} (hρ : 0 < ρ)
    (hB : closedBall x₀ ρ ⊆ Ω) : closedBall (0 : Rn n) 1 ⊆ (fun y => x₀ + ρ • y) ⁻¹' Ω := by
  intro y hy
  refine hB ?_
  rw [mem_closedBall, dist_zero_right] at hy
  change x₀ + ρ • y ∈ closedBall x₀ ρ
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
  calc ρ * ‖y‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hy hρ.le
    _ = ρ := mul_one ρ

/-- If `x₀ + ρ y ∈ Σ^H(Ω)`, `‖y‖ < 1` and `B̄_ρ(x₀) ⊆ Ω`, then `y ∈ Σ^H(B_1)` for the rescaling
`u_{x₀,ρ}`. (The `hmem` step of
`NaberValtorta.hausdorffN_not_tendsto_frequencyN_inter_ball_eq_zero`.) -/
theorem mem_sigmaH_ball_oneHomRescale [NeZero n] {Ω : Set (Rn n)} {u χ : Rn n → ℝ}
    {x₀ y : Rn n} {ρ : ℝ} (hρ : 0 < ρ) (hB : closedBall x₀ ρ ⊆ Ω)
    (hy : x₀ + ρ • y ∈ sigmaH Ω u χ) (hy1 : ‖y‖ < 1) :
    y ∈ sigmaH (ball 0 1) (oneHomRescale u x₀ ρ) (chiRescale χ x₀ ρ) := by
  refine ⟨mem_ball_zero_iff.2 hy1,
    (NaberValtorta.mem_closure_oneHomRescale_iff u x₀ y hρ).2 hy.2.1, fun r hr hrB => ?_⟩
  rw [NaberValtorta.monotonicityM_oneHomRescale_apply u χ x₀ y hρ]
  exact hy.2.2 (ρ * r) (mul_pos hρ hr)
    ((NaberValtorta.closedBall_add_smul_subset_ball hρ hrB).trans
      (ball_subset_closedBall.trans hB))

/-- **Theorem 7.2 (2) at a general point** (rescaled). Let `(u, χ)` be a
variational solution on `Ω`, `x₀ ∈ Σ^H(Ω)` and `B̄_ρ(x₀) ⊆ Ω`. Then `Σ^H(Ω) ∩ B_{ρ/100}(x₀)` is
countably `ℋ^{n-1}`-rectifiable and has finite `ℋ^{n-1}` measure.

Proof: the rescaling `u_{x₀,ρ}` is a solution on `T⁻¹ Ω ⊇ B̄_1`, `T y = x₀ + ρ y`, with
`0 ∈ Σ^H(B_1)`; apply `NaberValtorta.sigmaH_main` with `N₊ := N_0(u_{x₀,ρ}; 1)`, pull back
`Σ^H(Ω) ∩ B_{ρ/100}(x₀)` along `T`, and use `ℋ^{n-1}(A) = ρ^{n-1} ℋ^{n-1}(T⁻¹ A)`. -/
theorem sigmaH_inter_ball_rectifiable_and_lt_top (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0}
    {u χ : Rn n → ℝ} (h : IsVariationalSolution Ω C_V u χ) {x₀ : Rn n}
    (hx₀ : x₀ ∈ sigmaH Ω u χ) {ρ : ℝ} (hρ : 0 < ρ) (hB : closedBall x₀ ρ ⊆ Ω) :
    IsCountablyRectifiable n (n - 1) (sigmaH Ω u χ ∩ ball x₀ (ρ / 100)) ∧
      hausdorffN n (n - 1) (sigmaH Ω u χ ∩ ball x₀ (ρ / 100)) < ∞ := by
  have : NeZero n := ⟨by omega⟩
  have h0 : (0 : Rn n) ∈ sigmaH (ball 0 1) (oneHomRescale u x₀ ρ) (chiRescale χ x₀ ρ) :=
    mem_sigmaH_ball_oneHomRescale hρ hB (by simpa using hx₀) (by simp)
  obtain ⟨C, hC⟩ := NaberValtorta.sigmaH_main hn
    (frequencyN (oneHomRescale u x₀ ρ) (chiRescale χ x₀ ρ) 0 1)
  obtain ⟨-, hfin, hrect⟩ := (hC _ C_V _ _ (h.rescale x₀ hρ)
    (closedBall_zero_one_subset_preimage hρ hB) le_rfl).2 h0
  have hsub : (fun y => x₀ + ρ • y) ⁻¹' (sigmaH Ω u χ ∩ ball x₀ (ρ / 100)) ⊆
      sigmaH (ball 0 1) (oneHomRescale u x₀ ρ) (chiRescale χ x₀ ρ) ∩ ball 0 (1 / 100) := by
    rintro y ⟨hyS, hyB⟩
    have hyB' : dist (x₀ + ρ • y) x₀ < ρ / 100 := hyB
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le] at hyB'
    have hy : ‖y‖ < 1 / 100 := by
      have h1 : ρ * ‖y‖ < ρ * (1 / 100) := by linarith
      exact lt_of_mul_lt_mul_left h1 hρ.le
    exact ⟨mem_sigmaH_ball_oneHomRescale hρ hB hyS (by linarith), mem_ball_zero_iff.2 hy⟩
  refine ⟨isCountablyRectifiable_of_preimage_affine hρ (hrect.mono hsub), ?_⟩
  rw [NaberValtorta.hausdorffN_eq_mul_preimage_affine (p := x₀) hρ (n - 1)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((measure_mono hsub).trans_lt (hfin.trans_lt ENNReal.ofReal_lt_top))

/-! ### `Σ^H` globally -/

/-- **`Σ^H` is countably `ℋ^{n-1}`-rectifiable** (proof of Theorem 8.7), for a variational
solution on any open `Ω`: Theorem 7.2 (2) near each point
(`sigmaH_inter_ball_rectifiable_and_lt_top`) and
Lindelöf (`isCountablyRectifiable_of_forall_mem_nhds`). -/
theorem isCountablyRectifiable_sigmaH (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0}
    {u χ : Rn n → ℝ} (h : IsVariationalSolution Ω C_V u χ) :
    IsCountablyRectifiable n (n - 1) (sigmaH Ω u χ) := by
  refine isCountablyRectifiable_of_forall_mem_nhds fun x hx => ?_
  obtain ⟨r, hr, hB⟩ := exists_closedBall_two_mul_subset h.isOpen hx.1
  exact ⟨ball x (2 * r / 100), ball_mem_nhds x (by positivity),
    (sigmaH_inter_ball_rectifiable_and_lt_top hn h hx (by positivity) hB).1⟩

/-- **`Σ^H` has locally finite `ℋ^{n-1}` measure in `Ω`** (proof of Theorem 8.7):
`ℋ^{n-1}(K ∩ Σ^H) < ∞` for every compact `K ⊆ Ω`. Near a point of `Σ^H` this is Theorem 7.2 (2)
(`sigmaH_inter_ball_rectifiable_and_lt_top`); a point of `K \ Σ^H` has the neighbourhood
`Ω \ Σ^H`, which is open (relative closedness of `Σ^H`, Proposition 3.5) and misses `Σ^H`. -/
theorem hausdorffN_inter_sigmaH_lt_top (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0}
    {u χ : Rn n → ℝ} (h : IsVariationalSolution Ω C_V u χ) {K : Set (Rn n)} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : hausdorffN n (n - 1) (K ∩ sigmaH Ω u χ) < ∞ := by
  have : NeZero n := ⟨by omega⟩
  refine measure_inter_lt_top_of_forall_mem_nhds _ hK fun x hxK => ?_
  by_cases hx : x ∈ sigmaH Ω u χ
  · obtain ⟨r, hr, hB⟩ := exists_closedBall_two_mul_subset h.isOpen hx.1
    exact ⟨ball x (2 * r / 100), ball_mem_nhds x (by positivity),
      (sigmaH_inter_ball_rectifiable_and_lt_top hn h hx (by positivity) hB).2⟩
  · refine ⟨Ω \ sigmaH Ω u χ, h.isOpen_diff_sigmaH.mem_nhds ⟨hKΩ hxK, hx⟩, ?_⟩
    rw [inter_sdiff_self, measure_empty]
    exact ENNReal.zero_lt_top

end InnerVariational.Main
