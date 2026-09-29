/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Packing
public import InnerVariational.Defs.GMT
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Basic.Polar
public import GMTFoundations.Defs.GMT

/-!
# Hausdorff measure from coverings, and countable rectifiability

Two general tools for Lemma 7.1 (3) and Theorem 7.2 (2)–(3) of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2).

* `hausdorffMeasure_le_of_cover`: if `A` is covered by `#F_m` closed balls of radius `a_m → 0`
  and `#F_m (2 a_m)^d ≤ K`, then `μH[d](A) ≤ K`.
* `hausdorffN_le_of_volume_thickening_le` (**Minkowski ⇒ Hausdorff**): if a bounded `A ⊆ ℝⁿ`
  satisfies `|B_s(A)| ≤ K s` for all small `s`, then `ℋ^{n-1}(A) ≤ 2^{n-1} ω_{n-1} K / ω_n`.
  The proof takes a maximal `2s`-separated subset `F` of `A`. The balls `B_s(y)`, `y ∈ F`, are
  disjoint and lie in `B_s(A)`, so `#F ω_n sⁿ ≤ K s`, and the balls `B̄_{2s}(y)` cover `A`.
* `IsCountablyRectifiable`: monotonicity, null sets, and countable unions.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Hausdorff measure from coverings -/

/-- If `A ⊆ ⋃_{y ∈ F_m} B̄_{a_m}(y)` with `a_m → 0` and `#F_m (2 a_m)^d ≤ K` for every `m`, then
`μH[d](A) ≤ K`. -/
theorem hausdorffMeasure_le_of_cover {d : ℕ} {A : Set (Rn n)} {K : ℝ} (F : ℕ → Finset (Rn n))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ m, 0 ≤ a m)
    (hcov : ∀ m, A ⊆ ⋃ y ∈ F m, closedBall y (a m))
    (hK : ∀ m, ((F m).card : ℝ) * (2 * a m) ^ d ≤ K) :
    μH[(d : ℝ)] A ≤ ENNReal.ofReal K := by
  have hr : Tendsto (fun m => ENNReal.ofReal (2 * a m)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (ha.const_mul 2)
    simpa using this
  refine (Measure.hausdorffMeasure_le_liminf_sum (ι := fun m => (F m : Set (Rn n))) (d : ℝ) A
    (fun m => ENNReal.ofReal (2 * a m)) hr (fun m y => closedBall (y : Rn n) (a m))
    (Eventually.of_forall fun m y => ediam_le_of_forall_dist_le fun u hu v hv => ?_)
    (Eventually.of_forall fun m => ?_)).trans ?_
  · linarith [dist_triangle_right u v (y : Rn n), mem_closedBall.1 hu, mem_closedBall.1 hv]
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov m hz)
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hzy⟩
  · refine liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_)
    calc ∑ y : (F m : Set (Rn n)), ediam (closedBall (y : Rn n) (a m)) ^ (d : ℝ)
        ≤ ∑ _y : (F m : Set (Rn n)), ENNReal.ofReal (2 * a m) ^ (d : ℝ) := by
          refine Finset.sum_le_sum fun y _ => ENNReal.rpow_le_rpow ?_ (Nat.cast_nonneg _)
          exact ediam_le_of_forall_dist_le fun u hu v hv => by
            linarith [dist_triangle_right u v (y : Rn n), mem_closedBall.1 hu,
              mem_closedBall.1 hv]
      _ = ENNReal.ofReal (((F m).card : ℝ) * (2 * a m) ^ d) := by
          rw [Finset.sum_const, Finset.card_univ, ENNReal.rpow_natCast, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_pow (by linarith [ha0 m])]
          congr 1
          simp
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hK m)

/-- `hausdorffMeasure_le_of_cover` for the normalized measure `ℋ^d = (ω_d/2^d) μH[d]`. -/
theorem hausdorffN_le_of_cover {d : ℕ} {A : Set (Rn n)} {K : ℝ} (F : ℕ → Finset (Rn n))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ m, 0 ≤ a m)
    (hcov : ∀ m, A ⊆ ⋃ y ∈ F m, closedBall y (a m))
    (hK : ∀ m, ((F m).card : ℝ) * (2 * a m) ^ d ≤ K) :
    hausdorffN n d A ≤ ENNReal.ofReal (unitBallVolume d / 2 ^ d * K) := by
  have hω := (unitBallVolume_pos d).le
  rw [hausdorffN, Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_right (hausdorffMeasure_le_of_cover F a ha ha0 hcov hK) _

/-- **Minkowski ⇒ Hausdorff.** If `A ⊆ B̄_ρ(z)` and `|B_s(A)| ≤ K s` for `0 < s ≤ s₀`, then
`ℋ^{n-1}(A) ≤ 2^{n-1} ω_{n-1} K / ω_n`. -/
theorem hausdorffN_le_of_volume_thickening_le (hn : 0 < n) {A : Set (Rn n)} {z : Rn n}
    {ρ K s₀ : ℝ} (hA : A ⊆ closedBall z ρ) (hK : 0 ≤ K) (hs₀ : 0 < s₀)
    (hvol : ∀ s, 0 < s → s ≤ s₀ → volume (thickening s A) ≤ ENNReal.ofReal (K * s)) :
    hausdorffN n (n - 1) A ≤
      ENNReal.ofReal (2 ^ (n - 1) * unitBallVolume (n - 1) * K / unitBallVolume n) := by
  classical
  have hω := unitBallVolume_pos n
  set s : ℕ → ℝ := fun m => s₀ / (m + 1) with hs_def
  have hs : ∀ m, 0 < s m := fun m => by positivity
  have hss₀ : ∀ m, s m ≤ s₀ := fun m =>
    div_le_self hs₀.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hs0 : Tendsto s atTop (𝓝 0) := by
    refine ((tendsto_const_div_atTop_nhds_zero_nat s₀).comp (tendsto_add_atTop_nat 1)).congr
      fun m => ?_
    simp [hs_def]
  -- the covering by `B̄_{2 s_m}` around a maximal `2 s_m`-separated subset
  set F : ℕ → Finset (Rn n) := fun m => net A (2 * s m) with hF
  have hcard : ∀ m, ((F m).card : ℝ) * s m ^ (n - 1) ≤ K / unitBallVolume n := by
    intro m
    have h2s : 0 < 2 * s m := by linarith [hs m]
    obtain ⟨hFA, hFsep, -⟩ := net_spec hA h2s
    have hdisj : (F m : Set (Rn n)).PairwiseDisjoint fun y => ball y (s m) :=
      pairwiseDisjoint_ball_of_pairwise hFsep
    have hU : ∀ y ∈ F m, ball y (s m) ⊆ thickening (s m) A := fun y hy w hw =>
      mem_thickening_iff.2 ⟨y, hFA hy, mem_ball.1 hw⟩
    have h := (card_mul_volume_ball_le (hs m) hdisj hU).trans (hvol _ (hs m) (hss₀ m))
    rw [ENNReal.ofReal_le_ofReal_iff (by have := hs m; positivity)] at h
    have hpow : s m ^ n = s m ^ (n - 1) * s m := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [le_div_iff₀ hω]
    have h' : ((F m).card * s m ^ (n - 1) * unitBallVolume n) * s m ≤ K * s m := by
      calc ((F m).card * s m ^ (n - 1) * unitBallVolume n) * s m
          = (F m).card * (unitBallVolume n * s m ^ n) := by rw [hpow]; ring
        _ ≤ K * s m := h
    exact le_of_mul_le_mul_right h' (hs m)
  have key := hausdorffN_le_of_cover (d := n - 1) (A := A)
    (K := 4 ^ (n - 1) * (K / unitBallVolume n)) F (fun m => 2 * s m)
    (by simpa using hs0.const_mul 2) (fun m => by linarith [hs m])
    (fun m w hw => by
      obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.1 (subset_net hA (by linarith [hs m] : 0 < 2 * s m) hw)
      exact mem_iUnion₂.2 ⟨y, hy, ball_subset_closedBall hwy⟩)
    (fun m => by
      calc ((F m).card : ℝ) * (2 * (2 * s m)) ^ (n - 1)
          = 4 ^ (n - 1) * (((F m).card : ℝ) * s m ^ (n - 1)) := by
            rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num, mul_pow]
            ring
        _ ≤ 4 ^ (n - 1) * (K / unitBallVolume n) :=
            mul_le_mul_of_nonneg_left (hcard m) (by positivity))
  refine key.trans_eq ?_
  congr 1
  rw [show (4 : ℝ) ^ (n - 1) = 2 ^ (n - 1) * 2 ^ (n - 1) by rw [← mul_pow]; norm_num]
  field_simp

/-! ### Countable rectifiability -/

theorem IsCountablyRectifiable.mono {k : ℕ} {A B : Set (Rn n)}
    (hB : IsCountablyRectifiable n k B) (hAB : A ⊆ B) : IsCountablyRectifiable n k A := by
  obtain ⟨f, hf, hnull⟩ := hB
  exact ⟨f, hf, measure_mono_null (diff_subset_diff_left hAB) hnull⟩

theorem isCountablyRectifiable_of_null {k : ℕ} {A : Set (Rn n)} (hA : hausdorffN n k A = 0) :
    IsCountablyRectifiable n k A :=
  ⟨fun _ _ => 0, fun _ => ⟨0, LipschitzWith.const 0⟩, measure_mono_null diff_subset hA⟩

/-- A countable union of countably `ℋ^k`-rectifiable sets is countably `ℋ^k`-rectifiable. -/
theorem isCountablyRectifiable_iUnion {k : ℕ} {ι : Type*} [Countable ι] {A : ι → Set (Rn n)}
    (hA : ∀ i, IsCountablyRectifiable n k (A i)) : IsCountablyRectifiable n k (⋃ i, A i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [iUnion_of_empty]
    exact isCountablyRectifiable_of_null (measure_empty)
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  choose f hf hnull using hA
  refine ⟨fun m => f (e m.unpair.1) m.unpair.2, fun m => hf _ _, ?_⟩
  refine measure_mono_null ?_ (measure_iUnion_null hnull)
  rintro x ⟨hxA, hx⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hxA
  refine mem_iUnion.2 ⟨i, hi, fun hxf => hx ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 hxf
  obtain ⟨m, rfl⟩ := he i
  refine mem_iUnion.2 ⟨Nat.pair m j, ?_⟩
  simpa [Nat.unpair_pair] using hj

theorem isCountablyRectifiable_biUnion {k : ℕ} {ι : Type*} {s : Set ι} (hs : s.Countable)
    {A : ι → Set (Rn n)} (hA : ∀ i ∈ s, IsCountablyRectifiable n k (A i)) :
    IsCountablyRectifiable n k (⋃ i ∈ s, A i) := by
  haveI := hs.to_subtype
  rw [biUnion_eq_iUnion]
  exact isCountablyRectifiable_iUnion fun i => hA i i.2

theorem IsCountablyRectifiable.union {k : ℕ} {A B : Set (Rn n)}
    (hA : IsCountablyRectifiable n k A) (hB : IsCountablyRectifiable n k B) :
    IsCountablyRectifiable n k (A ∪ B) := by
  rw [union_eq_iUnion]
  exact isCountablyRectifiable_iUnion fun b => by cases b <;> assumption

end InnerVariational.NaberValtorta
