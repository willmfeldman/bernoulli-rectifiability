/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.VolumeEstimate
public import InnerVariational.NaberValtorta.Hausdorff
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
import InnerVariational.NaberValtorta.Reifenberg
import InnerVariational.NaberValtorta.Packing
public import InnerVariational.NaberValtorta.Data
import InnerVariational.Basic.Polar

/-!
# Lemma 7.1 (3): Hausdorff bound and rectifiability

Lemma 7.1 (3) of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for the abstract data
`JonesData` with `t = 0`. Let `S' = S ∩ B_r(x)` with `0 < r ≤ R` and `N_z(20 r) < 1 + δ` on `S'`.
Then `ℋ^{n-1}(S') ≤ C r^{n-1}` and `S'` is countably `ℋ^{n-1}`-rectifiable
(`hausdorffN_le_and_rectifiable_of_frequency_lt`).

## Proof

* **Hausdorff bound** (`hausdorffN_inter_ball_le`). Restricting the data to `B_r(x)`
  (`JonesData.restrict`), Lemma 7.1 (2) holds on every ball `B_ρ(w)`, `ρ ≤ r`. Minkowski ⇒
  Hausdorff (`hausdorffN_le_of_volume_thickening_le`) turns it into
  `ℋ^{n-1}(S' ∩ B_ρ(w)) ≤ C ρ^{n-1}`, for every `ρ > 0`.
* **Rectifiability.** Cover `B_r(x)` by finitely many balls `B_{r/2}(p)` and apply the rescaled
  rectifiable Reifenberg theorem (`rectifiable_reifenberg_ball`) of A. Naber and D. Valtorta,
  *Rectifiable-Reifenberg and the regularity of stationary and minimizing harmonic maps*, Ann. of
  Math. (2) 185 (2017), no. 1, 131–227, Theorem 3.3 ([NV]; rectifiability part, proved in
  gmt-foundations, https://github.com/willmfeldman/gmt-foundations, v0.1.0) to
  `T = S' ∩ B_r(p) ⊆ B_{2 · r/2}(p)`. Its hypothesis is checked in `setLIntegral_jonesBetaSq_le`,
  as in the paper's proof of (3): the dyadic bound, the Jones estimate for `ν = ℋ^{n-1}⌊T`
  (Theorem 6.1), Tonelli, the density bound `ν(B_ρ(w)) ≤ C ρ^{n-1}`, and the telescoping sum
  `Σ_k (N_w(20 a_k) − N_w(a_k)) ≤ N_w(20 τ) − 1 < δ`. Tonelli is where the measurability of
  `w ↦ N_w(ρ)` (`JonesData.measurable_N`) is used.

The paper applies [NV, Theorem 3.3] at the normalised scale `B_1` and checks the hypothesis only
for balls of radius `σ ≤ 1`, while [NV] needs it on every ball in `B_2`. The patches `T ⊆ B_r(p)`
keep every scale `≤ r ≤ R`, where the Jones estimate is available.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

namespace JonesData

variable {CJ : ℝ}

/-- The restriction of `JonesData` to `S ∩ A`, for a measurable `A`. The Jones estimate for
measures carried by `S ∩ A` is a special case of the one for measures carried by `S`. -/
def restrict (J : JonesData n CJ) (A : Set (Rn n)) (hA : MeasurableSet A) : JonesData n CJ where
  S := J.S ∩ A
  N := J.N
  t := J.t
  R := J.R
  t_nonneg := J.t_nonneg
  R_pos := J.R_pos
  measurableSet_S := J.measurableSet_S.inter hA
  measurable_N := J.measurable_N
  monotoneOn z hz := J.monotoneOn z hz.1
  one_le z hz := J.one_le z hz.1
  jones μ hμ hS y hy :=
    J.jones μ hμ (measure_mono_null (compl_subset_compl.2 inter_subset_left) hS) y hy.1

end JonesData

/-! ### Local volume and Hausdorff bounds -/

/-- **Lemma 7.1 (2) on smaller balls.** Under the hypotheses of Lemma 7.1 at `(x, r)`, for every
ball `B_ρ(w)` with `ρ ≤ r` and every `s ∈ [t, ρ]`, `s > 0`:
`|B_s(S ∩ B_r(x) ∩ B_ρ(w))| ≤ C s ρ^{n-1}`. -/
theorem volume_thickening_inter_ball_le (hn : 2 ≤ n) (CJ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (J : JonesData n CJ) (x : Rn n) (r : ℝ),
      0 < r → r ≤ J.R → (∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δ) →
      ∀ (w : Rn n) (ρ : ℝ), 0 < ρ → ρ ≤ r → ∀ s : ℝ, 0 < s → J.t ≤ s → s ≤ ρ →
        volume (thickening s (J.S ∩ ball x r ∩ ball w ρ)) ≤
          ENNReal.ofReal (C * s * ρ ^ (n - 1)) := by
  obtain ⟨δ, hδ, C, hC, h⟩ := volume_estimate_of_frequency_lt hn CJ
  refine ⟨δ, hδ, C, hC, fun J x r hr hrR hN w ρ hρ hρr s hs hts hsρ => ?_⟩
  refine (h (J.restrict (ball x r) measurableSet_ball) w ρ hρ (hρr.trans hrR)
    (fun z hz => ?_)).2 s hs hts hsρ
  have hz' : z ∈ J.S ∩ ball x r := hz.1
  have hρR : ρ ≤ J.R := hρr.trans hrR
  calc J.N z (20 * ρ) ≤ J.N z (20 * r) :=
        J.monotoneOn z hz'.1 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
          (by linarith)
    _ < 1 + δ := hN z hz'

/-- **Local Hausdorff bound** (proof of Lemma 7.1 (3)). Under the hypotheses of Lemma 7.1 at
`(x, r)` with `t = 0`: `ℋ^{n-1}(S ∩ B_r(x) ∩ B_ρ(w)) ≤ C ρ^{n-1}` for every ball `B_ρ(w)`. -/
theorem hausdorffN_inter_ball_le (hn : 2 ≤ n) (CJ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (J : JonesData n CJ), J.t = 0 →
      ∀ (x : Rn n) (r : ℝ), 0 < r → r ≤ J.R →
      (∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δ) →
      ∀ (w : Rn n) (ρ : ℝ), 0 < ρ →
        hausdorffN n (n - 1) (J.S ∩ ball x r ∩ ball w ρ) ≤ ENNReal.ofReal (C * ρ ^ (n - 1)) := by
  obtain ⟨δ, hδ, C, hC, h⟩ := volume_thickening_inter_ball_le hn CJ
  have hω := unitBallVolume_pos n
  have hω' := unitBallVolume_pos (n - 1)
  set C' := 2 ^ (n - 1) * unitBallVolume (n - 1) * C / unitBallVolume n with hC'
  have hC'0 : 0 < C' := by positivity
  refine ⟨δ, hδ, C', hC'0, fun J ht x r hr hrR hN => ?_⟩
  have hsmall : ∀ (w : Rn n) (ρ : ℝ), 0 < ρ → ρ ≤ r →
      hausdorffN n (n - 1) (J.S ∩ ball x r ∩ ball w ρ) ≤ ENNReal.ofReal (C' * ρ ^ (n - 1)) := by
    intro w ρ hρ hρr
    have key := hausdorffN_le_of_volume_thickening_le (by omega)
      (A := J.S ∩ ball x r ∩ ball w ρ) (z := w) (ρ := ρ) (K := C * ρ ^ (n - 1))
      (inter_subset_right.trans ball_subset_closedBall) (by positivity) hρ
      (fun s hs hsρ => by
        refine (h J x r hr hrR hN w ρ hρ hρr s hs (by rw [ht]; exact hs.le) hsρ).trans_eq ?_
        congr 1
        ring)
    refine key.trans_eq ?_
    congr 1
    rw [hC']
    ring
  intro w ρ hρ
  rcases le_or_gt ρ r with hρr | hρr
  · exact hsmall w ρ hρ hρr
  · calc hausdorffN n (n - 1) (J.S ∩ ball x r ∩ ball w ρ)
        ≤ hausdorffN n (n - 1) (J.S ∩ ball x r ∩ ball x r) :=
          measure_mono fun z hz => ⟨hz.1, hz.1.2⟩
      _ ≤ ENNReal.ofReal (C' * r ^ (n - 1)) := hsmall x r hr le_rfl
      _ ≤ ENNReal.ofReal (C' * ρ ^ (n - 1)) := by
          gcongr

/-! ### The Reifenberg integral for `ℋ^{n-1}⌊T` -/

/-- **The hypothesis of the rectifiable Reifenberg theorem** (proof of Lemma 7.1 (3)). Let `t = 0`,
`T ⊆ S` measurable with `ℋ^{n-1}(T) < ∞`, `ℋ^{n-1}(T ∩ B_ρ(w)) ≤ C_H ρ^{n-1}` for all balls, and
`N_w(20 τ) ≤ 1 + δ` on `T`, with `τ ≤ R`. Then, for `ν = ℋ^{n-1}⌊T`,
`∫_{T ∩ B_τ(y)} ∫_0^τ β²_ν(z, ρ) dρ/ρ dℋ^{n-1}(z) ≤ A max(CJ, 1) C_H² 2^{n-1} δ τ^{n-1}`
with `A = 19 · 20^{n+1}`. -/
theorem setLIntegral_jonesBetaSq_le (hn : 2 ≤ n) {CJ : ℝ} (J : JonesData n CJ) (ht : J.t = 0)
    {T : Set (Rn n)} (hTm : MeasurableSet T) (hTS : T ⊆ J.S)
    (hTfin : hausdorffN n (n - 1) T < ∞) {CH δ : ℝ} (hCH : 0 ≤ CH) (hδ : 0 ≤ δ)
    (hloc : ∀ (w : Rn n) (ρ : ℝ), 0 < ρ →
      hausdorffN n (n - 1) (T ∩ ball w ρ) ≤ ENNReal.ofReal (CH * ρ ^ (n - 1)))
    (y : Rn n) {τ : ℝ} (hτ : 0 < τ) (hτR : τ ≤ J.R)
    (hN : ∀ w ∈ T, J.N w (20 * τ) ≤ 1 + δ) :
    ∫⁻ z in T ∩ ball y τ, (∫⁻ ρ in Ioo 0 τ,
        jonesBetaSq ((hausdorffN n (n - 1)).restrict T) z ρ / ENNReal.ofReal ρ)
        ∂hausdorffN n (n - 1) ≤
      ENNReal.ofReal (19 * 20 ^ (n + 1) * (max CJ 1 * CH) * δ * (CH * (2 * τ) ^ (n - 1))) := by
  classical
  have hn0 : 0 < n := by omega
  set ℋ := hausdorffN n (n - 1) with hℋ
  set ν := ℋ.restrict T with hν
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hTfin.ne
  set κ := ℋ.restrict (T ∩ ball y τ) with hκ
  have : IsFiniteMeasure κ :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hTfin.ne (measure_mono inter_subset_left))
  have hνS : ν J.Sᶜ = 0 := by
    rw [hν, Measure.restrict_apply' hTm]
    exact measure_mono_null (fun w hw => (hw.1 (hTS hw.2)).elim) measure_empty
  have htpos : ∀ ρ : ℝ, 0 < ρ → J.t < ρ := fun ρ h => by rw [ht]; exact h
  have ha0 : ∀ k : ℕ, 0 < τ / 20 ^ k := fun k => by positivity
  have haτ : ∀ k : ℕ, τ / 20 ^ k ≤ τ := fun k => div_le_self hτ.le (one_le_pow₀ (by norm_num))
  set m := max CJ 1 with hm_def
  have hm : 0 < m := lt_max_of_lt_right one_pos
  set A : ℝ := 19 * 20 ^ (n + 1) with hA
  set G : ℕ → Rn n → ℝ≥0∞ := fun k w =>
    ENNReal.ofReal (J.N w (20 * (τ / 20 ^ k)) - J.N w (τ / 20 ^ k)) with hG
  have hGm : ∀ k, Measurable (G k) := fun k =>
    ENNReal.measurable_ofReal.comp
      ((J.measurable_N _ (by linarith [ha0 k]) (by linarith [haτ k])).sub
        (J.measurable_N _ (ha0 k) (by linarith [haτ k, ha0 k])))
  set Φ : ℕ → Rn n × Rn n → ℝ≥0∞ := fun k =>
    {p : Rn n × Rn n | dist p.2 p.1 < τ / 20 ^ k}.indicator (fun p => G k p.2) with hΦ
  have hΦm : ∀ k, Measurable (Φ k) := fun k =>
    ((hGm k).comp measurable_snd).indicator
      (measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const)
  have hΦball : ∀ k z w, Φ k (z, w) = (ball z (τ / 20 ^ k)).indicator (G k) w := by
    intro k z w
    simp only [hΦ, indicator_apply, mem_ofPred_eq, mem_ball]
  -- Step 1: the dyadic bound and the Jones estimate
  have hstep1 : ∀ z ∈ T ∩ ball y τ, ∫⁻ ρ in Ioo 0 τ, jonesBetaSq ν z ρ / ENNReal.ofReal ρ ≤
      ENNReal.ofReal A * ∑' k, ENNReal.ofReal (m / (τ / 20 ^ k) ^ (n - 1)) *
        ∫⁻ w, Φ k (z, w) ∂ν := by
    intro z hz
    refine (lintegral_jonesBetaSq_le_tsum hn0 ν z hτ).trans
      (mul_le_mul_right (ENNReal.tsum_le_tsum fun k => ?_) _)
    refine (J.jones ν hνfin hνS z (hTS hz.1) (τ / 20 ^ k) (ha0 k) (by rw [ht]; exact (ha0 k).le)
      ((haτ k).trans hτR)).trans ?_
    simp_rw [hΦball]
    rw [lintegral_indicator measurableSet_ball]
    gcongr
    exact le_max_left _ _
  -- Step 2: Tonelli and the density bound
  have hstep3 : ∀ k, ∫⁻ z, ENNReal.ofReal (m / (τ / 20 ^ k) ^ (n - 1)) *
      ∫⁻ w, Φ k (z, w) ∂ν ∂κ ≤ ENNReal.ofReal (m * CH) * ∫⁻ w in ball y (2 * τ), G k w ∂ν := by
    intro k
    have hinner : ∀ w, ∫⁻ z, Φ k (z, w) ∂κ ≤ (ball y (2 * τ)).indicator
        (fun w => ENNReal.ofReal (CH * (τ / 20 ^ k) ^ (n - 1)) * G k w) w := by
      intro w
      have hΦw : (fun z => Φ k (z, w)) = (ball w (τ / 20 ^ k)).indicator (fun _ => G k w) := by
        ext z
        rw [hΦball]
        simp only [indicator_apply, mem_ball]
        rw [dist_comm]
      rw [hΦw, lintegral_indicator_const measurableSet_ball, hκ,
        Measure.restrict_apply measurableSet_ball]
      by_cases hw : w ∈ ball y (2 * τ)
      · rw [indicator_of_mem hw, mul_comm]
        gcongr
        calc ℋ (ball w (τ / 20 ^ k) ∩ (T ∩ ball y τ)) ≤ ℋ (T ∩ ball w (τ / 20 ^ k)) :=
              measure_mono fun v hv => ⟨hv.2.1, hv.1⟩
          _ ≤ _ := hloc w _ (ha0 k)
      · rw [indicator_of_notMem hw]
        have hempty : ball w (τ / 20 ^ k) ∩ (T ∩ ball y τ) = ∅ := by
          ext v
          simp only [mem_inter_iff, mem_ball, mem_empty_iff_false, iff_false]
          rintro ⟨h1, -, h2⟩
          apply hw
          rw [mem_ball]
          linarith [dist_triangle w v y, dist_comm v w, haτ k]
        rw [hempty, measure_empty, mul_zero]
    have hak : (τ / 20 ^ k) ^ (n - 1) ≠ 0 := by have := ha0 k; positivity
    calc ∫⁻ z, ENNReal.ofReal (m / (τ / 20 ^ k) ^ (n - 1)) * ∫⁻ w, Φ k (z, w) ∂ν ∂κ
        = ENNReal.ofReal (m / (τ / 20 ^ k) ^ (n - 1)) * ∫⁻ w, ∫⁻ z, Φ k (z, w) ∂κ ∂ν := by
          rw [lintegral_const_mul _ (hΦm k).lintegral_prod_right',
            lintegral_lintegral_swap (f := fun z w => Φ k (z, w)) (hΦm k).aemeasurable]
      _ ≤ ENNReal.ofReal (m / (τ / 20 ^ k) ^ (n - 1)) * ∫⁻ w, (ball y (2 * τ)).indicator
            (fun w => ENNReal.ofReal (CH * (τ / 20 ^ k) ^ (n - 1)) * G k w) w ∂ν := by
          gcongr with w
          exact hinner w
      _ = ENNReal.ofReal (m * CH) * ∫⁻ w in ball y (2 * τ), G k w ∂ν := by
          rw [lintegral_indicator measurableSet_ball,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
            ← ENNReal.ofReal_mul (by have := ha0 k; positivity)]
          congr 2
          field_simp
  -- Step 3: telescoping
  have htel : ∀ w ∈ T, ∑' k, G k w ≤ ENNReal.ofReal δ := by
    intro w hw
    have hwS := hTS hw
    refine ENNReal.tsum_le_of_sum_range_le fun M => ?_
    have hnn : ∀ k ∈ Finset.range M,
        0 ≤ J.N w (20 * (τ / 20 ^ k)) - J.N w (τ / 20 ^ k) := fun k _ =>
      sub_nonneg.2 (J.monotoneOn w hwS ⟨htpos _ (ha0 k), by linarith [haτ k, ha0 k]⟩
        ⟨htpos _ (by linarith [ha0 k]), by linarith [haτ k]⟩ (by linarith [ha0 k]))
    simp only [hG]
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    have hM0 : 0 < τ / 20 ^ M := ha0 M
    have hsM : ∀ k < M, τ / 20 ^ M / 2 < τ / 20 ^ k := fun k hk => by
      have h1 : τ / 20 ^ M ≤ τ / 20 ^ k :=
        div_le_div_of_nonneg_left hτ.le (by positivity) (pow_le_pow_right₀ (by norm_num) hk.le)
      linarith
    have h := sum_range_sub_le (f := J.N w) (t := J.t) (s := τ / 20 ^ M / 2) (τ := τ) (M := M)
      hsM (by positivity) (by rw [ht]; positivity) (by linarith [haτ M])
      (fun ρ hρ hρ' => J.one_le w hwS ρ ⟨hρ, by linarith⟩)
    linarith [hN w hw]
  have hstep4 : ∫⁻ w in ball y (2 * τ), ∑' k, G k w ∂ν ≤
      ENNReal.ofReal δ * ENNReal.ofReal (CH * (2 * τ) ^ (n - 1)) := by
    rw [hν, Measure.restrict_restrict measurableSet_ball]
    calc ∫⁻ w in ball y (2 * τ) ∩ T, ∑' k, G k w ∂ℋ
        ≤ ∫⁻ _w in ball y (2 * τ) ∩ T, ENNReal.ofReal δ ∂ℋ :=
          setLIntegral_mono' (measurableSet_ball.inter hTm) fun w hw => htel w hw.2
      _ = ENNReal.ofReal δ * ℋ (ball y (2 * τ) ∩ T) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (CH * (2 * τ) ^ (n - 1)) := by
          gcongr
          rw [inter_comm]
          exact hloc y (2 * τ) (by positivity)
  calc ∫⁻ z in T ∩ ball y τ, (∫⁻ ρ in Ioo 0 τ, jonesBetaSq ν z ρ / ENNReal.ofReal ρ) ∂ℋ
      ≤ ∫⁻ z in T ∩ ball y τ, ENNReal.ofReal A * ∑' k, ENNReal.ofReal (m / (τ / 20 ^ k) ^ (n - 1)) *
          ∫⁻ w, Φ k (z, w) ∂ν ∂ℋ := setLIntegral_mono' (hTm.inter measurableSet_ball) hstep1
    _ = ENNReal.ofReal A * ∑' k, ∫⁻ z, ENNReal.ofReal (m / (τ / 20 ^ k) ^ (n - 1)) *
          ∫⁻ w, Φ k (z, w) ∂ν ∂κ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_tsum fun k => ((hΦm k).lintegral_prod_right'.const_mul _).aemeasurable]
    _ ≤ ENNReal.ofReal A * ∑' k, ENNReal.ofReal (m * CH) * ∫⁻ w in ball y (2 * τ), G k w ∂ν := by
        gcongr with k
        exact hstep3 k
    _ = ENNReal.ofReal A * (ENNReal.ofReal (m * CH) * ∫⁻ w in ball y (2 * τ), ∑' k, G k w ∂ν) := by
        rw [ENNReal.tsum_mul_left, lintegral_tsum fun k => (hGm k).aemeasurable]
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (m * CH) *
          (ENNReal.ofReal δ * ENNReal.ofReal (CH * (2 * τ) ^ (n - 1)))) := by
        gcongr
    _ = ENNReal.ofReal (A * (m * CH) * δ * (CH * (2 * τ) ^ (n - 1))) := by
        rw [← ENNReal.ofReal_mul hδ, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ m * CH),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ A)]
        congr 1
        ring

/-! ### Lemma 7.1 (3) -/

/-- **Lemma 7.1 (3)**, for abstract data with `t = 0`. There
are `δ(n, CJ) > 0` and `C(n, CJ)` such that, if `0 < r ≤ R` and `N_z(20 r) < 1 + δ` for every
`z ∈ S ∩ B_r(x)`, then

* `ℋ^{n-1}(S ∩ B_r(x) ∩ B_ρ(w)) ≤ C ρ^{n-1}` for every ball `B_ρ(w)`;
* `ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}`;
* `S ∩ B_r(x)` is countably `ℋ^{n-1}`-rectifiable.

The rectifiability comes from the rescaled [NV, Theorem 3.3] (`rectifiable_reifenberg_ball`) on
the patches `S ∩ B_r(x) ∩ B_r(p) ⊆ B_{2 · r/2}(p)`, where `B_{r/2}(p)` runs over a finite cover
of `B_r(x)`. -/
theorem hausdorffN_le_and_rectifiable_of_frequency_lt (hn : 2 ≤ n) (CJ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (J : JonesData n CJ), J.t = 0 →
      ∀ (x : Rn n) (r : ℝ), 0 < r → r ≤ J.R →
      (∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δ) →
      (∀ (w : Rn n) (ρ : ℝ), 0 < ρ →
        hausdorffN n (n - 1) (J.S ∩ ball x r ∩ ball w ρ) ≤ ENNReal.ofReal (C * ρ ^ (n - 1))) ∧
      hausdorffN n (n - 1) (J.S ∩ ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) ∧
      IsCountablyRectifiable n (n - 1) (J.S ∩ ball x r) := by
  have hn0 : 0 < n := by omega
  obtain ⟨δH, hδH, CH, hCH, hH⟩ := hausdorffN_inter_ball_le hn CJ
  obtain ⟨δ6, hδ6, h6⟩ := rectifiable_reifenberg_ball (n := n) hn CH
  have hm : 0 < max CJ 1 := lt_max_of_lt_right one_pos
  set A : ℝ := 19 * 20 ^ (n + 1) * (max CJ 1 * CH) * (CH * 2 ^ (n - 1)) with hA
  have hA0 : 0 < A := by positivity
  set δ := min δH (δ6 ^ 2 / 2 / A) with hδ_def
  have hδ0 : 0 < δ := lt_min hδH (by positivity)
  have hδH' : δ ≤ δH := min_le_left _ _
  have hδA : A * δ ≤ δ6 ^ 2 / 2 := by
    have h : δ ≤ δ6 ^ 2 / 2 / A := min_le_right _ _
    rw [le_div_iff₀ hA0] at h
    linarith
  refine ⟨δ, hδ0, CH, hCH, ?_⟩
  intro J ht x r hr hrR hN
  have hN' : ∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δH := fun z hz =>
    (hN z hz).trans_le (by linarith)
  have hloc := hH J ht x r hr hrR hN'
  have htot : hausdorffN n (n - 1) (J.S ∩ ball x r) ≤ ENNReal.ofReal (CH * r ^ (n - 1)) := by
    have := hloc x r hr
    rwa [inter_assoc, inter_self] at this
  refine ⟨hloc, htot, ?_⟩
  obtain ⟨E, -, hE⟩ := exists_cover_ball x hr.le (by positivity : 0 < r / 2)
  refine IsCountablyRectifiable.mono (isCountablyRectifiable_biUnion E.countable_toSet
    (A := fun p => J.S ∩ ball x r ∩ ball p r ∩ ball p (r / 2)) fun p _ => ?_) ?_
  · set T := J.S ∩ ball x r ∩ ball p r with hT
    have hTm : MeasurableSet T :=
      (J.measurableSet_S.inter measurableSet_ball).inter measurableSet_ball
    have hTsub : T ⊆ ball p (2 * (r / 2)) := by
      rw [show 2 * (r / 2) = r by ring]
      exact inter_subset_right
    have hTS : T ⊆ J.S := fun z hz => hz.1.1
    have hTfin : hausdorffN n (n - 1) T < ∞ :=
      (measure_mono inter_subset_left).trans_lt (htot.trans_lt ENNReal.ofReal_lt_top)
    have hTloc : ∀ (w : Rn n) (ρ : ℝ), 0 < ρ →
        hausdorffN n (n - 1) (T ∩ ball w ρ) ≤ ENNReal.ofReal (CH * ρ ^ (n - 1)) :=
      fun w ρ hρ => (measure_mono (fun z hz => ⟨hz.1.1, hz.2⟩ :
        T ∩ ball w ρ ⊆ J.S ∩ ball x r ∩ ball w ρ)).trans (hloc w ρ hρ)
    refine h6 p (r / 2) (by positivity) T hTm hTsub hTfin hTloc fun y τ hτ hyτ => ?_
    have hτr : τ ≤ r := by
      have := le_of_ball_subset_ball hn0 hτ hyτ
      linarith
    have hτR : τ ≤ J.R := hτr.trans hrR
    refine lt_of_le_of_lt (setLIntegral_jonesBetaSq_le hn J ht hTm hTS hTfin hCH.le hδ0.le hTloc
      y hτ hτR fun w hw => ?_) ?_
    · have hw' : w ∈ J.S ∩ ball x r := hw.1
      calc J.N w (20 * τ) ≤ J.N w (20 * r) :=
            J.monotoneOn w hw'.1 ⟨by rw [ht]; linarith, by linarith⟩
              ⟨by rw [ht]; linarith, by linarith⟩ (by linarith)
        _ ≤ 1 + δ := (hN w hw').le
    · have hτn : 0 < τ ^ (n - 1) := by positivity
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      calc 19 * 20 ^ (n + 1) * (max CJ 1 * CH) * δ * (CH * (2 * τ) ^ (n - 1))
          = A * δ * τ ^ (n - 1) := by rw [hA, mul_pow]; ring
        _ ≤ δ6 ^ 2 / 2 * τ ^ (n - 1) := mul_le_mul_of_nonneg_right hδA hτn.le
        _ < δ6 ^ 2 * τ ^ (n - 1) := by
            have : 0 < δ6 ^ 2 * τ ^ (n - 1) := by positivity
            linarith
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 (hE hz.2)
    refine mem_iUnion₂.2 ⟨p, hp, ⟨⟨hz, ?_⟩, hzp⟩⟩
    exact ball_subset_ball (by linarith) hzp

end InnerVariational.NaberValtorta
