/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.HighestDensity
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import GMTFoundations.Defs.GMT

/-!
# Discrete measures and elementary properties of the Jones number

This file collects the elementary facts about the squared Jones number `jonesBetaSq` (defined in
§6.1) that the Naber–Valtorta argument of Lemma 7.1 uses, in D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2). The discrete measures are those of the discrete Reifenberg theorem of
A. Naber and D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and minimizing
harmonic maps*, Ann. of Math. (2) 185 (2017), no. 1, 131–227, Theorem 3.4 ([NV]).

* `discreteMeasure J c x = ∑_{j ∈ J} c_j δ_{x_j}`, a finite discrete measure, with its
  evaluation, integration and push-forward lemmas.
* `jonesBetaSq_discreteMeasure_eq_zero_of_disjoint`: `β²_μ(y, ρ) = 0` when the balls
  `B_{r_j}(x_j)` are disjoint and `ρ ≤ r_j` (equation (7.24)), because then at most one atom
  lies in `B_ρ(y)`.
* `jonesBetaSq_mul_le`: `β²_μ(y, aρ) ≤ a^{-(n+1)} β²_μ(y, ρ)` for `a ∈ (0, 1]` (the "elementary
  inequality" in the proof of Lemma 7.1).
* `lintegral_jonesBetaSq_le_tsum`: `∫_0^s β²_μ(y, ρ) dρ/ρ ≤ 19·20^{n+1} ∑_k β²_μ(y, s 20^{-k})`
  (the dyadic bound after (7.24)).
* `jonesBetaSq_map_affine`, `jonesBetaSq_smul`, `jonesBetaSq_smul_map_affine`: behaviour under
  `x ↦ p + σ x` and scalar multiples of the measure (the rescaling in the proof of Lemma 7.1).

## Notes on the paper

* The proof of Lemma 7.1 states the scaling inequality for `β_μ`, with a constant `C(n)` for
  `a ∈ [1/20, 1]`. We prove the `β²_μ` version, with the explicit constant `a^{-(n+1)}`. The
  direction is the one in the paper: shrinking the ball can only increase `β²`
  by the factor coming from the normalisation `r^{-(n+1)}`.
* After (7.24) the paper says "at most one of the `x_i` can be contained in `B_ρ(y)`" when
  `ρ < s`; the same holds for `ρ ≤ s`, which is what we use. Also, the positions `x_i` need not be
  distinct as long as all the atoms in the ball sit at one point
  (`jonesBetaSq_discreteMeasure_eq_zero`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ} {ι : Type*}

/-! ### Discrete measures -/

/-- The finite discrete measure `∑_{j ∈ J} c_j δ_{x_j}` on `ℝⁿ`. The measures of Lemma 7.1 are
`discreteMeasure J (fun _ => s^{n-1}) x` (proof of Lemma 7.1), and those of [NV, Theorem 3.4]
(`Registry.discrete_reifenberg`) are `discreteMeasure J (fun j => ω_{n-1} r_j^{n-1}) x`. -/
def discreteMeasure (J : Finset ι) (c : ι → ℝ≥0∞) (x : ι → Rn n) : Measure (Rn n) :=
  ∑ j ∈ J, c j • Measure.dirac (x j)

theorem discreteMeasure_apply (J : Finset ι) (c : ι → ℝ≥0∞) (x : ι → Rn n) (s : Set (Rn n)) :
    discreteMeasure J c x s = ∑ j ∈ J, c j * s.indicator 1 (x j) := by
  simp [discreteMeasure, Measure.coe_finsetSum, Measure.dirac_apply]

theorem lintegral_discreteMeasure (J : Finset ι) (c : ι → ℝ≥0∞) (x : ι → Rn n)
    (f : Rn n → ℝ≥0∞) :
    ∫⁻ z, f z ∂discreteMeasure J c x = ∑ j ∈ J, c j * f (x j) := by
  simp [discreteMeasure, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

theorem setLIntegral_discreteMeasure (J : Finset ι) (c : ι → ℝ≥0∞) (x : ι → Rn n)
    {s : Set (Rn n)} (hs : MeasurableSet s) (f : Rn n → ℝ≥0∞) :
    ∫⁻ z in s, f z ∂discreteMeasure J c x = ∑ j ∈ J, c j * s.indicator f (x j) := by
  rw [← lintegral_indicator hs, lintegral_discreteMeasure]

theorem map_discreteMeasure (J : Finset ι) (c : ι → ℝ≥0∞) (x : ι → Rn n) {T : Rn n → Rn n}
    (hT : Measurable T) :
    (discreteMeasure J c x).map T = discreteMeasure J c (T ∘ x) := by
  simp only [discreteMeasure, Measure.map_finset_sum hT.aemeasurable]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_smul _ hT.aemeasurable, Measure.map_dirac' hT]
  rfl

theorem smul_discreteMeasure (a : ℝ≥0∞) (J : Finset ι) (c : ι → ℝ≥0∞) (x : ι → Rn n) :
    a • discreteMeasure J c x = discreteMeasure J (fun j => a * c j) x := by
  simp [discreteMeasure, Finset.smul_sum, smul_smul]

/-! ### The terms of the infimum defining `jonesBetaSq` -/

/-- The quantity `r^{-(n-1)} ∫_{B_r(x)} ⟪y - p, ν⟫² / r² dμ(y)` inside the infimum defining
`jonesBetaSq`: the normalised `L²` distance of `μ⌊B_r(x)` to the hyperplane through `p` with
normal `ν`. -/
def jonesTerm (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) (p ν : Rn n) : ℝ≥0∞ :=
  (∫⁻ y in ball x r, ENNReal.ofReal (⟪y - p, ν⟫ ^ 2 / r ^ 2) ∂μ) / ENNReal.ofReal (r ^ (n - 1))

theorem jonesBetaSq_eq_iInf (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    jonesBetaSq μ x r = ⨅ (p : Rn n) (ν : Rn n) (_ : ‖ν‖ = 1), jonesTerm μ x r p ν :=
  rfl

theorem jonesBetaSq_le_jonesTerm (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) (p : Rn n)
    {ν : Rn n} (hν : ‖ν‖ = 1) : jonesBetaSq μ x r ≤ jonesTerm μ x r p ν :=
  (iInf_le _ p).trans <| (iInf_le _ ν).trans <| iInf_le _ hν

theorem mul_jonesBetaSq {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) (μ : Measure (Rn n)) (x : Rn n)
    (r : ℝ) :
    c * jonesBetaSq μ x r = ⨅ (p : Rn n) (ν : Rn n) (_ : ‖ν‖ = 1), c * jonesTerm μ x r p ν := by
  simp_rw [jonesBetaSq_eq_iInf, ENNReal.mul_iInf_of_ne hc₀ hc]

/-- A unit vector in `ℝⁿ`, `n > 0`. -/
theorem exists_norm_eq_one (hn : 0 < n) : ∃ ν : Rn n, ‖ν‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩

/-! ### Vanishing -/

/-- `β²_μ(y, ρ) = 0` when `μ⌊B_ρ(y)` is concentrated at one point `p`: take any hyperplane
through `p`. -/
theorem jonesBetaSq_eq_zero_of_measure_diff_singleton (hn : 0 < n) {μ : Measure (Rn n)}
    {y p : Rn n} {ρ : ℝ} (h : μ (ball y ρ \ {p}) = 0) : jonesBetaSq μ y ρ = 0 := by
  obtain ⟨ν, hν⟩ := exists_norm_eq_one hn
  refine le_antisymm ((jonesBetaSq_le_jonesTerm μ y ρ p hν).trans (le_of_eq ?_)) zero_le
  have hae : ∀ᵐ z ∂μ.restrict (ball y ρ), ENNReal.ofReal (⟪z - p, ν⟫ ^ 2 / ρ ^ 2) = 0 := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with z hz hzb
    have hzp : z = p := by
      by_contra hne
      exact hz ⟨hzb, hne⟩
    simp [hzp]
  rw [jonesTerm, lintegral_congr_ae hae, lintegral_zero, ENNReal.zero_div]

/-- `β²_μ(y, ρ) = 0` for `ρ ≤ 0`, since the ball is empty. -/
theorem jonesBetaSq_of_nonpos (hn : 0 < n) (μ : Measure (Rn n)) (y : Rn n) {ρ : ℝ}
    (hρ : ρ ≤ 0) : jonesBetaSq μ y ρ = 0 :=
  jonesBetaSq_eq_zero_of_measure_diff_singleton (p := y) hn (by simp [ball_eq_empty.2 hρ])

/-- `β²_μ(y, ρ) = 0` for a discrete measure all of whose atoms in `B_ρ(y)` sit at one point
(equation (7.24)). -/
theorem jonesBetaSq_discreteMeasure_eq_zero (hn : 0 < n) {J : Finset ι} {c : ι → ℝ≥0∞}
    {x : ι → Rn n} {y : Rn n} {ρ : ℝ}
    (h : ∀ i ∈ J, ∀ j ∈ J, x i ∈ ball y ρ → x j ∈ ball y ρ → x i = x j) :
    jonesBetaSq (discreteMeasure J c x) y ρ = 0 := by
  have hp : ∃ p, ∀ j ∈ J, x j ∉ ball y ρ \ {p} := by
    by_cases hex : ∃ i ∈ J, x i ∈ ball y ρ
    · obtain ⟨i, hi, hxi⟩ := hex
      exact ⟨x i, fun j hj hxj => hxj.2 (h j hj i hi hxj.1 hxi)⟩
    · push Not at hex
      exact ⟨y, fun j hj hxj => hex j hj hxj.1⟩
  obtain ⟨p, hp⟩ := hp
  refine jonesBetaSq_eq_zero_of_measure_diff_singleton (p := p) hn ?_
  rw [discreteMeasure_apply]
  exact Finset.sum_eq_zero fun j hj => by simp [indicator_of_notMem (hp j hj)]

/-- `β²_μ(y, ρ) = 0` for `μ = ∑ c_j δ_{x_j}` when the balls `B_{r_j}(x_j)` are disjoint and
`ρ ≤ r_j` for all `j`: two atoms in `B_ρ(y)` would be at distance `< 2ρ ≤ r_i + r_j`
(equation (7.24), where `r_j = s`). -/
theorem jonesBetaSq_discreteMeasure_eq_zero_of_disjoint (hn : 0 < n) {J : Finset ι}
    {c : ι → ℝ≥0∞} {x : ι → Rn n} {r : ι → ℝ} (hr : ∀ j ∈ J, 0 < r j)
    (hdisj : (J : Set ι).Pairwise fun i j => Disjoint (ball (x i) (r i)) (ball (x j) (r j)))
    {y : Rn n} {ρ : ℝ} (hρ : ∀ j ∈ J, ρ ≤ r j) :
    jonesBetaSq (discreteMeasure J c x) y ρ = 0 := by
  refine jonesBetaSq_discreteMeasure_eq_zero hn fun i hi j hj hxi hxj => ?_
  by_contra hne
  have hij : i ≠ j := fun hij => hne (hij ▸ rfl)
  have hd := (disjoint_ball_ball_iff (hr i hi) (hr j hj)).1 (hdisj hi hj hij)
  have := dist_triangle_right (x i) (x j) y
  rw [mem_ball] at hxi hxj
  linarith [hρ i hi, hρ j hj]

/-! ### Change of radius -/

theorem jonesTerm_mul_le (hn : 0 < n) (μ : Measure (Rn n)) (y p ν : Rn n) {a ρ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hρ : 0 < ρ) :
    jonesTerm μ y (a * ρ) p ν ≤ ENNReal.ofReal (a⁻¹ ^ (n + 1)) * jonesTerm μ y ρ p ν := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : ∫⁻ z in ball y (a * ρ), ENNReal.ofReal (⟪z - p, ν⟫ ^ 2 / (a * ρ) ^ 2) ∂μ ≤
      ENNReal.ofReal (a⁻¹ ^ 2) * ∫⁻ z in ball y ρ, ENNReal.ofReal (⟪z - p, ν⟫ ^ 2 / ρ ^ 2) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (lintegral_mono_set (ball_subset_ball (by nlinarith))).trans
      (lintegral_mono fun z => le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hA : ENNReal.ofReal (a ^ m) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hA' : ENNReal.ofReal (a ^ m) ≠ ∞ := ENNReal.ofReal_ne_top
  have hreal : a⁻¹ ^ (m + 1 + 1) = a⁻¹ ^ 2 * (a ^ m)⁻¹ := by
    rw [inv_pow, inv_pow, ← mul_inv, ← pow_add]
    ring
  rw [jonesTerm, jonesTerm, Nat.add_sub_cancel, mul_pow a ρ m,
    ENNReal.ofReal_mul (pow_nonneg ha.le m), hreal, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos (by positivity),
    div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hA) (Or.inl hA')]
  calc (∫⁻ z in ball y (a * ρ), ENNReal.ofReal (⟪z - p, ν⟫ ^ 2 / (a * ρ) ^ 2) ∂μ) *
        ((ENNReal.ofReal (a ^ m))⁻¹ * (ENNReal.ofReal (ρ ^ m))⁻¹)
      ≤ (ENNReal.ofReal (a⁻¹ ^ 2) * ∫⁻ z in ball y ρ, ENNReal.ofReal (⟪z - p, ν⟫ ^ 2 / ρ ^ 2) ∂μ) *
        ((ENNReal.ofReal (a ^ m))⁻¹ * (ENNReal.ofReal (ρ ^ m))⁻¹) := by gcongr
    _ = _ := by ring

/-- **Change of radius** (proof of Lemma 7.1): for `0 < a ≤ 1`,
`β²_μ(y, aρ) ≤ a^{-(n+1)} β²_μ(y, ρ)`. The ball shrinks, and the normalisation `r^{-(n+1)}`
costs the factor `a^{-(n+1)}`. -/
theorem jonesBetaSq_mul_le (hn : 0 < n) (μ : Measure (Rn n)) (y : Rn n) {a ρ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    jonesBetaSq μ y (a * ρ) ≤ ENNReal.ofReal (a⁻¹ ^ (n + 1)) * jonesBetaSq μ y ρ := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [jonesBetaSq_of_nonpos hn μ y (mul_nonpos_of_nonneg_of_nonpos ha.le hρ)]
    exact zero_le
  have hc₀ : ENNReal.ofReal (a⁻¹ ^ (n + 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [mul_jonesBetaSq hc₀ ENNReal.ofReal_ne_top]
  refine le_iInf fun p => le_iInf fun ν => le_iInf fun hν => ?_
  exact (jonesBetaSq_le_jonesTerm μ y _ p hν).trans (jonesTerm_mul_le hn μ y p ν ha ha1 hρ)

/-- The change-of-radius inequality in the form used for the dyadic decomposition: for
`ρ ∈ (t/20, t]`, `β²_μ(y, ρ) ≤ 20^{n+1} β²_μ(y, t)`. -/
theorem jonesBetaSq_le_of_mem_Ioc (hn : 0 < n) (μ : Measure (Rn n)) (y : Rn n) {t ρ : ℝ}
    (hρ : ρ ∈ Ioc (t / 20) t) :
    jonesBetaSq μ y ρ ≤ ENNReal.ofReal (20 ^ (n + 1)) * jonesBetaSq μ y t := by
  obtain ⟨h1, h2⟩ := hρ
  have ht : 0 < t := by linarith [show 0 ≤ t / 20 from by linarith]
  have hρ0 : 0 < ρ := by linarith
  have ha : 0 < ρ / t := div_pos hρ0 ht
  have hρt : ρ = ρ / t * t := by field_simp
  calc jonesBetaSq μ y ρ = jonesBetaSq μ y (ρ / t * t) := by rw [← hρt]
    _ ≤ ENNReal.ofReal ((ρ / t)⁻¹ ^ (n + 1)) * jonesBetaSq μ y t :=
      jonesBetaSq_mul_le hn μ y ha ((div_le_one ht).2 h2)
    _ ≤ ENNReal.ofReal (20 ^ (n + 1)) * jonesBetaSq μ y t := by
      gcongr
      rw [inv_div, div_le_iff₀ hρ0]
      linarith

/-! ### Dyadic decomposition -/

/-- **Dyadic bound** (proof of Lemma 7.1):
`∫_0^s β²_μ(y, ρ) dρ/ρ ≤ 19 · 20^{n+1} ∑_k β²_μ(y, s 20^{-k})`.
The integral `dρ/ρ` is written `∫⁻ ρ in Ioo 0 s, _ / ENNReal.ofReal ρ`, as in
`Registry.discrete_reifenberg`. -/
theorem lintegral_jonesBetaSq_le_tsum (hn : 0 < n) (μ : Measure (Rn n)) (y : Rn n) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ ρ in Ioo 0 s, jonesBetaSq μ y ρ / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (19 * 20 ^ (n + 1)) * ∑' k : ℕ, jonesBetaSq μ y (s / 20 ^ k) := by
  have hcover : Ioo 0 s ⊆ ⋃ k : ℕ, Ioc (s / 20 ^ k / 20) (s / 20 ^ k) := by
    rintro ρ ⟨h0, hρs⟩
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := s / ρ) (y := (20 : ℝ))
      (by rw [le_div_iff₀ h0]; linarith) (by norm_num)
    have h20 : (0 : ℝ) < 20 ^ k := by positivity
    refine mem_iUnion.2 ⟨k, ?_, ?_⟩
    · rw [div_div, div_lt_iff₀ (by positivity), ← pow_succ]
      rw [div_lt_iff₀ h0] at hk2
      linarith
    · rw [le_div_iff₀ h20]
      rw [le_div_iff₀ h0] at hk1
      linarith
  have hpiece : ∀ k : ℕ, ∫⁻ ρ in Ioc (s / 20 ^ k / 20) (s / 20 ^ k),
      jonesBetaSq μ y ρ / ENNReal.ofReal ρ ≤
        ENNReal.ofReal (19 * 20 ^ (n + 1)) * jonesBetaSq μ y (s / 20 ^ k) := by
    intro k
    set t := s / 20 ^ k with ht_def
    have ht : 0 < t := by positivity
    have hbound : ∀ ρ ∈ Ioc (t / 20) t, jonesBetaSq μ y ρ / ENNReal.ofReal ρ ≤
        ENNReal.ofReal (20 ^ (n + 1)) * jonesBetaSq μ y t * ENNReal.ofReal (20 / t) := by
      intro ρ hρ
      have hρ0 : 0 < ρ := by linarith [hρ.1, show 0 < t / 20 from by positivity]
      rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hρ0]
      gcongr
      · exact jonesBetaSq_le_of_mem_Ioc hn μ y hρ
      · rw [inv_eq_one_div, div_le_div_iff₀ hρ0 ht]
        linarith [hρ.1]
    calc ∫⁻ ρ in Ioc (t / 20) t, jonesBetaSq μ y ρ / ENNReal.ofReal ρ
        ≤ ∫⁻ _ in Ioc (t / 20) t,
            ENNReal.ofReal (20 ^ (n + 1)) * jonesBetaSq μ y t * ENNReal.ofReal (20 / t) :=
          setLIntegral_mono' measurableSet_Ioc hbound
      _ = ENNReal.ofReal (20 ^ (n + 1)) * jonesBetaSq μ y t *
            (ENNReal.ofReal (20 / t) * ENNReal.ofReal (t - t / 20)) := by
          rw [setLIntegral_const, Real.volume_Ioc, mul_assoc]
      _ = ENNReal.ofReal (19 * 20 ^ (n + 1)) * jonesBetaSq μ y t := by
          rw [← ENNReal.ofReal_mul (by positivity),
            show 20 / t * (t - t / 20) = 19 by field_simp; ring,
            ENNReal.ofReal_mul (by norm_num), mul_comm (ENNReal.ofReal 19)]
          ring
  calc ∫⁻ ρ in Ioo 0 s, jonesBetaSq μ y ρ / ENNReal.ofReal ρ
      ≤ ∫⁻ ρ in ⋃ k : ℕ, Ioc (s / 20 ^ k / 20) (s / 20 ^ k),
          jonesBetaSq μ y ρ / ENNReal.ofReal ρ := lintegral_mono_set hcover
    _ ≤ ∑' k : ℕ, ∫⁻ ρ in Ioc (s / 20 ^ k / 20) (s / 20 ^ k),
          jonesBetaSq μ y ρ / ENNReal.ofReal ρ := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (19 * 20 ^ (n + 1)) * jonesBetaSq μ y (s / 20 ^ k) :=
      ENNReal.tsum_le_tsum hpiece
    _ = _ := ENNReal.tsum_mul_left

/-! ### Scaling and translation -/

theorem div_mul_eq_div_div_of_ne {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha : a ≠ ∞) (x b : ℝ≥0∞) :
    x / (a * b) = x / b / a := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha₀) (Or.inl ha),
    mul_comm a⁻¹, mul_assoc]

/-- The map `z ↦ p + σ z`, `σ ≠ 0`, is a measurable embedding of `ℝⁿ`. -/
theorem measurableEmbedding_affine {p : Rn n} {σ : ℝ} (hσ : σ ≠ 0) :
    MeasurableEmbedding fun z : Rn n => p + σ • z :=
  ((Homeomorph.smulOfNeZero σ hσ).trans (Homeomorph.addLeft p)).measurableEmbedding

theorem preimage_affine_ball {p : Rn n} {σ : ℝ} (hσ : 0 < σ) (y : Rn n) (ρ : ℝ) :
    (fun z : Rn n => p + σ • z) ⁻¹' ball (p + σ • y) (σ * ρ) = ball y ρ := by
  ext z
  simp only [mem_preimage, mem_ball, dist_add_left, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos hσ]
  exact mul_lt_mul_iff_right₀ hσ

theorem jonesTerm_map_affine (μ : Measure (Rn n)) {p : Rn n} {σ : ℝ} (hσ : 0 < σ)
    (y q ν : Rn n) (ρ : ℝ) :
    jonesTerm (μ.map fun z => p + σ • z) (p + σ • y) (σ * ρ) (p + σ • q) ν =
      jonesTerm μ y ρ q ν / ENNReal.ofReal (σ ^ (n - 1)) := by
  have hT := measurableEmbedding_affine (p := p) hσ.ne'
  have hA : ENNReal.ofReal (σ ^ (n - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [jonesTerm, jonesTerm, hT.restrict_map, hT.lintegral_map, preimage_affine_ball hσ,
    mul_pow σ ρ (n - 1), ENNReal.ofReal_mul (by positivity),
    div_mul_eq_div_div_of_ne hA ENNReal.ofReal_ne_top]
  congr 2
  refine lintegral_congr fun z => ?_
  simp only [add_sub_add_left_eq_sub, ← smul_sub, real_inner_smul_left]
  congr 1
  rw [mul_pow, mul_pow, mul_div_mul_left _ _ (by positivity)]

/-- **Scaling and translation** (proof of Lemma 7.1): for `T z = p + σ z`, `σ > 0`,
`β²_{T_# μ}(T y, σ ρ) = σ^{-(n-1)} β²_μ(y, ρ)`. -/
theorem jonesBetaSq_map_affine (μ : Measure (Rn n)) {p : Rn n} {σ : ℝ} (hσ : 0 < σ)
    (y : Rn n) (ρ : ℝ) :
    jonesBetaSq (μ.map fun z => p + σ • z) (p + σ • y) (σ * ρ) =
      jonesBetaSq μ y ρ / ENNReal.ofReal (σ ^ (n - 1)) := by
  have hA : ENNReal.ofReal (σ ^ (n - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hsurj : Function.Surjective fun q : Rn n => p + σ • q :=
    ((Homeomorph.smulOfNeZero σ hσ.ne').trans (Homeomorph.addLeft p)).surjective
  rw [jonesBetaSq_eq_iInf, jonesBetaSq_eq_iInf, ← hsurj.iInf_comp]
  simp_rw [jonesTerm_map_affine μ hσ, ENNReal.iInf_div_of_ne hA ENNReal.ofReal_ne_top]

/-- Scalar multiples: `β²_{cμ} = c β²_μ` for `c ≠ 0, ∞`. -/
theorem jonesBetaSq_smul {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) (μ : Measure (Rn n))
    (x : Rn n) (r : ℝ) : jonesBetaSq (c • μ) x r = c * jonesBetaSq μ x r := by
  rw [mul_jonesBetaSq hc₀ hc, jonesBetaSq_eq_iInf]
  simp only [jonesTerm, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, mul_div_assoc]

/-- Scale invariance (proof of Lemma 7.1): with `T z = p + σ z`, `σ > 0`, the measure
`σ^{n-1} T_# μ` has the same Jones numbers at `(T y, σ ρ)` as `μ` at `(y, ρ)`. This is how
Lemma 7.1 passes to the rescaled solution `u(p + σ ·)/σ` with the balls `B_{s/σ}((x_i − p)/σ)`. -/
theorem jonesBetaSq_smul_map_affine (μ : Measure (Rn n)) {p : Rn n} {σ : ℝ} (hσ : 0 < σ)
    (y : Rn n) (ρ : ℝ) :
    jonesBetaSq (ENNReal.ofReal (σ ^ (n - 1)) • μ.map fun z => p + σ • z) (p + σ • y) (σ * ρ) =
      jonesBetaSq μ y ρ := by
  have hA : ENNReal.ofReal (σ ^ (n - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [jonesBetaSq_smul hA ENNReal.ofReal_ne_top, jonesBetaSq_map_affine μ hσ,
    ENNReal.mul_div_cancel hA ENNReal.ofReal_ne_top]

end InnerVariational.NaberValtorta
