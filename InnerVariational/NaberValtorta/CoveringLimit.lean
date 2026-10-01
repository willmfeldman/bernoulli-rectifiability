/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Covering
public import InnerVariational.NaberValtorta.Rectifiable
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.NaberValtorta.Hausdorff
public import InnerVariational.NaberValtorta.Data
import InnerVariational.Basic.Polar

/-!
# Theorem 7.2 (2)–(3): the case `t = 0`

Theorem 7.2 (2) and (3) of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for abstract data.
The set is `S = J.S` of a `JonesData` `J` with `t = 0` (the paper's `Σ^H`). The covering tree
needs the dichotomy (Theorem 6.3), which the abstract data only provide at scales `≥ s > 0`. So
we assume that for every `s > 0` there is an `NVData` `D_s` with `D_s.t ≤ s` that contains
`J.S ∩ B̄_{5r₀}(c)` and has the same frequencies there (for a variational solution:
`D_s.S = Σ^H_s ∩ K`, see `NaberValtorta/Instance.lean`).

## Main statement

`hausdorffN_le_and_rectifiable_and_frequency`: there is `C = C(n, CJ, N₊, ε)` such that for
`2 r₀ ≤ R`:

1. `|B_s(S ∩ B_{r₀}(c))| ≤ C s r₀^{n-1}` for `0 < s ≤ r₀` (Theorem 7.2 (1) for `D_s`);
2. `ℋ^{n-1}(S ∩ B_{r₀}(c)) ≤ C r₀^{n-1}` (Minkowski ⇒ Hausdorff), and `S ∩ B_{r₀}(c)` is
   countably `ℋ^{n-1}`-rectifiable;
3. `N_x(0+) = 1` for `ℋ^{n-1}`-a.e. `x ∈ S ∩ B_{r₀}(c)`.

## Proof of (2)–(3) (`exists_null_cover`)

Fix `δ₁ > 0` and `δ₂ = min(δ₁, 1/20, 1/(4 C_S))`. For `m ∈ ℕ` run the covering tree of
`D_m = D_{r₀ δ₂^m}` down to generation `m`. Every point of `S ∩ B_{r₀}(c)` lies in a terminal
ball `B̄_{r_j}(x)`, `j < m`, or in a ball of generation `m`. On `B_{2 r_j}(x)` the frequencies of
`J` satisfy `N_z(40 r_j) < 1 + δ₁`, so Lemma 7.1 (3) applies there. The points that lie in a ball
of generation `m` for **every** `m` form a set `A` with `ℋ^{n-1}(A) = 0`, because
`#(generation m) · r_m^{n-1} ≤ C 2^{-m}`. The paper shows `ℋ^{n-2+τ}(A) < ∞` instead
(in its proof of (2)), which is stronger than needed.

(2) then follows from Lemma 7.1 (3) on the countably many good balls. For (3), use
`δ₁ = 1/(k+1)` for all `k`: off the null set `⋃_k A_k`, every `x` lies in good balls with
`N_x(0+) ≤ N_x(20 ρ) < 1 + 1/(k+1)` for all `k`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-- **The null set and the good balls** (proof of Theorem 7.2 (2)–(3)). Fix `δ₁ > 0`. Every
point of `S ∩ B_{r₀}(c)` lies in an `ℋ^{n-1}`-null set `A` or in one of countably many balls
`B_ρ(x)`, `0 < ρ ≤ R`, on which `N_z(20 ρ) < 1 + δ₁` for all `z ∈ S ∩ B_ρ(x)`. -/
theorem exists_null_cover (hn : 2 ≤ n) {CJ Nplus : ℝ} {ε : ℝ → ℝ}
    (hε : ∀ δ, 0 < δ → 0 < ε δ) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) (J : JonesData n CJ) (c : Rn n)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀J : 2 * r₀ ≤ J.R)
    (hD : ∀ s, 0 < s → ∃ D : NVData n CJ Nplus ε, D.t ≤ s ∧
      J.S ∩ closedBall c (5 * r₀) ⊆ D.S ∧ (∀ z ∈ J.S ∩ closedBall c (5 * r₀), D.N z = J.N z) ∧
      2 * r₀ ≤ D.R ∧ closedBall c (5 * r₀) ⊆ D.K) :
    ∃ A : Set (Rn n), hausdorffN n (n - 1) A = 0 ∧ ∃ B : Set (Rn n × ℝ), B.Countable ∧
      (∀ p ∈ B, 0 < p.2 ∧ p.2 ≤ J.R ∧ ∀ z ∈ J.S ∩ ball p.1 p.2, J.N z (20 * p.2) < 1 + δ₁) ∧
      J.S ∩ ball c r₀ ⊆ A ∪ ⋃ p ∈ B, ball p.1 p.2 := by
  classical
  have hCS := tubeConst_pos n
  set δ₂ := min (min δ₁ (1 / 20)) (1 / (4 * tubeConst n)) with hδ₂_def
  have hδ₂ : 0 < δ₂ := lt_min (lt_min hδ₁ (by norm_num)) (by positivity)
  have hδ₂₁ : δ₂ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₂20 : δ₂ ≤ 1 / 20 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₂1 : δ₂ < 1 := by linarith
  have hδ₂2 : δ₂ ≤ 1 / 2 := by linarith
  have hδ₂CS : 2 * tubeConst n * δ₂ ≤ 1 / 2 := by
    have h : δ₂ ≤ 1 / (4 * tubeConst n) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hε₂ := hε δ₂ hδ₂
  have hθ : 0 < weightBase n δ₂ := zero_lt_one.trans_le (one_le_weightBase n δ₂)
  set M := 3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) with hM
  have hM0 : 0 < M := by positivity
  have hrj0 : ∀ j : ℕ, 0 < r₀ * δ₂ ^ j := fun j => by positivity
  have hrjr₀ : ∀ j : ℕ, r₀ * δ₂ ^ j ≤ r₀ := fun j =>
    mul_le_of_le_one_right hr₀.le (pow_le_one₀ hδ₂.le hδ₂1.le)
  have hrjle : ∀ i j : ℕ, i ≤ j → r₀ * δ₂ ^ j ≤ r₀ * δ₂ ^ i := fun i j hij =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ₂.le hδ₂1.le hij) hr₀.le
  choose D hDt hDS hDN hDR hDK using fun m : ℕ => hD (r₀ * δ₂ ^ m) (hrj0 m)
  set G : ℕ → ℕ → Finset (Rn n) := fun m => coverGen (D m).S (D m).N δ₁ δ₂ c r₀ with hG
  -- the null set: points in a ball of generation `m` of the `m`-th tree, for every `m`
  set A : Set (Rn n) := {z | ∀ m, z ∈ ⋃ x ∈ G m m, closedBall x (r₀ * δ₂ ^ m)} with hA
  have hcount : ∀ m, ((G m m).card : ℝ) * (r₀ * δ₂ ^ m) ^ (n - 1) ≤
      M * r₀ ^ (n - 1) * (1 / 2) ^ m := fun m =>
    (D m).card_mul_pow_le hn hδ₂ hδ₂₁ hδ₂20 hε₂ hr₀ (hDR m) (hDK m) hδ₂CS m (hDt m)
  set K : ℝ := 2 ^ (n - 1) * M * r₀ ^ (n - 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hAj : ∀ j : ℕ, hausdorffN n (n - 1) A ≤
      ENNReal.ofReal (unitBallVolume (n - 1) / 2 ^ (n - 1) * (K * (1 / 2) ^ j)) := by
    intro j
    refine hausdorffN_le_of_cover (fun m => G (m + j) (m + j)) (fun m => r₀ * δ₂ ^ (m + j))
      ?_ (fun m => (hrj0 _).le) (fun m z hz => hz (m + j)) (fun m => ?_)
    · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hδ₂.le hδ₂1).comp
        (tendsto_add_atTop_nat j)).const_mul r₀
      simpa using h
    · calc ((G (m + j) (m + j)).card : ℝ) * (2 * (r₀ * δ₂ ^ (m + j))) ^ (n - 1)
          = 2 ^ (n - 1) * (((G (m + j) (m + j)).card : ℝ) * (r₀ * δ₂ ^ (m + j)) ^ (n - 1)) := by
            rw [mul_pow]
            ring
        _ ≤ 2 ^ (n - 1) * (M * r₀ ^ (n - 1) * (1 / 2) ^ (m + j)) :=
            mul_le_mul_of_nonneg_left (hcount _) (by positivity)
        _ ≤ 2 ^ (n - 1) * (M * r₀ ^ (n - 1) * (1 / 2) ^ j) := by
            have hp : (1 / 2 : ℝ) ^ (m + j) ≤ (1 / 2) ^ j :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left j m)
            have h1 : 0 ≤ M * r₀ ^ (n - 1) := by positivity
            have h2 : (0 : ℝ) ≤ 2 ^ (n - 1) := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp h1) h2
        _ = K * (1 / 2) ^ j := by rw [hK]; ring
  have hAnull : hausdorffN n (n - 1) A = 0 := by
    have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (unitBallVolume (n - 1) / 2 ^ (n - 1) * K)
    rw [mul_zero] at h0
    have h1 := ENNReal.tendsto_ofReal h0
    rw [ENNReal.ofReal_zero] at h1
    have h2 : Tendsto (fun j : ℕ => ENNReal.ofReal
        (unitBallVolume (n - 1) / 2 ^ (n - 1) * (K * (1 / 2) ^ j))) atTop (𝓝 0) :=
      h1.congr fun j => by congr 1; ring
    exact le_antisymm (ge_of_tendsto' h2 hAj) zero_le
  refine ⟨A, hAnull, ?_⟩
  -- the good balls: `B_{2 r_j}(x)` for the terminal centres `x` of generation `j < m`
  set B : Set (Rn n × ℝ) := ⋃ m : ℕ, ⋃ j ∈ Finset.range m,
    (fun x => (x, 2 * (r₀ * δ₂ ^ j))) ''
      {x | x ∈ G m j ∧ maxFrequency (D m).S (D m).N x (2 * (r₀ * δ₂ ^ j)) < 1 + δ₁} with hB
  refine ⟨B, ?_, ?_, ?_⟩
  · refine countable_iUnion fun m => (Finset.range m).countable_toSet.biUnion fun j _ => ?_
    exact ((G m j).countable_toSet.mono fun x hx => hx.1).image _
  · intro p hp
    obtain ⟨m, hp⟩ := mem_iUnion.1 hp
    obtain ⟨j, hj, hp⟩ := mem_iUnion₂.1 hp
    obtain ⟨x, ⟨hx, hterm⟩, rfl⟩ := hp
    have hjm : j < m := Finset.mem_range.1 hj
    change 0 < 2 * (r₀ * δ₂ ^ j) ∧ 2 * (r₀ * δ₂ ^ j) ≤ J.R ∧
      ∀ z ∈ J.S ∩ ball x (2 * (r₀ * δ₂ ^ j)), J.N z (20 * (2 * (r₀ * δ₂ ^ j))) < 1 + δ₁
    refine ⟨by linarith [hrj0 j], by linarith [hrjr₀ j], fun z hz => ?_⟩
    have hdist := dist_lt_of_mem_coverGen hδ₂.le hδ₂2 hr₀.le j x hx
    have hzc : z ∈ J.S ∩ closedBall c (5 * r₀) := by
      refine ⟨hz.1, mem_closedBall.2 ?_⟩
      linarith [dist_triangle z x c, mem_ball.1 hz.2, hrj0 j]
    have hzD : z ∈ (D m).S ∩ closedBall x (2 * (r₀ * δ₂ ^ j)) :=
      ⟨hDS m hzc, ball_subset_closedBall hz.2⟩
    have htj : (D m).t < 20 * (2 * (r₀ * δ₂ ^ j)) := by
      linarith [hDt m, hrjle j m hjm.le, hrj0 j]
    calc J.N z (20 * (2 * (r₀ * δ₂ ^ j))) = (D m).N z (20 * (2 * (r₀ * δ₂ ^ j))) := by
          rw [hDN m z hzc]
      _ ≤ maxFrequency (D m).S (D m).N x (2 * (r₀ * δ₂ ^ j)) :=
          (D m).le_maxFrequency hzD htj (by linarith [hrjr₀ j, hDR m])
      _ < 1 + δ₁ := hterm
  · intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inl hzA
    right
    simp only [hA, mem_ofPred_eq, not_forall] at hzA
    obtain ⟨m, hm⟩ := hzA
    have hzm : z ∈ (D m).S ∩ ball c r₀ :=
      ⟨hDS m ⟨hz.1, ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
        hz.2⟩, hz.2⟩
    rcases mem_coverGen_or (N := (D m).N) (δ₁ := δ₁) hδ₂ hr₀ hzm m with
      ⟨j, hj, x, hx, hterm, hzx⟩ | ⟨x, hx, hzx⟩
    · refine mem_iUnion₂.2 ⟨(x, 2 * (r₀ * δ₂ ^ j)), ?_, ?_⟩
      · exact mem_iUnion.2 ⟨m, mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hj, x, ⟨hx, hterm⟩, rfl⟩⟩
      · exact mem_ball.2 (by linarith [mem_closedBall.1 hzx, hrj0 j])
    · exact (hm (mem_iUnion₂.2 ⟨x, hx, hzx⟩)).elim

/-- **Theorem 7.2 (1)–(3) for `t = 0`**, for abstract data. There
is `C = C(n, CJ, N₊, ε)` with the following property. Let `J` be `JonesData` with `t = 0`,
`2 r₀ ≤ R`, and assume that for every `s > 0` some `NVData` `D` with `D.t ≤ s`, `2 r₀ ≤ D.R` and
`B̄_{5r₀}(c) ⊆ D.K` contains `J.S ∩ B̄_{5r₀}(c)` and has the frequencies of `J` there. Then

1. `|B_s(S ∩ B_{r₀}(c))| ≤ C s r₀^{n-1}` for `0 < s ≤ r₀`;
2. `ℋ^{n-1}(S ∩ B_{r₀}(c)) ≤ C r₀^{n-1}` and `S ∩ B_{r₀}(c)` is countably
   `ℋ^{n-1}`-rectifiable;
3. `N_x(r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e. `x ∈ S ∩ B_{r₀}(c)`. -/
theorem hausdorffN_le_and_rectifiable_and_frequency (hn : 2 ≤ n) (CJ Nplus : ℝ) (ε : ℝ → ℝ)
    (hε : ∀ δ, 0 < δ → 0 < ε δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : JonesData n CJ) (c : Rn n) (r₀ : ℝ), J.t = 0 → 0 < r₀ →
      2 * r₀ ≤ J.R →
      (∀ s, 0 < s → ∃ D : NVData n CJ Nplus ε, D.t ≤ s ∧
        J.S ∩ closedBall c (5 * r₀) ⊆ D.S ∧ (∀ z ∈ J.S ∩ closedBall c (5 * r₀), D.N z = J.N z) ∧
        2 * r₀ ≤ D.R ∧ closedBall c (5 * r₀) ⊆ D.K) →
      (∀ s, 0 < s → s ≤ r₀ →
        volume (thickening s (J.S ∩ ball c r₀)) ≤ ENNReal.ofReal (C * s * r₀ ^ (n - 1))) ∧
      hausdorffN n (n - 1) (J.S ∩ ball c r₀) ≤ ENNReal.ofReal (C * r₀ ^ (n - 1)) ∧
      IsCountablyRectifiable n (n - 1) (J.S ∩ ball c r₀) ∧
      hausdorffN n (n - 1) {x | x ∈ J.S ∩ ball c r₀ ∧ ¬ Tendsto (J.N x) (𝓝[>] 0) (𝓝 1)} = 0 := by
  have hn0 : 0 < n := by omega
  obtain ⟨C1, hC1, h1⟩ := volume_thickening_le hn CJ Nplus ε hε
  obtain ⟨δ3, hδ3, C3, -, h3⟩ := hausdorffN_le_and_rectifiable_of_frequency_lt hn CJ
  have hω := unitBallVolume_pos n
  have hω' := unitBallVolume_pos (n - 1)
  set C2 := 2 ^ (n - 1) * unitBallVolume (n - 1) * C1 / unitBallVolume n with hC2
  have hC2pos : 0 < C2 := by positivity
  refine ⟨C1 + C2, by positivity, fun J c r₀ ht hr₀ hr₀J hD => ?_⟩
  have hR : 0 < J.R := by linarith
  -- (1): Theorem 7.2 (1) for `D_s`
  have hvol : ∀ s, 0 < s → s ≤ r₀ →
      volume (thickening s (J.S ∩ ball c r₀)) ≤ ENNReal.ofReal (C1 * s * r₀ ^ (n - 1)) := by
    intro s hs hsr₀
    obtain ⟨D, hDt, hDS, -, hDR, hDK⟩ := hD s hs
    refine (measure_mono (thickening_subset_of_subset s
      (show J.S ∩ ball c r₀ ⊆ D.S ∩ ball c r₀ from fun z hz => ⟨hDS ⟨hz.1, ?_⟩, hz.2⟩))).trans
      (h1 D c r₀ hr₀ hDR hDK s hs hDt hsr₀)
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz.2
  refine ⟨fun s hs hsr₀ => (hvol s hs hsr₀).trans (ENNReal.ofReal_le_ofReal ?_), ?_, ?_, ?_⟩
  · have : 0 ≤ C2 * s * r₀ ^ (n - 1) := by positivity
    nlinarith
  · -- (2), Hausdorff bound: Minkowski ⇒ Hausdorff
    refine (hausdorffN_le_of_volume_thickening_le hn0 (A := J.S ∩ ball c r₀) (z := c) (ρ := r₀)
      (K := C1 * r₀ ^ (n - 1)) (inter_subset_right.trans ball_subset_closedBall) (by positivity)
      hr₀ fun s hs hsr₀ => (hvol s hs hsr₀).trans_eq (by congr 1; ring)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ C1 * r₀ ^ (n - 1) := by positivity
    have e : 2 ^ (n - 1) * unitBallVolume (n - 1) * (C1 * r₀ ^ (n - 1)) / unitBallVolume n =
        C2 * r₀ ^ (n - 1) := by rw [hC2]; ring
    rw [e]
    nlinarith
  · -- (2), rectifiability: Lemma 7.1 (3) on the good balls
    obtain ⟨A, hA, B, hBc, hB, hcov⟩ := exists_null_cover hn hε hδ3 J c hr₀ hr₀J hD
    refine IsCountablyRectifiable.mono (IsCountablyRectifiable.union
      (isCountablyRectifiable_of_null hA)
      (isCountablyRectifiable_biUnion hBc (A := fun p => J.S ∩ ball p.1 p.2) fun p hp =>
        (h3 J ht p.1 p.2 (hB p hp).1 (hB p hp).2.1 (hB p hp).2.2).2.2)) ?_
    intro z hz
    rcases hcov hz with hzA | hzB
    · exact Or.inl hzA
    · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hzB
      exact Or.inr (mem_iUnion₂.2 ⟨p, hp, hz.1, hzp⟩)
  · -- (3): the good balls for `δ₁ = 1/(k+1)`, `k ∈ ℕ`
    have hk : ∀ k : ℕ, ∃ A : Set (Rn n), hausdorffN n (n - 1) A = 0 ∧
        ∀ z ∈ J.S ∩ ball c r₀, z ∉ A → ∃ ρ, 0 < ρ ∧ ρ ≤ J.R ∧
          J.N z (20 * ρ) < 1 + 1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨A, hA, B, -, hB, hcov⟩ := exists_null_cover hn hε (by positivity : (0 : ℝ) <
        1 / ((k : ℝ) + 1)) J c hr₀ hr₀J hD
      refine ⟨A, hA, fun z hz hzA => ?_⟩
      rcases hcov hz with hzA' | hzB
      · exact (hzA hzA').elim
      obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hzB
      exact ⟨p.2, (hB p hp).1, (hB p hp).2.1, (hB p hp).2.2 z ⟨hz.1, hzp⟩⟩
    choose A hA hgood using hk
    refine measure_mono_null ?_ (measure_iUnion_null hA)
    rintro z ⟨hz, hzN⟩
    by_contra hzA
    simp only [mem_iUnion, not_exists] at hzA
    apply hzN
    have hzS := hz.1
    have hone : ∀ ρ, 0 < ρ → ρ ≤ 20 * J.R → 1 ≤ J.N z ρ := fun ρ hρ hρR =>
      J.one_le z hzS ρ ⟨by rw [ht]; exact hρ, hρR⟩
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 20 * J.R)] with ρ hρ
      exact ha.trans_le (hone ρ hρ.1 hρ.2.le)
    · obtain ⟨k, hkb⟩ := exists_nat_one_div_lt (by linarith : 0 < b - 1)
      obtain ⟨ρ, hρ, hρR, hρN⟩ := hgood k z hz (hzA k)
      filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 20 * ρ)] with ρ' hρ'
      calc J.N z ρ' ≤ J.N z (20 * ρ) :=
            J.monotoneOn z hzS ⟨by rw [ht]; exact hρ'.1, by linarith [hρ'.2]⟩
              ⟨by rw [ht]; positivity, by linarith⟩ hρ'.2.le
        _ < 1 + 1 / ((k : ℝ) + 1) := hρN
        _ < b := by linarith

end InnerVariational.NaberValtorta
