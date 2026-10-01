/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.VolumeEstimate
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import InnerVariational.NaberValtorta.Packing
public import InnerVariational.NaberValtorta.Data
import InnerVariational.Basic.Polar

/-!
# Theorem 7.2 (1): the Naber–Valtorta covering

The covering argument of Theorem 7.2 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite
Hausdorff measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure
Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2),
for the abstract data `NVData` (`NaberValtorta/Data.lean`).

## The covering tree

Fix `c`, `r₀` and parameters `δ₁`, `δ₂`, and write `r_k = r₀ δ₂^k`. The *potential* of a ball
`B_r(x)` is `P(x, r) = N^max(x, 2r) = sup {N_y(40 r) : y ∈ S ∩ B̄_{2r}(x)}`. A ball is *terminal*
if `P(x, r) < 1 + δ₁`.

* `coverGen S N δ₁ δ₂ c r₀ k` is the `Finset` of centres of generation `k`, all with radius
  `r_k`. Generation `0` is a maximal `r₀`-separated subset of `S ∩ B_{r₀}(c)`. The children of a
  non-terminal centre `x` of generation `k` form a maximal `δ₂ r_k`-separated subset of
  `S ∩ B̄_{r_k}(x)`.
* `mem_coverGen_or`: every point of `S ∩ B_{r₀}(c)` lies in a terminal ball of some generation
  `j < k` or in a ball of generation `k`.
* `dist_lt_of_mem_coverGen`: the centres of generation `k` lie in `B_{3r₀ − 2r_k}(c)`.

## Counting (the proof of Theorem 7.2, before (7.27))

The paper bounds `#U^k` by tracking the number of large frequency drops along each ancestry, by
`[C_S δ₂^{-n}]^D [C_L δ₂^{2−n}]^k`. The constants `C_S` and `C_L` appear interchanged there, and
a factor `Σ_{j ≤ D} binom(k, j)` for the positions of the large-drop steps is not written; this
does not affect the conclusion. We bound the count with a weighted argument instead, which needs
no combinatorial factor: a centre `x` of generation `k` gets the weight
`θ^{P(x, r_k)/ε₂}`, where `ε₂ = ε(δ₂)` and `θ = max(1, 3ⁿ/(C_S δ₂²))`.

The paper applies the dichotomy (Theorem 6.3) on `B_r(x)` and concludes that every
`y ∈ B_{δ₂ r}(x_i) ∩ Σ^H_t` of a child ball disjoint from the exceptional set has
`N_y(r) ≤ N^max_t(x, r) − ε`. That holds only for `y ∈ B̄_r(x)`, and the child balls stick out
of `B_r(x)`. Here the potential is `P(x, r) = N^max(x, 2r)` and the dichotomy is applied to
`B_{2r_k}(x)`, which contains every child ball `B̄_{2δ₂ r_k}(y)` since `δ₂ ≤ 1/20`. Then

* every child `y` has `P(y, r_{k+1}) ≤ P(x, r_k)`;
* a child at distance `≥ 4δ₂ r_k` from the subspace `L` has a large drop,
  `P(y, r_{k+1}) ≤ P(x, r_k) − ε₂`;
* at most `C_S δ₂^{2−n}` children are within `4δ₂ r_k` of `L` (`card_mul_le_of_subset_thickening`),
  and at most `(3/δ₂)ⁿ` children exist in total.

So the total weight grows by a factor at most `2 C_S δ₂^{2−n}` per generation
(`sum_weight_children_le`). The weights lie in `[1, θ^{N₊/ε₂}]`, which bounds
`#(generation k) ≤ 3ⁿ θ^{N₊/ε₂} (2 C_S δ₂^{2−n})^k`.

## Theorem 7.2 (1)

`volume_thickening_le`: for `s ∈ [t, r₀]`, `|B_s(S ∩ B_{r₀}(c))| ≤ C s r₀^{n−1}`. Stop at the
generation `K` with `r_K ∈ [s, s/δ₂)`. The terminal balls are handled by Lemma 7.1 (2) applied on
`B_{2r_j}(x)`, the balls of generation `K` by their volume. With `2 C_S δ₂ ≤ 1/2` the sums over
generations are geometric.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Maximal frequency -/

theorem maxFrequency_le {S : Set (Rn n)} {N : Rn n → ℝ → ℝ} {x : Rn n} {r M : ℝ}
    (hne : (S ∩ closedBall x r).Nonempty) (h : ∀ y ∈ S ∩ closedBall x r, N y (20 * r) ≤ M) :
    maxFrequency S N x r ≤ M :=
  csSup_le (hne.image _) (forall_mem_image.2 h)

namespace JonesData

variable {CJ : ℝ} (J : JonesData n CJ)

theorem N_le_N {z : Rn n} (hz : z ∈ J.S) {a b : ℝ} (ha : J.t < a) (hab : a ≤ b)
    (hb : b ≤ 20 * J.R) : J.N z a ≤ J.N z b :=
  J.monotoneOn z hz ⟨ha, hab.trans hb⟩ ⟨ha.trans_le hab, hb⟩ hab

end JonesData

namespace NVData

variable {CJ Nplus : ℝ} {ε : ℝ → ℝ} (D : NVData n CJ Nplus ε)

theorem bddAbove_maxFrequency (x : Rn n) {r : ℝ} (ht : D.t < 20 * r) (hr : r ≤ D.R) :
    BddAbove ((fun y => D.N y (20 * r)) '' (D.S ∩ closedBall x r)) :=
  ⟨Nplus, forall_mem_image.2 fun y hy => D.le_Nplus y hy.1 _ ⟨ht, by linarith⟩⟩

theorem le_maxFrequency {x y : Rn n} {r : ℝ} (hy : y ∈ D.S ∩ closedBall x r) (ht : D.t < 20 * r)
    (hr : r ≤ D.R) : D.N y (20 * r) ≤ maxFrequency D.S D.N x r :=
  le_csSup (D.bddAbove_maxFrequency x ht hr) (mem_image_of_mem _ hy)

theorem one_le_maxFrequency {x y : Rn n} {r : ℝ} (hy : y ∈ D.S ∩ closedBall x r)
    (ht : D.t < 20 * r) (hr : r ≤ D.R) : 1 ≤ maxFrequency D.S D.N x r :=
  (D.one_le y hy.1 _ ⟨ht, by linarith⟩).trans (D.le_maxFrequency hy ht hr)

theorem maxFrequency_le_Nplus {x : Rn n} {r : ℝ} (hne : (D.S ∩ closedBall x r).Nonempty)
    (ht : D.t < 20 * r) (hr : r ≤ D.R) : maxFrequency D.S D.N x r ≤ Nplus :=
  maxFrequency_le hne fun y hy => D.le_Nplus y hy.1 _ ⟨ht, by linarith⟩

end NVData

/-! ### The covering tree -/

open scoped Classical in
/-- The centres of generation `k` of the covering tree (proof of Theorem 7.2), all with radius
`r₀ δ₂^k`. Generation `0` is a maximal `r₀`-separated subset of `S ∩ B_{r₀}(c)`. The children of
a non-terminal centre `x` (`1 + δ₁ ≤ N^max(x, 2 r₀ δ₂^k)`) form a maximal
`δ₂ r₀ δ₂^k`-separated subset of `S ∩ B̄_{r₀ δ₂^k}(x)`. -/
def coverGen (S : Set (Rn n)) (N : Rn n → ℝ → ℝ) (δ₁ δ₂ : ℝ) (c : Rn n) (r₀ : ℝ) :
    ℕ → Finset (Rn n)
  | 0 => net (S ∩ ball c r₀) r₀
  | k + 1 => ((coverGen S N δ₁ δ₂ c r₀ k).filter fun x =>
        1 + δ₁ ≤ maxFrequency S N x (2 * (r₀ * δ₂ ^ k))).biUnion
      fun x => net (S ∩ closedBall x (r₀ * δ₂ ^ k)) (δ₂ * (r₀ * δ₂ ^ k))

section CoverGen

variable {S : Set (Rn n)} {N : Rn n → ℝ → ℝ} {δ₁ δ₂ : ℝ} {c : Rn n} {r₀ : ℝ}

open scoped Classical in
theorem mem_coverGen_succ {k : ℕ} {y : Rn n} :
    y ∈ coverGen S N δ₁ δ₂ c r₀ (k + 1) ↔ ∃ x ∈ coverGen S N δ₁ δ₂ c r₀ k,
      1 + δ₁ ≤ maxFrequency S N x (2 * (r₀ * δ₂ ^ k)) ∧
        y ∈ net (S ∩ closedBall x (r₀ * δ₂ ^ k)) (δ₂ * (r₀ * δ₂ ^ k)) := by
  simp only [coverGen, Finset.mem_biUnion, Finset.mem_filter, and_assoc]

theorem coverGen_subset (k : ℕ) : ↑(coverGen S N δ₁ δ₂ c r₀ k) ⊆ S := by
  cases k with
  | zero => exact (net_subset _ _).trans inter_subset_left
  | succ k =>
    intro y hy
    obtain ⟨x, -, -, hy⟩ := mem_coverGen_succ.1 (Finset.mem_coe.1 hy)
    exact (net_subset _ _ hy).1

theorem dist_lt_of_mem_coverGen (hδ₂ : 0 ≤ δ₂) (hδ₂' : δ₂ ≤ 1 / 2) (hr₀ : 0 ≤ r₀) :
    ∀ k : ℕ, ∀ x ∈ coverGen S N δ₁ δ₂ c r₀ k, dist x c < 3 * r₀ - 2 * (r₀ * δ₂ ^ k) := by
  intro k
  induction k with
  | zero =>
    intro x hx
    have := mem_ball.1 (net_subset _ _ hx).2
    simp only [pow_zero, mul_one]
    linarith
  | succ k ih =>
    intro y hy
    obtain ⟨x, hx, -, hy⟩ := mem_coverGen_succ.1 hy
    have h1 := mem_closedBall.1 (net_subset _ _ hy).2
    have h2 := ih x hx
    have hrk : 0 ≤ r₀ * δ₂ ^ k := by positivity
    rw [pow_succ, ← mul_assoc]
    nlinarith [dist_triangle y x c]

/-- **Coverage.** Every point of `S ∩ B_{r₀}(c)` lies in a terminal ball of a generation `j < k`
or in a ball of generation `k`. -/
theorem mem_coverGen_or (hδ₂ : 0 < δ₂) (hr₀ : 0 < r₀) {z : Rn n} (hz : z ∈ S ∩ ball c r₀) :
    ∀ k : ℕ, (∃ j < k, ∃ x ∈ coverGen S N δ₁ δ₂ c r₀ j,
        maxFrequency S N x (2 * (r₀ * δ₂ ^ j)) < 1 + δ₁ ∧ z ∈ closedBall x (r₀ * δ₂ ^ j)) ∨
      ∃ x ∈ coverGen S N δ₁ δ₂ c r₀ k, z ∈ closedBall x (r₀ * δ₂ ^ k) := by
  intro k
  induction k with
  | zero =>
    right
    have hcov := subset_net ((inter_subset_right).trans (ball_subset_closedBall (x := c)))
      hr₀ hz
    simp only [mem_iUnion] at hcov
    obtain ⟨x, hx, hzx⟩ := hcov
    exact ⟨x, hx, by simpa using ball_subset_closedBall hzx⟩
  | succ k ih =>
    rcases ih with ⟨j, hj, x, hx, h⟩ | ⟨x, hx, hzx⟩
    · exact Or.inl ⟨j, by omega, x, hx, h⟩
    by_cases hterm : maxFrequency S N x (2 * (r₀ * δ₂ ^ k)) < 1 + δ₁
    · exact Or.inl ⟨k, by omega, x, hx, hterm, hzx⟩
    right
    have hcov := subset_net (inter_subset_right (s := S)) (by positivity : 0 < δ₂ * (r₀ * δ₂ ^ k))
      ⟨hz.1, hzx⟩
    simp only [mem_iUnion] at hcov
    obtain ⟨y, hy, hzy⟩ := hcov
    refine ⟨y, mem_coverGen_succ.2 ⟨x, hx, not_lt.1 hterm, hy⟩, ?_⟩
    rw [pow_succ, ← mul_assoc, mul_comm _ δ₂]
    exact ball_subset_closedBall hzy

theorem card_coverGen_zero_le (hr₀ : 0 < r₀) :
    ((coverGen S N δ₁ δ₂ c r₀ 0).card : ℝ) ≤ 3 ^ n := by
  have h := card_le_of_pairwise_le_dist hr₀ hr₀.le
    ((net_subset _ _).trans (inter_subset_right.trans ball_subset_closedBall))
    (net_pairwise (S ∩ ball c r₀) r₀) (z := c)
  rw [show 2 * r₀ / r₀ + 1 = 3 by field_simp; norm_num] at h
  exact h

end CoverGen

/-! ### Constants and child counts -/

/-- The tube-packing constant `C_S = 81 · 3^{n−2} · 2ⁿ / ω_n`: at most `C_S δ₂^{2−n}` of the
`δ₂ r`-separated points of `B̄_r(x)` lie within `4 δ₂ r` of an affine subspace of dimension
`≤ n − 2` (`card_le_of_subset_thickening`). -/
def tubeConst (n : ℕ) : ℝ :=
  81 * 3 ^ (n - 2) * 2 ^ n / unitBallVolume n

theorem tubeConst_pos (n : ℕ) : 0 < tubeConst n := by
  have := unitBallVolume_pos n
  unfold tubeConst
  positivity

/-- The base `θ = max(1, 3ⁿ / (C_S δ₂²))` of the weights `θ^{P/ε₂}`. -/
def weightBase (n : ℕ) (δ₂ : ℝ) : ℝ :=
  max 1 (3 ^ n / (tubeConst n * δ₂ ^ 2))

theorem one_le_weightBase (n : ℕ) (δ₂ : ℝ) : 1 ≤ weightBase n δ₂ :=
  le_max_left _ _

/-- The growth factor `2 C_S δ₂^{2−n}` of the total weight per generation. -/
def growth (n : ℕ) (δ₂ : ℝ) : ℝ :=
  2 * tubeConst n / δ₂ ^ (n - 2)

theorem growth_pos (n : ℕ) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) : 0 < growth n δ₂ := by
  have := tubeConst_pos n
  unfold growth
  positivity

/-- A `δ₂ r`-separated subset of `B̄_r(x)` has at most `(3/δ₂)ⁿ` points. -/
theorem card_le_of_subset_closedBall {F : Finset (Rn n)} {x : Rn n} {δ₂ r : ℝ} (hδ₂ : 0 < δ₂)
    (hδ₂1 : δ₂ ≤ 1) (hr : 0 < r) (hFx : ↑F ⊆ closedBall x r)
    (hF : (F : Set (Rn n)).Pairwise fun y z => δ₂ * r ≤ dist y z) :
    (F.card : ℝ) ≤ (3 / δ₂) ^ n := by
  refine (card_le_of_pairwise_le_dist (by positivity) hr.le hFx hF).trans
    (pow_le_pow_left₀ (by positivity) ?_ n)
  rw [show 2 * r / (δ₂ * r) = 2 / δ₂ by field_simp]
  have : 1 ≤ 1 / δ₂ := by rw [le_div_iff₀ hδ₂]; linarith
  have h3 : 3 / δ₂ = 2 / δ₂ + 1 / δ₂ := by ring
  linarith

/-- **Small-drop count** (proof of Theorem 7.2). A `δ₂ r`-separated subset of `B̄_r(x)` within
`4 δ₂ r` of an affine subspace of dimension `≤ n − 2` has at most `C_S δ₂^{2−n}` points. -/
theorem card_le_of_subset_thickening (hn : 2 ≤ n) {L : AffineSubspace ℝ (Rn n)}
    (hL : Module.finrank ℝ L.direction ≤ n - 2) {F : Finset (Rn n)} {x : Rn n} {δ₂ r : ℝ}
    (hδ₂ : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) (hr : 0 < r) (hFx : ↑F ⊆ closedBall x r)
    (hFL : ↑F ⊆ thickening (4 * (δ₂ * r)) (L : Set (Rn n)))
    (hF : (F : Set (Rn n)).Pairwise fun y z => δ₂ * r ≤ dist y z) :
    (F.card : ℝ) ≤ tubeConst n / δ₂ ^ (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hω := unitBallVolume_pos (m + 2)
  have h := card_mul_le_of_subset_thickening hn hL (by positivity) hr.le (by positivity) hFx hFL hF
  have h3 : (2 * r + δ₂ * r) ^ m ≤ (3 * r) ^ m :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) m
  set X := δ₂ ^ 2 * r ^ (m + 2) with hX
  have hX0 : 0 < X := by positivity
  have e1 : (δ₂ * r / 2) ^ (m + 2) = δ₂ ^ m * X / 2 ^ (m + 2) := by
    rw [div_pow, mul_pow, pow_add δ₂]
    ring
  have e2 : (2 * (4 * (δ₂ * r)) + δ₂ * r) ^ 2 * (3 * r) ^ m = 81 * 3 ^ m * X := by
    rw [mul_pow, hX, pow_add r]
    ring
  have h' : (F.card : ℝ) * (unitBallVolume (m + 2) * (δ₂ ^ m * X / 2 ^ (m + 2))) ≤
      81 * 3 ^ m * X := by
    rw [← e1, ← e2]
    exact h.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h'' : (F.card : ℝ) * (unitBallVolume (m + 2) * δ₂ ^ m) * X ≤
      (81 * 3 ^ m * 2 ^ (m + 2)) * X := by
    have := mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ 2 ^ (m + 2))
    calc (F.card : ℝ) * (unitBallVolume (m + 2) * δ₂ ^ m) * X
        = (F.card : ℝ) * (unitBallVolume (m + 2) * (δ₂ ^ m * X / 2 ^ (m + 2))) * 2 ^ (m + 2) := by
          field_simp
      _ ≤ 81 * 3 ^ m * X * 2 ^ (m + 2) := this
      _ = (81 * 3 ^ m * 2 ^ (m + 2)) * X := by ring
  have key := le_of_mul_le_mul_right h'' hX0
  rw [tubeConst, Nat.add_sub_cancel, div_div, le_div_iff₀ (by positivity)]
  linarith

/-- `(3/δ₂)ⁿ ≤ C_S δ₂^{2−n} θ`: the large-drop children are paid for by the factor `1/θ`. -/
theorem three_div_pow_le (hn : 2 ≤ n) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) :
    (3 / δ₂) ^ n ≤ tubeConst n / δ₂ ^ (n - 2) * weightBase n δ₂ := by
  have hC := tubeConst_pos n
  have hθ : 3 ^ n / (tubeConst n * δ₂ ^ 2) ≤ weightBase n δ₂ := le_max_right _ _
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hθ (by positivity))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel, div_pow]
  field_simp
  ring

/-- `Σ_{a ∈ ⋃ᵢ tᵢ} f a ≤ Σᵢ Σ_{a ∈ tᵢ} f a` for nonnegative `f`. -/
theorem sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a := Finset.sum_nonneg fun a _ => hf a
    linarith

/-- `2 C_S δ₂^{2−n} · δ₂^{n−1} = 2 C_S δ₂`. -/
theorem growth_mul_pow (hn : 2 ≤ n) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) :
    growth n δ₂ * δ₂ ^ (n - 1) = 2 * tubeConst n * δ₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [growth, Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega, pow_succ]
  field_simp

/-! ### The weighted count -/

namespace NVData

variable {CJ Nplus : ℝ} {ε : ℝ → ℝ} (D : NVData n CJ Nplus ε)

/-- **One generation of the covering** (proof of Theorem 7.2). Let `B_r(x)` be a
non-terminal ball, `x ∈ S`, with `B̄_{2r}(x) ⊆ K`, `2r ≤ R` and `t ≤ δ₂ r`. Its children are the
points of a maximal `δ₂ r`-separated subset of `S ∩ B̄_r(x)`. The weights
`θ^{P/ε₂}`, `P(y, ρ) = N^max(y, 2ρ)`, satisfy
`Σ_children θ^{P(y, δ₂ r)/ε₂} ≤ 2 C_S δ₂^{2−n} θ^{P(x, r)/ε₂}`.

The dichotomy is applied to `B̄_{2r}(x)`, which contains every `B̄_{2δ₂ r}(y)`. (The paper applies
it to `B_r(x)`, whose frequency-drop conclusion does not cover the parts of the child balls
outside `B_r(x)`; see the module docstring.) -/
theorem sum_weight_children_le (hn : 2 ≤ n) {δ₁ δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ₂₁ : δ₂ ≤ δ₁)
    (hδ₂20 : δ₂ ≤ 1 / 20) (hε₂ : 0 < ε δ₂) {x : Rn n} {r : ℝ} (hr : 0 < r)
    (htr : D.t ≤ δ₂ * r) (hrR : 2 * r ≤ D.R) (hK : closedBall x (2 * r) ⊆ D.K) (hx : x ∈ D.S)
    (hP : 1 + δ₁ ≤ maxFrequency D.S D.N x (2 * r)) :
    ∑ y ∈ net (D.S ∩ closedBall x r) (δ₂ * r),
        weightBase n δ₂ ^ (maxFrequency D.S D.N y (2 * (δ₂ * r)) / ε δ₂) ≤
      growth n δ₂ * weightBase n δ₂ ^ (maxFrequency D.S D.N x (2 * r) / ε δ₂) := by
  classical
  set θ := weightBase n δ₂ with hθ_def
  set ε₂ := ε δ₂ with hε₂_def
  set P := maxFrequency D.S D.N x (2 * r) with hP_def
  set ch := net (D.S ∩ closedBall x r) (δ₂ * r) with hch
  have hθ1 : 1 ≤ θ := one_le_weightBase n δ₂
  have hθ0 : 0 < θ := by linarith
  have hCS := tubeConst_pos n
  have hδ₂1 : δ₂ ≤ 1 := by linarith
  have ha : 0 < δ₂ * r := by positivity
  have hδr : δ₂ * r ≤ r / 20 := by nlinarith
  have hR0 : 0 < D.R := by linarith
  have ht : D.t < 20 * (2 * r) := by linarith
  obtain h | ⟨L, hL, hE⟩ := D.dichotomy δ₂ hδ₂ x (2 * r) (by positivity) (by linarith) hrR hK
    ⟨x, hx, mem_closedBall_self (by positivity)⟩
  · exfalso
    linarith
  have hchS : ∀ y ∈ ch, y ∈ D.S ∩ closedBall x r := fun y hy => net_subset _ _ hy
  have hz : ∀ y ∈ ch, ∀ z ∈ D.S ∩ closedBall y (2 * (δ₂ * r)),
      z ∈ D.S ∩ closedBall x (2 * r) ∧ D.N z (20 * (2 * (δ₂ * r))) ≤ D.N z (2 * r) := by
    intro y hy z hz'
    have h1 := mem_closedBall.1 (hchS y hy).2
    have h2 := mem_closedBall.1 hz'.2
    refine ⟨⟨hz'.1, mem_closedBall.2 (by linarith [dist_triangle z y x])⟩, ?_⟩
    exact D.N_le_N hz'.1 (by linarith) (by linarith) (by linarith)
  have hne : ∀ y ∈ ch, (D.S ∩ closedBall y (2 * (δ₂ * r))).Nonempty := fun y hy =>
    ⟨y, (hchS y hy).1, mem_closedBall_self (by positivity)⟩
  have hPy_le : ∀ y ∈ ch, maxFrequency D.S D.N y (2 * (δ₂ * r)) ≤ P := fun y hy =>
    maxFrequency_le (hne y hy) fun z hz' => by
      obtain ⟨hzx, hzN⟩ := hz y hy z hz'
      exact hzN.trans ((D.N_le_N hzx.1 (by linarith) (by linarith) (by linarith)).trans
        (D.le_maxFrequency hzx ht hrR))
  have hPy_drop : ∀ y ∈ ch, y ∉ thickening (4 * (δ₂ * r)) (L : Set (Rn n)) →
      maxFrequency D.S D.N y (2 * (δ₂ * r)) ≤ P - ε₂ := fun y hy hyL =>
    maxFrequency_le (hne y hy) fun z hz' => by
      obtain ⟨hzx, hzN⟩ := hz y hy z hz'
      refine hzN.trans ?_
      by_contra hlt
      rw [not_le] at hlt
      have hzE : z ∈ thickening (δ₂ * (2 * r)) (L : Set (Rn n)) := hE ⟨hzx, by linarith⟩
      obtain ⟨l, hl, hzl⟩ := mem_thickening_iff.1 hzE
      have hyz := mem_closedBall.1 hz'.2
      rw [dist_comm] at hyz
      exact hyL (mem_thickening_iff.2 ⟨l, hl, by linarith [dist_triangle y z l]⟩)
  set T := ch.filter (· ∈ thickening (4 * (δ₂ * r)) (L : Set (Rn n))) with hT
  have hpt : ∀ y ∈ ch, θ ^ (maxFrequency D.S D.N y (2 * (δ₂ * r)) / ε₂) ≤
      (if y ∈ thickening (4 * (δ₂ * r)) (L : Set (Rn n)) then θ ^ (P / ε₂) else 0) +
        θ ^ (P / ε₂) / θ := by
    intro y hy
    have hw0 : 0 ≤ θ ^ (P / ε₂) / θ := by positivity
    split_ifs with hyL
    · have := Real.rpow_le_rpow_of_exponent_le hθ1
        (div_le_div_of_nonneg_right (hPy_le y hy) hε₂.le)
      linarith
    · rw [zero_add, ← Real.rpow_sub_one hθ0.ne']
      refine Real.rpow_le_rpow_of_exponent_le hθ1 ?_
      rw [le_sub_iff_add_le, div_add_one hε₂.ne', div_le_div_iff_of_pos_right hε₂]
      linarith [hPy_drop y hy hyL]
  have hTcard : (T.card : ℝ) ≤ tubeConst n / δ₂ ^ (n - 2) :=
    card_le_of_subset_thickening hn hL hδ₂ hδ₂1 hr
      (fun y hy => (hchS y (Finset.mem_filter.1 hy).1).2)
      (fun y hy => (Finset.mem_filter.1 hy).2)
      ((net_pairwise _ _).mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))
  have hchcard : (ch.card : ℝ) ≤ (3 / δ₂) ^ n :=
    card_le_of_subset_closedBall hδ₂ hδ₂1 hr (fun y hy => (hchS y hy).2) (net_pairwise _ _)
  have hw : 0 ≤ θ ^ (P / ε₂) := by positivity
  have hch' : (ch.card : ℝ) * (θ ^ (P / ε₂) / θ) ≤ tubeConst n / δ₂ ^ (n - 2) * θ ^ (P / ε₂) := by
    calc (ch.card : ℝ) * (θ ^ (P / ε₂) / θ)
        ≤ (tubeConst n / δ₂ ^ (n - 2) * θ) * (θ ^ (P / ε₂) / θ) :=
          mul_le_mul_of_nonneg_right (hchcard.trans (three_div_pow_le hn hδ₂)) (by positivity)
      _ = tubeConst n / δ₂ ^ (n - 2) * θ ^ (P / ε₂) := by
          field_simp
  calc ∑ y ∈ ch, θ ^ (maxFrequency D.S D.N y (2 * (δ₂ * r)) / ε₂)
      ≤ ∑ y ∈ ch, ((if y ∈ thickening (4 * (δ₂ * r)) (L : Set (Rn n)) then θ ^ (P / ε₂) else 0) +
          θ ^ (P / ε₂) / θ) := Finset.sum_le_sum hpt
    _ = T.card * θ ^ (P / ε₂) + ch.card * (θ ^ (P / ε₂) / θ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
          nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ tubeConst n / δ₂ ^ (n - 2) * θ ^ (P / ε₂) + tubeConst n / δ₂ ^ (n - 2) * θ ^ (P / ε₂) :=
        add_le_add (mul_le_mul_of_nonneg_right hTcard hw) hch'
    _ = growth n δ₂ * θ ^ (P / ε₂) := by
        unfold growth
        ring

/-- **Weighted count of a generation.** For `t ≤ r₀ δ₂^k`, the total weight of generation `k` is
at most `3ⁿ θ^{N₊/ε₂} (2 C_S δ₂^{2−n})^k`. -/
theorem sum_weight_coverGen_le (hn : 2 ≤ n) {δ₁ δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ₂₁ : δ₂ ≤ δ₁)
    (hδ₂20 : δ₂ ≤ 1 / 20) (hε₂ : 0 < ε δ₂) {c : Rn n} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr₀R : 2 * r₀ ≤ D.R) (hK : closedBall c (5 * r₀) ⊆ D.K) :
    ∀ k : ℕ, D.t ≤ r₀ * δ₂ ^ k →
      ∑ x ∈ coverGen D.S D.N δ₁ δ₂ c r₀ k,
          weightBase n δ₂ ^ (maxFrequency D.S D.N x (2 * (r₀ * δ₂ ^ k)) / ε δ₂) ≤
        3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * growth n δ₂ ^ k := by
  classical
  have hθ1 := one_le_weightBase n δ₂
  have hδ₂1 : δ₂ ≤ 1 := by linarith
  have hδ₂2 : δ₂ ≤ 1 / 2 := by linarith
  intro k
  induction k with
  | zero =>
    intro ht
    simp only [pow_zero, mul_one] at ht ⊢
    refine (Finset.sum_le_card_nsmul _ _ (weightBase n δ₂ ^ (Nplus / ε δ₂)) fun x hx => ?_).trans ?_
    · refine Real.rpow_le_rpow_of_exponent_le hθ1 (div_le_div_of_nonneg_right ?_ hε₂.le)
      exact D.maxFrequency_le_Nplus ⟨x, coverGen_subset 0 hx, mem_closedBall_self (by positivity)⟩
        (by linarith) hr₀R
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (card_coverGen_zero_le hr₀) (by positivity)
  | succ k ih =>
    intro ht
    set rk := r₀ * δ₂ ^ k with hrk
    have hrk0 : 0 < rk := by positivity
    have hrk1 : r₀ * δ₂ ^ (k + 1) = δ₂ * rk := by rw [hrk, pow_succ]; ring
    have hrkr₀ : rk ≤ r₀ := mul_le_of_le_one_right hr₀.le (pow_le_one₀ hδ₂.le hδ₂1)
    rw [hrk1] at ht ⊢
    have ht' : D.t ≤ rk := ht.trans (mul_le_of_le_one_left hrk0.le hδ₂1)
    have hw0 : ∀ y : Rn n, ∀ ρ : ℝ, 0 ≤ weightBase n δ₂ ^ (maxFrequency D.S D.N y ρ / ε δ₂) :=
      fun y ρ => by positivity
    calc ∑ y ∈ coverGen D.S D.N δ₁ δ₂ c r₀ (k + 1),
          weightBase n δ₂ ^ (maxFrequency D.S D.N y (2 * (δ₂ * rk)) / ε δ₂)
        ≤ ∑ x ∈ (coverGen D.S D.N δ₁ δ₂ c r₀ k).filter
              (fun x => 1 + δ₁ ≤ maxFrequency D.S D.N x (2 * rk)),
            ∑ y ∈ net (D.S ∩ closedBall x rk) (δ₂ * rk),
              weightBase n δ₂ ^ (maxFrequency D.S D.N y (2 * (δ₂ * rk)) / ε δ₂) :=
          sum_biUnion_le_of_nonneg _ _ fun y => hw0 y _
      _ ≤ ∑ x ∈ (coverGen D.S D.N δ₁ δ₂ c r₀ k).filter
              (fun x => 1 + δ₁ ≤ maxFrequency D.S D.N x (2 * rk)),
            growth n δ₂ * weightBase n δ₂ ^ (maxFrequency D.S D.N x (2 * rk) / ε δ₂) := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨hx, hP⟩ := Finset.mem_filter.1 hx
          have hdist := dist_lt_of_mem_coverGen hδ₂.le hδ₂2 hr₀.le k x hx
          refine D.sum_weight_children_le hn hδ₂ hδ₂₁ hδ₂20 hε₂ hrk0 ht (by linarith)
            ((closedBall_subset_closedBall' ?_).trans hK) (coverGen_subset k hx) hP
          linarith
      _ ≤ ∑ x ∈ coverGen D.S D.N δ₁ δ₂ c r₀ k,
            growth n δ₂ * weightBase n δ₂ ^ (maxFrequency D.S D.N x (2 * rk) / ε δ₂) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ =>
            mul_nonneg (growth_pos n hδ₂).le (hw0 x _)
      _ = growth n δ₂ * ∑ x ∈ coverGen D.S D.N δ₁ δ₂ c r₀ k,
            weightBase n δ₂ ^ (maxFrequency D.S D.N x (2 * rk) / ε δ₂) := by
          rw [Finset.mul_sum]
      _ ≤ growth n δ₂ * (3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * growth n δ₂ ^ k) :=
          mul_le_mul_of_nonneg_left (ih ht') (growth_pos n hδ₂).le
      _ = 3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * growth n δ₂ ^ (k + 1) := by ring

/-- **Count of a generation** (proof of Theorem 7.2, via a weighted count; see the module
docstring for the count used here). For `t ≤ r₀ δ₂^k`,
`#(generation k) ≤ 3ⁿ θ^{N₊/ε₂} (2 C_S δ₂^{2−n})^k`. -/
theorem card_coverGen_le (hn : 2 ≤ n) {δ₁ δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ₂₁ : δ₂ ≤ δ₁)
    (hδ₂20 : δ₂ ≤ 1 / 20) (hε₂ : 0 < ε δ₂) {c : Rn n} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr₀R : 2 * r₀ ≤ D.R) (hK : closedBall c (5 * r₀) ⊆ D.K) (k : ℕ)
    (ht : D.t ≤ r₀ * δ₂ ^ k) :
    ((coverGen D.S D.N δ₁ δ₂ c r₀ k).card : ℝ) ≤
      3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * growth n δ₂ ^ k := by
  refine le_trans ?_ (D.sum_weight_coverGen_le hn hδ₂ hδ₂₁ hδ₂20 hε₂ hr₀ hr₀R hK k ht)
  have hrk0 : 0 < r₀ * δ₂ ^ k := by positivity
  have hrk : r₀ * δ₂ ^ k ≤ r₀ :=
    mul_le_of_le_one_right hr₀.le (pow_le_one₀ hδ₂.le (by linarith))
  have h := Finset.card_nsmul_le_sum (coverGen D.S D.N δ₁ δ₂ c r₀ k)
    (fun x => weightBase n δ₂ ^ (maxFrequency D.S D.N x (2 * (r₀ * δ₂ ^ k)) / ε δ₂)) 1
    fun x hx => Real.one_le_rpow (one_le_weightBase n δ₂) (div_nonneg (zero_le_one.trans
      (D.one_le_maxFrequency ⟨coverGen_subset k hx, mem_closedBall_self (by positivity)⟩
        (by linarith) (by linarith))) hε₂.le)
  rwa [nsmul_eq_mul, mul_one] at h

/-- `#(generation j) · r_j^{n−1} ≤ 3ⁿ θ^{N₊/ε₂} r₀^{n−1} 2^{−j}` when `2 C_S δ₂ ≤ 1/2`. -/
theorem card_mul_pow_le (hn : 2 ≤ n) {δ₁ δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ₂₁ : δ₂ ≤ δ₁)
    (hδ₂20 : δ₂ ≤ 1 / 20) (hε₂ : 0 < ε δ₂) {c : Rn n} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr₀R : 2 * r₀ ≤ D.R) (hK : closedBall c (5 * r₀) ⊆ D.K)
    (hδ₂CS : 2 * tubeConst n * δ₂ ≤ 1 / 2) (j : ℕ) (ht : D.t ≤ r₀ * δ₂ ^ j) :
    ((coverGen D.S D.N δ₁ δ₂ c r₀ j).card : ℝ) * (r₀ * δ₂ ^ j) ^ (n - 1) ≤
      3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * r₀ ^ (n - 1) * (1 / 2) ^ j := by
  have hc := D.card_coverGen_le hn hδ₂ hδ₂₁ hδ₂20 hε₂ hr₀ hr₀R hK j ht
  have hA := growth_mul_pow hn hδ₂
  have hθ : 0 < weightBase n δ₂ := zero_lt_one.trans_le (one_le_weightBase n δ₂)
  have hCS := tubeConst_pos n
  calc ((coverGen D.S D.N δ₁ δ₂ c r₀ j).card : ℝ) * (r₀ * δ₂ ^ j) ^ (n - 1)
      ≤ (3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * growth n δ₂ ^ j) *
          (r₀ * δ₂ ^ j) ^ (n - 1) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * r₀ ^ (n - 1) *
          (growth n δ₂ * δ₂ ^ (n - 1)) ^ j := by ring
    _ ≤ 3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) * r₀ ^ (n - 1) * (1 / 2) ^ j := by
        rw [hA]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hδ₂CS j) (by positivity)

end NVData

/-! ### Theorem 7.2 (1) -/

/-- **Theorem 7.2 (1)**, for abstract data. There is
`C = C(n, CJ, N₊, ε)` such that for every `D : NVData n CJ N₊ ε`, every ball `B_{r₀}(c)` with
`2r₀ ≤ R` and `B̄_{5r₀}(c) ⊆ K`, and every `s ∈ [t, r₀]`, `s > 0`:
`|B_s(S ∩ B_{r₀}(c))| ≤ C s r₀^{n−1}`.

Proof (as in the paper's proof of (1)): run the covering tree with `δ₁ = δ` of Lemma 7.1 and
`δ₂ = min(δ₁, 1/20, 1/(4 C_S))` down to the generation `K` with `r_K ∈ [s, s/δ₂)`. The terminal
balls `B_{r_j}(x)`, `j < K`, contribute `≤ C s r_j^{n−1}` each by Lemma 7.1 (2) applied on
`B_{2r_j}(x)`; the balls of generation `K` contribute `|B_{2r_K}| ≤ C r_K^{n−1} s/δ₂` each. Since
`#(generation j) r_j^{n−1} ≤ C r₀^{n−1} 2^{−j}`, both sums are `≤ C s r₀^{n−1}`. -/
theorem volume_thickening_le (hn : 2 ≤ n) (CJ Nplus : ℝ) (ε : ℝ → ℝ)
    (hε : ∀ δ, 0 < δ → 0 < ε δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : NVData n CJ Nplus ε) (c : Rn n) (r₀ : ℝ), 0 < r₀ → 2 * r₀ ≤ D.R →
      closedBall c (5 * r₀) ⊆ D.K → ∀ s : ℝ, 0 < s → D.t ≤ s → s ≤ r₀ →
        volume (thickening s (D.S ∩ ball c r₀)) ≤ ENNReal.ofReal (C * s * r₀ ^ (n - 1)) := by
  classical
  obtain ⟨δV, hδV, CV, hCV, hV⟩ := volume_estimate_of_frequency_lt hn CJ
  have hCS := tubeConst_pos n
  have hω := unitBallVolume_pos n
  set δ₂ := min (min δV (1 / 20)) (1 / (4 * tubeConst n)) with hδ₂_def
  have hδ₂ : 0 < δ₂ := lt_min (lt_min hδV (by norm_num)) (by positivity)
  have hδ₂V : δ₂ ≤ δV := (min_le_left _ _).trans (min_le_left _ _)
  have hδ₂20 : δ₂ ≤ 1 / 20 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₂1 : δ₂ < 1 := by linarith
  have hδ₂CS : 2 * tubeConst n * δ₂ ≤ 1 / 2 := by
    have h : δ₂ ≤ 1 / (4 * tubeConst n) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hε₂ := hε δ₂ hδ₂
  have hθ : 0 < weightBase n δ₂ := zero_lt_one.trans_le (one_le_weightBase n δ₂)
  set M := 3 ^ n * weightBase n δ₂ ^ (Nplus / ε δ₂) with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M * (2 ^ n * CV + 2 ^ n * unitBallVolume n / δ₂), by positivity, ?_⟩
  intro D c r₀ hr₀ hr₀R hK s hs hts hsr₀
  set G := coverGen D.S D.N δV δ₂ c r₀ with hG
  -- the stopping generation `K`, with `r_K ∈ [s, s/δ₂)`
  have hex : ∃ k : ℕ, r₀ * δ₂ ^ (k + 1) < s := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hs hr₀) hδ₂1
    refine ⟨k, ?_⟩
    have h1 : δ₂ ^ (k + 1) ≤ δ₂ ^ k := pow_le_pow_of_le_one hδ₂.le hδ₂1.le (Nat.le_succ k)
    rw [lt_div_iff₀ hr₀] at hk
    nlinarith
  set K := Nat.find hex with hK_def
  have hK1 : r₀ * δ₂ ^ (K + 1) < s := Nat.find_spec hex
  have hKs : s ≤ r₀ * δ₂ ^ K := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0, pow_zero, mul_one]
      exact hsr₀
    · obtain ⟨j, hj⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
      have h := Nat.find_min hex (show j < K by omega)
      rw [hj]
      exact not_lt.1 h
  have hrj : ∀ j ≤ K, s ≤ r₀ * δ₂ ^ j := fun j hj =>
    hKs.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ₂.le hδ₂1.le hj) hr₀.le)
  have hrj0 : ∀ j : ℕ, 0 < r₀ * δ₂ ^ j := fun j => by positivity
  have hrjr₀ : ∀ j : ℕ, r₀ * δ₂ ^ j ≤ r₀ := fun j =>
    mul_le_of_le_one_right hr₀.le (pow_le_one₀ hδ₂.le hδ₂1.le)
  have hcount : ∀ j ≤ K, ((G j).card : ℝ) * (r₀ * δ₂ ^ j) ^ (n - 1) ≤
      M * r₀ ^ (n - 1) * (1 / 2) ^ j := fun j hj =>
    D.card_mul_pow_le hn hδ₂ hδ₂V hδ₂20 hε₂ hr₀ hr₀R hK hδ₂CS j (hts.trans (hrj j hj))
  -- the covering of `B_s(S ∩ B_{r₀}(c))`
  set T : ℕ → Finset (Rn n) := fun j =>
    (G j).filter fun x => maxFrequency D.S D.N x (2 * (r₀ * δ₂ ^ j)) < 1 + δV with hT
  have hcover : thickening s (D.S ∩ ball c r₀) ⊆
      (⋃ j ∈ Finset.range K, ⋃ x ∈ T j, thickening s (D.S ∩ ball x (2 * (r₀ * δ₂ ^ j)))) ∪
        ⋃ x ∈ G K, ball x (2 * (r₀ * δ₂ ^ K)) := by
    intro z' hz'
    obtain ⟨z, hz, hz'z⟩ := mem_thickening_iff.1 hz'
    rcases mem_coverGen_or hδ₂ hr₀ hz K with ⟨j, hj, x, hx, hterm, hzx⟩ | ⟨x, hx, hzx⟩
    · refine Or.inl (mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hj, mem_iUnion₂.2
        ⟨x, Finset.mem_filter.2 ⟨hx, hterm⟩, mem_thickening_iff.2 ⟨z, ⟨hz.1, ?_⟩, hz'z⟩⟩⟩)
      have h1 := mem_closedBall.1 hzx
      exact mem_ball.2 (by linarith [hrj0 j])
    · refine Or.inr (mem_iUnion₂.2 ⟨x, hx, mem_ball.2 ?_⟩)
      linarith [dist_triangle z' z x, mem_closedBall.1 hzx]
  -- terminal balls: Lemma 7.1 (2) on `B_{2 r_j}(x)`
  have hterm_vol : ∀ j ∈ Finset.range K, ∀ x ∈ T j,
      volume (thickening s (D.S ∩ ball x (2 * (r₀ * δ₂ ^ j)))) ≤
        ENNReal.ofReal (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1)) := by
    intro j hj x hx
    obtain ⟨-, hterm⟩ := Finset.mem_filter.1 hx
    have hj' := hrj j (Finset.mem_range.1 hj).le
    refine (hV D.toJonesData x (2 * (r₀ * δ₂ ^ j)) (by linarith [hrj0 j])
      (by linarith [hrjr₀ j]) (fun z hz => ?_)).2 s hs hts (by linarith [hrj0 j])
    exact (D.le_maxFrequency ⟨hz.1, ball_subset_closedBall hz.2⟩ (by linarith [hrj0 j])
      (by linarith [hrjr₀ j])).trans_lt hterm
  -- the real bound
  have h22 : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hsum : ∑ j ∈ Finset.range K, ((T j).card : ℝ) * (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1)) ≤
      CV * s * 2 ^ (n - 1) * M * r₀ ^ (n - 1) * 2 := by
    calc ∑ j ∈ Finset.range K, ((T j).card : ℝ) * (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1))
        ≤ ∑ j ∈ Finset.range K, (CV * s * 2 ^ (n - 1) * M * r₀ ^ (n - 1)) * (1 / 2) ^ j := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hTG : ((T j).card : ℝ) ≤ (G j).card := Nat.cast_le.2 (Finset.card_filter_le _ _)
          have hc := hcount j (Finset.mem_range.1 hj).le
          calc ((T j).card : ℝ) * (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1))
              ≤ (G j).card * (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1)) :=
                mul_le_mul_of_nonneg_right hTG (by positivity)
            _ = CV * s * 2 ^ (n - 1) * ((G j).card * (r₀ * δ₂ ^ j) ^ (n - 1)) := by
                rw [mul_pow]
                ring
            _ ≤ CV * s * 2 ^ (n - 1) * (M * r₀ ^ (n - 1) * (1 / 2) ^ j) :=
                mul_le_mul_of_nonneg_left hc (by positivity)
            _ = (CV * s * 2 ^ (n - 1) * M * r₀ ^ (n - 1)) * (1 / 2) ^ j := by ring
      _ = (CV * s * 2 ^ (n - 1) * M * r₀ ^ (n - 1)) * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ CV * s * 2 ^ (n - 1) * M * r₀ ^ (n - 1) * 2 :=
          mul_le_mul_of_nonneg_left (sum_geometric_two_le K) (by positivity)
  have hlast : ((G K).card : ℝ) * (unitBallVolume n * (2 * (r₀ * δ₂ ^ K)) ^ n) ≤
      2 ^ n * unitBallVolume n * M * r₀ ^ (n - 1) * (s / δ₂) := by
    have hc := hcount K le_rfl
    have hrK : r₀ * δ₂ ^ K ≤ s / δ₂ := by
      rw [le_div_iff₀ hδ₂]
      rw [pow_succ, ← mul_assoc] at hK1
      exact hK1.le
    have hpow : (2 * (r₀ * δ₂ ^ K)) ^ n =
        2 ^ n * ((r₀ * δ₂ ^ K) ^ (n - 1) * (r₀ * δ₂ ^ K)) := by
      rw [mul_pow, ← pow_succ, Nat.sub_add_cancel (by omega)]
    have hhalf : (1 / 2 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hc' : ((G K).card : ℝ) * (r₀ * δ₂ ^ K) ^ (n - 1) ≤ M * r₀ ^ (n - 1) :=
      hc.trans (by
        calc M * r₀ ^ (n - 1) * (1 / 2) ^ K ≤ M * r₀ ^ (n - 1) * 1 :=
              mul_le_mul_of_nonneg_left hhalf (by positivity)
          _ = M * r₀ ^ (n - 1) := mul_one _)
    calc ((G K).card : ℝ) * (unitBallVolume n * (2 * (r₀ * δ₂ ^ K)) ^ n)
        = 2 ^ n * unitBallVolume n * (((G K).card : ℝ) * (r₀ * δ₂ ^ K) ^ (n - 1)) *
            (r₀ * δ₂ ^ K) := by
          rw [hpow]
          ring
      _ ≤ 2 ^ n * unitBallVolume n * (M * r₀ ^ (n - 1)) * (s / δ₂) := by
          gcongr
      _ = 2 ^ n * unitBallVolume n * M * r₀ ^ (n - 1) * (s / δ₂) := by ring
  have hfinal : ∑ j ∈ Finset.range K, ((T j).card : ℝ) * (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1)) +
      ((G K).card : ℝ) * (unitBallVolume n * (2 * (r₀ * δ₂ ^ K)) ^ n) ≤
      M * (2 ^ n * CV + 2 ^ n * unitBallVolume n / δ₂) * s * r₀ ^ (n - 1) := by
    have e : CV * s * 2 ^ (n - 1) * M * r₀ ^ (n - 1) * 2 +
        2 ^ n * unitBallVolume n * M * r₀ ^ (n - 1) * (s / δ₂) =
        M * (2 ^ n * CV + 2 ^ n * unitBallVolume n / δ₂) * s * r₀ ^ (n - 1) := by
      rw [← h22]
      field_simp
    linarith
  calc volume (thickening s (D.S ∩ ball c r₀))
      ≤ volume ((⋃ j ∈ Finset.range K, ⋃ x ∈ T j,
            thickening s (D.S ∩ ball x (2 * (r₀ * δ₂ ^ j)))) ∪
          ⋃ x ∈ G K, ball x (2 * (r₀ * δ₂ ^ K))) := measure_mono hcover
    _ ≤ volume (⋃ j ∈ Finset.range K, ⋃ x ∈ T j,
            thickening s (D.S ∩ ball x (2 * (r₀ * δ₂ ^ j)))) +
          volume (⋃ x ∈ G K, ball x (2 * (r₀ * δ₂ ^ K))) := measure_union_le _ _
    _ ≤ (∑ j ∈ Finset.range K, ∑ x ∈ T j,
            ENNReal.ofReal (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1))) +
          ∑ x ∈ G K, ENNReal.ofReal (unitBallVolume n * (2 * (r₀ * δ₂ ^ K)) ^ n) := by
        gcongr
        · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j hj =>
            (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x hx =>
              hterm_vol j hj x hx))
        · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x _ =>
            (volume_ball_eq x (by linarith [hrj0 K])).le)
    _ = ENNReal.ofReal (∑ j ∈ Finset.range K,
            ((T j).card : ℝ) * (CV * s * (2 * (r₀ * δ₂ ^ j)) ^ (n - 1)) +
          ((G K).card : ℝ) * (unitBallVolume n * (2 * (r₀ * δ₂ ^ K)) ^ n)) := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => by positivity) (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        · rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (M * (2 ^ n * CV + 2 ^ n * unitBallVolume n / δ₂) * s * r₀ ^ (n - 1)) :=
        ENNReal.ofReal_le_ofReal hfinal

end InnerVariational.NaberValtorta
