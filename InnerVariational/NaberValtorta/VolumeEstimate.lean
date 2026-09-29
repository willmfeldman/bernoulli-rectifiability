/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Data
public import InnerVariational.NaberValtorta.Packing
public import InnerVariational.NaberValtorta.Reifenberg
import Mathlib.Data.Real.StarOrdered
public import InnerVariational.NaberValtorta.Discrete
import InnerVariational.Basic.Polar

/-!
# Lemma 7.1: volume estimate when the maximal frequency is close to one

Lemma 7.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), parts (1) and (2), for
the abstract data `JonesData` (`NaberValtorta/Data.lean`).

Let `S' = S ∩ B_r(x)` with `r ≤ R`, and assume `N_z(20 r) < 1 + δ` for all `z ∈ S'`. Then for
`s ∈ [t, r]`, `s > 0`:

1. every `2s`-separated finite subset of `S'` has at most `C (r/s)^{n-1}` points
   (`card_le_of_frequency_lt`);
2. `|B_s(S')| ≤ C s r^{n-1}` (`volume_thickening_le_of_frequency_lt`).

`δ` and `C` depend only on `n` and on the constant `CJ` of the Jones estimate.

## Proof (a localised form of the paper's proof of (1))

Fix `s`. The claim `P(k)`: for every `p` and every `σ ∈ [s, min(r/2, 20^k s)]`, a `2s`-separated
`F ⊆ S' ∩ B_σ(p)` has at most `C_* (σ/s)^{n-1}` points. `P(0)` is trivial. For the step, apply
the discrete Reifenberg theorem of A. Naber and D. Valtorta, *Rectifiable-Reifenberg and the
regularity of stationary and minimizing harmonic maps*, Ann. of Math. (2) 185 (2017), no. 1,
131–227, Theorem 3.4 ([NV], proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0), on `B_σ(p) ⊆ B_{2σ}(p)` to
`μ = Σ_{y∈F} ω_{n-1} s^{n-1} δ_y` (`card_le_step`). For a ball `B_τ(q) ⊆ B_{2σ}(p)`, so `τ ≤ r`:

* `∫_0^τ β²_μ(z, ρ) dρ/ρ ≤ A Σ_{k<M} β²_μ(z, τ 20^{-k})`, where `M` is the first `k` with
  `τ 20^{-k} ≤ s`. The Jones numbers at scales `≤ s` vanish.
* The Jones estimate bounds `β²_μ(z, a_k)`, `a_k = τ 20^{-k} ∈ (s, τ]`, by the frequency drops
  `G_k(w) = N_w(20 a_k) − N_w(a_k)` of the atoms `w ∈ B_{a_k}(z)`.
* After exchanging the sums, each `w` is counted `#(F ∩ B_{a_k}(w)) ≤ 161ⁿ C_* (a_k/s)^{n-1}`
  times. This uses `P(k)` on balls of radius `a_k / 80` (`card_le_of_forall_card_le`).
* `Σ_{k<M} G_k(w) ≤ N_w(20τ) − 1 < δ` by telescoping.

So the Reifenberg integral is `≤ K δ τ^{n-1}`, with `K` depending on `n`, `CJ` and `C_*`, and it
is `< δ_R² τ^{n-1}` for `δ` small.

Theorem 6.1 at `(y, ρ)` uses the solution on `B_{50ρ}(y)`, which a solution on `B_{25r}(x)`
provides only for `ρ < 0.48 r`, so we restrict to scales `≤ r` (a localised form of the paper's
induction at the fixed scale `B_1`). The constants change, but still depend only on `n` and `CJ`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Elementary lemmas -/

theorem le_of_ball_subset_ball (hn : 0 < n) {y p : Rn n} {τ σ : ℝ} (hτ : 0 < τ)
    (h : ball y τ ⊆ ball p σ) : τ ≤ σ := by
  haveI := nontrivial_rn hn
  have hσ : 0 < σ := pos_of_mem_ball (h (mem_ball_self hτ))
  have := diam_mono h isBounded_ball
  rw [diam_ball_eq y hτ.le, diam_ball_eq p hσ.le] at this
  linarith

/-- The first index `k` with `τ / 20^k ≤ s` exists for `s > 0`. -/
theorem exists_div_pow_le {τ s : ℝ} (hs : 0 < s) : ∃ k : ℕ, τ / 20 ^ k ≤ s := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (τ / s) (by norm_num : (1 : ℝ) < 20)
  refine ⟨k, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hs] at hk
  linarith

/-- Telescoping: if `s < τ / 20^k` for `k < M`, `t ≤ s < τ`, `0 < s`, and `f ≥ 1` on
`(t, 20τ]`, then `Σ_{k<M} (f(20 τ 20^{-k}) − f(τ 20^{-k})) ≤ f(20 τ) − 1`. -/
theorem sum_range_sub_le {f : ℝ → ℝ} {t s τ : ℝ} {M : ℕ} (hM : ∀ k < M, s < τ / 20 ^ k)
    (hs : 0 < s) (hts : t ≤ s) (hsτ : s < τ) (h1 : ∀ ρ, t < ρ → ρ ≤ 20 * τ → 1 ≤ f ρ) :
    ∑ k ∈ Finset.range M, (f (20 * (τ / 20 ^ k)) - f (τ / 20 ^ k)) ≤ f (20 * τ) - 1 := by
  have hτ : 0 < τ := by linarith
  have hrw : ∀ k : ℕ, τ / 20 ^ k = 20 * (τ / 20 ^ (k + 1)) := fun k => by
    rw [pow_succ]
    field_simp
  set g : ℕ → ℝ := fun k => f (20 * (τ / 20 ^ k)) with hg
  have hterm : ∀ k ∈ Finset.range M, f (20 * (τ / 20 ^ k)) - f (τ / 20 ^ k) = g k - g (k + 1) :=
    fun k _ => by rw [hg]; dsimp only; rw [← hrw k]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  have hg0 : g 0 = f (20 * τ) := by rw [hg]; simp
  rw [hg0]
  rcases M with _ | m
  · rw [hg0]
    linarith [h1 (20 * τ) (by linarith) le_rfl]
  · have hm := hM m (Nat.lt_succ_self m)
    have hgm : g (m + 1) = f (τ / 20 ^ m) := by rw [hg]; dsimp only; rw [← hrw m]
    rw [hgm]
    have hle : τ / 20 ^ m ≤ 20 * τ := by
      calc τ / 20 ^ m ≤ τ := div_le_self hτ.le (one_le_pow₀ (by norm_num))
        _ ≤ 20 * τ := by linarith
    linarith [h1 _ (by linarith) hle]

/-! ### Counting from the induction hypothesis -/

/-- **Local count.** Suppose every `2s`-separated finite `G ⊆ A ∩ B_σ(p)` with `σ ∈ [s, b]` has at
most `C (σ/s)^{n-1}` points, `C ≥ 1`. Then a `2s`-separated finite `G ⊆ A ∩ B_ρ(w)` with
`s < ρ ≤ 80 b` has at most `161ⁿ C (ρ/s)^{n-1}` points. Cover `B_ρ(w)` by `161ⁿ` balls of radius
`ρ/80`. -/
theorem card_le_of_forall_card_le {A : Set (Rn n)} {s b C : ℝ} (hs : 0 < s) (hC : 1 ≤ C)
    (hyp : ∀ (p : Rn n) (σ : ℝ), s ≤ σ → σ ≤ b → ∀ G : Finset (Rn n), ↑G ⊆ A ∩ ball p σ →
      (G : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
      (G.card : ℝ) ≤ C * (σ / s) ^ (n - 1))
    {w : Rn n} {ρ : ℝ} (hρs : s < ρ) (hρb : ρ / 80 ≤ b) {G : Finset (Rn n)}
    (hGA : ↑G ⊆ A ∩ ball w ρ) (hG : (G : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z)) :
    (G.card : ℝ) ≤ 161 ^ n * C * (ρ / s) ^ (n - 1) := by
  classical
  have hρ : 0 < ρ := hs.trans hρs
  set a := ρ / 80 with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨E, hEcard, hcov⟩ := exists_cover_ball w hρ.le ha
  have h161 : 2 * ρ / a + 1 = 161 := by
    rw [ha_def]
    field_simp
    norm_num
  rw [h161] at hEcard
  have hC0 : 0 ≤ C := by linarith
  have hone : 1 ≤ ρ / s := by rw [le_div_iff₀ hs]; linarith
  have hpow : 1 ≤ (ρ / s) ^ (n - 1) := one_le_pow₀ hone
  -- each piece has at most `C (ρ/s)^{n-1}` points
  have hpiece : ∀ e ∈ E, ((G.filter (· ∈ ball e a)).card : ℝ) ≤ C * (ρ / s) ^ (n - 1) := by
    intro e _
    have hsub : ↑(G.filter (· ∈ ball e a)) ⊆ A ∩ ball e a := by
      intro y hy
      rw [Finset.coe_filter] at hy
      exact ⟨(hGA hy.1).1, hy.2⟩
    have hsep : (↑(G.filter (· ∈ ball e a)) : Set (Rn n)).Pairwise
        (fun y z => 2 * s ≤ dist y z) :=
      hG.mono (by intro y hy; rw [Finset.coe_filter] at hy; exact hy.1)
    by_cases hsa : s ≤ a
    · calc ((G.filter (· ∈ ball e a)).card : ℝ) ≤ C * (a / s) ^ (n - 1) :=
            hyp e a hsa hρb _ hsub hsep
        _ ≤ C * (ρ / s) ^ (n - 1) := by
            gcongr
            linarith
    · have h1 : (G.filter (· ∈ ball e a)).card ≤ 1 :=
        card_le_one_of_pairwise_le_dist (p := e) (σ := a) (by linarith)
          (fun y hy => hsub hy |>.2) hsep
      calc ((G.filter (· ∈ ball e a)).card : ℝ) ≤ 1 := by exact_mod_cast h1
        _ ≤ C * (ρ / s) ^ (n - 1) := by nlinarith
  have hGsub : G ⊆ E.biUnion fun e => G.filter (· ∈ ball e a) := by
    intro y hy
    obtain ⟨e, he, hye⟩ := mem_iUnion₂.1 (hcov (hGA hy).2)
    exact Finset.mem_biUnion.2 ⟨e, he, Finset.mem_filter.2 ⟨hy, hye⟩⟩
  calc (G.card : ℝ) ≤ ∑ e ∈ E, ((G.filter (· ∈ ball e a)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hGsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E, C * (ρ / s) ^ (n - 1) := Finset.sum_le_sum hpiece
    _ = E.card * (C * (ρ / s) ^ (n - 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 161 ^ n * (C * (ρ / s) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_right hEcard (mul_nonneg hC0 (by positivity))
    _ = 161 ^ n * C * (ρ / s) ^ (n - 1) := by ring

/-! ### The inductive step -/

/-- The constant `A · B · ω_{n-1} 161ⁿ C 2^{n-1}` of the Reifenberg integral bound in
`card_le_step`. Here `A = 19 · 20^{n+1}` is the constant of the dyadic decomposition and
`B = max(CJ, 1) ω_{n-1} 161ⁿ C`. -/
def stepConst (n : ℕ) (CJ C : ℝ) : ℝ :=
  19 * 20 ^ (n + 1) * (max CJ 1 * unitBallVolume (n - 1) * 161 ^ n * C) *
    (unitBallVolume (n - 1) * 161 ^ n * C * 2 ^ (n - 1))

theorem stepConst_pos (n : ℕ) (CJ : ℝ) {C : ℝ} (hC : 0 < C) : 0 < stepConst n CJ C := by
  have := unitBallVolume_pos (n - 1)
  have : 0 < max CJ 1 := lt_max_of_lt_right one_pos
  unfold stepConst
  positivity

/-- **Inductive step of Lemma 7.1 (1)** (localised). Let `S' = S ∩ B_r(x)` with
`N_z(20 r) < 1 + δ` on `S'`. Assume the count `#G ≤ C (σ'/s)^{n-1}` for `2s`-separated
`G ⊆ S' ∩ B_{σ'}(p')` and all `σ' ∈ [s, b]` (`hyp`). Then the same count holds for
`σ ∈ [s, min(r/2, 20 b)]`.

The discrete Reifenberg theorem is used through its hypothesis `hR`, with constants `δR` and
`DR ≤ C`, and `δ` is small: `stepConst n CJ C · δ ≤ δR²/2`. -/
theorem card_le_step (hn : 2 ≤ n) {CJ : ℝ} (J : JonesData n CJ) {δR DR C δ : ℝ}
    (hR : ∀ (p : Rn n) (σ s : ℝ), 0 < s → s ≤ σ → ∀ F : Finset (Rn n), ↑F ⊆ ball p σ →
      (F : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
      (∀ (y : Rn n) (τ : ℝ), 0 < τ → ball y τ ⊆ ball p (2 * σ) →
        ∫⁻ z in ball y τ, (∫⁻ ρ in Ioo 0 τ,
            jonesBetaSq (discreteMeasure F (fun _ => ENNReal.ofReal
              (unitBallVolume (n - 1) * s ^ (n - 1))) id) z ρ / ENNReal.ofReal ρ)
          ∂(discreteMeasure F (fun _ => ENNReal.ofReal
              (unitBallVolume (n - 1) * s ^ (n - 1))) id) <
          ENNReal.ofReal (δR ^ 2 * τ ^ (n - 1))) →
      (F.card : ℝ) * s ^ (n - 1) < DR * σ ^ (n - 1))
    (hDC : DR ≤ C) (hC : 1 ≤ C) (hδ : stepConst n CJ C * δ ≤ δR ^ 2 / 2)
    (hδR : 0 < δR) {x : Rn n} {r s b : ℝ} (hrR : r ≤ J.R) (hs : 0 < s) (hts : J.t ≤ s)
    (hN : ∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δ)
    (hyp : ∀ (p : Rn n) (σ : ℝ), s ≤ σ → σ ≤ b → ∀ G : Finset (Rn n),
      ↑G ⊆ (J.S ∩ ball x r) ∩ ball p σ →
      (G : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
      (G.card : ℝ) ≤ C * (σ / s) ^ (n - 1))
    {p : Rn n} {σ : ℝ} (hsσ : s ≤ σ) (hσr : 2 * σ ≤ r) (hσb : σ ≤ 20 * b)
    {F : Finset (Rn n)} (hF : ↑F ⊆ (J.S ∩ ball x r) ∩ ball p σ)
    (hFsep : (F : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z)) :
    (F.card : ℝ) ≤ C * (σ / s) ^ (n - 1) := by
  classical
  have hn0 : 0 < n := by omega
  have hσ : 0 < σ := hs.trans_le hsσ
  have hb : 0 < b := by linarith
  have hω : 0 < unitBallVolume (n - 1) := unitBallVolume_pos _
  have hC0 : 0 < C := by linarith
  set c : ℝ≥0∞ := ENNReal.ofReal (unitBallVolume (n - 1) * s ^ (n - 1)) with hc_def
  set μ := discreteMeasure F (fun _ => c) id with hμ_def
  suffices hint : ∀ (q : Rn n) (τ : ℝ), 0 < τ → ball q τ ⊆ ball p (2 * σ) →
      ∫⁻ z in ball q τ, (∫⁻ ρ in Ioo 0 τ, jonesBetaSq μ z ρ / ENNReal.ofReal ρ) ∂μ <
        ENNReal.ofReal (δR ^ 2 * τ ^ (n - 1)) by
    have key := hR p σ s hs hsσ F (hF.trans inter_subset_right) hFsep hint
    have hs' : 0 < s ^ (n - 1) := by positivity
    rw [div_pow, mul_div_assoc', le_div_iff₀ hs']
    exact key.le.trans (mul_le_mul_of_nonneg_right hDC (by positivity))
  intro q τ hτ hqτ
  have hτσ : τ ≤ 2 * σ := le_of_ball_subset_ball hn0 hτ hqτ
  have hτr : τ ≤ r := hτσ.trans hσr
  have hFS : ∀ w ∈ F, w ∈ J.S := fun w hw => (hF hw).1.1
  have hδR2 : 0 < δR ^ 2 * τ ^ (n - 1) := by positivity
  -- the Jones numbers vanish at scales `≤ s`
  have hvanish : ∀ z ρ, ρ ≤ s → jonesBetaSq μ z ρ = 0 := fun z ρ hρ =>
    jonesBetaSq_discreteMeasure_eq_zero_of_disjoint hn0 (r := fun _ => s) (fun _ _ => hs)
      (fun y hy w hw hyw => ball_disjoint_ball (by
        simp only [id]
        linarith [hFsep hy hw hyw]))
      (fun _ _ => hρ)
  -- `M` is the first index with `τ / 20^M ≤ s`
  have hex := exists_div_pow_le (τ := τ) hs
  set M := Nat.find hex with hM_def
  have hMge : ∀ k, M ≤ k → τ / 20 ^ k ≤ s := fun k hk =>
    (div_le_div_of_nonneg_left hτ.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hk)).trans (Nat.find_spec hex)
  have hMlt : ∀ k < M, s < τ / 20 ^ k := fun k hk => lt_of_not_ge (Nat.find_min hex hk)
  have hI : ∀ z, ∫⁻ ρ in Ioo 0 τ, jonesBetaSq μ z ρ / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (19 * 20 ^ (n + 1)) *
        ∑ k ∈ Finset.range M, jonesBetaSq μ z (τ / 20 ^ k) := by
    intro z
    refine (lintegral_jonesBetaSq_le_tsum hn0 μ z hτ).trans_eq ?_
    congr 1
    exact tsum_eq_sum fun k hk => hvanish z _ (hMge k (by simpa using hk))
  rw [setLIntegral_discreteMeasure F (fun _ => c) id measurableSet_ball]
  by_cases hτs : τ ≤ s
  · -- small balls: all the Jones numbers vanish
    have hM0 : M = 0 := (Nat.find_eq_zero hex).2 (by simpa using hτs)
    have hI0 : ∀ z, ∫⁻ ρ in Ioo 0 τ, jonesBetaSq μ z ρ / ENNReal.ofReal ρ = 0 := fun z =>
      le_antisymm ((hI z).trans (by rw [hM0]; simp)) (zero_le)
    refine lt_of_le_of_lt (le_of_eq ?_) (ENNReal.ofReal_pos.2 hδR2)
    exact Finset.sum_eq_zero fun z _ => by simp [indicator_apply, hI0]
  push Not at hτs
  -- constants
  set A : ℝ := 19 * 20 ^ (n + 1) with hA
  set B : ℝ := max CJ 1 * unitBallVolume (n - 1) * 161 ^ n * C with hB
  have hCJ : 0 < max CJ 1 := lt_max_of_lt_right one_pos
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set E : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (max CJ 1 / (τ / 20 ^ k) ^ (n - 1)) with hE
  set G : ℕ → Rn n → ℝ≥0∞ := fun k w =>
    ENNReal.ofReal (J.N w (20 * (τ / 20 ^ k)) - J.N w (τ / 20 ^ k)) with hG
  set X : ℝ≥0∞ := c * ENNReal.ofReal A * ENNReal.ofReal B with hX
  have hak : ∀ k, 0 < τ / 20 ^ k := fun k => by positivity
  have hakτ : ∀ k, τ / 20 ^ k ≤ τ := fun k => div_le_self hτ.le (one_le_pow₀ (by norm_num))
  -- `μ` is a finite measure carried by `S`
  have hfin : IsFiniteMeasure μ := ⟨by
    rw [hμ_def, discreteMeasure_apply]
    exact ENNReal.sum_lt_top.2 fun j _ => by simp [hc_def]⟩
  have hSc : μ J.Sᶜ = 0 := by
    rw [hμ_def, discreteMeasure_apply]
    exact Finset.sum_eq_zero fun y hy => by
      simp [hFS y hy]
  -- the Jones estimate at the scales `τ / 20^k > s`
  have hJ : ∀ z ∈ F, ∀ k < M, jonesBetaSq μ z (τ / 20 ^ k) ≤
      E k * ∑ w ∈ F, c * (ball z (τ / 20 ^ k)).indicator (G k) w := by
    intro z hz k hk
    refine (J.jones μ hfin hSc z (hFS z hz) _ (hak k) (hts.trans (hMlt k hk).le)
      ((hakτ k).trans (hτr.trans hrR))).trans ?_
    rw [hμ_def, setLIntegral_discreteMeasure F (fun _ => c) id measurableSet_ball]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))) _
  -- telescoping of the frequency drops
  have htel : ∀ w ∈ F, ∑ k ∈ Finset.range M, G k w ≤ ENNReal.ofReal δ := by
    intro w hw
    have hwS := hFS w hw
    have hnn : ∀ k ∈ Finset.range M,
        0 ≤ J.N w (20 * (τ / 20 ^ k)) - J.N w (τ / 20 ^ k) := fun k hk =>
      J.sub_nonneg_of_le hwS (hts.trans_lt (hMlt k (Finset.mem_range.1 hk)))
        (by linarith [hak k]) (by linarith [hakτ k])
    simp only [hG]
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := sum_range_sub_le (f := J.N w) (t := J.t) (M := M) hMlt hs hts hτs
      (fun ρ hρ hρ' => J.one_le w hwS ρ ⟨hρ, by linarith⟩)
    have h2 : J.N w (20 * τ) ≤ J.N w (20 * r) :=
      J.monotoneOn w hwS ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    have h3 := hN w (hF hw).1
    linarith
  -- local counts
  have hcount : ∀ w ∈ F, ∀ {ρ : ℝ}, s < ρ → ρ ≤ 4 * σ →
      ((F.filter (· ∈ ball w ρ)).card : ℝ) ≤ 161 ^ n * C * (ρ / s) ^ (n - 1) := by
    intro w _ ρ hρs hρσ
    refine card_le_of_forall_card_le (w := w) hs hC hyp hρs (by linarith) ?_ ?_
    · intro y hy
      rw [Finset.coe_filter] at hy
      exact ⟨(hF hy.1).1, hy.2⟩
    · exact hFsep.mono (by intro y hy; rw [Finset.coe_filter] at hy; exact hy.1)
  -- Step 1: bound each point's contribution
  have hstep1 : ∑ z ∈ F, c *
        (ball q τ).indicator (fun z => ∫⁻ ρ in Ioo 0 τ, jonesBetaSq μ z ρ / ENNReal.ofReal ρ)
          (id z) ≤
      ∑ z ∈ F, ∑ k ∈ Finset.range M, ∑ w ∈ F,
        if z ∈ ball q τ ∧ w ∈ ball z (τ / 20 ^ k) then
          c * ENNReal.ofReal A * E k * c * G k w else 0 := by
    refine Finset.sum_le_sum fun z hz => ?_
    dsimp only [id]
    by_cases hzq : z ∈ ball q τ
    · rw [indicator_of_mem hzq]
      calc c * ∫⁻ ρ in Ioo 0 τ, jonesBetaSq μ z ρ / ENNReal.ofReal ρ
          ≤ c * (ENNReal.ofReal A * ∑ k ∈ Finset.range M, jonesBetaSq μ z (τ / 20 ^ k)) :=
            mul_le_mul_right (hI z) c
        _ ≤ c * (ENNReal.ofReal A * ∑ k ∈ Finset.range M,
              E k * ∑ w ∈ F, c * (ball z (τ / 20 ^ k)).indicator (G k) w) := by
            gcongr with k hk
            exact hJ z hz k (Finset.mem_range.1 hk)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [indicator_apply]
            by_cases hw : w ∈ ball z (τ / 20 ^ k)
            · rw [if_pos hw, if_pos ⟨hzq, hw⟩]
              ring
            · rw [if_neg hw, if_neg fun h => hw h.2]
              simp
    · rw [indicator_of_notMem hzq, mul_zero]
      exact zero_le
  -- Step 2: count the points `z` seeing a given atom `w`
  have hstep2 : ∀ k ∈ Finset.range M, ∀ w ∈ F,
      (∑ z ∈ F, if z ∈ ball q τ ∧ w ∈ ball z (τ / 20 ^ k) then
          c * ENNReal.ofReal A * E k * c * G k w else 0) ≤
        X * (if w ∈ ball q (2 * τ) then G k w else 0) := by
    intro k hk w hw
    have hk' := Finset.mem_range.1 hk
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hwq : w ∈ ball q (2 * τ)
    · rw [if_pos hwq]
      have hsub : F.filter (fun z => z ∈ ball q τ ∧ w ∈ ball z (τ / 20 ^ k)) ⊆
          F.filter (· ∈ ball w (τ / 20 ^ k)) := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, mem_ball_comm.1 hz.2.2⟩
      have hcard : ((F.filter (fun z => z ∈ ball q τ ∧ w ∈ ball z (τ / 20 ^ k))).card : ℝ≥0∞) ≤
          ENNReal.ofReal (161 ^ n * C * ((τ / 20 ^ k) / s) ^ (n - 1)) := by
        rw [← ENNReal.ofReal_natCast]
        refine ENNReal.ofReal_le_ofReal ?_
        refine le_trans ?_ (hcount w hw (hMlt k hk') (by linarith [hakτ k]))
        exact_mod_cast Finset.card_le_card hsub
      have hBk : ENNReal.ofReal (161 ^ n * C * ((τ / 20 ^ k) / s) ^ (n - 1)) * E k * c =
          ENNReal.ofReal B := by
        have hKk : 0 ≤ 161 ^ n * C * ((τ / 20 ^ k) / s) ^ (n - 1) := by
          have := hak k
          positivity
        have hEk : 0 ≤ max CJ 1 / (τ / 20 ^ k) ^ (n - 1) := by
          have := hak k
          positivity
        rw [hE, hc_def]
        dsimp only
        rw [← ENNReal.ofReal_mul hKk, ← ENNReal.ofReal_mul (mul_nonneg hKk hEk)]
        congr 1
        rw [hB, div_pow, div_pow]
        have : (τ / 20 ^ k) ^ (n - 1) ≠ 0 := by have := hak k; positivity
        have : s ^ (n - 1) ≠ 0 := by positivity
        field_simp
      calc _ ≤ ENNReal.ofReal (161 ^ n * C * ((τ / 20 ^ k) / s) ^ (n - 1)) *
            (c * ENNReal.ofReal A * E k * c * G k w) := mul_le_mul_left hcard _
        _ = c * ENNReal.ofReal A *
            (ENNReal.ofReal (161 ^ n * C * ((τ / 20 ^ k) / s) ^ (n - 1)) * E k * c) *
              G k w := by ring
        _ = X * G k w := by rw [hBk, hX]
    · rw [if_neg hwq, mul_zero]
      have hempty : F.filter (fun z => z ∈ ball q τ ∧ w ∈ ball z (τ / 20 ^ k)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun z _ hz => hwq ?_
        rw [mem_ball] at hz ⊢
        have := dist_triangle w z q
        rw [mem_ball] at hz
        linarith [hz.1, hz.2, hakτ k, dist_comm w z]
      rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
  -- Step 3: sum the frequency drops
  have hF2 : ((F.filter (· ∈ ball q (2 * τ))).card : ℝ≥0∞) ≤
      ENNReal.ofReal (161 ^ n * C * (2 * τ / s) ^ (n - 1)) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    refine card_le_of_forall_card_le (w := q) hs hC hyp (by linarith) (by linarith) ?_ ?_
    · intro y hy
      rw [Finset.coe_filter] at hy
      exact ⟨(hF hy.1).1, hy.2⟩
    · exact hFsep.mono (by intro y hy; rw [Finset.coe_filter] at hy; exact hy.1)
  have hfinal : X * (ENNReal.ofReal (161 ^ n * C * (2 * τ / s) ^ (n - 1)) * ENNReal.ofReal δ) =
      ENNReal.ofReal (stepConst n CJ C * δ * τ ^ (n - 1)) := by
    have hcr : 0 ≤ unitBallVolume (n - 1) * s ^ (n - 1) := by positivity
    have hK2 : 0 ≤ 161 ^ n * C * (2 * τ / s) ^ (n - 1) := by positivity
    rw [hX, hc_def, ← ENNReal.ofReal_mul hK2, ← ENNReal.ofReal_mul hcr,
      ← ENNReal.ofReal_mul (mul_nonneg hcr hA0),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hcr hA0) hB0)]
    congr 1
    rw [stepConst, hA, hB, div_pow, mul_pow]
    have : s ^ (n - 1) ≠ 0 := by positivity
    field_simp
  calc ∑ z ∈ F, c *
        (ball q τ).indicator (fun z => ∫⁻ ρ in Ioo 0 τ, jonesBetaSq μ z ρ / ENNReal.ofReal ρ)
          (id z)
      ≤ ∑ z ∈ F, ∑ k ∈ Finset.range M, ∑ w ∈ F,
        if z ∈ ball q τ ∧ w ∈ ball z (τ / 20 ^ k) then
          c * ENNReal.ofReal A * E k * c * G k w else 0 := hstep1
    _ = ∑ k ∈ Finset.range M, ∑ w ∈ F, ∑ z ∈ F,
        if z ∈ ball q τ ∧ w ∈ ball z (τ / 20 ^ k) then
          c * ENNReal.ofReal A * E k * c * G k w else 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range M, ∑ w ∈ F, X * (if w ∈ ball q (2 * τ) then G k w else 0) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun w hw => hstep2 k hk w hw
    _ = X * ∑ w ∈ F, if w ∈ ball q (2 * τ) then ∑ k ∈ Finset.range M, G k w else 0 := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.mul_sum]
        split_ifs <;> simp
    _ ≤ X * ∑ w ∈ F, if w ∈ ball q (2 * τ) then ENNReal.ofReal δ else 0 := by
        gcongr with w hw
        split_ifs
        · exact htel w hw
        · exact le_rfl
    _ = X * ((F.filter (· ∈ ball q (2 * τ))).card * ENNReal.ofReal δ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ X * (ENNReal.ofReal (161 ^ n * C * (2 * τ / s) ^ (n - 1)) * ENNReal.ofReal δ) :=
        mul_le_mul_right (mul_le_mul_left hF2 _) X
    _ = ENNReal.ofReal (stepConst n CJ C * δ * τ ^ (n - 1)) := hfinal
    _ ≤ ENNReal.ofReal (δR ^ 2 / 2 * τ ^ (n - 1)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hδ (by positivity))
    _ < ENNReal.ofReal (δR ^ 2 * τ ^ (n - 1)) :=
        (ENNReal.ofReal_lt_ofReal_iff hδR2).2 (by linarith)

/-! ### Induction on the scale -/

/-- **The induction of Lemma 7.1 (1).** For every `k`, the count `#G ≤ C (σ/s)^{n-1}` holds for
`2s`-separated `G ⊆ S' ∩ B_σ(p)` with `σ ∈ [s, min(r/2, 20^k s)]`. -/
theorem card_le_aux (hn : 2 ≤ n) {CJ : ℝ} (J : JonesData n CJ) {δR DR C δ : ℝ}
    (hR : ∀ (p : Rn n) (σ s : ℝ), 0 < s → s ≤ σ → ∀ F : Finset (Rn n), ↑F ⊆ ball p σ →
      (F : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
      (∀ (y : Rn n) (τ : ℝ), 0 < τ → ball y τ ⊆ ball p (2 * σ) →
        ∫⁻ z in ball y τ, (∫⁻ ρ in Ioo 0 τ,
            jonesBetaSq (discreteMeasure F (fun _ => ENNReal.ofReal
              (unitBallVolume (n - 1) * s ^ (n - 1))) id) z ρ / ENNReal.ofReal ρ)
          ∂(discreteMeasure F (fun _ => ENNReal.ofReal
              (unitBallVolume (n - 1) * s ^ (n - 1))) id) <
          ENNReal.ofReal (δR ^ 2 * τ ^ (n - 1))) →
      (F.card : ℝ) * s ^ (n - 1) < DR * σ ^ (n - 1))
    (hDC : DR ≤ C) (hC : 1 ≤ C) (hδ : stepConst n CJ C * δ ≤ δR ^ 2 / 2)
    (hδR : 0 < δR) {x : Rn n} {r s : ℝ} (hrR : r ≤ J.R) (hs : 0 < s) (hts : J.t ≤ s)
    (hN : ∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δ) (k : ℕ) :
    ∀ (p : Rn n) (σ : ℝ), s ≤ σ → σ ≤ min (r / 2) (20 ^ k * s) → ∀ G : Finset (Rn n),
      ↑G ⊆ (J.S ∩ ball x r) ∩ ball p σ →
      (G : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
      (G.card : ℝ) ≤ C * (σ / s) ^ (n - 1) := by
  induction k with
  | zero =>
    intro p σ hsσ hσ G hG hGsep
    have hσs : σ ≤ s := by simpa using hσ.trans (min_le_right _ _)
    have h1 : G.card ≤ 1 := card_le_one_of_pairwise_le_dist (p := p) (σ := σ) (by linarith)
      (fun y hy => (hG hy).2) hGsep
    have : 1 ≤ (σ / s) ^ (n - 1) := one_le_pow₀ ((le_div_iff₀ hs).2 (by linarith))
    calc (G.card : ℝ) ≤ 1 := by exact_mod_cast h1
      _ ≤ C * (σ / s) ^ (n - 1) := by nlinarith
  | succ k ih =>
    intro p σ hsσ hσ G hG hGsep
    have h1 : σ ≤ r / 2 := hσ.trans (min_le_left _ _)
    have h2 : σ ≤ 20 ^ (k + 1) * s := hσ.trans (min_le_right _ _)
    have hσb : σ ≤ 20 * min (r / 2) (20 ^ k * s) := by
      rcases min_cases (r / 2) (20 ^ k * s) with h | h
      · rw [h.1]
        linarith
      · rw [h.1]
        rw [pow_succ] at h2
        linarith
    exact card_le_step hn J hR hDC hC hδ hδR hrR hs hts hN ih hsσ (by linarith) hσb hG hGsep

/-! ### Lemma 7.1 (1) and (2) -/

/-- **Lemma 7.1 (1)**, for abstract data. There are `δ(n, CJ) > 0` and `C(n, CJ)`
such that the following holds. Let `0 < r ≤ R` and assume `N_z(20 r) < 1 + δ` for every
`z ∈ S ∩ B_r(x)`. Then for `s ∈ [t, r]`, `s > 0`, every `2s`-separated finite subset of
`S ∩ B_r(x)` (equivalently: every family of disjoint balls `B_s(x_i)` centred there) has at most
`C (r/s)^{n-1}` points.

The paper's hypothesis is `N^max_t(x, r) < 1 + δ`, which bounds `N_z(20 r)` on `S ∩ B̄_r(x)`.
Here only `z ∈ S ∩ B_r(x)` is needed. -/
theorem card_le_of_frequency_lt (hn : 2 ≤ n) (CJ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (J : JonesData n CJ) (x : Rn n) (r : ℝ),
      0 < r → r ≤ J.R → (∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δ) →
      ∀ s : ℝ, 0 < s → J.t ≤ s → s ≤ r → ∀ F : Finset (Rn n), ↑F ⊆ J.S ∩ ball x r →
        (F : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
        (F.card : ℝ) ≤ C * (r / s) ^ (n - 1) := by
  obtain ⟨δR, hδR, DR, hR⟩ := discrete_reifenberg_finset (n := n) hn
  set C := max DR 1 with hC_def
  have hC : 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  have hK := stepConst_pos n CJ hC0
  refine ⟨δR ^ 2 / 2 / stepConst n CJ C, by positivity, 161 ^ n * C, by positivity, ?_⟩
  intro J x r hr hrR hN s hs hts hsr F hF hFsep
  have hδ : stepConst n CJ C * (δR ^ 2 / 2 / stepConst n CJ C) ≤ δR ^ 2 / 2 :=
    (mul_div_cancel₀ _ hK.ne').le
  have P := card_le_aux hn J hR (le_max_left _ _) hC hδ hδR hrR hs hts hN
  rcases hsr.lt_or_eq with hsr' | rfl
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (r / s) (by norm_num : (1 : ℝ) < 20)
    have hk' : r / 80 ≤ min (r / 2) (20 ^ k * s) := by
      refine le_min (by linarith) ?_
      rw [div_lt_iff₀ hs] at hk
      linarith
    exact card_le_of_forall_card_le hs hC (P k) hsr' hk'
      (fun y hy => ⟨hF hy, (hF hy).2⟩) hFsep
  · have h1 : F.card ≤ 1 := card_le_one_of_pairwise_le_dist (p := x) (σ := s) le_rfl
      (fun y hy => (hF hy).2) hFsep
    rw [div_self hs.ne', one_pow, mul_one]
    calc (F.card : ℝ) ≤ 1 := by exact_mod_cast h1
      _ ≤ 161 ^ n * C := by
        have : (1 : ℝ) ≤ 161 ^ n := one_le_pow₀ (by norm_num)
        nlinarith

/-- **Counts give a Minkowski bound.** If every `2s`-separated finite subset of `A ⊆ B_r(x)` has at
most `C (r/s)^{n-1}` points, then `|B_s(A)| ≤ 3ⁿ ω_n C s r^{n-1}`. A maximal `2s`-separated subset
`F` of `A` gives `B_s(A) ⊆ ⋃_{y ∈ F} B_{3s}(y)` (Vitali). -/
theorem volume_thickening_le_of_card_le (hn : 0 < n) {A : Set (Rn n)} {x : Rn n} {r s C : ℝ}
    (hA : A ⊆ ball x r) (hs : 0 < s)
    (hcard : ∀ F : Finset (Rn n), ↑F ⊆ A →
      (F : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
      (F.card : ℝ) ≤ C * (r / s) ^ (n - 1)) :
    volume (thickening s A) ≤ ENNReal.ofReal (C * 3 ^ n * unitBallVolume n * s * r ^ (n - 1)) := by
  classical
  have h2s : 0 < 2 * s := by positivity
  obtain ⟨hFA, hFsep, hcov⟩ := net_spec (hA.trans ball_subset_closedBall) h2s
  have hsub : thickening s A ⊆ ⋃ y ∈ net A (2 * s), ball y (3 * s) := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := mem_thickening_iff.1 hz
    obtain ⟨y, hy, hay⟩ := mem_iUnion₂.1 (hcov ha)
    refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
    rw [mem_ball] at hay ⊢
    linarith [dist_triangle z a y]
  have hF := hcard _ hFA hFsep
  have hC : 0 ≤ C * (r / s) ^ (n - 1) := (Nat.cast_nonneg _).trans hF
  calc volume (thickening s A) ≤ volume (⋃ y ∈ net A (2 * s), ball y (3 * s)) := measure_mono hsub
    _ ≤ ∑ y ∈ net A (2 * s), volume (ball y (3 * s)) := measure_biUnion_finset_le _ _
    _ = (net A (2 * s)).card * ENNReal.ofReal (unitBallVolume n * (3 * s) ^ n) := by
        rw [Finset.sum_congr rfl fun y _ => volume_ball_eq y (by positivity : 0 < 3 * s),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (C * (r / s) ^ (n - 1)) *
          ENNReal.ofReal (unitBallVolume n * (3 * s) ^ n) := by
        refine mul_le_mul_left ?_ _
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hF
    _ = ENNReal.ofReal (C * 3 ^ n * unitBallVolume n * s * r ^ (n - 1)) := by
        rw [← ENNReal.ofReal_mul hC]
        congr 1
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hs0 : s ≠ 0 := hs.ne'
        simp only [Nat.add_sub_cancel]
        rw [div_pow, mul_pow]
        field_simp
        ring

/-- **Lemma 7.1 (1)–(2)**, for abstract data. There are
`δ(n, CJ) > 0` and `C(n, CJ)` such that, if `0 < r ≤ R` and `N_z(20 r) < 1 + δ` for every
`z ∈ S ∩ B_r(x)`, then for every `s ∈ [t, r]`, `s > 0`:

1. every `2s`-separated finite subset of `S ∩ B_r(x)` has at most `C (r/s)^{n-1}` points;
2. `|B_s(S ∩ B_r(x))| ≤ C s r^{n-1}`. -/
theorem volume_estimate_of_frequency_lt (hn : 2 ≤ n) (CJ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (J : JonesData n CJ) (x : Rn n) (r : ℝ),
      0 < r → r ≤ J.R → (∀ z ∈ J.S ∩ ball x r, J.N z (20 * r) < 1 + δ) →
      (∀ s : ℝ, 0 < s → J.t ≤ s → s ≤ r → ∀ F : Finset (Rn n), ↑F ⊆ J.S ∩ ball x r →
        (F : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
        (F.card : ℝ) ≤ C * (r / s) ^ (n - 1)) ∧
      (∀ s : ℝ, 0 < s → J.t ≤ s → s ≤ r →
        volume (thickening s (J.S ∩ ball x r)) ≤ ENNReal.ofReal (C * s * r ^ (n - 1))) := by
  obtain ⟨δ, hδ, C, hC, h⟩ := card_le_of_frequency_lt hn CJ
  have hω := unitBallVolume_pos n
  refine ⟨δ, hδ, C * (1 + 3 ^ n * unitBallVolume n), by positivity, ?_⟩
  intro J x r hr hrR hN
  have hC' : C ≤ C * (1 + 3 ^ n * unitBallVolume n) := by
    have : 0 ≤ C * (3 ^ n * unitBallVolume n) := by positivity
    nlinarith
  refine ⟨fun s hs hts hsr F hF hFsep => ?_, fun s hs hts hsr => ?_⟩
  · refine (h J x r hr hrR hN s hs hts hsr F hF hFsep).trans ?_
    exact mul_le_mul_of_nonneg_right hC' (by positivity)
  · refine (volume_thickening_le_of_card_le (by omega) inter_subset_right hs
      fun F hF hFsep => h J x r hr hrR hN s hs hts hsr F hF hFsep).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have : C * 3 ^ n * unitBallVolume n ≤ C * (1 + 3 ^ n * unitBallVolume n) := by nlinarith
    calc C * 3 ^ n * unitBallVolume n * s * r ^ (n - 1)
        = (C * 3 ^ n * unitBallVolume n) * (s * r ^ (n - 1)) := by ring
      _ ≤ C * (1 + 3 ^ n * unitBallVolume n) * (s * r ^ (n - 1)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = C * (1 + 3 ^ n * unitBallVolume n) * s * r ^ (n - 1) := by ring

end InnerVariational.NaberValtorta
