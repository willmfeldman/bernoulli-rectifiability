/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.InstanceQ
public import InnerVariational.NaberValtorta.Main
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.NaberValtorta.CoveringLimit
import InnerVariational.NaberValtorta.Hausdorff
import InnerVariational.NaberValtorta.Covering

/-!
# Theorem 7.2 (1)–(2) for variational solutions with a Lipschitz coefficient

`NaberValtorta.sigmaHQ_main` is Theorem 7.2 (1)–(2) of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2), for a variational solution with a Lipschitz coefficient `Q`
(`QBounds Ω Q L c C'`, `κ = weissKappa L c C'`), in the form of the constant-coefficient
`NaberValtorta.sigmaH_main`. The paper treats `Q ≡ 1`. With a Lipschitz coefficient:

* the frequency is the modified frequency `Ñ = N + κ² s²/2` (`modFrequencyN`) and the
  hypothesis is `Ñ_0(u; 1) ≤ N₊`;
* `Σ^H_t` is `Σ^H_{Q,t} = sigmaHQr (B_1) Q u χ κ t` and `Σ^H` is `Σ^H_Q = sigmaHQ (B_1) Q u χ`;
* the smallness `κ ≤ 1/2` is assumed (it holds after rescaling a small ball to `B_1`, since
  `κ` scales like a length; see `NaberValtorta/MainFrequencyQ.lean` for the local consequences
  without this hypothesis).

The constant `C` depends only on `n` and `N₊`, not on `Q`, `L`, `c`, `C'`.

## Proof

As for `Q ≡ 1` (`NaberValtorta/Main.lean`), with the data of `NaberValtorta/InstanceQ.lean`:
`N' = K(n, N₊)` from Lemma 4.6 (`modFrequencyN_change_of_point`), `CJ = C(N', n)` from Theorem 6.1
(`jonesBetaSqQ_le`) and `ε = ε(N', ·, n)` from Theorem 6.3 (`frequency_drop_dichotomyQ`), all
with a Lipschitz coefficient. For (1), `Z_0(t) ≥ 0` propagates to `Z_0(1/4) ≥ 0`
(`modMonotonicityM_nonneg`); for (2), `Z_0(1/4) ≥ 0` holds on `Σ^H_Q`
(`modMonotonicityM_nonneg_of_mem_sigmaHQ`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-- The function `δ ↦ ε(N', δ, n)` of Theorem 6.3 with a Lipschitz coefficient (`1` for
`δ ≤ 0`, where it is never used). -/
def dichotomyEpsQ (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np : ℝ) (δ : ℝ) : ℝ :=
  if hδ : 0 < δ then Classical.choose (frequency_drop_dichotomyQ n hn Np δ hδ) else 1

theorem dichotomyEpsQ_spec (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    dichotomyEpsQ n hn Np δ ∈ Ioo (0 : ℝ) 1 ∧
    ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ) (x : Rn n)
      (r t : ℝ),
      QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ → 0 < r →
      weissKappa L c C' * (50 * r) ≤ 1 / 2 → ball x (50 * r) ⊆ Ω → t ∈ Ioc 0 r →
      let Nmax := sSup ((fun y => modFrequencyN (weissKappa L c C') Q u χ y (20 * r)) ''
        (closedBall x r ∩ sigmaHQr Ω Q u χ (weissKappa L c C') t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ P : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ P.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHQr Ω Q u χ (weissKappa L c C') t |
          Nmax - modFrequencyN (weissKappa L c C') Q u χ y r < dichotomyEpsQ n hn Np δ} ⊆
          thickening (δ * r) (P : Set (Rn n)) := by
  unfold dichotomyEpsQ
  rw [dite_eq_left hδ]
  exact Classical.choose_spec (frequency_drop_dichotomyQ n hn Np δ hδ)

/-- **Theorem 7.2** (1)–(2) with a Lipschitz coefficient. Let `(u, χ)` be a variational solution
for `Q` on an open `Ω ⊇ B̄_1` with `QBounds Ω Q L c C'`, `κ = weissKappa L c C' ≤ 1/2` and
`Ñ_0(u; 1) ≤ N₊`. Then, with `C = C(n, N₊)`:
1. if `0 ∈ Σ^H_{Q,t}(B_1)`, `t > 0`, then `|B_s(Σ^H_{Q,t}(B_1) ∩ B_{1/100})| ≤ C s` for
   `t ≤ s ≤ 1`;
2. if `0 ∈ Σ^H_Q(B_1)`, then `|B_s(Σ^H_Q(B_1) ∩ B_{1/100})| ≤ C s` for `0 < s ≤ 1`,
   `ℋ^{n-1}(Σ^H_Q(B_1) ∩ B_{1/100}) ≤ C`, and `Σ^H_Q(B_1) ∩ B_{1/100}` is countably
   `ℋ^{n-1}`-rectifiable. -/
theorem sigmaHQ_main (hn : 2 ≤ n) (Nplus : ℝ) :
    ∃ C : ℝ, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ),
      QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ → closedBall 0 1 ⊆ Ω →
      weissKappa L c C' ≤ 1 / 2 → modFrequencyN (weissKappa L c C') Q u χ 0 1 ≤ Nplus →
      (∀ t : ℝ, 0 < t → (0 : Rn n) ∈ sigmaHQr (ball 0 1) Q u χ (weissKappa L c C') t →
        ∀ s : ℝ, t ≤ s → s ≤ 1 →
        volume (thickening s (sigmaHQr (ball 0 1) Q u χ (weissKappa L c C') t ∩
          ball 0 (1 / 100))) ≤ ENNReal.ofReal (C * s)) ∧
      ((0 : Rn n) ∈ sigmaHQ (ball 0 1) Q u χ →
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          volume (thickening s (sigmaHQ (ball 0 1) Q u χ ∩ ball 0 (1 / 100))) ≤
            ENNReal.ofReal (C * s)) ∧
        hausdorffN n (n - 1) (sigmaHQ (ball 0 1) Q u χ ∩ ball 0 (1 / 100)) ≤ ENNReal.ofReal C ∧
        IsCountablyRectifiable n (n - 1) (sigmaHQ (ball 0 1) Q u χ ∩ ball 0 (1 / 100))) := by
  have : NeZero n := ⟨by omega⟩
  -- constants
  obtain ⟨Np, hNp⟩ := modFrequencyN_change_of_point n Nplus
  obtain ⟨CJ, hCJ⟩ := jonesBetaSqQ_le n Np
  set ε := dichotomyEpsQ n hn Np with hε_def
  have hεpos : ∀ δ, 0 < δ → 0 < ε δ := fun δ hδ => (dichotomyEpsQ_spec n hn Np hδ).1.1
  obtain ⟨C₁, hC₁, H₁⟩ := volume_thickening_le hn CJ Np ε hεpos
  obtain ⟨C₂, hC₂, H₂⟩ := hausdorffN_le_and_rectifiable_and_frequency hn CJ Np ε hεpos
  -- the cover
  set r₀ : ℝ := 1 / 240 with hr₀_def
  have hr₀ : 0 < r₀ := by norm_num [hr₀_def]
  obtain ⟨F', hF'sub, hF'fin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Rn n) (1 / 100)) hr₀
  set F := hF'fin.toFinset with hF_def
  have hcov : ∀ A : Set (Rn n), A ⊆ ball 0 (1 / 100) → A ⊆ ⋃ p ∈ F, A ∩ ball p r₀ := by
    intro A hA x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hcover (ball_subset_closedBall (hA hx)))
    exact mem_iUnion₂.2 ⟨p, hF'fin.mem_toFinset.2 hp, hx, hxp⟩
  have hcK : ∀ p ∈ F, closedBall p (5 * r₀) ⊆ closedBall (0 : Rn n) (1 / 10) := by
    intro p hp
    have := mem_closedBall.1 (hF'sub (hF'fin.mem_toFinset.1 hp))
    refine closedBall_subset_closedBall' ?_
    rw [hr₀_def]
    linarith
  have hBK : ball (0 : Rn n) (1 / 100) ⊆ closedBall 0 (1 / 10) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  set V := (volume (ball (0 : Rn n) 2)).toReal with hV_def
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set M : ℝ := (F.card : ℝ) with hM_def
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hr₀n : 0 ≤ r₀ ^ (n - 1) := pow_nonneg hr₀.le _
  refine ⟨M * (C₁ + C₂) * r₀ ^ (n - 1) + V / r₀, ?_⟩
  set C := M * (C₁ + C₂) * r₀ ^ (n - 1) + V / r₀ with hC_def
  have hVr : 0 ≤ V / r₀ := div_nonneg hV hr₀.le
  have hCV : V / r₀ ≤ C := by
    have : 0 ≤ M * (C₁ + C₂) * r₀ ^ (n - 1) := by positivity
    linarith
  have hC1 : ∀ s, 0 < s → M * (C₁ * s * r₀ ^ (n - 1)) ≤ C * s := by
    intro s hs
    have : 0 ≤ M * C₂ * r₀ ^ (n - 1) * s + V / r₀ * s := by positivity
    have e : C * s = M * (C₁ * s * r₀ ^ (n - 1)) + (M * C₂ * r₀ ^ (n - 1) * s + V / r₀ * s) := by
      rw [hC_def]; ring
    linarith
  have hC2 : ∀ s, 0 < s → M * (C₂ * s * r₀ ^ (n - 1)) ≤ C * s := by
    intro s hs
    have : 0 ≤ M * C₁ * r₀ ^ (n - 1) * s + V / r₀ * s := by positivity
    have e : C * s = M * (C₂ * s * r₀ ^ (n - 1)) + (M * C₁ * r₀ ^ (n - 1) * s + V / r₀ * s) := by
      rw [hC_def]; ring
    linarith
  have hC3 : M * (C₂ * r₀ ^ (n - 1)) ≤ C := by
    have : 0 ≤ M * C₁ * r₀ ^ (n - 1) + V / r₀ := by positivity
    have e : C = M * (C₂ * r₀ ^ (n - 1)) + (M * C₁ * r₀ ^ (n - 1) + V / r₀) := by
      rw [hC_def]; ring
    linarith
  intro Ω C_V Q u χ L c C' hQ h hΩ hκ hN0
  set κ := weissKappa L c C' with hκdef
  have hk : 0 ≤ κ := weissKappa_nonneg_of_closedBall hQ hΩ
  have hB1 : ball (0 : Rn n) 1 ⊆ Ω := ball_subset_closedBall.trans hΩ
  -- the specialised upstream facts
  have hCJu := fun x r μ => hCJ Ω C_V Q u χ L c C' x r μ hQ h
  have hεu : ∀ δ, 0 < δ → ∀ (x : Rn n) (r t : ℝ), 0 < r → κ * (50 * r) ≤ 1 / 2 →
      ball x (50 * r) ⊆ Ω → t ∈ Ioc 0 r →
      let Nmax := sSup ((fun y => modFrequencyN κ Q u χ y (20 * r)) ''
        (closedBall x r ∩ sigmaHQr Ω Q u χ κ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ P : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ P.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHQr Ω Q u χ κ t |
          Nmax - modFrequencyN κ Q u χ y r < ε δ} ⊆ thickening (δ * r) (P : Set (Rn n)) :=
    fun δ hδ x r t => (dichotomyEpsQ_spec n hn Np hδ).2 Ω C_V Q u χ L c C' x r t hQ h
  have hNK : (0 : Rn n) ∈ closure {y | 0 < u y} → 0 ≤ modMonotonicityM κ Q u χ 0 (1 / 4) →
      ∀ z ∈ closedBall (0 : Rn n) (1 / 10), ∀ ρ, 0 < ρ → ρ < 1 / 2 →
        modFrequencyN κ Q u χ z ρ ≤ Np := by
    intro h0 hZ z hz ρ hρ hρ2
    refine hNp Ω C_V Q u χ L c C' 0 1 hQ h one_pos hΩ h0 hZ (by linarith) hN0 z ?_ ρ hρ
      (by linarith)
    have := mem_closedBall.1 hz
    rw [mem_ball]
    linarith
  have h4Ω : closedBall (0 : Rn n) (1 / 4) ⊆ Ω :=
    (closedBall_subset_closedBall (by norm_num)).trans hΩ
  refine ⟨?_, ?_⟩
  · -- (1)
    intro t ht h0 s hts hs1
    rcases le_or_gt s r₀ with hsr | hsr
    · have htr : t ≤ r₀ := hts.trans hsr
      have ht4 : t ≤ 1 / 4 := by rw [hr₀_def] at htr; linarith
      have hZ4 : 0 ≤ modMonotonicityM κ Q u χ 0 (1 / 4) :=
        h.modMonotonicityM_nonneg hQ h0.2.2.1 ht h0.2.2.2 (by nlinarith) h4Ω ⟨ht4, le_rfl⟩
      let D := solNVDataQ hQ h hΩ hκ hCJu ε hεu t ht (by rw [hr₀_def] at htr; linarith)
        (hNK h0.2.2.1 hZ4)
      refine (volume_thickening_le_of_subset_biUnion (B := fun p => D.S ∩ ball p r₀)
        (a := C₁ * s * r₀ ^ (n - 1)) (fun x hx => ?_) fun p hp => ?_).trans
        (ENNReal.ofReal_le_ofReal (hC1 s (ht.trans_le hts)))
      · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hcov _ inter_subset_right hx)
        refine mem_iUnion₂.2 ⟨p, hp, ⟨?_, hBK hxp.1.2⟩, hxp.2⟩
        exact (mem_sigmaHQr_ball_iff hΩ (hBK hxp.1.2) (by linarith)).1 hxp.1.1
      · exact H₁ D p r₀ hr₀ (by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num) (hcK p hp) s
          (ht.trans_le hts) hts hsr
    · exact volume_thickening_le_of_lt inter_subset_right hr₀ hsr hs1 hCV
  · -- (2)
    intro h0
    have h0Ω : (0 : Rn n) ∈ sigmaHQ Ω Q u χ := ⟨hB1 h0.1, h0.2.1, h0.2.2⟩
    have hZ4 : 0 ≤ modMonotonicityM κ Q u χ 0 (1 / 4) :=
      h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ h0Ω (by norm_num) (by nlinarith) h4Ω
    have hN := hNK h0.2.1 hZ4
    have hmemr : ∀ z ∈ sigmaHQ (ball 0 1) Q u χ ∩ closedBall 0 (1 / 10), ∀ ρ, 0 < ρ → ρ ≤ 1 / 6 →
        z ∈ sigmaHQr Ω Q u χ κ ρ := fun z hz ρ hρ hρ6 =>
      h.mem_sigmaHQr_of_mem_sigmaHQ hQ ⟨hB1 hz.1.1, hz.1.2.1, hz.1.2.2⟩ hρ (by nlinarith)
        (closedBall_subset_of_mem_K hΩ hz.2 (by linarith))
    let J := solJonesDataQ hQ h hΩ hκ hCJu (sigmaHQ (ball 0 1) Q u χ ∩ closedBall 0 (1 / 10)) 0
      le_rfl (measurableSet_sigmaHQ_inter hQ h hΩ) inter_subset_right
      (fun z hz ρ hρ _ hρ6 => hmemr z hz ρ hρ hρ6) (fun z hz => hN z hz.2)
    have hD : ∀ p ∈ F, ∀ s, 0 < s → ∃ D : NVData n CJ Np ε, D.t ≤ s ∧
        J.S ∩ closedBall p (5 * r₀) ⊆ D.S ∧
        (∀ z ∈ J.S ∩ closedBall p (5 * r₀), D.N z = J.N z) ∧
        2 * r₀ ≤ D.R ∧ closedBall p (5 * r₀) ⊆ D.K := by
      intro p hp s hs
      have hτ : 0 < min s r₀ := lt_min hs hr₀
      have hτR : min s r₀ ≤ 1 / 120 := (min_le_right _ _).trans (by rw [hr₀_def]; norm_num)
      refine ⟨solNVDataQ hQ h hΩ hκ hCJu ε hεu (min s r₀) hτ hτR hN, min_le_left _ _, ?_,
        fun z _ => rfl, by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num, hcK p hp⟩
      rintro z ⟨hz, -⟩
      exact ⟨hmemr z hz _ hτ (by linarith), hz.2⟩
    have H := fun p (hp : p ∈ F) => H₂ J p r₀ rfl hr₀
      (by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num) (hD p hp)
    have hsub : sigmaHQ (ball 0 1) Q u χ ∩ ball 0 (1 / 100) ⊆ ⋃ p ∈ F, J.S ∩ ball p r₀ := by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hcov _ inter_subset_right hx)
      exact mem_iUnion₂.2 ⟨p, hp, ⟨hxp.1.1, hBK hxp.1.2⟩, hxp.2⟩
    refine ⟨fun s hs hs1 => ?_, ?_, ?_⟩
    · rcases le_or_gt s r₀ with hsr | hsr
      · exact (volume_thickening_le_of_subset_biUnion hsub (a := C₂ * s * r₀ ^ (n - 1))
          fun p hp => (H p hp).1 s hs hsr).trans (ENNReal.ofReal_le_ofReal (hC2 s hs))
      · exact volume_thickening_le_of_lt inter_subset_right hr₀ hsr hs1 hCV
    · exact (hausdorffN_le_of_subset_biUnion hsub (a := C₂ * r₀ ^ (n - 1))
        fun p hp => (H p hp).2.1).trans (ENNReal.ofReal_le_ofReal hC3)
    · exact (isCountablyRectifiable_biUnion F.countable_toSet fun p hp => (H p hp).2.2.1).mono
        hsub

end InnerVariational.NaberValtorta
