/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Instance
import Mathlib.Data.Real.StarOrdered
public import InnerVariational.NaberValtorta.Inputs
import InnerVariational.NaberValtorta.CoveringLimit
import InnerVariational.NaberValtorta.Hausdorff
import InnerVariational.NaberValtorta.Covering
import GMTFoundations.GMT.ApproxTangent

/-!
# Theorem 7.2 (1)–(2) for variational solutions

`NaberValtorta.sigmaH_main` has exactly the statement of `Statements.sigmaH_main`, Theorem 7.2
(1)–(2) of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), which is proved by it.
The statement differs from the printed one as follows (see `Statements.sigmaH_main`): the ball
`B_{1/100}(x)` (with `x` unbound) is centred at `0`; (1) is stated for `t ≤ s ≤ 1`; the case
`t = 0` uses `Σ^H` (the paper does not define `Σ^H_0`); and the solution is assumed on an open
`Ω ⊇ B̄_1`, since the hypothesis `N_0(u; 1) ≤ N₊` reads `u` on `∂B_1`.

## Proof

Let `N' = K(n, N₊)` be the constant of Lemma 4.6, `CJ = C(N', n)` the constant of Theorem 6.1 and
`ε = ε(N', ·, n)` the function of Theorem 6.3. Theorem 7.2 for the abstract data
(`volume_thickening_le`, `hausdorffN_le_and_rectifiable_and_frequency`) gives constants `C₁`, `C₂`
depending only on `(n, CJ, N', ε)`, hence only on `(n, N₊)`.

Cover `B̄_{1/100}` by finitely many balls `B_{r₀}(c)`, `r₀ = 1/240`, with centres
`c ∈ B̄_{1/100}` (the cover depends only on `n`). Then `2r₀ = R = 1/120` and
`B̄_{5r₀}(c) ⊆ K = B̄_{1/10}`, so the abstract theorems apply on each ball `B_{r₀}(c)` to the
data of `NaberValtorta/Instance.lean`. Summing over the cover gives (1) for `s ≤ r₀` and (2). For
`s ∈ (r₀, 1]` the bound `|B_s(A)| ≤ |B_2| ≤ (|B_2|/r₀) s` for `A ⊆ B_{1/100}` is trivial.

For (1), `s ≤ r₀` forces `t ≤ r₀ ≤ 1/4`, so `M_0(1/4) ≥ M_0(t) ≥ |B_1|` (Proposition 3.4), which
is the hypothesis of Lemma 4.6 at `(0, 1)`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-- The function `δ ↦ ε(N', δ, n)` of Theorem 6.3 (`1` for `δ ≤ 0`, where it is never used). -/
def dichotomyEps (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np : ℝ) (δ : ℝ) : ℝ :=
  if hδ : 0 < δ then Classical.choose (Inputs.frequency_drop_dichotomy n hn Np δ hδ) else 1

theorem dichotomyEps_spec (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    dichotomyEps n hn Np δ ∈ Ioo (0 : ℝ) 1 ∧
    ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r t : ℝ),
      IsVariationalSolution Ω C_V u χ → 0 < r → ball x (50 * r) ⊆ Ω → t ∈ Icc 0 r →
      (closedBall x r ∩ sigmaHr Ω u χ t).Nonempty →
      let Nmax := sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ L : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ L.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHr Ω u χ t | Nmax - frequencyN u χ y r < dichotomyEps n hn Np δ}
          ⊆ thickening (δ * r) (L : Set (Rn n)) := by
  unfold dichotomyEps
  rw [dif_pos hδ]
  exact Classical.choose_spec (Inputs.frequency_drop_dichotomy n hn Np δ hδ)

/-- Summing a volume bound over a finite cover. -/
theorem volume_thickening_le_of_subset_biUnion {A : Set (Rn n)} {F : Finset (Rn n)}
    {B : Rn n → Set (Rn n)} (hA : A ⊆ ⋃ c ∈ F, B c) {s a : ℝ}
    (hB : ∀ c ∈ F, volume (thickening s (B c)) ≤ ENNReal.ofReal a) :
    volume (thickening s A) ≤ ENNReal.ofReal (F.card * a) := by
  have hsub : thickening s A ⊆ ⋃ c ∈ F, thickening s (B c) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 (hA hy)
    exact mem_iUnion₂.2 ⟨c, hc, mem_thickening_iff.2 ⟨y, hyc, hxy⟩⟩
  calc volume (thickening s A) ≤ volume (⋃ c ∈ F, thickening s (B c)) := measure_mono hsub
    _ ≤ ∑ c ∈ F, volume (thickening s (B c)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ F, ENNReal.ofReal a := Finset.sum_le_sum hB
    _ = ENNReal.ofReal (F.card * a) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

/-- Summing a Hausdorff bound over a finite cover. -/
theorem hausdorffN_le_of_subset_biUnion {A : Set (Rn n)} {F : Finset (Rn n)}
    {B : Rn n → Set (Rn n)} (hA : A ⊆ ⋃ c ∈ F, B c) {a : ℝ}
    (hB : ∀ c ∈ F, hausdorffN n (n - 1) (B c) ≤ ENNReal.ofReal a) :
    hausdorffN n (n - 1) A ≤ ENNReal.ofReal (F.card * a) := by
  calc hausdorffN n (n - 1) A ≤ hausdorffN n (n - 1) (⋃ c ∈ F, B c) := measure_mono hA
    _ ≤ ∑ c ∈ F, hausdorffN n (n - 1) (B c) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ F, ENNReal.ofReal a := Finset.sum_le_sum hB
    _ = ENNReal.ofReal (F.card * a) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

/-- The trivial large-scale bound: for `A ⊆ B_{1/100}` and `r₀ < s ≤ 1`,
`|B_s(A)| ≤ |B_2| ≤ (|B_2|/r₀) s`. -/
theorem volume_thickening_le_of_lt {A : Set (Rn n)} (hA : A ⊆ ball 0 (1 / 100)) {r₀ s : ℝ}
    (hr₀ : 0 < r₀) (hs : r₀ < s) (hs1 : s ≤ 1) {C : ℝ}
    (hC : (volume (ball (0 : Rn n) 2)).toReal / r₀ ≤ C) :
    volume (thickening s A) ≤ ENNReal.ofReal (C * s) := by
  have hsub : thickening s A ⊆ ball (0 : Rn n) 2 := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have := mem_ball.1 (hA hy)
    rw [mem_ball]
    calc dist x 0 ≤ dist x y + dist y 0 := dist_triangle _ _ _
      _ < 2 := by linarith
  have hV : 0 ≤ (volume (ball (0 : Rn n) 2)).toReal := ENNReal.toReal_nonneg
  calc volume (thickening s A) ≤ volume (ball (0 : Rn n) 2) := measure_mono hsub
    _ = ENNReal.ofReal (volume (ball (0 : Rn n) 2)).toReal :=
      (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
    _ ≤ ENNReal.ofReal (C * s) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (volume (ball (0 : Rn n) 2)).toReal =
          (volume (ball (0 : Rn n) 2)).toReal / r₀ * r₀ := by
        field_simp
      rw [h1]
      have h2 : 0 ≤ (volume (ball (0 : Rn n) 2)).toReal / r₀ := div_nonneg hV hr₀.le
      nlinarith

/-- **Theorem 7.2** (1)–(2), with exactly the statement of `Statements.sigmaH_main`, whose
docstring lists the differences from the printed statement. See the module docstring for the
proof. -/
theorem sigmaH_main (hn : 2 ≤ n) (Nplus : ℝ) :
    ∃ C : ℝ, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ), IsVariationalSolution Ω C_V u χ →
      closedBall 0 1 ⊆ Ω → frequencyN u χ 0 1 ≤ Nplus →
      (∀ t : ℝ, 0 < t → (0 : Rn n) ∈ sigmaHr (ball 0 1) u χ t → ∀ s : ℝ, t ≤ s → s ≤ 1 →
        volume (thickening s (sigmaHr (ball 0 1) u χ t ∩ ball 0 (1 / 100))) ≤
          ENNReal.ofReal (C * s)) ∧
      ((0 : Rn n) ∈ sigmaH (ball 0 1) u χ →
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          volume (thickening s (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100))) ≤
            ENNReal.ofReal (C * s)) ∧
        hausdorffN n (n - 1) (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100)) ≤ ENNReal.ofReal C ∧
        IsCountablyRectifiable n (n - 1) (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100))) := by
  haveI : NeZero n := ⟨by omega⟩
  -- constants
  obtain ⟨Np, hNp⟩ := Inputs.frequencyN_change_of_point n Nplus
  obtain ⟨CJ, hCJ⟩ := Inputs.jonesBetaSq_le n Np
  set ε := dichotomyEps n hn Np with hε_def
  have hεpos : ∀ δ, 0 < δ → 0 < ε δ := fun δ hδ => (dichotomyEps_spec n hn Np hδ).1.1
  obtain ⟨C₁, hC₁, H₁⟩ := volume_thickening_le hn CJ Np ε hεpos
  obtain ⟨C₂, hC₂, H₂⟩ := hausdorffN_le_and_rectifiable_and_frequency hn CJ Np ε hεpos
  -- the cover
  set r₀ : ℝ := 1 / 240 with hr₀_def
  have hr₀ : 0 < r₀ := by norm_num [hr₀_def]
  obtain ⟨F', hF'sub, hF'fin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Rn n) (1 / 100)) hr₀
  set F := hF'fin.toFinset with hF_def
  have hcov : ∀ A : Set (Rn n), A ⊆ ball 0 (1 / 100) → A ⊆ ⋃ c ∈ F, A ∩ ball c r₀ := by
    intro A hA x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcover (ball_subset_closedBall (hA hx)))
    exact mem_iUnion₂.2 ⟨c, hF'fin.mem_toFinset.2 hc, hx, hxc⟩
  have hcK : ∀ c ∈ F, closedBall c (5 * r₀) ⊆ closedBall (0 : Rn n) (1 / 10) := by
    intro c hc
    have := mem_closedBall.1 (hF'sub (hF'fin.mem_toFinset.1 hc))
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
  have hCV : V / r₀ ≤ C := by
    have : 0 ≤ M * (C₁ + C₂) * r₀ ^ (n - 1) := by positivity
    linarith
  have hC1 : ∀ s, 0 < s → M * (C₁ * s * r₀ ^ (n - 1)) ≤ C * s := by
    intro s hs
    have : 0 ≤ M * C₂ * r₀ ^ (n - 1) * s + V / r₀ * s := by
      have : 0 ≤ V / r₀ := div_nonneg hV hr₀.le
      positivity
    have e : C * s = M * (C₁ * s * r₀ ^ (n - 1)) + (M * C₂ * r₀ ^ (n - 1) * s + V / r₀ * s) := by
      rw [hC_def]; ring
    linarith
  have hC2 : ∀ s, 0 < s → M * (C₂ * s * r₀ ^ (n - 1)) ≤ C * s := by
    intro s hs
    have : 0 ≤ M * C₁ * r₀ ^ (n - 1) * s + V / r₀ * s := by
      have : 0 ≤ V / r₀ := div_nonneg hV hr₀.le
      positivity
    have e : C * s = M * (C₂ * s * r₀ ^ (n - 1)) + (M * C₁ * r₀ ^ (n - 1) * s + V / r₀ * s) := by
      rw [hC_def]; ring
    linarith
  have hC3 : M * (C₂ * r₀ ^ (n - 1)) ≤ C := by
    have : 0 ≤ M * C₁ * r₀ ^ (n - 1) + V / r₀ := by
      have : 0 ≤ V / r₀ := div_nonneg hV hr₀.le
      positivity
    have e : C = M * (C₂ * r₀ ^ (n - 1)) + (M * C₁ * r₀ ^ (n - 1) + V / r₀) := by
      rw [hC_def]; ring
    linarith
  intro Ω C_V u χ h hΩ hN0
  -- the specialised upstream facts
  have hCJu := fun x r μ => hCJ Ω C_V u χ x r μ h
  have hεu : ∀ δ, 0 < δ → ∀ (x : Rn n) (r t : ℝ), 0 < r → ball x (50 * r) ⊆ Ω →
      t ∈ Icc 0 r → (closedBall x r ∩ sigmaHr Ω u χ t).Nonempty →
      let Nmax := sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ L : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ L.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHr Ω u χ t | Nmax - frequencyN u χ y r < ε δ} ⊆
          thickening (δ * r) (L : Set (Rn n)) :=
    fun δ hδ x r t => (dichotomyEps_spec n hn Np hδ).2 Ω C_V u χ x r t h
  have hNK : (0 : Rn n) ∈ closure {y | 0 < u y} →
      unitBallVolume n ≤ monotonicityM u χ 0 (1 / 4) →
      ∀ z ∈ closedBall (0 : Rn n) (1 / 10), ∀ ρ, 0 < ρ → ρ < 1 / 2 → frequencyN u χ z ρ ≤ Np := by
    intro h0 hM z hz ρ hρ hρ2
    refine hNp Ω C_V u χ 0 1 h one_pos hΩ h0 hM hN0 z ?_ ρ hρ (by linarith)
    have := mem_closedBall.1 hz
    rw [mem_ball]
    linarith
  refine ⟨?_, ?_⟩
  · -- (1)
    intro t ht h0 s hts hs1
    rcases le_or_gt s r₀ with hsr | hsr
    · have htr : t ≤ r₀ := hts.trans hsr
      have hM4 : unitBallVolume n ≤ monotonicityM u χ 0 (1 / 4) :=
        h0.2.2.2.trans (Inputs.monotonicityM_le h ht (by rw [hr₀_def] at htr; linarith)
          ((closedBall_subset_closedBall (by norm_num)).trans hΩ))
      let D := solNVData h hΩ hCJu ε hεu t ht (by rw [hr₀_def] at htr; linarith)
        (hNK h0.2.2.1 hM4)
      have hs0 : 0 < s := ht.trans_le hts
      refine (volume_thickening_le_of_subset_biUnion (B := fun c => D.S ∩ ball c r₀)
        (a := C₁ * s * r₀ ^ (n - 1)) (fun x hx => ?_) fun c hc => ?_).trans
        (ENNReal.ofReal_le_ofReal (hC1 s (ht.trans_le hts)))
      · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcov _ inter_subset_right hx)
        refine mem_iUnion₂.2 ⟨c, hc, ⟨?_, hBK hxc.1.2⟩, hxc.2⟩
        exact (mem_sigmaHr_ball_iff hΩ (hBK hxc.1.2) (by rw [hr₀_def] at htr; linarith)).1 hxc.1.1
      · exact H₁ D c r₀ hr₀ (by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num) (hcK c hc) s
          (ht.trans_le hts) hts hsr
    · exact volume_thickening_le_of_lt inter_subset_right hr₀ hsr hs1 hCV
  · -- (2)
    intro h0
    have hM4 : unitBallVolume n ≤ monotonicityM u χ 0 (1 / 4) :=
      h0.2.2 (1 / 4) (by norm_num) (closedBall_subset_ball' (by norm_num))
    have hN := hNK h0.2.1 hM4
    let J := solJonesData h hΩ hCJu (sigmaH (ball 0 1) u χ ∩ closedBall 0 (1 / 10)) 0 le_rfl
      (measurableSet_sigmaH_inter h hΩ) inter_subset_right
      (fun z hz ρ hρ _ hρ6 => (mem_sigmaHr_ball_iff hΩ hz.2 (by linarith)).1
        (mem_sigmaHr_of_mem_sigmaH hz.1 hρ (closedBall_subset_ball_one hz.2 (by linarith))))
      (fun z hz => hN z hz.2)
    have hD : ∀ c ∈ F, ∀ s, 0 < s → ∃ D : NVData n CJ Np ε, D.t ≤ s ∧
        J.S ∩ closedBall c (5 * r₀) ⊆ D.S ∧
        (∀ z ∈ J.S ∩ closedBall c (5 * r₀), D.N z = J.N z) ∧
        2 * r₀ ≤ D.R ∧ closedBall c (5 * r₀) ⊆ D.K := by
      intro c hc s hs
      have hτ : 0 < min s r₀ := lt_min hs hr₀
      have hτR : min s r₀ ≤ 1 / 120 := (min_le_right _ _).trans (by rw [hr₀_def]; norm_num)
      refine ⟨solNVData h hΩ hCJu ε hεu (min s r₀) hτ hτR hN, min_le_left _ _, ?_,
        fun z _ => rfl, by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num, hcK c hc⟩
      rintro z ⟨⟨hzH, hzK⟩, -⟩
      refine ⟨(mem_sigmaHr_ball_iff hΩ hzK (by linarith)).1
        (mem_sigmaHr_of_mem_sigmaH hzH hτ (closedBall_subset_ball_one hzK (by linarith))), hzK⟩
    have H := fun c (hc : c ∈ F) => H₂ J c r₀ rfl hr₀
      (by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num) (hD c hc)
    have hsub : sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100) ⊆ ⋃ c ∈ F, J.S ∩ ball c r₀ := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcov _ inter_subset_right hx)
      exact mem_iUnion₂.2 ⟨c, hc, ⟨hxc.1.1, hBK hxc.1.2⟩, hxc.2⟩
    refine ⟨fun s hs hs1 => ?_, ?_, ?_⟩
    · rcases le_or_gt s r₀ with hsr | hsr
      · exact (volume_thickening_le_of_subset_biUnion hsub (a := C₂ * s * r₀ ^ (n - 1))
          fun c hc => (H c hc).1 s hs hsr).trans (ENNReal.ofReal_le_ofReal (hC2 s hs))
      · exact volume_thickening_le_of_lt inter_subset_right hr₀ hsr hs1 hCV
    · exact (hausdorffN_le_of_subset_biUnion hsub (a := C₂ * r₀ ^ (n - 1))
        fun c hc => (H c hc).2.1).trans (ENNReal.ofReal_le_ofReal hC3)
    · exact (isCountablyRectifiable_biUnion F.countable_toSet fun c hc => (H c hc).2.2.1).mono
        hsub

end InnerVariational.NaberValtorta
