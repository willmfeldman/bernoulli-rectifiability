/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Estimates.Dichotomy.Setup
public import InnerVariational.Kernel.Rescale
public import InnerVariational.Blowup.Approx1D
public import InnerVariational.Defs.HighestDensity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Estimates.GeneralPosition
import InnerVariational.Estimates.Dichotomy.Rescale
import InnerVariational.Frequency.Concrete
import InnerVariational.Basic.Polar

/-!
# Theorem 6.3: the frequency drop dichotomy

This file proves Theorem 6.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be
a variational solution on `B_{50r}(x)`, `δ > 0`, `N₊`, and
`t ∈ [0, r]`. Put `N̄ = max_{y ∈ B̄_r(x) ∩ Σ^H_t} N_y(u; 20r) ≤ N₊`. Then there is
`ε = ε(N₊, δ, n) ∈ (0, 1)` such that either `N̄ < 1 + δ`, or the set
`E = {y ∈ B̄_r(x) ∩ Σ^H_t : N̄ − N_y(u; r) < ε}` lies in the `δr`-neighbourhood of an affine
subspace of dimension `≤ n − 2`.

## Main results

* `frequency_drop_dichotomy_of_subset`: the theorem for an arbitrary set `S ⊆ B̄_r(x)` of points
  `y ∈ closure {u > 0}` with `M_y(u; t) ≥ |B_1|` for some `t ∈ (0, r]`, in place of
  `B̄_r(x) ∩ Σ^H_t`.
* `frequency_drop_dichotomy`: the theorem for `Σ^H_t = sigmaHr`, `t ∈ [0, r]`. At `t = 0` the
  set `sigmaHr Ω u χ 0` is empty (`sigmaHr_zero`), so this case is vacuous.
* `frequency_drop_dichotomy_sigmaH`: the case `t = 0` in the paper's sense, `Σ^H_0 = Σ^H`.

## Proof

By contradiction and compactness, as in the paper. Take counterexamples with
`ε_k = 1/(2(k+1)) → 0`. In each, `E_k` lies in no `δr`-neighbourhood of an `(n−2)`-plane, so it
contains points `a₀, a_1, …, a_{n−1}` in `δr`-general position (`Estimates/GeneralPosition.lean`,
with coefficient bound `C(δ, n)` in place of the `1/δ` stated in the proof).
The one-step estimate (`exists_tangential_bound`) bounds the tangential energy of `u_k` on
`B_{10r}(a₀) ∖ B_{5r}(a₀)`, with respect to the unit normal `ν_k` of the `a_i − a₀`, by
`K (ε_k + 2ε_k²) (10r)ⁿ H_{a₀}(10r)`. Theorem 5.3, in its direction-free form
`approx1D_limit_frequency_eq_one`, is applied to `u_k` rescaled at `a₀` with scale `10 r` and
gives `N_{a₀}(u_k; 5r) → 1`. But `N_{a₀}(u_k; 5r) > N̄_k − ε_k ≥ 1 + δ − ε_k`, a contradiction.

## Deviations

* **Maximum as `sSup`.** The paper's `N̄` is a maximum. We use
  `maxFrequencyN u χ S r = sSup {N_y(u; 20r) : y ∈ S}`. The proof only uses
  `N_y(u; 20r) ≤ N̄` for `y ∈ S`, which holds when the image is bounded above. If the image is not
  bounded above, `sSup = 0 < 1 + δ` and the first alternative holds trivially. For a variational
  solution the maximum is attained (continuity of `y ↦ N_y(u; 20r)`, `Frequency/Concrete.lean`),
  so this case does not
  arise and the formal statement is not stronger than the paper's.
* **`t = 0`.** `sigmaHr Ω u χ 0` is empty with our definitions (`M_x(u; 0) = 0`). The paper's
  `Σ^H_0` (not defined there) means `Σ^H`; that case is `frequency_drop_dichotomy_sigmaH`.
* **Domain.** The paper assumes a variational solution on `B_{50r}(x)`; we assume
  `ball x (50 r) ⊆ Ω`. The proof only uses `B_{31r}(x)`.
* **Lemma 6.2 is not used**, **scale 10 instead of 18**, and **comparability of `H` centred
  at `a₀`**: see `Estimates/Dichotomy/Setup.lean`.
-/

open MeasureTheory Metric Set Filter Topology Module InnerProductSpace
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The maximal frequency `N̄ = sup_{y ∈ S} N_y(u; 20 r)` of Theorem 6.3 and Section 7
(the paper's `N^max`), as a supremum instead of a maximum (see the module docstring). -/
def maxFrequencyN (u χ : Rn n → ℝ) (S : Set (Rn n)) (r : ℝ) : ℝ :=
  sSup ((fun y => frequencyN u χ y (20 * r)) '' S)

/-- `M_x(u; 0) = 0`: both `D` and `H` vanish at radius `0` with our conventions. -/
theorem monotonicityM_zero (u χ : Rn n → ℝ) (x : Rn n) : monotonicityM u χ x 0 = 0 := by
  simp [monotonicityM, energyD, heightH]

/-- With our definitions `Σ^H_0` is empty: `M_x(u; 0) = 0 < |B_1|`. The paper's `Σ^H_0` (which
it does not define) means `Σ^H`. -/
theorem sigmaHr_zero (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : sigmaHr Ω u χ 0 = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  have h := hy.2.2.2
  rw [monotonicityM_zero] at h
  exact (unitBallVolume_pos n).not_ge h

namespace Dichotomy

/-- The tolerances `ε_k = 1/(2(k+1))` of the contradiction argument. -/
def tol (k : ℕ) : ℝ := 1 / 2 * (1 / ((k : ℝ) + 1))

theorem tol_mem_Ioo (k : ℕ) : tol k ∈ Ioo (0 : ℝ) 1 := by
  have h1 : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  exact ⟨by unfold tol; positivity, by unfold tol; linarith⟩

theorem tendsto_tol : Tendsto tol atTop (𝓝 0) := by
  have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
  rw [mul_zero] at this
  exact this

end Dichotomy

open Dichotomy in
/-- **Theorem 6.3** for an arbitrary set `S ⊆ B̄_r(x)` of
points `y ∈ closure {u > 0}` with `M_y(u; t) ≥ |B_1|` for some `t ∈ (0, r]`. The constant `ε`
depends only on `n`, `N₊` and `δ`. -/
theorem frequency_drop_dichotomy_of_subset (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np δ : ℝ)
    (hδ : 0 < δ) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ)
      (S : Set (Rn n)),
      IsVariationalSolution Ω C u χ → 0 < r → ball x (50 * r) ⊆ Ω → S ⊆ closedBall x r →
      (∀ y ∈ S, y ∈ closure {z | 0 < u z} ∧
        ∃ t, 0 < t ∧ t ≤ r ∧ unitBallVolume n ≤ monotonicityM u χ y t) →
      maxFrequencyN u χ S r ≤ Np →
      maxFrequencyN u χ S r < 1 + δ ∨
        ∃ L : AffineSubspace ℝ (Rn n), finrank ℝ L.direction ≤ n - 2 ∧
          {y ∈ S | maxFrequencyN u χ S r - frequencyN u χ y r < ε} ⊆
            thickening (δ * r) (L : Set (Rn n)) := by
  obtain ⟨K, hK0, hK⟩ := exists_tangential_bound n Np hδ
  by_contra hcon
  -- a counterexample for each tolerance `tol k`
  have key : ∀ k : ℕ, ∃ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ)
      (S : Set (Rn n)),
      IsVariationalSolution Ω C u χ ∧ 0 < r ∧ ball x (50 * r) ⊆ Ω ∧ S ⊆ closedBall x r ∧
      (∀ y ∈ S, y ∈ closure {z | 0 < u z} ∧
        ∃ t, 0 < t ∧ t ≤ r ∧ unitBallVolume n ≤ monotonicityM u χ y t) ∧
      maxFrequencyN u χ S r ≤ Np ∧ 1 + δ ≤ maxFrequencyN u χ S r ∧
      ∀ L : AffineSubspace ℝ (Rn n), finrank ℝ L.direction ≤ n - 2 →
        ¬ {y ∈ S | maxFrequencyN u χ S r - frequencyN u χ y r < tol k} ⊆
          thickening (δ * r) (L : Set (Rn n)) := by
    intro k
    by_contra hk
    refine hcon ⟨tol k, tol_mem_Ioo k, fun Ω C u χ x r S h1 h2 h3 h4 h5 h6 => ?_⟩
    by_contra hne
    exact hk ⟨Ω, C, u, χ, x, r, S, h1, h2, h3, h4, h5, h6,
      not_lt.1 fun hlt => hne (Or.inl hlt), fun L hL hsub => hne (Or.inr ⟨L, hL, hsub⟩)⟩
  choose Ω C u χ x r S hsol hr hΩ hSx hSy hNp hbig hnot using key
  -- the maximal frequencies are genuine suprema
  have hbdd : ∀ k, BddAbove ((fun y => frequencyN (u k) (χ k) y (20 * r k)) '' S k) := by
    intro k
    by_contra hb
    have h0 : maxFrequencyN (u k) (χ k) (S k) (r k) = 0 := Real.sSup_of_not_bddAbove hb
    have := hbig k
    rw [h0] at this
    linarith
  -- the points of `E_k` are pinched
  have hpinch : ∀ k, ∀ y ∈ S k,
      maxFrequencyN (u k) (χ k) (S k) (r k) - frequencyN (u k) (χ k) y (r k) < tol k →
      IsPinched (u k) (χ k) (x k) (r k) (maxFrequencyN (u k) (χ k) (S k) (r k)) (tol k) y := by
    intro k y hy hyE
    obtain ⟨hcl, t, ht, htr, hM⟩ := hSy k y hy
    exact ⟨hSx k hy, hcl, ⟨t, ht, htr, hM⟩, le_csSup (hbdd k) (mem_image_of_mem _ hy),
      by linarith⟩
  -- general position and the one-step estimate
  have hstep : ∀ k, ∃ a₀ : Rn n,
      IsPinched (u k) (χ k) (x k) (r k) (maxFrequencyN (u k) (χ k) (S k) (r k)) (tol k) a₀ ∧
      ∃ ν : Rn n, ‖ν‖ = 1 ∧
        ∫ z in ball a₀ (10 * r k) \ ball a₀ (10 * r k / 2),
            ‖gradient (u k) z - ⟪gradient (u k) z, ν⟫ • ν‖ ^ 2 ≤
          K * (tol k + 2 * tol k ^ 2) * ((10 * r k) ^ n * heightH (u k) a₀ (10 * r k)) := by
    intro k
    have hEx : {y ∈ S k | maxFrequencyN (u k) (χ k) (S k) (r k) -
        frequencyN (u k) (χ k) y (r k) < tol k} ⊆ closedBall (x k) (r k) :=
      fun y hy => hSx k hy.1
    obtain ⟨a₀, ha₀E, a, haE, -, horth, hcoef⟩ :=
      exists_generalPosition_orthonormal hδ (hr k) hEx (hnot k)
    have ha₀ := hpinch k a₀ ha₀E.1 ha₀E.2
    have ha : ∀ i, IsPinched (u k) (χ k) (x k) (r k) (maxFrequencyN (u k) (χ k) (S k) (r k))
        (tol k) (a i) := fun i => hpinch k (a i) (haE i).1 (haE i).2
    obtain ⟨ν, hν, hbound⟩ := hK (Ω k) (C k) (u k) (χ k) (x k) a₀ a (r k)
      (maxFrequencyN (u k) (χ k) (S k) (r k)) (tol k) (hsol k) (hr k) (hΩ k) (hNp k) ha₀ ha
      horth fun i => by
        obtain ⟨c, -, hcb, hce⟩ := hcoef i
        exact ⟨c, hcb, hce⟩
    exact ⟨a₀, ha₀, ν, hν, hbound⟩
  choose a₀ ha₀ ν hν hbound using hstep
  -- the rescaled sequence at scale `10 r` (the paper's `18` is outside the pinched range)
  have hρpos : ∀ k, 0 < 10 * r k := fun k => by linarith [hr k]
  set v : ℕ → Rn n → ℝ := fun k => oneHomRescale (u k) (a₀ k) (10 * r k) with hv
  set η : ℕ → Rn n → ℝ := fun k => chiRescale (χ k) (a₀ k) (10 * r k) with hη
  have hNρ : ∀ k (s : ℝ),
      frequencyN (v k) (η k) 0 s = frequencyN (u k) (χ k) (a₀ k) (10 * r k * s) :=
    fun k s => frequencyN_oneHomRescale (u k) (χ k) (a₀ k) (hρpos k) s
  have hMρ : ∀ k (s : ℝ),
      monotonicityM (v k) (η k) 0 s = monotonicityM (u k) (χ k) (a₀ k) (10 * r k * s) :=
    fun k s => monotonicityM_oneHomRescale (u k) (χ k) (a₀ k) (hρpos k) s
  have hHρ : ∀ k, heightH (v k) 0 1 = heightH (u k) (a₀ k) (10 * r k) := fun k => by
    have := heightH_oneHomRescale (u k) (a₀ k) (hρpos k) 1
    rwa [mul_one] at this
  have hTρ : ∀ k, ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2 =
      ((10 * r k) ^ n)⁻¹ * ∫ y in ball (a₀ k) (10 * r k) \ ball (a₀ k) (10 * r k / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2 := fun k =>
    setIntegral_tangential_oneHomRescale (u k) (a₀ k) (hρpos k) (ν k)
  have hΩ' : ∀ k, ball (0 : Rn n) 3 ⊆ (fun y => a₀ k + (10 * r k) • y) ⁻¹' Ω k := by
    intro k y hy
    refine hΩ k ?_
    have h1 := mem_closedBall.1 (ha₀ k).mem_closedBall
    have h2 : ‖y‖ < 3 := mem_ball_zero_iff.1 hy
    have h3 := mul_lt_mul_of_pos_left h2 (hρpos k)
    rw [mem_ball]
    calc dist (a₀ k + (10 * r k) • y) (x k) ≤
          dist (a₀ k + (10 * r k) • y) (a₀ k) + dist (a₀ k) (x k) := dist_triangle _ _ _
      _ = 10 * r k * ‖y‖ + dist (a₀ k) (x k) := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hρpos k).le]
      _ < 50 * r k := by linarith [hr k]
  have hsol' : ∀ k, IsVariationalSolution (ball (0 : Rn n) 3) (C k) (v k) (η k) := fun k =>
    ((hsol k).rescale (a₀ k) (hρpos k)).mono isOpen_ball (hΩ' k)
  have hcl' : ∀ k, (0 : Rn n) ∈ closure {y | 0 < v k y} := fun k =>
    (zero_mem_closure_oneHomRescale_iff (u k) (a₀ k) (hρpos k)).2 (ha₀ k).mem_closure
  have e5 : ∀ k, 10 * r k * (1 / 2) = 5 * r k := fun k => by ring
  have e20 : ∀ k, 10 * r k * 2 = 20 * r k := fun k => by ring
  have h5 : ∀ k, 5 * r k ∈ Icc (r k) (20 * r k) := fun k =>
    ⟨by linarith [hr k], by linarith [hr k]⟩
  have h20 : ∀ k, 20 * r k ∈ Icc (r k) (20 * r k) := fun k => ⟨by linarith [hr k], le_rfl⟩
  have hM' : ∀ k, unitBallVolume n ≤ monotonicityM (v k) (η k) 0 (1 / 2) := fun k => by
    rw [hMρ, e5]
    exact ((ha₀ k).frequencyN_mem (hsol k) (hr k) (hΩ k)).1 _ (h5 k)
  have hN' : ∀ k, frequencyN (v k) (η k) 0 2 ≤ Np := fun k => by
    rw [hNρ, e20]
    exact (((ha₀ k).frequencyN_mem (hsol k) (hr k) (hΩ k)).2.2 _ (h20 k)).2.trans (hNp k)
  have hpinchN : ∀ k, 0 ≤ frequencyN (v k) (η k) 0 2 - frequencyN (v k) (η k) 0 (1 / 2) ∧
      frequencyN (v k) (η k) 0 2 - frequencyN (v k) (η k) 0 (1 / 2) ≤ tol k := fun k => by
    rw [hNρ, hNρ, e5, e20]
    obtain ⟨-, hmono, hN⟩ := (ha₀ k).frequencyN_mem (hsol k) (hr k) (hΩ k)
    have hle := hmono (h5 k) (h20 k) (by linarith [hr k])
    have ha := hN _ (h5 k)
    have hb := hN _ (h20 k)
    constructor <;> linarith [ha.1, hb.2]
  have hδ' : Tendsto (fun k => frequencyN (v k) (η k) 0 2 - frequencyN (v k) (η k) 0 (1 / 2))
      atTop (𝓝 0) :=
    squeeze_zero (fun k => (hpinchN k).1) (fun k => (hpinchN k).2) tendsto_tol
  -- the tangential energy of the rescaled sequence
  have htan_le : ∀ k, 0 ≤ (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) / heightH (v k) 0 1 ∧
      (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) / heightH (v k) 0 1 ≤
        K * (tol k + 2 * tol k ^ 2) := fun k => by
    have hHpos : 0 < heightH (u k) (a₀ k) (10 * r k) :=
      (hsol k).heightH_pos (ha₀ k).mem_closure (hρpos k)
        ((ha₀ k).closedBall_subset (hΩ k) (by linarith [hr k]))
    rw [hTρ, hHρ]
    have hρn : 0 < (10 * r k) ^ n := pow_pos (hρpos k) n
    constructor
    · refine div_nonneg (mul_nonneg (inv_nonneg.2 hρn.le) ?_) hHpos.le
      exact setIntegral_nonneg (measurableSet_ball.diff measurableSet_ball)
        fun _ _ => sq_nonneg _
    · rw [div_le_iff₀ hHpos]
      calc ((10 * r k) ^ n)⁻¹ * ∫ y in ball (a₀ k) (10 * r k) \ ball (a₀ k) (10 * r k / 2),
            ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2 ≤
          ((10 * r k) ^ n)⁻¹ * (K * (tol k + 2 * tol k ^ 2) *
            ((10 * r k) ^ n * heightH (u k) (a₀ k) (10 * r k))) :=
            mul_le_mul_of_nonneg_left (hbound k) (inv_nonneg.2 hρn.le)
        _ = K * (tol k + 2 * tol k ^ 2) * heightH (u k) (a₀ k) (10 * r k) := by
            rw [mul_left_comm (K * (tol k + 2 * tol k ^ 2)), ← mul_assoc,
              inv_mul_cancel₀ hρn.ne', one_mul]
  have htol2 : Tendsto (fun k => K * (tol k + 2 * tol k ^ 2)) atTop (𝓝 0) := by
    have := (tendsto_tol.add ((tendsto_tol.pow 2).const_mul 2)).const_mul K
    simpa using this
  have htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) / heightH (v k) 0 1)
      atTop (𝓝 0) :=
    squeeze_zero (fun k => (htan_le k).1) (fun k => (htan_le k).2) htol2
  -- Theorem 5.3, direction-free form
  have hlim := approx1D_limit_frequency_eq_one hn hν hsol'
    (closedBall_subset_ball (by norm_num)) hcl' hM' hN' hδ' htan
  -- the contradiction: `N_{a₀}(u_k; 5r) > N̄_k − ε_k ≥ 1 + δ − ε_k`
  have hev1 : ∀ᶠ k in atTop, frequencyN (v k) (η k) 0 (1 / 2) < 1 + δ / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ k in atTop, tol k < δ / 2 := tendsto_tol.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  rw [hNρ, e5] at hk1
  have h1 := (((ha₀ k).frequencyN_mem (hsol k) (hr k) (hΩ k)).2.2 _ (h5 k)).1
  have h2 := hbig k
  linarith

/-- **Theorem 6.3**, with `Σ^H_t = sigmaHr Ω u χ t` and `t ∈ [0, r]`. The constant
`ε ∈ (0, 1)` depends only on `n`, `N₊` and `δ`. The maximum is a supremum (see the module
docstring). At `t = 0` the hypothesis
`(B̄_r(x) ∩ Σ^H_0).Nonempty` fails (`sigmaHr_zero`); the paper's `t = 0` case is
`frequency_drop_dichotomy_sigmaH`. -/
theorem frequency_drop_dichotomy (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np δ : ℝ) (hδ : 0 < δ) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r t : ℝ),
      IsVariationalSolution Ω C_V u χ → 0 < r → ball x (50 * r) ⊆ Ω → t ∈ Icc 0 r →
      (closedBall x r ∩ sigmaHr Ω u χ t).Nonempty →
      let Nmax := sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ L : AffineSubspace ℝ (Rn n),
        finrank ℝ L.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHr Ω u χ t | Nmax - frequencyN u χ y r < ε} ⊆
          thickening (δ * r) (L : Set (Rn n)) := by
  obtain ⟨ε, hε, H⟩ := frequency_drop_dichotomy_of_subset n hn Np δ hδ
  refine ⟨ε, hε, fun Ω C_V u χ x r t hsol hr hΩ ht hne => ?_⟩
  intro Nmax hN
  have ht0 : 0 < t := by
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      obtain ⟨y, hy⟩ := hne
      rw [sigmaHr_zero] at hy
      exact absurd hy.2 (notMem_empty y)
    · exact h0
  exact H Ω C_V u χ x r _ hsol hr hΩ inter_subset_left
    (fun y hy => ⟨hy.2.2.2.1, t, ht0, ht.2, hy.2.2.2.2⟩) hN

/-- **Theorem 6.3 for `Σ^H`** (the paper's case `t = 0`, `Σ^H_0 = Σ^H`). -/
theorem frequency_drop_dichotomy_sigmaH (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np δ : ℝ)
    (hδ : 0 < δ) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ),
      IsVariationalSolution Ω C_V u χ → 0 < r → ball x (50 * r) ⊆ Ω →
      let Nmax := sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaH Ω u χ))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ L : AffineSubspace ℝ (Rn n),
        finrank ℝ L.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaH Ω u χ | Nmax - frequencyN u χ y r < ε} ⊆
          thickening (δ * r) (L : Set (Rn n)) := by
  obtain ⟨ε, hε, H⟩ := frequency_drop_dichotomy_of_subset n hn Np δ hδ
  refine ⟨ε, hε, fun Ω C_V u χ x r hsol hr hΩ => ?_⟩
  intro Nmax hN
  refine H Ω C_V u χ x r _ hsol hr hΩ inter_subset_left
    (fun y hy => ⟨hy.2.2.1, r, hr, le_rfl, ?_⟩) hN
  refine hy.2.2.2 r hr ((closedBall_subset_ball' ?_).trans hΩ)
  have := mem_closedBall.1 hy.1
  linarith

end InnerVariational
