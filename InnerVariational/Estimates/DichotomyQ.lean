/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Estimates.DichotomyQ.Setup
public import InnerVariational.Estimates.Dichotomy
public import InnerVariational.Blowup.Approx1DQ
public import InnerVariational.Kernel.Rescale
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Estimates.GeneralPosition
import InnerVariational.Estimates.Dichotomy.Rescale
import InnerVariational.Frequency.ConcreteQ

/-!
# Theorem 6.3 with a Lipschitz coefficient: the frequency drop dichotomy

Theorem 6.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for a variational
solution with a Lipschitz coefficient `Q` (`QBounds Ω Q L c C'`, `κ = weissKappa L c C'`).

The frequency is the modified frequency `Ñ = N + κ² s²/2` (`modFrequencyN`), which is
nondecreasing and `≥ 1` on `Σ^H_{Q,t}` (`sigmaHQr`). Let `B_{50r}(x) ⊆ Ω` with the standing
smallness `κ · 50 r ≤ 1/2`, `δ > 0`, `N₊`, and `t ∈ (0, r]`. Put
`N̄ = sup_{y ∈ B̄_r(x) ∩ Σ^H_{Q,t}} Ñ_y(u; 20r) ≤ N₊`. Then there is
`ε = ε(N₊, δ, n) ∈ (0, 1)`, independent of `Q`, `L`, `c` and `C'`, such that either `N̄ < 1 + δ`,
or `E = {y ∈ B̄_r(x) ∩ Σ^H_{Q,t} : N̄ − Ñ_y(u; r) < ε}` lies in the `δr`-neighbourhood of an affine
subspace of dimension `≤ n − 2`.

## Main results

* `frequency_drop_dichotomyQ_of_subset`: for an arbitrary set `S ⊆ B̄_r(x)` of points
  `y ∈ closure {u > 0}` with `Z_y(t) ≥ 0` for some `t ∈ (0, r]`.
* `frequency_drop_dichotomyQ`: for `Σ^H_{Q,t} = sigmaHQr Ω Q u χ κ t`, `t ∈ (0, r]`.

## Proof

As in the constant-coefficient case (`Estimates/Dichotomy.lean`): by contradiction and
compactness, with counterexamples for the tolerances `ε_k → 0`, points in general position, the
one-step estimate (`exists_tangential_boundQ`) and Theorem 5.3 with Lipschitz coefficients
(`approx1DQ_limit_frequency_eq_one`) for the rescalings at `a₀` with scale `10 r`. The rescaled
coefficient `Q(a₀ + 10 r ·)` has `κ̃ = 10 r κ`, so `2 κ̃ ≤ 1/2` by the standing smallness, and the
rescaled `Z̃(1/2)`, `Ñ̃(1/2)`, `Ñ̃(2)` are `Z_{a₀}(5r)`, `Ñ_{a₀}(5r)`, `Ñ_{a₀}(20r)`.

## Differences from the paper

The paper treats `Q ≡ 1`; the pinching is stated here for `Ñ` instead of `N`, and the smallness
`κ · 50 r ≤ 1/2` is assumed. The case `t = 0` is stated with `Σ^H_Q`. The other differences
(supremum instead of maximum, no Lemma 6.2, scale `10` instead of `18`, comparability of `H`
centred at `a₀`) are those of the constant-coefficient case.
-/

open MeasureTheory Metric Set Filter Topology Module InnerProductSpace
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The maximal modified frequency `N̄ = sup_{y ∈ S} Ñ_y(u; 20 r)` of Theorem 6.3 with a
Lipschitz coefficient, as a supremum. -/
def maxModFrequencyN (κ : ℝ) (Q u χ : Rn n → ℝ) (S : Set (Rn n)) (r : ℝ) : ℝ :=
  sSup ((fun y => modFrequencyN κ Q u χ y (20 * r)) '' S)

open Dichotomy in
/-- **Theorem 6.3 with a Lipschitz coefficient** for an arbitrary set `S ⊆ B̄_r(x)` of points
`y ∈ closure {u > 0}` with `Z_y(t) ≥ 0` for some `t ∈ (0, r]`. The constant `ε` depends only on
`n`, `N₊` and `δ`. -/
theorem frequency_drop_dichotomyQ_of_subset (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np δ : ℝ)
    (hδ : 0 < δ) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ)
      (x : Rn n) (r : ℝ) (S : Set (Rn n)),
      QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C Q u χ → 0 < r →
      weissKappa L c C' * (50 * r) ≤ 1 / 2 → ball x (50 * r) ⊆ Ω → S ⊆ closedBall x r →
      (∀ y ∈ S, y ∈ closure {z | 0 < u z} ∧
        ∃ t, 0 < t ∧ t ≤ r ∧ 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ y t) →
      maxModFrequencyN (weissKappa L c C') Q u χ S r ≤ Np →
      maxModFrequencyN (weissKappa L c C') Q u χ S r < 1 + δ ∨
        ∃ P : AffineSubspace ℝ (Rn n), finrank ℝ P.direction ≤ n - 2 ∧
          {y ∈ S | maxModFrequencyN (weissKappa L c C') Q u χ S r -
            modFrequencyN (weissKappa L c C') Q u χ y r < ε} ⊆
            thickening (δ * r) (P : Set (Rn n)) := by
  obtain ⟨K, hK0, hK⟩ := exists_tangential_boundQ n Np hδ
  by_contra hcon
  -- a counterexample for each tolerance `tol k`
  have key : ∀ k : ℕ, ∃ (Ω : Set (Rn n)) (C : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ)
      (x : Rn n) (r : ℝ) (S : Set (Rn n)),
      QBounds Ω Q L c C' ∧ IsVariationalSolutionQ Ω C Q u χ ∧ 0 < r ∧
      weissKappa L c C' * (50 * r) ≤ 1 / 2 ∧ ball x (50 * r) ⊆ Ω ∧ S ⊆ closedBall x r ∧
      (∀ y ∈ S, y ∈ closure {z | 0 < u z} ∧
        ∃ t, 0 < t ∧ t ≤ r ∧ 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ y t) ∧
      maxModFrequencyN (weissKappa L c C') Q u χ S r ≤ Np ∧
      1 + δ ≤ maxModFrequencyN (weissKappa L c C') Q u χ S r ∧
      ∀ P : AffineSubspace ℝ (Rn n), finrank ℝ P.direction ≤ n - 2 →
        ¬ {y ∈ S | maxModFrequencyN (weissKappa L c C') Q u χ S r -
            modFrequencyN (weissKappa L c C') Q u χ y r < tol k} ⊆
          thickening (δ * r) (P : Set (Rn n)) := by
    intro k
    by_contra hk
    refine hcon ⟨tol k, tol_mem_Ioo k,
      fun Ω C Q u χ L c C' x r S h0 h1 h2 h2' h3 h4 h5 h6 => ?_⟩
    by_contra hne
    exact hk ⟨Ω, C, Q, u, χ, L, c, C', x, r, S, h0, h1, h2, h2', h3, h4, h5, h6,
      not_lt.1 fun hlt => hne (Or.inl hlt), fun P hP hsub => hne (Or.inr ⟨P, hP, hsub⟩)⟩
  choose Ω C Q u χ L c C' x r S hQ hsol hr hκ hΩ hSx hSy hNp hbig hnot using key
  set κ : ℕ → ℝ := fun k => weissKappa (L k) (c k) (C' k) with hκdef
  set Nbar : ℕ → ℝ := fun k => maxModFrequencyN (κ k) (Q k) (u k) (χ k) (S k) (r k) with hNbar
  -- the maximal frequencies are genuine suprema
  have hbdd : ∀ k, BddAbove ((fun y => modFrequencyN (κ k) (Q k) (u k) (χ k) y (20 * r k)) ''
      S k) := by
    intro k
    by_contra hb
    have h0 : maxModFrequencyN (κ k) (Q k) (u k) (χ k) (S k) (r k) = 0 :=
      Real.sSup_of_not_bddAbove hb
    have := hbig k
    rw [h0] at this
    linarith
  -- the points of `E_k` are pinched
  have hpinch : ∀ k, ∀ y ∈ S k, Nbar k - modFrequencyN (κ k) (Q k) (u k) (χ k) y (r k) < tol k →
      IsPinchedQ (κ k) (Q k) (u k) (χ k) (x k) (r k) (Nbar k) (tol k) y := by
    intro k y hy hyE
    obtain ⟨hcl, t, ht, htr, hZ⟩ := hSy k y hy
    exact ⟨hSx k hy, hcl, ⟨t, ht, htr, hZ⟩, le_csSup (hbdd k) (mem_image_of_mem _ hy),
      by linarith⟩
  -- general position and the one-step estimate
  have hstep : ∀ k, ∃ a₀ : Rn n,
      IsPinchedQ (κ k) (Q k) (u k) (χ k) (x k) (r k) (Nbar k) (tol k) a₀ ∧
      ∃ ν : Rn n, ‖ν‖ = 1 ∧
        ∫ z in ball a₀ (10 * r k) \ ball a₀ (10 * r k / 2),
            ‖gradient (u k) z - ⟪gradient (u k) z, ν⟫ • ν‖ ^ 2 ≤
          K * (4 * tol k + 144 * tol k ^ 2) * ((10 * r k) ^ n * heightH (u k) a₀ (10 * r k)) := by
    intro k
    have hEx : {y ∈ S k | Nbar k - modFrequencyN (κ k) (Q k) (u k) (χ k) y (r k) < tol k} ⊆
        closedBall (x k) (r k) := fun y hy => hSx k hy.1
    obtain ⟨a₀, ha₀E, a, haE, -, horth, hcoef⟩ :=
      exists_generalPosition_orthonormal hδ (hr k) hEx (hnot k)
    have ha₀ := hpinch k a₀ ha₀E.1 ha₀E.2
    have ha : ∀ i, IsPinchedQ (κ k) (Q k) (u k) (χ k) (x k) (r k) (Nbar k) (tol k) (a i) :=
      fun i => hpinch k (a i) (haE i).1 (haE i).2
    obtain ⟨ν, hν, hbound⟩ := hK (Ω k) (C k) (Q k) (u k) (χ k) (L k) (c k) (C' k) (x k) a₀ a
      (r k) (Nbar k) (tol k) (hQ k) (hsol k) (hr k) (hκ k) (hΩ k) (hNp k) ha₀ ha horth
      fun i => by
        obtain ⟨c, -, hcb, hce⟩ := hcoef i
        exact ⟨c, hcb, hce⟩
    exact ⟨a₀, ha₀, ν, hν, hbound⟩
  choose a₀ ha₀ ν hν hbound using hstep
  have hk0 : ∀ k, 0 ≤ κ k := fun k =>
    (hQ k).weissKappa_nonneg ((ha₀ k).mem_domain (hr k) (hΩ k))
  -- the rescaled sequence at scale `10 r`
  have hρpos : ∀ k, 0 < 10 * r k := fun k => by linarith [hr k]
  set v : ℕ → Rn n → ℝ := fun k => oneHomRescale (u k) (a₀ k) (10 * r k) with hv
  set η : ℕ → Rn n → ℝ := fun k => chiRescale (χ k) (a₀ k) (10 * r k) with hη
  set Qt : ℕ → Rn n → ℝ := fun k y => Q k (a₀ k + (10 * r k) • y) with hQt
  set Lt : ℕ → ℝ≥0 := fun k => Real.toNNReal (10 * r k) * L k with hLt
  have hκt : ∀ k, weissKappa (Lt k) (c k) (C' k) = 10 * r k * κ k := fun k =>
    weissKappa_toNNReal_mul (hρpos k).le (L k) (c k) (C' k)
  have hNρ : ∀ k (s : ℝ), modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 s =
      modFrequencyN (κ k) (Q k) (u k) (χ k) (a₀ k) (10 * r k * s) := fun k s => by
    rw [hκt]
    exact modFrequencyN_oneHomRescale (Q k) (u k) (χ k) (a₀ k) (hρpos k) (κ k) s
  have hZρ : ∀ k (s : ℝ),
      modMonotonicityM (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 s =
        modMonotonicityM (κ k) (Q k) (u k) (χ k) (a₀ k) (10 * r k * s) := fun k s => by
    rw [hκt]
    exact modMonotonicityM_oneHomRescale (Q k) (u k) (χ k) (a₀ k) (hρpos k) (κ k) s
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
  have hQ' : ∀ k, QBounds (ball (0 : Rn n) 3) (Qt k) (Lt k) (c k) (C' k) := fun k =>
    ((hQ k).rescale (a₀ k) (hρpos k)).mono (hΩ' k)
  have hsol' : ∀ k, IsVariationalSolutionQ (ball (0 : Rn n) 3) (C k) (Qt k) (v k) (η k) :=
    fun k => ((hsol k).rescale (a₀ k) (hρpos k)).mono isOpen_ball (hΩ' k)
  have hcl' : ∀ k, (0 : Rn n) ∈ closure {y | 0 < v k y} := fun k =>
    (zero_mem_closure_oneHomRescale_iff (u k) (a₀ k) (hρpos k)).2 (ha₀ k).mem_closure
  have e5 : ∀ k, 10 * r k * (1 / 2) = 5 * r k := fun k => by ring
  have e20 : ∀ k, 10 * r k * 2 = 20 * r k := fun k => by ring
  have h5 : ∀ k, 5 * r k ∈ Icc (r k) (20 * r k) := fun k =>
    ⟨by linarith [hr k], by linarith [hr k]⟩
  have h20 : ∀ k, 20 * r k ∈ Icc (r k) (20 * r k) := fun k => ⟨by linarith [hr k], le_rfl⟩
  have hmem := fun k => (ha₀ k).modFrequencyN_mem (hQ k) (hsol k) (hr k) (hκ k) (hΩ k)
  have hκ' : ∀ k, weissKappa (Lt k) (c k) (C' k) * 2 ≤ 1 / 2 := fun k => by
    rw [hκt]
    have := hκ k
    have := hk0 k
    have := hr k
    nlinarith
  have hZ' : ∀ k, 0 ≤ modMonotonicityM (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0
      (1 / 2) := fun k => by
    rw [hZρ, e5]
    exact (hmem k).1 _ (h5 k)
  have hN' : ∀ k, modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 2 ≤ Np :=
    fun k => by
      rw [hNρ, e20]
      exact ((hmem k).2.2 _ (h20 k)).2.trans (hNp k)
  have hpinchN : ∀ k,
      0 ≤ modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 2 -
        modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 (1 / 2) ∧
      modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 2 -
        modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 (1 / 2) ≤
        tol k := fun k => by
    rw [hNρ, hNρ, e5, e20]
    obtain ⟨-, hmono, hN⟩ := hmem k
    have hle := hmono (h5 k) (h20 k) (by linarith [hr k])
    have ha := hN _ (h5 k)
    have hb := hN _ (h20 k)
    constructor <;> linarith [ha.1, hb.2]
  have hδ' : Tendsto (fun k =>
      modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 2 -
        modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 (1 / 2))
      atTop (𝓝 0) :=
    squeeze_zero (fun k => (hpinchN k).1) (fun k => (hpinchN k).2) tendsto_tol
  -- the tangential energy of the rescaled sequence
  have htan_le : ∀ k, 0 ≤ (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) / heightH (v k) 0 1 ∧
      (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) / heightH (v k) 0 1 ≤
        K * (4 * tol k + 144 * tol k ^ 2) := fun k => by
    have hHpos : 0 < heightH (u k) (a₀ k) (10 * r k) :=
      (hsol k).heightH_pos (hQ k) (ha₀ k).mem_closure (hρpos k)
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
          ((10 * r k) ^ n)⁻¹ * (K * (4 * tol k + 144 * tol k ^ 2) *
            ((10 * r k) ^ n * heightH (u k) (a₀ k) (10 * r k))) :=
            mul_le_mul_of_nonneg_left (hbound k) (inv_nonneg.2 hρn.le)
        _ = K * (4 * tol k + 144 * tol k ^ 2) * heightH (u k) (a₀ k) (10 * r k) := by
            rw [mul_left_comm (K * (4 * tol k + 144 * tol k ^ 2)), ← mul_assoc,
              inv_mul_cancel₀ hρn.ne', one_mul]
  have htol2 : Tendsto (fun k => K * (4 * tol k + 144 * tol k ^ 2)) atTop (𝓝 0) := by
    have := ((tendsto_tol.const_mul 4).add ((tendsto_tol.pow 2).const_mul 144)).const_mul K
    simpa using this
  have htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) / heightH (v k) 0 1)
      atTop (𝓝 0) :=
    squeeze_zero (fun k => (htan_le k).1) (fun k => (htan_le k).2) htol2
  -- Theorem 5.3 with Lipschitz coefficients
  have hlim := (approx1DQ_limit_frequency_eq_one hn hν hQ' hsol'
    (closedBall_subset_ball (by norm_num)) hκ' hcl' hZ' hN' hδ' htan).1
  -- the contradiction: `Ñ_{a₀}(5r) > N̄_k − ε_k ≥ 1 + δ − ε_k`
  have hev1 : ∀ᶠ k in atTop,
      modFrequencyN (weissKappa (Lt k) (c k) (C' k)) (Qt k) (v k) (η k) 0 (1 / 2) < 1 + δ / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ k in atTop, tol k < δ / 2 := tendsto_tol.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  rw [hNρ, e5] at hk1
  have h1 := ((hmem k).2.2 _ (h5 k)).1
  have h2 := hbig k
  linarith

/-- **Theorem 6.3 with a Lipschitz coefficient**, with `Σ^H_{Q,t} = sigmaHQr Ω Q u χ κ t` and
`t ∈ (0, r]`, under the standing smallness `κ · 50 r ≤ 1/2`. The constant `ε ∈ (0, 1)` depends
only on `n`, `N₊` and `δ`. The maximum is a supremum. -/
theorem frequency_drop_dichotomyQ (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np δ : ℝ) (hδ : 0 < δ) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0)
      (c C' : ℝ) (x : Rn n) (r t : ℝ),
      QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ → 0 < r →
      weissKappa L c C' * (50 * r) ≤ 1 / 2 → ball x (50 * r) ⊆ Ω → t ∈ Ioc 0 r →
      let Nmax := sSup ((fun y => modFrequencyN (weissKappa L c C') Q u χ y (20 * r)) ''
        (closedBall x r ∩ sigmaHQr Ω Q u χ (weissKappa L c C') t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ P : AffineSubspace ℝ (Rn n),
        finrank ℝ P.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHQr Ω Q u χ (weissKappa L c C') t |
          Nmax - modFrequencyN (weissKappa L c C') Q u χ y r < ε} ⊆
          thickening (δ * r) (P : Set (Rn n)) := by
  obtain ⟨ε, hε, H⟩ := frequency_drop_dichotomyQ_of_subset n hn Np δ hδ
  refine ⟨ε, hε, fun Ω C_V Q u χ L c C' x r t hQ hsol hr hκ hΩ ht => ?_⟩
  intro Nmax hN
  exact H Ω C_V Q u χ L c C' x r _ hQ hsol hr hκ hΩ inter_subset_left
    (fun y hy => ⟨hy.2.2.2.1, t, ht.1, ht.2, hy.2.2.2.2⟩) hN

end InnerVariational
