/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.ConcreteQ.Basic
public import InnerVariational.Monotonicity.LimitsQ
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal
import InnerVariational.Basic.Polar

/-!
# Lemma 4.6 (change of point) with a Lipschitz coefficient

Lemma 4.6 of Kriventsov–Weiss for variational solutions with a Lipschitz coefficient `Q`, and
the continuity of the frequency quantities in the centre.

## Main results

* `IsVariationalSolutionQ.heightH_change_of_point_le`: `H_y(5r/8) ≤ C(n) H_x(r)` for
  `y ∈ B_{r/4}(x)`; no hypothesis on `x`.
* `IsVariationalSolutionQ.heightH_le_change_of_point`: `H_x(r) ≤ C(n, N₊) H_y(5r/8)` when
  `x ∈ closure {u > 0}`, `Z_x(r/4) ≥ 0`, `κ r ≤ 1/2` and `Ñ_x(r) ≤ N₊`.
* `IsVariationalSolutionQ.modFrequencyN_change_of_point_le`: under the same hypotheses,
  `Ñ_y(s) ≤ K(n, N₊)` for `y ∈ B_{r/4}(x)` and `0 < s < r/2`.
* Continuity in the centre: `continuousAt_weightedEnergyD`, `continuousAt_heightH`,
  `continuousAt_modFrequencyN`, `continuousAt_modMonotonicityM`, and
  `continuousOn_modFrequencyN`.

## Differences from the paper

The paper treats `Q ≡ 1`. As in the constant-coefficient case
(`Frequency/Concrete/ChangeOfPoint.lean`) the bound on the frequency is some `K(n, N₊)`, which is
what the paper's proof gives, rather than `max{1, C(n) N_x(r)}`. With a Lipschitz coefficient the
proof splits according to the sign of `Z_y(s)`: if `Z_y(s) < 0`, then `N_y(s) < 1` and there is
nothing to prove; if `Z_y(s) ≥ 0`, then `Ñ_y` is nondecreasing on `[s, 5r/8]` and the argument of
the constant-coefficient case applies to `Ñ_y ≤ N_y + V_y + κ² r² / 2`.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The constant `K(n, N₊) = max{2, 2 (8/5)ⁿ (N₊' + 4 N₊' + 1) K'(n, N₊) + 1}`, `N₊' = max N₊ 1`,
where `K' = heightHChangeConst' n N₊`, of Lemma 4.6 on `Ñ` with a Lipschitz coefficient
(`IsVariationalSolutionQ.modFrequencyN_change_of_point_le`). -/
def modFrequencyNChangeConst (n : ℕ) (Np : ℝ) : ℝ :=
  max 2 (2 * (8 / 5) ^ n * (max Np 1 + (4 * max Np 1 + 1)) * heightHChangeConst' n Np + 1)

theorem two_le_modFrequencyNChangeConst (n : ℕ) (Np : ℝ) : 2 ≤ modFrequencyNChangeConst n Np :=
  le_max_left _ _

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-! ### Lemma 4.6 -/

section ChangeOfPoint

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
include hQ h

/-- `∫_{B_r(x)} u² ≤ r^{n+2} H_x(u; r)` when `B̄_r(x) ⊆ Ω`. -/
theorem integral_ball_sq_le {r : ℝ} (hr : 0 < r) (hΩ : closedBall x r ⊆ Ω) :
    ∫ y in ball x r, u y ^ 2 ≤ r ^ (n + 2) * heightH u x r := by
  have hint := h.integrableOn_sq_of_closedBall hΩ
  rw [integral_ball_eq hr.le hint, intervalIntegral.integral_of_le hr.le]
  have hII := (intervalIntegrable_sphereIntegral hr.le hint).1
  calc ∫ s in Ioc 0 r, sphereIntegral (fun y => u y ^ 2) x s
      ≤ ∫ _ in Ioc 0 r, r ^ (n + 1) * heightH u x r := by
        refine setIntegral_mono_on hII (integrableOn_const measure_Ioc_lt_top.ne)
          measurableSet_Ioc fun s hs => ?_
        rw [sphereIntegral_sq_eq u x hs.1.ne', pow_succ_eq_pow_pred_mul_sq,
          pow_succ_eq_pow_pred_mul_sq (n := n) r, mul_assoc, mul_assoc]
        exact mul_le_mul (pow_le_pow_left₀ hs.1.le hs.2 _)
          (h.sq_mul_heightH_le hQ hs.1 hs.2 hΩ)
          (by have := heightH_nonneg u x hs.1.le; positivity) (by positivity)
    _ = r ^ (n + 2) * heightH u x r := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hr.le]; ring

omit hQ in
/-- If `c ≤ ∫_{∂B_s(x)} u²` for every `s ∈ [ρ, ρ']`, then
`(ρ' − ρ) c ≤ ∫_{B_{ρ'}(x) ∖ B_ρ(x)} u²`. -/
theorem mul_le_integral_annulus_sq {ρ ρ' c₀ : ℝ} (hρ : 0 ≤ ρ) (hρρ' : ρ ≤ ρ')
    (hΩ : closedBall x ρ' ⊆ Ω)
    (hc : ∀ s ∈ Icc ρ ρ', c₀ ≤ sphereIntegral (fun y => u y ^ 2) x s) :
    (ρ' - ρ) * c₀ ≤ ∫ y in ball x ρ' \ ball x ρ, u y ^ 2 := by
  have hint := h.integrableOn_sq_of_closedBall hΩ
  rw [integral_ball_diff_ball hρ hρρ' hint]
  have hII : IntervalIntegrable (sphereIntegral (fun y => u y ^ 2) x) volume ρ ρ' :=
    (intervalIntegrable_sphereIntegral (hρ.trans hρρ') hint).mono_set (by
      rw [uIcc_of_le hρρ', uIcc_of_le (hρ.trans hρρ')]; exact Icc_subset_Icc hρ le_rfl)
  calc (ρ' - ρ) * c₀ = ∫ _ in ρ..ρ', c₀ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ _ := intervalIntegral.integral_mono_on hρρ' intervalIntegrable_const hII hc

/-- **Lemma 4.6, upper bound on `H`**: if `0 < r`, `B̄_r(x) ⊆ Ω` and `y ∈ B_{r/4}(x)`, then
`H_y(u; 5r/8) ≤ 8 (8/5)^{n+1} H_x(u; r)`. No hypothesis on `x` is needed. -/
theorem heightH_change_of_point_le {r : ℝ} (hr : 0 < r) (hΩ : closedBall x r ⊆ Ω) {y : Rn n}
    (hy : y ∈ ball x (r / 4)) :
    heightH u y (5 / 8 * r) ≤ heightHChangeConst n * heightH u x r := by
  have hyx : dist y x < r / 4 := hy
  have hsub1 : closedBall y (3 / 4 * r) ⊆ closedBall x r := fun z hz => by
    rw [mem_closedBall] at hz ⊢; linarith [dist_triangle z y x]
  have hsub2 : ball y (3 / 4 * r) ⊆ ball x r := fun z hz => by
    rw [mem_ball] at hz ⊢; linarith [dist_triangle z y x]
  have hρ : 0 < 5 / 8 * r := by positivity
  have hlow : (3 / 4 * r - 5 / 8 * r) * ((5 / 8 * r) ^ (n + 1) * heightH u y (5 / 8 * r)) ≤
      ∫ z in ball y (3 / 4 * r) \ ball y (5 / 8 * r), u z ^ 2 := by
    refine h.mul_le_integral_annulus_sq hρ.le (by linarith) (hsub1.trans hΩ) fun s hs => ?_
    have hs0 : 0 < s := hρ.trans_le hs.1
    rw [sphereIntegral_sq_eq u y hs0.ne', pow_succ_eq_pow_pred_mul_sq,
      pow_succ_eq_pow_pred_mul_sq (n := n) s, mul_assoc, mul_assoc]
    have hHy0 := heightH_nonneg u y hρ.le
    exact mul_le_mul (pow_le_pow_left₀ hρ.le hs.1 _)
      (h.sq_mul_heightH_le hQ hρ hs.1
        ((closedBall_subset_closedBall hs.2).trans (hsub1.trans hΩ)))
      (by positivity) (by positivity)
  have hup : ∫ z in ball y (3 / 4 * r) \ ball y (5 / 8 * r), u z ^ 2 ≤
      ∫ z in ball x r, u z ^ 2 :=
    setIntegral_mono_set (h.integrableOn_sq_of_closedBall hΩ)
      (.of_forall fun z => sq_nonneg (u z)) (diff_subset.trans hsub2).eventuallyLE
  have hball := h.integral_ball_sq_le hQ hr hΩ
  have key : r ^ (n + 2) * (1 / 8 * (5 / 8) ^ (n + 1) * heightH u y (5 / 8 * r)) ≤
      r ^ (n + 2) * heightH u x r := by
    have e : (3 / 4 * r - 5 / 8 * r) * ((5 / 8 * r) ^ (n + 1) * heightH u y (5 / 8 * r)) =
        r ^ (n + 2) * (1 / 8 * (5 / 8) ^ (n + 1) * heightH u y (5 / 8 * r)) := by
      rw [mul_pow]; ring
    linarith
  have key2 := le_of_mul_le_mul_left key (by positivity)
  have hK : heightHChangeConst n * (1 / 8 * (5 / 8) ^ (n + 1)) = 1 := by
    rw [heightHChangeConst,
      show (8 : ℝ) * (8 / 5) ^ (n + 1) * (1 / 8 * (5 / 8) ^ (n + 1)) = (8 / 5 * (5 / 8)) ^ (n + 1)
        by rw [mul_pow]; ring]
    norm_num
  calc heightH u y (5 / 8 * r)
      = heightHChangeConst n * (1 / 8 * (5 / 8) ^ (n + 1)) * heightH u y (5 / 8 * r) := by
        rw [hK, one_mul]
    _ = heightHChangeConst n * (1 / 8 * (5 / 8) ^ (n + 1) * heightH u y (5 / 8 * r)) := by ring
    _ ≤ heightHChangeConst n * heightH u x r :=
        mul_le_mul_of_nonneg_left key2 (heightHChangeConst_pos n).le

/-- **Lemma 4.6, lower bound on `H`, with a Lipschitz coefficient**: if `x ∈ closure {u > 0}`,
`0 < r`, `B̄_r(x) ⊆ Ω`, `Z_x(r/4) ≥ 0`, `κ r ≤ 1/2` and `Ñ_x(r) ≤ N₊`, then
`H_x(u; r) ≤ K H_y(u; 5r/8)` for every `y ∈ B_{r/4}(x)`, with `K = heightHChangeConst' n N₊`. -/
theorem heightH_le_change_of_point (hx : x ∈ closure {y | 0 < u y}) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall x r ⊆ Ω)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x (r / 4))
    (hκ : weissKappa L c C' * r ≤ 1 / 2) {Np : ℝ}
    (hN : modFrequencyN (weissKappa L c C') Q u χ x r ≤ Np) {y : Rn n}
    (hy : y ∈ ball x (r / 4)) :
    heightH u x r ≤ heightHChangeConst' n Np * heightH u y (5 / 8 * r) := by
  have hyx : dist y x < r / 4 := hy
  set Np' := max Np 1 + 1 with hNp'def
  set Cd := Abstract.RadialData.doublingConst Np' with hCd
  have hCd0 : 0 < Cd := Abstract.RadialData.doublingConst_pos Np'
  have hNp' : 1 < Np' := by linarith [le_max_right Np 1]
  have hr4 : 0 < r / 4 := by positivity
  have hNr : modFrequencyN (weissKappa L c C') Q u χ x r ≤ Np' :=
    hN.trans (by linarith [le_max_left Np 1])
  have hr2 : closedBall x (r / 2) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hΩ
  have hZ2 : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x (r / 2) :=
    h.modMonotonicityM_nonneg hQ hx hr4 hZ hκ hΩ ⟨by linarith, by linarith⟩
  have hk := hQ.weissKappa_nonneg (hΩ (mem_closedBall_self hr.le))
  have hκ2 : weissKappa L c C' * (r / 2) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by linarith) hk).trans hκ
  have hN2 : modFrequencyN (weissKappa L c C') Q u χ x (r / 2) ≤ Np' :=
    (h.monotoneOn_modFrequencyN hQ hx hr4 hZ hκ hΩ ⟨by linarith, by linarith⟩
      ⟨by linarith, le_rfl⟩ (by linarith)).trans hNr
  have hdoub : ∀ s ∈ Icc (r / 4) (3 / 8 * r), heightH u x r ≤ Cd ^ 2 * heightH u x s := by
    intro s hs
    have h1 := (h.heightH_doubling hQ hx (t := r / 2) (r := r) (by positivity) (by linarith)
      (by linarith) hZ2 hκ hΩ hNp' hNr (s := r / 2) ⟨le_rfl, by linarith⟩).2
    have h2 := (h.heightH_doubling hQ hx (t := r / 4) (r := r / 2) hr4 (by linarith)
      (by linarith) hZ hκ2 hr2 hNp' hN2 (s := s) ⟨hs.1, by linarith [hs.2]⟩).2
    calc heightH u x r ≤ Cd * heightH u x (r / 2) := h1
      _ ≤ Cd * (Cd * heightH u x s) := mul_le_mul_of_nonneg_left h2 hCd0.le
      _ = Cd ^ 2 * heightH u x s := by ring
  have hlow : (3 / 8 * r - r / 4) * ((r / 4) ^ (n + 1) * heightH u x r / Cd ^ 2) ≤
      ∫ z in ball x (3 / 8 * r) \ ball x (r / 4), u z ^ 2 := by
    refine h.mul_le_integral_annulus_sq (by positivity) (by linarith)
      ((closedBall_subset_closedBall (by linarith)).trans hΩ) fun s hs => ?_
    have hs0 : 0 < s := by linarith [hs.1]
    rw [sphereIntegral_sq_eq u x hs0.ne']
    have hH0 := heightH_nonneg u x hs0.le
    have hd := hdoub s hs
    calc (r / 4) ^ (n + 1) * heightH u x r / Cd ^ 2 ≤ (r / 4) ^ (n + 1) * heightH u x s := by
          rw [div_le_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left hd
            (pow_nonneg (by positivity : (0 : ℝ) ≤ r / 4) (n + 1))
          linarith
      _ ≤ s ^ (n + 1) * heightH u x s :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hs.1 _) hH0
  have hρ : 0 < 5 / 8 * r := by positivity
  have hcl : closedBall y (5 / 8 * r) ⊆ Ω := fun z hz => hΩ (by
    rw [mem_closedBall] at hz ⊢; linarith [dist_triangle z y x])
  have hsub : ball x (3 / 8 * r) ⊆ ball y (5 / 8 * r) := fun z hz => by
    rw [mem_ball] at hz ⊢; linarith [dist_triangle z x y, dist_comm x y]
  have hup : ∫ z in ball x (3 / 8 * r) \ ball x (r / 4), u z ^ 2 ≤
      ∫ z in ball y (5 / 8 * r), u z ^ 2 :=
    setIntegral_mono_set (h.integrableOn_sq_of_closedBall hcl)
      (.of_forall fun z => sq_nonneg (u z)) (diff_subset.trans hsub).eventuallyLE
  have hball := h.integral_ball_sq_le hQ (x := y) hρ hcl
  have hHy0 := heightH_nonneg u y hρ.le
  have hK := heightHChangeConst'_pos n Np
  have e1 : (3 / 8 * r - r / 4) * ((r / 4) ^ (n + 1) * heightH u x r / Cd ^ 2) =
      r ^ (n + 2) * (heightH u x r / heightHChangeConst' n Np) := by
    rw [heightHChangeConst', ← hNp'def, ← hCd, div_pow]
    field_simp
    ring
  have e2 : (5 / 8 * r) ^ (n + 2) * heightH u y (5 / 8 * r) ≤
      r ^ (n + 2) * heightH u y (5 / 8 * r) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) ?_) hHy0
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have key : r ^ (n + 2) * (heightH u x r / heightHChangeConst' n Np) ≤
      r ^ (n + 2) * heightH u y (5 / 8 * r) := by linarith
  have := le_of_mul_le_mul_left key (by positivity)
  rwa [div_le_iff₀ hK, mul_comm] at this

/-- **Lemma 4.6, bound on `Ñ`, with a Lipschitz coefficient**: if `x ∈ closure {u > 0}`,
`0 < r`, `B̄_r(x) ⊆ Ω`, `Z_x(r/4) ≥ 0`, `κ r ≤ 1/2` and `Ñ_x(r) ≤ N₊`, then
`Ñ_y(u; s) ≤ K(n, N₊)` for every `y ∈ B_{r/4}(x)` and `0 < s < r/2`,
`K = modFrequencyNChangeConst n N₊`.

The argument is that of `IsVariationalSolution.frequencyN_change_of_point_le`, with a case split:
* if `H_y(s) = 0`, then `Ñ_y(s) = κ² s² / 2 ≤ 1/8`;
* if `H_y(s) > 0` and `Z_y(s) < 0`, then `N_y(s) < 1 − κ² s² / 8` and `Ñ_y(s) < 2`;
* otherwise `Ñ_y` is nondecreasing on `[s, 5r/8]` (Lemma 4.1 at `y`, which need not lie in
  `closure {u > 0}`), and `Ñ_y(s) ≤ Ñ_y(5r/8) ≤ (N_y + V_y)(5r/8) + 1/8`; the right-hand side is
  bounded as in the constant-coefficient case, using a radius `σ ∈ (7r/8, r)` where `V_x(σ)` is
  bounded, `H_x(σ) ≤ e^{1/32} H_x(r) ≤ 2 H_x(r)` and the lower bound of Lemma 4.6 on `H`. -/
theorem modFrequencyN_change_of_point_le (hx : x ∈ closure {y | 0 < u y}) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall x r ⊆ Ω)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x (r / 4))
    (hκ : weissKappa L c C' * r ≤ 1 / 2) {Np : ℝ}
    (hN : modFrequencyN (weissKappa L c C') Q u χ x r ≤ Np) {y : Rn n}
    (hy : y ∈ ball x (r / 4)) {s : ℝ} (hs : 0 < s) (hsr : s < r / 2) :
    modFrequencyN (weissKappa L c C') Q u χ y s ≤ modFrequencyNChangeConst n Np := by
  set κ := weissKappa L c C' with hκdef
  have hk : 0 ≤ κ := hQ.weissKappa_nonneg (hΩ (mem_closedBall_self hr.le))
  have hK2 := two_le_modFrequencyNChangeConst n Np
  have hks : κ * s ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (by linarith) hk).trans hκ
  have hks2 : κ ^ 2 * s ^ 2 ≤ 1 / 4 := sq_mul_sq_le_of_mul_le hk hs.le hks
  -- the case `H_y(s) = 0`
  rcases (heightH_nonneg u y hs.le).lt_or_eq with hHs | hHs
  swap
  · rw [modFrequencyN, weightedFrequencyN, ← hHs, div_zero, zero_add]
    linarith
  -- the case `Z_y(s) < 0`
  rcases lt_or_ge (modMonotonicityM κ Q u χ y s) 0 with hZy | hZy
  · rw [modMonotonicityM_eq hHs.ne'] at hZy
    have : weightedFrequencyN Q u χ y s - 1 + κ ^ 2 * s ^ 2 / 8 < 0 := by
      by_contra hc
      push Not at hc
      exact absurd hZy (not_lt.2 (mul_nonneg hHs.le hc))
    rw [modFrequencyN]
    linarith
  -- the main case
  have hyx : dist y x < r / 4 := hy
  set ρ := 5 / 8 * r with hρdef
  have hρ : 0 < ρ := by positivity
  have hclρ : closedBall y ρ ⊆ Ω := fun z hz => hΩ (by
    rw [mem_closedBall] at hz ⊢; linarith [dist_triangle z y x])
  have hsρ : s ≤ ρ := by linarith
  have hκρ : κ * ρ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (by linarith) hk).trans hκ
  -- `Ñ_y(s) ≤ Ñ_y(ρ) ≤ (N_y + V_y)(ρ) + 1/8`
  have hmono := (h.monotoneOn_modFrequencyN_of_heightH_pos hQ (x := y) hs hHs hZy hκρ hclρ).1
    ⟨le_rfl, hsρ⟩ ⟨hsρ, le_rfl⟩ hsρ
  have hHρ : 0 < heightH u y ρ := h.heightH_pos_of_le hQ hs hsρ hclρ hHs
  have hballρ : ball y ρ ⊆ Ω := ball_subset_closedBall.trans hclρ
  have hNV := h.weightedFrequencyN_add_weightedVolumeV hQ (x := y) hballρ
  have hV := h.weightedVolumeV_nonneg (x := y) hρ.le hballρ
  have hκρ2 : κ ^ 2 * ρ ^ 2 / 2 ≤ 1 / 8 := by
    have := sq_mul_sq_le_of_mul_le hk hρ.le hκρ
    linarith
  -- a radius `σ ∈ (7r/8, r)` with `V_x(σ) < v`
  set Mp := max Np 1 with hMp
  set v := 4 * Mp + 1 with hv
  have hMp1 : 1 ≤ Mp := le_max_right _ _
  have hNpM : Np ≤ Mp := le_max_left _ _
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen hr.le hΩ
  have hr4 : 0 < r / 4 := by positivity
  let d := h.radialDataErr hQ hR' hr4 (by linarith : r / 4 ≤ r) hRR'
  have hHx : ∀ s ∈ Icc (r / 4) r, 0 < d.heightH s := fun s hs' =>
    h.heightH_pos hQ hx (hr4.trans_le hs'.1) ((closedBall_subset_closedBall hs'.2).trans hΩ)
  have hZ78 : 0 ≤ d.modM (7 / 8 * r) :=
    h.modMonotonicityM_nonneg hQ hx hr4 hZ hκ hΩ ⟨by linarith, by linarith⟩
  have hN78 : 1 ≤ modFrequencyN κ Q u χ x (7 / 8 * r) :=
    h.one_le_modFrequencyN hQ hx hr4 hZ hκ hΩ ⟨by linarith, by linarith⟩
  have hlog : 1 / 8 ≤ Real.log r - Real.log (7 / 8 * r) := by
    rw [← Real.log_div hr.ne' (by positivity)]
    have e : r / (7 / 8 * r) = 8 / 7 := by field_simp
    rw [e]
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 8 / 7)
    norm_num at this ⊢
    linarith
  obtain ⟨σ, hσ, hVσ⟩ := d.exists_volumeV_lt (t₁ := 7 / 8 * r) (t₂ := r) (by linarith)
    (by linarith) le_rfl (fun s hs' => hHx s ⟨by linarith [hs'.1], hs'.2⟩) hZ78 hκ (v := v)
    (by positivity) (by
      change modFrequencyN κ Q u χ x r - modFrequencyN κ Q u χ x (7 / 8 * r) <
        v ^ 2 / 2 * (Real.log r - Real.log (7 / 8 * r))
      have hv2 : 16 * Mp < v ^ 2 := by nlinarith
      have hv0 : 0 ≤ v ^ 2 := sq_nonneg v
      nlinarith)
  have hσmem : σ ∈ Icc (r / 4) r := ⟨by linarith [hσ.1], hσ.2.le⟩
  have hσ0 : 0 < σ := by linarith [hσ.1]
  rw [h.radialDataErr_volumeV hQ hR' hr4 _ hRR' hσ0] at hVσ
  have hclσ : closedBall x σ ⊆ Ω := (closedBall_subset_closedBall hσ.2.le).trans hΩ
  have hballσ : ball x σ ⊆ Ω := ball_subset_closedBall.trans hclσ
  have hHσ : 0 < heightH u x σ := h.heightH_pos hQ hx hσ0 hclσ
  have hNσ : weightedFrequencyN Q u χ x σ ≤ Mp :=
    ((weightedFrequencyN_le_modFrequencyN κ Q u χ x σ).trans
      ((h.monotoneOn_modFrequencyN hQ hx hr4 hZ hκ hΩ hσmem ⟨by linarith, le_rfl⟩
        hσ.2.le).trans hN)).trans hNpM
  have hN1σ : 1 - κ ^ 2 * σ ^ 2 / 8 ≤ weightedFrequencyN Q u χ x σ :=
    h.one_sub_le_weightedFrequencyN hQ hx hr4 hZ hκ hΩ hσmem
  have hκσ : κ ^ 2 * σ ^ 2 ≤ 1 / 4 :=
    sq_mul_sq_le_of_mul_le hk hσ0.le ((mul_le_mul_of_nonneg_left hσ.2.le hk).trans hκ)
  have hVσ0 : 0 ≤ weightedVolumeV Q u χ x σ := h.weightedVolumeV_nonneg hσ0.le hballσ
  have hHσr : heightH u x σ ≤ 2 * heightH u x r := by
    have h1 := h.heightH_le_exp_mul hQ hx hr4 hZ hκ hΩ hσmem ⟨by linarith, le_rfl⟩ hσ.2.le
    have h2 : Real.exp (κ ^ 2 * (r ^ 2 - σ ^ 2) / 8) ≤ 2 := by
      refine le_trans ?_ exp_one_div_thirtyTwo_le_two
      refine le_trans (Real.exp_le_exp.2 ?_) (exp_sq_mul_sq_div_eight_le hk hr.le hκ)
      have h3 : 0 ≤ κ ^ 2 * σ ^ 2 := by positivity
      have e : κ ^ 2 * (r ^ 2 - σ ^ 2) / 8 = κ ^ 2 * r ^ 2 / 8 - κ ^ 2 * σ ^ 2 / 8 := by ring
      linarith only [h3, e]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (heightH_nonneg u x hr.le))
  -- `∫_{B_σ(x)} |∇u|² ≤ 2 rⁿ H_x(r) (Mp + v)`
  have hNVσ := h.weightedFrequencyN_add_weightedVolumeV hQ hballσ
  set Gx := ∫ z in ball x σ, ‖gradient u z‖ ^ 2 with hGx
  have hGxeq : Gx = σ ^ n * heightH u x σ *
      (weightedFrequencyN Q u χ x σ + weightedVolumeV Q u χ x σ) := by
    rw [hNVσ]
    field_simp
  have hGx_le : Gx ≤ r ^ n * (2 * heightH u x r) * (Mp + v) := by
    rw [hGxeq]
    have h1 : σ ^ n * heightH u x σ ≤ r ^ n * (2 * heightH u x r) :=
      mul_le_mul (pow_le_pow_left₀ hσ0.le hσ.2.le _) hHσr hHσ.le (by positivity)
    have h2 : weightedFrequencyN Q u χ x σ + weightedVolumeV Q u χ x σ ≤ Mp + v := by linarith
    exact mul_le_mul h1 h2 (by linarith)
      (mul_nonneg (pow_nonneg hr.le _) (mul_nonneg zero_le_two (heightH_nonneg u x hr.le)))
  -- `∫_{B_ρ(y)} |∇u|² ≤ ∫_{B_σ(x)} |∇u|²`
  have hsubσ : ball y ρ ⊆ ball x σ := fun z hz => by
    rw [mem_ball] at hz ⊢; linarith [dist_triangle z y x, hσ.1]
  have hGy_le : ∫ z in ball y ρ, ‖gradient u z‖ ^ 2 ≤ Gx :=
    setIntegral_mono_set (h.integrableOn_norm_gradient_sq hQ hballσ)
      (.of_forall fun z => sq_nonneg _) hsubσ.eventuallyLE
  -- `H_x(r) ≤ K' H_y(ρ)`
  have hlowH := h.heightH_le_change_of_point hQ hx hr hΩ hZ hκ hN hy
  have hK' := heightHChangeConst'_pos n Np
  have hGy : ∫ z in ball y ρ, ‖gradient u z‖ ^ 2 ≤
      2 * r ^ n * (Mp + v) * heightHChangeConst' n Np * heightH u y ρ := by
    calc ∫ z in ball y ρ, ‖gradient u z‖ ^ 2 ≤ r ^ n * (2 * heightH u x r) * (Mp + v) :=
          hGy_le.trans hGx_le
      _ = 2 * r ^ n * (Mp + v) * heightH u x r := by ring
      _ ≤ 2 * r ^ n * (Mp + v) * (heightHChangeConst' n Np * heightH u y ρ) :=
          mul_le_mul_of_nonneg_left hlowH (by positivity)
      _ = _ := by ring
  have hfin : (ρ ^ n)⁻¹ * (∫ z in ball y ρ, ‖gradient u z‖ ^ 2) / heightH u y ρ ≤
      2 * (8 / 5) ^ n * (Mp + v) * heightHChangeConst' n Np := by
    rw [div_le_iff₀ hHρ]
    have e : (ρ ^ n)⁻¹ * r ^ n = (8 / 5) ^ n := by
      rw [hρdef, mul_pow, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), mul_one,
        ← inv_pow]
      norm_num
    calc (ρ ^ n)⁻¹ * (∫ z in ball y ρ, ‖gradient u z‖ ^ 2)
        ≤ (ρ ^ n)⁻¹ * (2 * r ^ n * (Mp + v) * heightHChangeConst' n Np * heightH u y ρ) :=
          mul_le_mul_of_nonneg_left hGy (by positivity)
      _ = 2 * ((ρ ^ n)⁻¹ * r ^ n) * (Mp + v) * heightHChangeConst' n Np * heightH u y ρ := by
          ring
      _ = _ := by rw [e]
  calc modFrequencyN κ Q u χ y s ≤ modFrequencyN κ Q u χ y ρ := hmono
    _ = weightedFrequencyN Q u χ y ρ + κ ^ 2 * ρ ^ 2 / 2 := rfl
    _ ≤ weightedFrequencyN Q u χ y ρ + weightedVolumeV Q u χ y ρ + 1 / 8 := by linarith
    _ = (ρ ^ n)⁻¹ * (∫ z in ball y ρ, ‖gradient u z‖ ^ 2) / heightH u y ρ + 1 / 8 := by
        rw [hNV]
    _ ≤ 2 * (8 / 5) ^ n * (Mp + v) * heightHChangeConst' n Np + 1 := by linarith
    _ ≤ modFrequencyNChangeConst n Np := le_max_right _ _

end ChangeOfPoint

/-! ### Continuity in the centre -/

section Continuity

variable (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
include h

omit h in
theorem measurable_indicator_of_continuousOn {f : Rn n → ℝ} (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) : Measurable (Ω.indicator f) := by
  classical
  rw [← piecewise_eq_indicator]
  exact hf.measurable_piecewise continuousOn_const hΩ.measurableSet

omit h in
theorem locallyIntegrable_of_abs_le {g : Rn n → ℝ} (hg : Measurable g) (M : ℝ)
    (hM : ∀ y, |g y| ≤ M) : LocallyIntegrable g := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact IntegrableOn.of_bound hK.measure_lt_top hg.aestronglyMeasurable M
    (.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)

/-- `y ↦ H_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω`. -/
theorem continuousAt_heightH {r : ℝ} (hr : 0 < r) (hx : closedBall x r ⊆ Ω) :
    ContinuousAt (fun y => heightH u y r) x := by
  have hS := continuousAt_sphereIntegral h.isOpen (h.continuousOn.pow 2) (x := x) (s := r)
    (by rwa [abs_of_pos hr])
  have h2 : ContinuousAt (fun y => sphereIntegral (fun z => u z ^ 2) y r) x :=
    hS.comp (f := fun y => (y, r)) (continuousAt_id.prodMk continuousAt_const)
  exact continuousAt_const.mul h2

include hQ in
/-- `y ↦ D^w_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω`. -/
theorem continuousAt_weightedEnergyD [NeZero n] {r : ℝ} (hr : 0 < r)
    (hx : closedBall x r ⊆ Ω) : ContinuousAt (fun y => weightedEnergyD Q u χ y r) x := by
  obtain ⟨R', hR', hR'Ω⟩ := exists_gt_ball_subset h.isOpen hr.le hx
  have hx₀ : x ∈ Ω := hx (mem_closedBall_self hr.le)
  set g₁ : Rn n → ℝ := Ω.indicator fun y => ‖gradient u y‖ ^ 2 with hg₁def
  set g₃ : Rn n → ℝ := Ω.indicator fun y => Q y ^ 2 * (1 - χ y) with hg₃def
  have hg₁ : LocallyIntegrable g₁ := by
    refine locallyIntegrable_of_abs_le (((measurable_gradient u).norm.pow_const 2).indicator
      h.isOpen.measurableSet) ((C : ℝ) ^ 2) fun y => ?_
    by_cases hy : y ∈ Ω
    · rw [hg₁def, indicator_of_mem hy, abs_of_nonneg (sq_nonneg _)]
      exact h.sq_norm_gradient_le hy
    · rw [hg₁def, indicator_of_notMem hy, abs_zero]; positivity
  have hg₃m : Measurable g₃ := by
    have e : g₃ = fun y => Ω.indicator (fun y => Q y ^ 2) y *
        (Ω.indicator (fun _ => (1 : ℝ)) y - Ω.indicator χ y) := by
      funext y
      by_cases hy : y ∈ Ω
      · simp [hg₃def, indicator_of_mem hy]
      · simp [hg₃def, indicator_of_notMem hy]
    rw [e]
    exact (measurable_indicator_of_continuousOn h.isOpen (hQ.continuousOn.pow 2)).mul
      ((measurable_const.indicator h.isOpen.measurableSet).sub h.measurable_chi)
  have hg₃ : LocallyIntegrable g₃ := by
    refine locallyIntegrable_of_abs_le hg₃m (C' ^ 2) fun y => ?_
    by_cases hy : y ∈ Ω
    · rw [hg₃def, indicator_of_mem hy, abs_of_nonneg (h.weight_nonneg hy)]
      exact h.weight_le hQ hy
    · rw [hg₃def, indicator_of_notMem hy, abs_zero]; positivity
  have hQc : ContinuousAt Q x := hQ.continuousOn.continuousAt (h.isOpen.mem_nhds hx₀)
  have hD : ContinuousAt (fun y => (r ^ n)⁻¹ *
      ((∫ z in ball y r, g₁ z) - ∫ z in ball y r, g₃ z) + Q y ^ 2 * unitBallVolume n) x :=
    (continuousAt_const.mul ((continuous_integral_ball hg₁ r).continuousAt.sub
      (continuous_integral_ball hg₃ r).continuousAt)).add ((hQc.pow 2).mul continuousAt_const)
  refine hD.congr ?_
  filter_upwards [ball_mem_nhds x (sub_pos.2 hR')] with y hy
  have hsub : ball y r ⊆ Ω := by
    intro z hz
    apply hR'Ω
    rw [mem_ball] at hy hz ⊢
    linarith [dist_triangle z y x]
  have e₁ : ∫ z in ball y r, g₁ z = ∫ z in ball y r, ‖gradient u z‖ ^ 2 :=
    setIntegral_congr_fun measurableSet_ball fun z hz => by
      rw [hg₁def, indicator_of_mem (hsub hz)]
  have e₃ : ∫ z in ball y r, g₃ z = ∫ z in ball y r, Q z ^ 2 * (1 - χ z) :=
    setIntegral_congr_fun measurableSet_ball fun z hz => by
      rw [hg₃def, indicator_of_mem (hsub hz)]
  rw [weightedEnergyD, e₁, e₃, h.integral_weightedEnergy_eq hQ hsub]

include hQ in
/-- `y ↦ N_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω` and `H_x(u; r) ≠ 0`. -/
theorem continuousAt_weightedFrequencyN [NeZero n] {r : ℝ} (hr : 0 < r)
    (hx : closedBall x r ⊆ Ω) (hH : heightH u x r ≠ 0) :
    ContinuousAt (fun y => weightedFrequencyN Q u χ y r) x := by
  have hx₀ : x ∈ Ω := hx (mem_closedBall_self hr.le)
  have hQc : ContinuousAt Q x := hQ.continuousOn.continuousAt (h.isOpen.mem_nhds hx₀)
  exact ((h.continuousAt_weightedEnergyD hQ hr hx).sub ((hQc.pow 2).mul continuousAt_const)).div
    (h.continuousAt_heightH hr hx) hH

include hQ in
/-- `y ↦ Ñ_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω` and `H_x(u; r) ≠ 0`. -/
theorem continuousAt_modFrequencyN [NeZero n] (κ : ℝ) {r : ℝ} (hr : 0 < r)
    (hx : closedBall x r ⊆ Ω) (hH : heightH u x r ≠ 0) :
    ContinuousAt (fun y => modFrequencyN κ Q u χ y r) x :=
  (h.continuousAt_weightedFrequencyN hQ hr hx hH).add continuousAt_const

include hQ in
/-- `y ↦ Z_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω`. -/
theorem continuousAt_modMonotonicityM [NeZero n] (κ : ℝ) {r : ℝ} (hr : 0 < r)
    (hx : closedBall x r ⊆ Ω) : ContinuousAt (fun y => modMonotonicityM κ Q u χ y r) x := by
  have hx₀ : x ∈ Ω := hx (mem_closedBall_self hr.le)
  have hQc : ContinuousAt Q x := hQ.continuousOn.continuousAt (h.isOpen.mem_nhds hx₀)
  exact (((h.continuousAt_weightedEnergyD hQ hr hx).sub (h.continuousAt_heightH hr hx)).sub
    ((hQc.pow 2).mul continuousAt_const)).add
    (continuousAt_const.mul (h.continuousAt_heightH hr hx))

include hQ in
/-- **Continuity of the modified frequency in the centre**: for fixed `r > 0`,
`y ↦ Ñ_y(u; r)` is continuous on `{y : B̄_r(y) ⊆ Ω, H_y(u; r) > 0}`. -/
theorem continuousOn_modFrequencyN [NeZero n] (κ : ℝ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun y => modFrequencyN κ Q u χ y r)
      {y | closedBall y r ⊆ Ω ∧ 0 < heightH u y r} :=
  fun _ hy => (h.continuousAt_modFrequencyN hQ κ hr hy.1 hy.2.ne').continuousWithinAt

end Continuity

end IsVariationalSolutionQ

/-- **Lemma 4.6, bound on `Ñ`, with a Lipschitz coefficient**, existential form: for every `N₊`
there is `K = K(n, N₊)` such that `Ñ_y(u; s) ≤ K` for `y ∈ B_{r/4}(x)` and `0 < s < r/2`,
whenever `x ∈ closure {u > 0}`, `B̄_r(x) ⊆ Ω`, `Z_x(r/4) ≥ 0`, `κ r ≤ 1/2` and `Ñ_x(r) ≤ N₊`. -/
theorem modFrequencyN_change_of_point (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ K : ℝ, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ)
      (x : Rn n) (r : ℝ), QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C Q u χ → 0 < r →
      closedBall x r ⊆ Ω → x ∈ closure {y | 0 < u y} →
      0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x (r / 4) →
      weissKappa L c C' * r ≤ 1 / 2 → modFrequencyN (weissKappa L c C') Q u χ x r ≤ Np →
      ∀ y ∈ ball x (r / 4), ∀ s, 0 < s → s < r / 2 →
        modFrequencyN (weissKappa L c C') Q u χ y s ≤ K :=
  ⟨modFrequencyNChangeConst n Np, fun _ _ _ _ _ _ _ _ _ _ hQ h hr hΩ hx hZ hκ hN _ hy _ hs hsr =>
    h.modFrequencyN_change_of_point_le hQ hx hr hΩ hZ hκ hN hy hs hsr⟩

end InnerVariational
