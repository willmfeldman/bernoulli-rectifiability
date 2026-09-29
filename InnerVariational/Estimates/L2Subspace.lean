/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Estimates.Jones
public import InnerVariational.Estimates.L2SubspaceQ
public import InnerVariational.Frequency.SigmaH
public import InnerVariational.Homogeneity.TwoPoint
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Data.Real.StarOrdered
public import InnerVariational.Frequency.Concrete
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Monotonicity.Radial
import InnerVariational.Kernel.BV
public import GMTFoundations.Defs.GMT

/-!
# `L²`-subspace approximation (Theorem 6.1)

Theorem 6.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2): for a variational
solution `(u, χ)` on `B̄_{50r}(x)` (see below), a finite measure `μ` carried by `Σ^H_r`,
`x ∈ Σ^H_r` and `N_x(u; 50r) ≤ N₊`,
`β²_μ(x, r) ≤ C(N₊, n) r^{1-n} ∫_{B_r(x)} (N_y(u; 20r) − N_y(u; r)) dμ(y)`.

## Proof

We work directly at scale `r` and centre `x`: the paper rescales to `r = 1`, `x = 0`, but every
ingredient (Lemmas 4.1, 4.3, 4.5, 4.6 in `Frequency/Concrete.lean` and Lemma 6.2 in
`Homogeneity/TwoPoint.lean`) is available at all scales. Write `S = B̄_r(x) ∩ Σ^H_r`,
`f(y) = N_y(20r) − N_y(r)` and `K = K(n, N₊)` (the constant of the corrected bound on `N` in
Lemma 4.6, `IsVariationalSolution.frequencyN_change_of_point_le`).

1. `N_y(20r) ≤ K` for `y ∈ B̄_r(x)` (`frequencyN_twenty_le`), and
   `H_y(20r) ≤ C_H H_{x₀}(10r)` for `y, x₀ ∈ B̄_r(x)` (`heightH_twenty_le`): Lemma 4.6 (both
   bounds on `H`) at centre `x` and Lemma 4.3.
2. `f` attains its minimum on the compact set `S` at some `x₀`.
3. If `f(x₀) > δ₀`, then `f > δ₀` `μ`-a.e. on `B_r(x)` and `β² ≤ μ(B_r(x)) / r^{n-1}` gives the
   claim (the paper's trivial case).
4. Otherwise (6.23): the annulus estimate at `y` and at `x₀`
   (`integral_annulus_homogeneity_le`) fed into Lemma 6.2 scaled by `ρ = 2r`
   (`integral_annulus_sq_inner_le`).
5. The Fubini step (`Estimates/Jones.lean`) with `A = B_{10r}(x₀) ∖ B_{5r}(x₀)`
   (`jonesBetaSq_mul_lintegral_le_of_isMinOn`).
6. The lower bound `∫_A |∇u|² ≥ (10r)ⁿ H_{x₀}(10r) / 4` (the last step of the paper's proof; we
   use the annulus `B_{10r} ∖ B_{5r}`, contained in the paper's,
   `le_integral_annulus_norm_gradient_sq`).

## Deviations from the paper

* The solution is assumed on `B̄_{50r}(x)` (the paper writes `B_{8r}(x)`).
* **Lemma 6.2 at scale 2.** The paper applies Lemma 6.2 to `x` and `x₀` with
  `|x − x₀| < 2` (both lie in `B_1`) on the annuli `B_{20} ∖ B_1`, i.e. Lemma 6.2 rescaled by `2`,
  and takes `N_{x}(1)` as the degree. We use the scaled form of Lemma 6.2 with `ρ = 2r`
  (`two_point_homogeneity_scaled_of_lipschitzOnWith`): the degrees are
  `N_y(2r)`, the hypotheses are on `B_{20r} ∖ B_{2r}` and the conclusion on
  `B_{18r}(x₀) ∖ B_{4r}(x₀)`, as in (6.23). We need `|y − x₀| < 2r` strictly: this holds for `y`
  in the open ball `B_r(x)`, which carries the integral.
* **The lower bound.** Only `V_{x₀}(5r)` needs to be small (Lemma 4.5 at
  `t = 5r`, outer radius `20r`); for `V_{x₀}(10r)` the sign `V ≥ 0` suffices. The annulus is
  `A = B_{10r}(x₀) ∖ B_{5r}(x₀)`, which is contained in the region `B_{18r} ∖ B_{4r}` of (6.23);
  the paper's `B_{10} ∖ B_4` works equally. The restriction to `{u > 0}` is not needed
  (`Estimates/Jones.lean`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Constants -/

/-- The threshold `δ₀(n, N₊) = 1 / (8 · 4ⁿ C(K + 1)²)` of the proof of Theorem 6.1, where
`K = frequencyNChangeConst n N₊` and `C` is the constant of Lemma 4.3. It makes the bound of
Lemma 4.5 on `V` at most `1/2`. -/
def l2SubspaceDelta (n : ℕ) (Np : ℝ) : ℝ :=
  1 / (8 * 4 ^ n * Abstract.RadialData.doublingConst (frequencyNChangeConst n Np + 1) ^ 2)

theorem l2SubspaceDelta_pos (n : ℕ) (Np : ℝ) : 0 < l2SubspaceDelta n Np := by
  have := Abstract.RadialData.doublingConst_pos (frequencyNChangeConst n Np + 1)
  unfold l2SubspaceDelta
  positivity

/-- The constant of the main case of Theorem 6.1 before the lower bound: the constant of
Lemma 6.2 times the constants of the annulus estimate. -/
def l2SubspaceFubiniConst (n : ℕ) (Np : ℝ) : ℝ :=
  twoPointConst n (frequencyNChangeConst n Np) * 20 ^ (n + 2) *
    (1 + 2 * frequencyNChangeConst n Np) * l2SubspaceHeightConst n Np

theorem l2SubspaceFubiniConst_nonneg (n : ℕ) (Np : ℝ) : 0 ≤ l2SubspaceFubiniConst n Np := by
  have h1 := twoPointConst_pos n (frequencyNChangeConst n Np)
  have h2 := one_le_frequencyNChangeConst n Np
  have h3 := l2SubspaceHeightConst_pos n Np
  unfold l2SubspaceFubiniConst
  have : 0 ≤ 1 + 2 * frequencyNChangeConst n Np := by linarith
  positivity

/-- The constant `C(N₊, n)` of Theorem 6.1. -/
def l2SubspaceConst (n : ℕ) (Np : ℝ) : ℝ :=
  max (l2SubspaceDelta n Np)⁻¹ (4 * l2SubspaceFubiniConst n Np / 10 ^ n)

namespace IsVariationalSolution

variable [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n} {r Np : ℝ}

/-- `M_x(s) ≥ |B_1|` for `x ∈ Σ^H_r`, `r ≤ s` and `B̄_s(x) ⊆ Ω` (Prop 3.4). -/
theorem unitBallVolume_le_monotonicityM_of_mem_sigmaHr (h : IsVariationalSolution Ω C u χ)
    (hr : 0 < r) (hx : x ∈ sigmaHr Ω u χ r) {s : ℝ} (hrs : r ≤ s) (hs : closedBall x s ⊆ Ω) :
    unitBallVolume n ≤ monotonicityM u χ x s :=
  hx.2.2.2.trans (h.monotonicityM_le hr hrs hs)

/-! ### Step 1: bounds on `N` and `H` near `x` -/

/-- `N_y(20r) ≤ K(n, N₊)` for `y ∈ B̄_r(x)` (Lemma 4.6 at centre `x`, radius `50r`, as in the
proof of Theorem 6.1). -/
theorem frequencyN_twenty_le (h : IsVariationalSolution Ω C u χ) (hr : 0 < r)
    (hΩ : closedBall x (50 * r) ⊆ Ω) (hx : x ∈ sigmaHr Ω u χ r)
    (hN : frequencyN u χ x (50 * r) ≤ Np) {y : Rn n} (hy : y ∈ closedBall x r) :
    frequencyN u χ y (20 * r) ≤ frequencyNChangeConst n Np := by
  rw [mem_closedBall] at hy
  refine h.frequencyN_change_of_point_le hx.2.2.1 (by positivity) hΩ ?_ hN ?_ (by positivity)
    (by linarith)
  · exact h.unitBallVolume_le_monotonicityM_of_mem_sigmaHr hr hx (by linarith)
      ((closedBall_subset_closedBall (by linarith)).trans hΩ)
  · rw [mem_ball]; linarith

/-- `H_y(20r) ≤ C_H H_{x₀}(10r)` for `y, x₀ ∈ B̄_r(x)` (proof of Theorem 6.1): the upper bound of
Lemma 4.6 at centre `x`, radius `32r`; Lemma 4.3 on `[16r, 32r]`; the lower bound of Lemma 4.6
at centre `x`, radius `16r`. -/
theorem heightH_twenty_le (h : IsVariationalSolution Ω C u χ) (hr : 0 < r)
    (hΩ : closedBall x (50 * r) ⊆ Ω) (hx : x ∈ sigmaHr Ω u χ r)
    (hN : frequencyN u χ x (50 * r) ≤ Np) {y x₀ : Rn n} (hy : y ∈ closedBall x r)
    (hx₀ : x₀ ∈ closedBall x r) :
    heightH u y (20 * r) ≤ l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) := by
  have hb : ball x (50 * r) ⊆ Ω := ball_subset_closedBall.trans hΩ
  refine IsVariationalSolutionQ.heightH_twenty_le (QBounds.one Ω) h.toQ hr
    (by simp [weissKappa_zero]) hΩ (by rwa [weissKappa_zero, h.sigmaHQr_one hr]) ?_ hy hx₀
  rwa [weissKappa_zero, h.modFrequencyN_one (by positivity) hb]

/-! ### Step 4: the estimate (6.23) -/

/-- The annulus estimate at a point `y ∈ B̄_r(x) ∩ Σ^H_r` (proof of Theorem 6.1), with degree
`N_y(2r)`: `∫_{B_{20r}(y)∖B_{2r}(y)} (∇u·(z−y) − N_y(2r) u)² ≤
(20r)^{n+2} H_y(20r) (1 + 2K) (N_y(20r) − N_y(r))`. -/
theorem integral_annulus_le_of_mem (h : IsVariationalSolution Ω C u χ) (hr : 0 < r)
    (hΩ : closedBall x (50 * r) ⊆ Ω) (hx : x ∈ sigmaHr Ω u χ r)
    (hN : frequencyN u χ x (50 * r) ≤ Np) {y : Rn n} (hy : y ∈ closedBall x r)
    (hyH : y ∈ sigmaHr Ω u χ r) :
    ∫ z in ball y (20 * r) \ ball y (2 * r),
        (⟪gradient u z, z - y⟫ - frequencyN u χ y (2 * r) * u z) ^ 2 ≤
      (20 * r) ^ (n + 2) * heightH u y (20 * r) * (1 + 2 * frequencyNChangeConst n Np) *
        (frequencyN u χ y (20 * r) - frequencyN u χ y r) := by
  have hΩy : closedBall y (20 * r) ⊆ Ω :=
    closedBall_subset_of_dist_le (mem_closedBall.1 hy) (by linarith) hΩ
  have hmono := h.monotoneOn_frequencyN_of_mem_sigmaHr hr hyH hΩy
  have h1 : 1 ≤ frequencyN u χ y (2 * r) :=
    h.one_le_frequencyN_of_mem_sigmaHr hr hyH hΩy ⟨by linarith, by linarith⟩
  have hK := h.frequencyN_twenty_le hr hΩ hx hN hy
  have hle1 : frequencyN u χ y r ≤ frequencyN u χ y (2 * r) :=
    hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hle2 : frequencyN u χ y (2 * r) ≤ frequencyN u χ y (20 * r) :=
    hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  refine (h.integral_annulus_homogeneity_le hyH.2.2.1 hr (by linarith) (by linarith) hyH.2.2.2
    hΩy).trans ?_
  have hA : 0 ≤ (20 * r) ^ (n + 2) * heightH u y (20 * r) :=
    mul_nonneg (by positivity) (heightH_nonneg _ _ (by positivity))
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hA) (by linarith) (by linarith)
    (mul_nonneg hA (by linarith))

/-- **The estimate (6.23)**, at scale `r`: if `x₀ ∈ B̄_r(x) ∩ Σ^H_r`,
`y ∈ B_r(x) ∩ Σ^H_r` and `f(x₀) ≤ f(y)`, where `f = N(20r) − N(r)`, then
`∫_{B_{18r}(x₀)∖B_{4r}(x₀)} ⟪∇u, y − x₀⟫² ≤ C (20r)^{n+2} H_{x₀}(10r) f(y)`. This is Lemma 6.2
scaled by `ρ = 2r` (`two_point_homogeneity_scaled_of_lipschitzOnWith`). -/
theorem integral_annulus_sq_inner_le (h : IsVariationalSolution Ω C u χ) (hr : 0 < r)
    (hΩ : closedBall x (50 * r) ⊆ Ω) (hx : x ∈ sigmaHr Ω u χ r)
    (hN : frequencyN u χ x (50 * r) ≤ Np) {x₀ y : Rn n} (hx₀ : x₀ ∈ closedBall x r)
    (hx₀H : x₀ ∈ sigmaHr Ω u χ r) (hy : y ∈ ball x r) (hyH : y ∈ sigmaHr Ω u χ r)
    (hmin : frequencyN u χ x₀ (20 * r) - frequencyN u χ x₀ r ≤
      frequencyN u χ y (20 * r) - frequencyN u χ y r) :
    ∫ z in ball x₀ (18 * r) \ ball x₀ (4 * r), ⟪gradient u z, y - x₀⟫ ^ 2 ≤
      twoPointConst n (frequencyNChangeConst n Np) *
        ((20 * r) ^ (n + 2) * (1 + 2 * frequencyNChangeConst n Np) *
          l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) *
            (frequencyN u χ y (20 * r) - frequencyN u χ y r)) := by
  set K := frequencyNChangeConst n Np with hKdef
  have hy' : y ∈ closedBall x r := ball_subset_closedBall hy
  have hΩ₀ : closedBall x₀ (20 * r) ⊆ Ω :=
    closedBall_subset_of_dist_le (mem_closedBall.1 hx₀) (by linarith) hΩ
  have hΩy : closedBall y (20 * r) ⊆ Ω :=
    closedBall_subset_of_dist_le (mem_closedBall.1 hy') (by linarith) hΩ
  have hmono₀ := h.monotoneOn_frequencyN_of_mem_sigmaHr hr hx₀H hΩ₀
  have hmonoy := h.monotoneOn_frequencyN_of_mem_sigmaHr hr hyH hΩy
  have hf₀ : 0 ≤ frequencyN u χ x₀ (20 * r) - frequencyN u χ x₀ r :=
    sub_nonneg.2 (hmono₀ ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith))
  have hK1 : 0 ≤ 1 + 2 * K := by linarith [one_le_frequencyNChangeConst n Np]
  have hH10 : 0 ≤ heightH u x₀ (10 * r) := heightH_nonneg _ _ (by positivity)
  have hCH := l2SubspaceHeightConst_pos n Np
  have hP : 0 ≤ (20 * r) ^ (n + 2) := by positivity
  -- the two annulus estimates, with a common right-hand side `δ`
  have hδ : ∀ w ∈ closedBall x r, w ∈ sigmaHr Ω u χ r →
      frequencyN u χ w (20 * r) - frequencyN u χ w r ≤
        frequencyN u χ y (20 * r) - frequencyN u χ y r →
      ∫ z in ball w (10 * (2 * r)) \ ball w (2 * r),
          (⟪gradient u z, z - w⟫ - frequencyN u χ w (2 * r) * u z) ^ 2 ≤
        (20 * r) ^ (n + 2) * (1 + 2 * K) * l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) *
          (frequencyN u χ y (20 * r) - frequencyN u χ y r) := by
    intro w hw hwH hfw
    have hΩw : closedBall w (20 * r) ⊆ Ω :=
      closedBall_subset_of_dist_le (mem_closedBall.1 hw) (by linarith) hΩ
    have hfw₀ : 0 ≤ frequencyN u χ w (20 * r) - frequencyN u χ w r :=
      sub_nonneg.2 (h.monotoneOn_frequencyN_of_mem_sigmaHr hr hwH hΩw ⟨le_rfl, by linarith⟩
        ⟨by linarith, le_rfl⟩ (by linarith))
    rw [show 10 * (2 * r) = 20 * r by ring]
    refine (h.integral_annulus_le_of_mem hr hΩ hx hN hw hwH).trans ?_
    have hHw := h.heightH_twenty_le hr hΩ hx hN hw hx₀
    calc (20 * r) ^ (n + 2) * heightH u w (20 * r) * (1 + 2 * K) *
          (frequencyN u χ w (20 * r) - frequencyN u χ w r)
        ≤ (20 * r) ^ (n + 2) * (l2SubspaceHeightConst n Np * heightH u x₀ (10 * r)) *
            (1 + 2 * K) * (frequencyN u χ y (20 * r) - frequencyN u χ y r) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHw hP) hK1) hfw
            hfw₀ (mul_nonneg (mul_nonneg hP (mul_nonneg hCH.le hH10)) hK1)
      _ = _ := by ring
  have H₀ := hδ x₀ hx₀ hx₀H hmin
  have Hy := hδ y hy' hyH le_rfl
  have hN₀ : frequencyN u χ x₀ (2 * r) ∈ Icc 1 K :=
    ⟨h.one_le_frequencyN_of_mem_sigmaHr hr hx₀H hΩ₀ ⟨by linarith, by linarith⟩,
      (hmono₀ ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)).trans
        (h.frequencyN_twenty_le hr hΩ hx hN hx₀)⟩
  have hNy : frequencyN u χ y (2 * r) ∈ Icc 1 K :=
    ⟨h.one_le_frequencyN_of_mem_sigmaHr hr hyH hΩy ⟨by linarith, by linarith⟩,
      (hmonoy ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)).trans
        (h.frequencyN_twenty_le hr hΩ hx hN hy')⟩
  have hLip : LipschitzOnWith C u (ball x₀ (20 * (2 * r))) :=
    h.lipschitzOnWith x₀ _ (ball_subset_closedBall.trans
      (closedBall_subset_of_dist_le (mem_closedBall.1 hx₀) (by linarith) hΩ))
  have hdist : dist y x₀ < 2 * r := by
    have h1 := mem_ball.1 hy
    have h2 := mem_closedBall.1 hx₀
    calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      _ < 2 * r := by rw [dist_comm x x₀]; linarith
  have h2 := (two_point_homogeneity_scaled_of_lipschitzOnWith hLip (by positivity) hdist hN₀ hNy
    H₀ Hy).2
  rw [show 9 * (2 * r) = 18 * r by ring, show 2 * (2 * r) = 4 * r by ring] at h2
  exact h2

/-! ### Step 6: the lower bound -/

/-- **The lower bound in the proof of Theorem 6.1**: if `x₀ ∈ B̄_r(x) ∩ Σ^H_r` and
`N_{x₀}(20r) − N_{x₀}(r) ≤ δ₀`, then `∫_{B_{10r}(x₀)∖B_{5r}(x₀)} |∇u|² ≥ (10r)ⁿ H_{x₀}(10r) / 4`.

With `I_s = ∫_{B_s(x₀)} |∇u|² = sⁿ H(s) (N(s) + V(s))` (4.11): `I_{5r} ≤ 2⁻ⁿ (10r)ⁿ H(10r)
(N(10r) + V(5r))` by `H(5r) ≤ H(10r)` and `N(5r) ≤ N(10r)`, and `I_{10r} ≥ (10r)ⁿ H(10r) N(10r)`
by `V(10r) ≥ 0`. Since `N(10r) ≥ 1`, `2⁻ⁿ ≤ 1/2` and `V(5r) ≤ 1/2` (Lemma 4.5 with the choice of
`δ₀`), `I_{10r} − I_{5r} ≥ (10r)ⁿ H(10r) / 4`. -/
theorem le_integral_annulus_norm_gradient_sq (h : IsVariationalSolution Ω C u χ) (hr : 0 < r)
    (hΩ : closedBall x (50 * r) ⊆ Ω) (hx : x ∈ sigmaHr Ω u χ r)
    (hN : frequencyN u χ x (50 * r) ≤ Np) {x₀ : Rn n} (hx₀ : x₀ ∈ closedBall x r)
    (hx₀H : x₀ ∈ sigmaHr Ω u χ r)
    (hsmall : frequencyN u χ x₀ (20 * r) - frequencyN u χ x₀ r ≤ l2SubspaceDelta n Np) :
    (10 * r) ^ n * heightH u x₀ (10 * r) / 4 ≤
      ∫ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ‖gradient u z‖ ^ 2 := by
  set K := frequencyNChangeConst n Np with hKdef
  set Cd := Abstract.RadialData.doublingConst (K + 1) with hCd
  have hCd0 : 0 < Cd := Abstract.RadialData.doublingConst_pos _
  have hΩ₀ : closedBall x₀ (20 * r) ⊆ Ω :=
    closedBall_subset_of_dist_le (mem_closedBall.1 hx₀) (by linarith) hΩ
  have hball : ∀ s, s ≤ 20 * r → ball x₀ s ⊆ Ω := fun s hs =>
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hs).trans hΩ₀)
  have hmono := h.monotoneOn_frequencyN_of_mem_sigmaHr hr hx₀H hΩ₀
  -- (4.11) in the form `I_s = sⁿ H(s) (N(s) + V(s))`
  have hI : ∀ s, 0 < s → s ≤ 20 * r → 0 < heightH u x₀ s →
      ∫ z in ball x₀ s, ‖gradient u z‖ ^ 2 =
        s ^ n * heightH u x₀ s * (frequencyN u χ x₀ s + volumeV u χ x₀ s) := by
    intro s hs hs20 hH
    rw [h.frequencyN_add_volumeV_eq hs (hball s hs20)]
    field_simp
  have hH : ∀ s, r ≤ s → s ≤ 20 * r → 0 < heightH u x₀ s := fun s hrs hs20 =>
    h.heightH_pos hx₀H.2.2.1 (hr.trans_le hrs) ((closedBall_subset_closedBall hs20).trans hΩ₀)
  have hH5 := hH (5 * r) (by linarith) (by linarith)
  have hH10 := hH (10 * r) (by linarith) (by linarith)
  have hHle : heightH u x₀ (5 * r) ≤ heightH u x₀ (10 * r) :=
    h.monotoneOn_heightH hx₀H.2.2.1 hr hx₀H.2.2.2 hΩ₀ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  have hNle : frequencyN u χ x₀ (5 * r) ≤ frequencyN u χ x₀ (10 * r) :=
    hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hN5 : 1 ≤ frequencyN u χ x₀ (5 * r) :=
    h.one_le_frequencyN_of_mem_sigmaHr hr hx₀H hΩ₀ ⟨by linarith, by linarith⟩
  have hN10 : 1 ≤ frequencyN u χ x₀ (10 * r) := hN5.trans hNle
  have hV5 : 0 ≤ volumeV u χ x₀ (5 * r) := h.volumeV_nonneg (by positivity) (hball _ (by linarith))
  have hV10 : 0 ≤ volumeV u χ x₀ (10 * r) :=
    h.volumeV_nonneg (by positivity) (hball _ (by linarith))
  -- Lemma 4.5: `V(5r) ≤ 1/2`
  have hV5le : volumeV u χ x₀ (5 * r) ≤ 1 / 2 := by
    have hδ₀ := l2SubspaceDelta_pos n Np
    have hK : frequencyN u χ x₀ (20 * r) < K + 1 := by
      linarith [h.frequencyN_twenty_le hr hΩ hx hN hx₀]
    have hdrop : frequencyN u χ x₀ (20 * r) - frequencyN u χ x₀ (5 * r) <
        2 * l2SubspaceDelta n Np := by
      have := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith :
        r ≤ 5 * r)
      linarith
    have hV := h.volumeV_le_sqrt hx₀H.2.2.1 (t := 5 * r) (r := 20 * r) (by positivity)
      (by linarith)
      (h.unitBallVolume_le_monotonicityM_of_mem_sigmaHr hr hx₀H (by linarith)
        ((closedBall_subset_closedBall (by linarith)).trans hΩ₀)) hΩ₀ hK hdrop
    have hsq : √(2 * l2SubspaceDelta n Np) = 1 / (2 * 2 ^ n * Cd) := by
      rw [show 2 * l2SubspaceDelta n Np = (1 / (2 * 2 ^ n * Cd)) ^ 2 by
        rw [l2SubspaceDelta, ← hKdef, ← hCd,
          show (4 : ℝ) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        field_simp
        ring]
      exact Real.sqrt_sq (by positivity)
    rw [hsq] at hV
    calc volumeV u χ x₀ (5 * r) ≤ 2 ^ n * Cd * (1 / (2 * 2 ^ n * Cd)) := hV
      _ = 1 / 2 := by field_simp
  -- the two integrals
  have hI5 := hI (5 * r) (by positivity) (by linarith) hH5
  have hI10 := hI (10 * r) (by positivity) (by linarith) hH10
  have hdiff : ∫ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ‖gradient u z‖ ^ 2 =
      (∫ z in ball x₀ (10 * r), ‖gradient u z‖ ^ 2) -
        ∫ z in ball x₀ (5 * r), ‖gradient u z‖ ^ 2 :=
    setIntegral_diff measurableSet_ball
      (h.integrableOn_norm_gradient_sq (hball _ (by linarith)))
      (ball_subset_ball (by linarith))
  rw [hdiff, hI5, hI10]
  -- arithmetic, with `T = (10r)ⁿ` and `b = 2⁻ⁿ`
  have hb0 : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  have hb2 : ((1 : ℝ) / 2) ^ n ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (NeZero.ne n)
  have h5 : (5 * r) ^ n = (1 / 2) ^ n * (10 * r) ^ n := by
    rw [← mul_pow]; ring_nf
  have hT0 : 0 ≤ (10 * r) ^ n := by positivity
  have hQ0 : 0 ≤ (10 * r) ^ n * heightH u x₀ (10 * r) := mul_nonneg hT0 hH10.le
  have hup : (5 * r) ^ n * heightH u x₀ (5 * r) *
      (frequencyN u χ x₀ (5 * r) + volumeV u χ x₀ (5 * r)) ≤
      (1 / 2) ^ n * (10 * r) ^ n * heightH u x₀ (10 * r) *
        (frequencyN u χ x₀ (10 * r) + volumeV u χ x₀ (5 * r)) := by
    rw [h5]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hHle (mul_nonneg hb0 hT0)) (by linarith)
      (by linarith) (mul_nonneg (mul_nonneg hb0 hT0) hH10.le)
  have hlow : (10 * r) ^ n * heightH u x₀ (10 * r) * frequencyN u χ x₀ (10 * r) ≤
      (10 * r) ^ n * heightH u x₀ (10 * r) *
        (frequencyN u χ x₀ (10 * r) + volumeV u χ x₀ (10 * r)) := by
    nlinarith [mul_nonneg hQ0 hV10]
  have key : 1 / 4 ≤ (1 - (1 / 2) ^ n) * frequencyN u χ x₀ (10 * r) -
      (1 / 2) ^ n * volumeV u χ x₀ (5 * r) := by
    nlinarith [mul_le_mul_of_nonneg_left hN10 (by linarith : (0 : ℝ) ≤ 1 - (1 / 2) ^ n),
      mul_le_mul hb2 hV5le hV5 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hkey := mul_le_mul_of_nonneg_left key hQ0
  linarith

/-! ### Step 5: the Fubini step -/

/-- **Steps 4–5 of the proof of Theorem 6.1**: if `x₀` minimizes `f = N(20r) − N(r)` over
`B̄_r(x) ∩ Σ^H_r` and `μ` is carried by `Σ^H_r`, then with `A = B_{10r}(x₀) ∖ B_{5r}(x₀)`,
`β²_μ(x, r) ∫_A |∇u|² ≤ C rⁿ H_{x₀}(10r) r^{1-n} ∫_{B_r(x)} f dμ`. -/
theorem jonesBetaSq_mul_lintegral_le_of_isMinOn (h : IsVariationalSolution Ω C u χ)
    (hr : 0 < r) (hΩ : closedBall x (50 * r) ⊆ Ω) (hx : x ∈ sigmaHr Ω u χ r)
    (hN : frequencyN u χ x (50 * r) ≤ Np) (μ : Measure (Rn n)) [IsFiniteMeasure μ]
    (hμ : μ (sigmaHr Ω u χ r)ᶜ = 0) {x₀ : Rn n} (hx₀ : x₀ ∈ closedBall x r)
    (hx₀H : x₀ ∈ sigmaHr Ω u χ r)
    (hmin : ∀ y ∈ closedBall x r ∩ sigmaHr Ω u χ r,
      frequencyN u χ x₀ (20 * r) - frequencyN u χ x₀ r ≤
        frequencyN u χ y (20 * r) - frequencyN u χ y r) :
    jonesBetaSq μ x r *
        ∫⁻ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ENNReal.ofReal (‖gradient u z‖ ^ 2) ≤
      ENNReal.ofReal (l2SubspaceFubiniConst n Np * r ^ n * heightH u x₀ (10 * r)) *
        (∫⁻ y in ball x r, ENNReal.ofReal (frequencyN u χ y (20 * r) - frequencyN u χ y r) ∂μ) /
          ENNReal.ofReal (r ^ (n - 1)) := by
  have hc0 : 0 ≤ l2SubspaceFubiniConst n Np * r ^ n * heightH u x₀ (10 * r) :=
    mul_nonneg (mul_nonneg (l2SubspaceFubiniConst_nonneg n Np) (by positivity))
      (heightH_nonneg _ _ (by positivity))
  refine (jonesBetaSq_mul_lintegral_le μ x r x₀ u).trans ?_
  gcongr ?_ / _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hae : ∀ᵐ y ∂(μ.restrict (ball x r)), y ∈ ball x r ∧ y ∈ sigmaHr Ω u χ r := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hμ)] with y hy1 hy2
    exact ⟨hy1, by simpa using hy2⟩
  refine lintegral_mono_ae (hae.mono fun y hy => ?_)
  obtain ⟨hy, hyH⟩ := hy
  have hΩ₀ : ball x₀ (18 * r) ⊆ Ω := ball_subset_closedBall.trans
    (closedBall_subset_of_dist_le (mem_closedBall.1 hx₀) (by linarith) hΩ)
  have hgint : IntegrableOn (fun z => ⟪gradient u z, y - x₀⟫ ^ 2 / r ^ 2)
      (ball x₀ (18 * r) \ ball x₀ (4 * r)) := by
    refine (IntegrableOn.of_bound measure_ball_lt_top ?_ ((C : ℝ) ^ 2 * ‖y - x₀‖ ^ 2 / r ^ 2)
      ?_).mono_set diff_subset
    · exact ((((measurable_gradient u).inner measurable_const).pow_const 2).div_const
        _).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      calc ⟪gradient u z, y - x₀⟫ ^ 2 = |⟪gradient u z, y - x₀⟫| ^ 2 := (sq_abs _).symm
        _ ≤ (‖gradient u z‖ * ‖y - x₀‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
        _ = ‖gradient u z‖ ^ 2 * ‖y - x₀‖ ^ 2 := mul_pow _ _ _
        _ ≤ (C : ℝ) ^ 2 * ‖y - x₀‖ ^ 2 := by
          gcongr; exact h.norm_gradient_le (hΩ₀ hz)
  have h63 := h.integral_annulus_sq_inner_le hr hΩ hx hN hx₀ hx₀H hy hyH
    (hmin y ⟨ball_subset_closedBall hy, hyH⟩)
  calc ∫⁻ z in ball x₀ (10 * r) \ ball x₀ (5 * r),
        ENNReal.ofReal (⟪gradient u z, y - x₀⟫ ^ 2 / r ^ 2)
      ≤ ∫⁻ z in ball x₀ (18 * r) \ ball x₀ (4 * r),
          ENNReal.ofReal (⟪gradient u z, y - x₀⟫ ^ 2 / r ^ 2) :=
        lintegral_mono_set (diff_subset_diff (ball_subset_ball (by linarith))
          (ball_subset_ball (by linarith)))
    _ = ENNReal.ofReal (∫ z in ball x₀ (18 * r) \ ball x₀ (4 * r),
          ⟪gradient u z, y - x₀⟫ ^ 2 / r ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hgint
          (ae_of_all _ fun z => div_nonneg (sq_nonneg _) (sq_nonneg _))).symm
    _ ≤ ENNReal.ofReal (l2SubspaceFubiniConst n Np * r ^ n * heightH u x₀ (10 * r) *
          (frequencyN u χ y (20 * r) - frequencyN u χ y r)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_div]
        calc (∫ z in ball x₀ (18 * r) \ ball x₀ (4 * r), ⟪gradient u z, y - x₀⟫ ^ 2) / r ^ 2
            ≤ (twoPointConst n (frequencyNChangeConst n Np) *
                ((20 * r) ^ (n + 2) * (1 + 2 * frequencyNChangeConst n Np) *
                  l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) *
                    (frequencyN u χ y (20 * r) - frequencyN u χ y r))) / r ^ 2 := by
              gcongr
          _ = _ := by
              rw [l2SubspaceFubiniConst, mul_pow]
              field_simp
              ring
    _ = _ := ENNReal.ofReal_mul hc0

end IsVariationalSolution

/-! ### Theorem 6.1 -/

/-- **Theorem 6.1**, with the solution on `B̄_{50r}(x)` (the paper writes `B_{8r}(x)`).
There is `C = C(N₊, n)` such that for every variational solution `(u, χ)` on `Ω ⊇ B̄_{50r}(x)`,
every finite measure `μ` carried by `Σ^H_r`, and every `x ∈ Σ^H_r` with `N_x(u; 50r) ≤ N₊`,
`β²_μ(x, r) ≤ C r^{1-n} ∫_{B_r(x)} (N_y(u; 20r) − N_y(u; r)) dμ(y)`.

The constant is `l2SubspaceConst n N₊`. This is the statement of
`NaberValtorta.Inputs.jonesBetaSq_le`, verbatim. The proof follows the paper's at scale `r`
(see the module docstring): the minimizer `x₀` of `f = N(20r) − N(r)` on `B̄_r(x) ∩ Σ^H_r`, the
trivial case `f(x₀) > δ₀`, and otherwise (6.23), the Fubini step and the lower bound on
`∫_A |∇u|²`. -/
theorem jonesBetaSq_le (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ CJ : ℝ, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ)
      (μ : Measure (Rn n)), IsVariationalSolution Ω C u χ → 0 < r →
      closedBall x (50 * r) ⊆ Ω → IsFiniteMeasure μ → μ (sigmaHr Ω u χ r)ᶜ = 0 →
      x ∈ sigmaHr Ω u χ r → frequencyN u χ x (50 * r) ≤ Np →
      jonesBetaSq μ x r ≤ ENNReal.ofReal (CJ / r ^ (n - 1)) *
        ∫⁻ y in ball x r, ENNReal.ofReal (frequencyN u χ y (20 * r) - frequencyN u χ y r) ∂μ := by
  refine ⟨l2SubspaceConst n Np, fun Ω C u χ x r μ h hr hΩ hμfin hμ hx hN => ?_⟩
  haveI := hμfin
  set S := closedBall x r ∩ sigmaHr Ω u χ r with hS
  have hSsub : ∀ y ∈ S, closedBall y (20 * r) ⊆ Ω := fun y hy =>
    closedBall_subset_of_dist_le (mem_closedBall.1 hy.1) (by linarith) hΩ
  -- Step 2: the minimizer `x₀`
  have hSclosed : IsClosed S := by
    refine isClosed_of_closure_subset fun z hz => ?_
    have hz1 : z ∈ closedBall x r := closure_minimal inter_subset_left isClosed_closedBall hz
    have hz2 : z ∈ closure (sigmaHr Ω u χ r) := closure_mono inter_subset_right hz
    exact ⟨hz1, h.closure_sigmaHr_inter_subset hr
      ⟨hz2, closedBall_subset_of_dist_le (mem_closedBall.1 hz1) (by linarith) hΩ⟩⟩
  have hScpt : IsCompact S :=
    (isCompact_closedBall x r).of_isClosed_subset hSclosed inter_subset_left
  have hpos : ∀ s, r ≤ s → s ≤ 20 * r → ∀ y ∈ S,
      closedBall y s ⊆ Ω ∧ 0 < heightH u y s := fun s hrs hs y hy => by
    have hΩs := (closedBall_subset_closedBall hs).trans (hSsub y hy)
    exact ⟨hΩs, h.heightH_pos hy.2.2.2.1 (hr.trans_le hrs) hΩs⟩
  have hfcont : ContinuousOn
      (fun y => frequencyN u χ y (20 * r) - frequencyN u χ y r) S :=
    ((h.continuousOn_frequencyN (by positivity : (0 : ℝ) < 20 * r)).mono
      fun y hy => hpos _ (by linarith) le_rfl y hy).sub
      ((h.continuousOn_frequencyN hr).mono fun y hy => hpos r le_rfl (by linarith) y hy)
  obtain ⟨x₀, hx₀S, hmin⟩ := hScpt.exists_isMinOn ⟨x, mem_closedBall_self hr.le, hx⟩ hfcont
  have hmin' : ∀ y ∈ S, frequencyN u χ x₀ (20 * r) - frequencyN u χ x₀ r ≤
      frequencyN u χ y (20 * r) - frequencyN u χ y r := fun y hy => hmin hy
  set I := ∫⁻ y in ball x r,
    ENNReal.ofReal (frequencyN u χ y (20 * r) - frequencyN u χ y r) ∂μ with hI
  suffices H : ∃ c ≤ l2SubspaceConst n Np,
      jonesBetaSq μ x r ≤ ENNReal.ofReal c * I / ENNReal.ofReal (r ^ (n - 1)) by
    obtain ⟨c, hc, H⟩ := H
    exact H.trans (ofReal_mul_div_le_ofReal_div_mul hc hr I)
  by_cases hsmall : frequencyN u χ x₀ (20 * r) - frequencyN u χ x₀ r ≤ l2SubspaceDelta n Np
  · -- Steps 4–6: the main case
    refine ⟨4 * l2SubspaceFubiniConst n Np / 10 ^ n, le_max_right _ _, ?_⟩
    have hlow := h.le_integral_annulus_norm_gradient_sq hr hΩ hx hN hx₀S.1 hx₀S.2 hsmall
    have hE := h.jonesBetaSq_mul_lintegral_le_of_isMinOn hr hΩ hx hN μ hμ hx₀S.1 hx₀S.2 hmin'
    have hH := (hpos (10 * r) (by linarith) (by linarith) x₀ hx₀S).2
    have ha0 : 0 < (10 * r) ^ n * heightH u x₀ (10 * r) / 4 := by positivity
    have hA : ENNReal.ofReal ((10 * r) ^ n * heightH u x₀ (10 * r) / 4) ≤
        ∫⁻ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ENNReal.ofReal (‖gradient u z‖ ^ 2) := by
      have hint : IntegrableOn (fun z => ‖gradient u z‖ ^ 2)
          (ball x₀ (10 * r) \ ball x₀ (5 * r)) :=
        (h.integrableOn_norm_gradient_sq (ball_subset_closedBall.trans
          (hpos (10 * r) (by linarith) (by linarith) x₀ hx₀S).1)).mono_set diff_subset
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hlow
    have hc0 : 0 ≤ 4 * l2SubspaceFubiniConst n Np / 10 ^ n :=
      div_nonneg (mul_nonneg (by norm_num) (l2SubspaceFubiniConst_nonneg n Np)) (by positivity)
    have hceq : l2SubspaceFubiniConst n Np * r ^ n * heightH u x₀ (10 * r) =
        4 * l2SubspaceFubiniConst n Np / 10 ^ n *
          ((10 * r) ^ n * heightH u x₀ (10 * r) / 4) := by
      rw [mul_pow]; field_simp
    rw [hceq, ENNReal.ofReal_mul hc0] at hE
    have h2 : jonesBetaSq μ x r * ENNReal.ofReal ((10 * r) ^ n * heightH u x₀ (10 * r) / 4) ≤
        ENNReal.ofReal (4 * l2SubspaceFubiniConst n Np / 10 ^ n) * I /
            ENNReal.ofReal (r ^ (n - 1)) *
          ENNReal.ofReal ((10 * r) ^ n * heightH u x₀ (10 * r) / 4) :=
      calc _ ≤ jonesBetaSq μ x r *
            ∫⁻ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ENNReal.ofReal (‖gradient u z‖ ^ 2) := by
            gcongr
        _ ≤ _ := hE
        _ = _ := by simp only [div_eq_mul_inv]; ring
    exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 ha0).ne' ENNReal.ofReal_ne_top).1 h2
  · -- Step 3: the trivial case `f(x₀) > δ₀`
    rw [not_le] at hsmall
    refine ⟨(l2SubspaceDelta n Np)⁻¹, le_max_left _ _, ?_⟩
    have hδ := l2SubspaceDelta_pos n Np
    refine (jonesBetaSq_le_measure_ball (NeZero.pos n) μ x r).trans ?_
    gcongr ?_ / _
    have hae : ∀ᵐ y ∂(μ.restrict (ball x r)), y ∈ ball x r ∧ y ∈ sigmaHr Ω u χ r := by
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hμ)] with y hy1 hy2
      exact ⟨hy1, by simpa using hy2⟩
    have hIδ : ENNReal.ofReal (l2SubspaceDelta n Np) * μ (ball x r) ≤ I := by
      rw [hI, ← setLIntegral_const]
      refine lintegral_mono_ae (hae.mono fun y hy => ENNReal.ofReal_le_ofReal ?_)
      exact hsmall.le.trans (hmin' y ⟨ball_subset_closedBall hy.1, hy.2⟩)
    calc μ (ball x r) = ENNReal.ofReal (l2SubspaceDelta n Np)⁻¹ *
          (ENNReal.ofReal (l2SubspaceDelta n Np) * μ (ball x r)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), inv_mul_cancel₀ hδ.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (l2SubspaceDelta n Np)⁻¹ * I := by gcongr

end InnerVariational
