/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Estimates.Jones
public import InnerVariational.Homogeneity.TwoPoint
public import GMTFoundations.Defs.GMT
public import InnerVariational.Frequency.SigmaHQ
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# `L²`-subspace approximation with a Lipschitz coefficient (Theorem 6.1)

Theorem 6.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for variational solutions
with a Lipschitz coefficient `Q` (`QBounds Ω Q L c C'`, `κ = weissKappa L c C'`): for `(u, χ)` on
`B̄_{50r}(x)` with `50 κ r ≤ 1/2`, a finite measure `μ` carried by `Σ^H_{Q,r}`, `x ∈ Σ^H_{Q,r}`
and `Ñ_x(u; 50r) ≤ N₊`,

`β²_μ(x, r) ≤ C(N₊, n) r^{1-n} ∫_{B_r(x)} (Ñ_y(u; 20r) − Ñ_y(u; r)) dμ(y)`,

where `Ñ = N + κ² s² / 2` is the modified frequency (`modFrequencyN`) and `Σ^H_{Q,r}` is
`sigmaHQr` (`Frequency/SigmaHQ.lean`).

## Proof

The proof of the constant-coefficient case (`Estimates/L2Subspace.lean`) goes through with the
following changes.
* The frequency bounds use Lemma 4.6 with a Lipschitz coefficient
  (`modFrequencyN_change_of_point_le`) and the monotonicity of `Ñ`.
* The annulus estimate at `y` with degree `Ñ_y(2r)` has an additional term of order
  `κ⁴ r⁴` (since `N = Ñ − κ² s² / 2` is not monotone). It is absorbed by the pinching itself:
  `Ñ_y(20r) − Ñ_y(r) ≥ κ² (400 − 1) r² / 8` (`sq_mul_sub_sq_le_modFrequencyN_sub`), and
  `κ r ≤ 1/100`.
* The lower bound on `∫_{B_{10r}(x₀) ∖ B_{5r}(x₀)} |∇u|²` uses `H(5r) ≤ e^{κ² (10r)² / 8} H(10r)`,
  `N(5r) ≤ N(10r) + κ² (10r)² / 2` and `N(10r) ≥ 1 − κ² (10r)² / 8` in place of the monotonicity
  of `H` and `N` and `N ≥ 1`.

## Differences from the paper

The paper treats `Q ≡ 1`. The hypothesis `50 κ r ≤ 1/2` restricts to scales at which the
coefficient is almost constant; for `Q ≡ 1` it is empty. As in the constant-coefficient file, the
solution is assumed on `B̄_{50r}(x)` (the paper writes `B_{8r}(x)`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Constants -/

/-- The constant `C_H(n, N₊)` with `H_y(20r) ≤ C_H H_{x₀}(10r)` for `y, x₀ ∈ B̄_r(x)`: the
product of the two constants of Lemma 4.6 and the constant of Lemma 4.3. -/
def l2SubspaceHeightConst (n : ℕ) (Np : ℝ) : ℝ :=
  heightHChangeConst n * Abstract.RadialData.doublingConst (max Np 1 + 1) *
    heightHChangeConst' n Np

theorem l2SubspaceHeightConst_pos (n : ℕ) (Np : ℝ) : 0 < l2SubspaceHeightConst n Np := by
  have h1 := heightHChangeConst_pos n
  have h2 := Abstract.RadialData.doublingConst_pos (max Np 1 + 1)
  have h3 := heightHChangeConst'_pos n Np
  unfold l2SubspaceHeightConst
  positivity


/-- The threshold `δ₀(n, N₊) = 1 / (96 · 4ⁿ C(K + 1)²)` of the proof of Theorem 6.1 with a
Lipschitz coefficient, where `K = modFrequencyNChangeConst n N₊` and `C` is the constant of
Lemma 4.3. It makes the bound of Lemma 4.5 on `V` at most `1/4`. -/
def l2SubspaceDeltaQ (n : ℕ) (Np : ℝ) : ℝ :=
  1 / (96 * 4 ^ n * Abstract.RadialData.doublingConst (modFrequencyNChangeConst n Np + 1) ^ 2)

theorem l2SubspaceDeltaQ_pos (n : ℕ) (Np : ℝ) : 0 < l2SubspaceDeltaQ n Np := by
  have := Abstract.RadialData.doublingConst_pos (modFrequencyNChangeConst n Np + 1)
  unfold l2SubspaceDeltaQ
  positivity

/-- The constant of the main case of Theorem 6.1 with a Lipschitz coefficient before the lower
bound. -/
def l2SubspaceFubiniConstQ (n : ℕ) (Np : ℝ) : ℝ :=
  twoPointConst n (modFrequencyNChangeConst n Np) * 20 ^ (n + 2) *
    (4 + 4 * modFrequencyNChangeConst n Np) * l2SubspaceHeightConst n Np

theorem l2SubspaceFubiniConstQ_nonneg (n : ℕ) (Np : ℝ) : 0 ≤ l2SubspaceFubiniConstQ n Np := by
  have h1 := twoPointConst_pos n (modFrequencyNChangeConst n Np)
  have h2 := two_le_modFrequencyNChangeConst n Np
  have h3 := l2SubspaceHeightConst_pos n Np
  unfold l2SubspaceFubiniConstQ
  have : 0 ≤ 4 + 4 * modFrequencyNChangeConst n Np := by linarith
  positivity

/-- The constant `C(N₊, n)` of Theorem 6.1 with a Lipschitz coefficient. -/
def l2SubspaceConstQ (n : ℕ) (Np : ℝ) : ℝ :=
  max (l2SubspaceDeltaQ n Np)⁻¹ (4 * l2SubspaceFubiniConstQ n Np / 10 ^ n)

/-- `e^{1/800} ≤ 101/100`. -/
theorem exp_one_div_eight_hundred_le : Real.exp (1 / 800) ≤ 101 / 100 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 800) (by norm_num) (by norm_num)
  have : (1 : ℝ) / (1 - 1 / 800) ≤ 101 / 100 := by norm_num
  linarith

/-! ### Elementary helpers -/

theorem closedBall_subset_of_dist_le {Ω : Set (Rn n)} {x y : Rn n} {r s t : ℝ}
    (hy : dist y x ≤ r) (hst : s + r ≤ t) (hΩ : closedBall x t ⊆ Ω) : closedBall y s ⊆ Ω :=
  (closedBall_subset_closedBall' (by linarith)).trans hΩ

/-- `ofReal c * I / ofReal (r^{n-1}) ≤ ofReal (C / r^{n-1}) * I` for `c ≤ C` and `r > 0`. -/
theorem ofReal_mul_div_le_ofReal_div_mul {c C' r : ℝ} (hcC : c ≤ C') (hr : 0 < r) (I : ℝ≥0∞) :
    ENNReal.ofReal c * I / ENNReal.ofReal (r ^ (n - 1)) ≤
      ENNReal.ofReal (C' / r ^ (n - 1)) * I := by
  rw [ENNReal.ofReal_div_of_pos (pow_pos hr _), div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  gcongr

namespace IsVariationalSolutionQ

variable [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {r Np : ℝ}
  {L : ℝ≥0} {c C' : ℝ}

section Setting

variable (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ) (hr : 0 < r)
  (hκ : weissKappa L c C' * (50 * r) ≤ 1 / 2) (hΩ : closedBall x (50 * r) ⊆ Ω)
  (hx : x ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r)
  (hN : modFrequencyN (weissKappa L c C') Q u χ x (50 * r) ≤ Np)
include hQ h hr hκ hΩ hx hN

omit [NeZero n] h hr hΩ hN in
theorem weissKappa_mul_le {s : ℝ} (hs : s ≤ 50 * r) : weissKappa L c C' * s ≤ 1 / 2 :=
  (mul_le_mul_of_nonneg_left hs (hQ.weissKappa_nonneg hx.1)).trans hκ

omit [NeZero n] h hΩ hN in
theorem weissKappa_sq_mul_sq_le : weissKappa L c C' ^ 2 * r ^ 2 ≤ 1 / 10000 := by
  have hk := hQ.weissKappa_nonneg hx.1
  have h1 : weissKappa L c C' * r ≤ 1 / 100 := by nlinarith
  have := sq_mul_sq_le_of_mul_le hk hr.le (by linarith : weissKappa L c C' * r ≤ 1 / 2)
  have h0 : 0 ≤ weissKappa L c C' * r := mul_nonneg hk hr.le
  have : (weissKappa L c C' * r) ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ h0 h1 2
  rw [mul_pow] at this
  linarith

omit hN in
/-- The frequency facts at a point `y ∈ B̄_r(x) ∩ Σ^H_{Q,r}`: `B̄_{20r}(y) ⊆ Ω`, `Ñ_y` is
nondecreasing on `[r, 20r]`, and for `s ∈ [r, 20r]`: `H_y(s) > 0`, `Z_y(s) ≥ 0`,
`N_y(s) ≥ 1 − κ² s² / 8` and `Ñ_y(s) ≥ 1`. -/
theorem frequency_facts {y : Rn n} (hy : y ∈ closedBall x r)
    (hyH : y ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r) :
    closedBall y (20 * r) ⊆ Ω ∧
      MonotoneOn (modFrequencyN (weissKappa L c C') Q u χ y) (Icc r (20 * r)) ∧
      ∀ s ∈ Icc r (20 * r), 0 < heightH u y s ∧
        0 ≤ modMonotonicityM (weissKappa L c C') Q u χ y s ∧
        1 - weissKappa L c C' ^ 2 * s ^ 2 / 8 ≤ weightedFrequencyN Q u χ y s ∧
        1 ≤ modFrequencyN (weissKappa L c C') Q u χ y s := by
  have hΩy : closedBall y (20 * r) ⊆ Ω :=
    closedBall_subset_of_dist_le (mem_closedBall.1 hy) (by linarith) hΩ
  have hκ20 := weissKappa_mul_le hQ hκ hx (s := 20 * r) (by linarith)
  exact ⟨hΩy, h.monotoneOn_modFrequencyN hQ hyH.2.2.1 hr hyH.2.2.2 hκ20 hΩy,
    fun s hs => h.frequency_bounds hQ hyH.2.2.1 hr hyH.2.2.2 hκ20 hΩy hs⟩

/-! ### Step 1: bounds on `Ñ` and `H` near `x` -/

/-- `Ñ_y(20r) ≤ K(n, N₊)` for `y ∈ B̄_r(x)` (Lemma 4.6 at centre `x`, radius `50r`). -/
theorem modFrequencyN_twenty_le {y : Rn n} (hy : y ∈ closedBall x r) :
    modFrequencyN (weissKappa L c C') Q u χ y (20 * r) ≤ modFrequencyNChangeConst n Np := by
  rw [mem_closedBall] at hy
  refine h.modFrequencyN_change_of_point_le hQ hx.2.2.1 (by positivity) hΩ ?_ hκ hN ?_
    (by positivity) (by linarith)
  · exact h.modMonotonicityM_nonneg hQ hx.2.2.1 hr hx.2.2.2 hκ hΩ ⟨by linarith, by linarith⟩
  · rw [mem_ball]; linarith

/-- `H_y(20r) ≤ C_H H_{x₀}(10r)` for `y, x₀ ∈ B̄_r(x)`: the upper bound of Lemma 4.6 at centre
`x`, radius `32r`; Lemma 4.3 on `[16r, 32r]`; the lower bound of Lemma 4.6 at centre `x`,
radius `16r`. -/
theorem heightH_twenty_le {y x₀ : Rn n} (hy : y ∈ closedBall x r)
    (hx₀ : x₀ ∈ closedBall x r) :
    heightH u y (20 * r) ≤ l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) := by
  rw [mem_closedBall] at hy hx₀
  have hmono := h.monotoneOn_modFrequencyN hQ hx.2.2.1 hr hx.2.2.2 hκ hΩ
  have hN32 : modFrequencyN (weissKappa L c C') Q u χ x (32 * r) ≤ Np :=
    (hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)).trans hN
  have hN16 : modFrequencyN (weissKappa L c C') Q u χ x (16 * r) ≤ Np :=
    (hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)).trans hN
  have hΩ32 : closedBall x (32 * r) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hΩ
  have hΩ16 : closedBall x (16 * r) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hΩ
  have hZ : ∀ s ∈ Icc r (50 * r), 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x s :=
    fun s hs => h.modMonotonicityM_nonneg hQ hx.2.2.1 hr hx.2.2.2 hκ hΩ hs
  have h1 := h.heightH_change_of_point_le hQ (y := y) (by positivity : (0 : ℝ) < 32 * r) hΩ32
    (by rw [mem_ball]; linarith)
  rw [show 5 / 8 * (32 * r) = 20 * r by ring] at h1
  have h2 := (h.heightH_doubling hQ hx.2.2.1 (t := 16 * r) (r := 32 * r) (by positivity)
    (by linarith) (by linarith) (hZ _ ⟨by linarith, by linarith⟩)
    (weissKappa_mul_le hQ hκ hx (by linarith)) hΩ32
    (Np := max Np 1 + 1) (by linarith [le_max_right Np 1])
    (hN32.trans (by linarith [le_max_left Np 1])) ⟨le_rfl, by linarith⟩).2
  have h3 := h.heightH_le_change_of_point hQ hx.2.2.1 (r := 16 * r) (y := x₀) (by positivity)
    hΩ16 (hZ _ ⟨by linarith, by linarith⟩) (weissKappa_mul_le hQ hκ hx (by linarith)) hN16
    (by rw [mem_ball]; linarith)
  rw [show 5 / 8 * (16 * r) = 10 * r by ring] at h3
  have hc := heightHChangeConst_pos n
  have hd := Abstract.RadialData.doublingConst_pos (max Np 1 + 1)
  calc heightH u y (20 * r) ≤ heightHChangeConst n * heightH u x (32 * r) := h1
    _ ≤ heightHChangeConst n * (Abstract.RadialData.doublingConst (max Np 1 + 1) *
          heightH u x (16 * r)) := mul_le_mul_of_nonneg_left h2 hc.le
    _ ≤ heightHChangeConst n * (Abstract.RadialData.doublingConst (max Np 1 + 1) *
          (heightHChangeConst' n Np * heightH u x₀ (10 * r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hd.le) hc.le
    _ = l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) := by
        unfold l2SubspaceHeightConst; ring

/-! ### Step 4: the estimate (6.23) -/

/-- The annulus estimate at a point `y ∈ B̄_r(x) ∩ Σ^H_{Q,r}`, with degree `Ñ_y(2r)`:
`∫_{B_{20r}(y)∖B_{2r}(y)} (∇u·(z−y) − Ñ_y(2r) u)² ≤
(20r)^{n+2} H_y(20r) (4 + 4K) (Ñ_y(20r) − Ñ_y(r))`. The error term of order `κ⁴ r⁴` of the
annulus estimate is absorbed by the growth `Ñ_y(20r) − Ñ_y(r) ≥ κ² (400 − 1) r² / 8`. -/
theorem integral_annulus_le_of_mem {y : Rn n} (hy : y ∈ closedBall x r)
    (hyH : y ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r) :
    ∫ z in ball y (20 * r) \ ball y (2 * r),
        (⟪gradient u z, z - y⟫ - modFrequencyN (weissKappa L c C') Q u χ y (2 * r) * u z) ^ 2 ≤
      (20 * r) ^ (n + 2) * heightH u y (20 * r) * (4 + 4 * modFrequencyNChangeConst n Np) *
        (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
          modFrequencyN (weissKappa L c C') Q u χ y r) := by
  set κ := weissKappa L c C' with hκdef
  set K := modFrequencyNChangeConst n Np with hKdef
  have hk := hQ.weissKappa_nonneg hx.1
  have hK2 : 2 ≤ K := two_le_modFrequencyNChangeConst n Np
  obtain ⟨hΩy, hmono, hfacts⟩ := h.frequency_facts hQ hr hκ hΩ hx hy hyH
  have hκ20 : κ * (20 * r) ≤ 1 / 2 := weissKappa_mul_le hQ hκ hx (by linarith)
  set N1 := modFrequencyN κ Q u χ y r
  set N2 := modFrequencyN κ Q u χ y (2 * r)
  set N20 := modFrequencyN κ Q u χ y (20 * r)
  have hle1 : N1 ≤ N2 := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hle2 : N2 ≤ N20 := hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hN2 : 1 ≤ N2 := (hfacts _ ⟨by linarith, by linarith⟩).2.2.2
  have hN20 : N20 ≤ K := h.modFrequencyN_twenty_le hQ hr hκ hΩ hx hN hy
  have hgrowth : κ ^ 2 * ((20 * r) ^ 2 - r ^ 2) / 8 ≤ N20 - N1 :=
    h.sq_mul_sub_sq_le_modFrequencyN_sub hQ hyH.2.2.1 hr hyH.2.2.2 hκ20 hΩy
      ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hkr := weissKappa_sq_mul_sq_le hQ hr hκ hx
  set δ := N20 - N1 with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have key := h.integral_annulus_sq_inner_gradient_sub_le hQ hyH.2.2.1 (t := r) (s₁ := 2 * r)
    (s₂ := 20 * r) hr (by linarith) (by linarith) hyH.2.2.2 hκ20 hΩy N2
  have hE : Real.exp (κ ^ 2 * (20 * r) ^ 2 / 8) ≤ 2 :=
    (exp_sq_mul_sq_div_eight_le hk (by positivity) hκ20).trans exp_one_div_thirtyTwo_le_two
  have hH : 0 < heightH u y (20 * r) := (hfacts _ ⟨by linarith, le_rfl⟩).1
  have hP : 0 ≤ (20 * r) ^ (n + 2) * heightH u y (20 * r) := by positivity
  -- the two terms of the maximum
  have hm1 : (N20 - N2) ^ 2 ≤ K * δ := by
    have h1 : 0 ≤ N20 - N2 := by linarith
    have h2 : N20 - N2 ≤ K := by linarith
    have h3 : N20 - N2 ≤ δ := by linarith
    calc (N20 - N2) ^ 2 = (N20 - N2) * (N20 - N2) := by ring
      _ ≤ K * δ := mul_le_mul h2 h3 h1 (by linarith)
  have hm2 : (N2 - κ ^ 2 * (20 * r) ^ 2 / 2 - N2) ^ 2 ≤ K * δ := by
    have e : (N2 - κ ^ 2 * (20 * r) ^ 2 / 2 - N2) ^ 2 =
        40000 * (κ ^ 2 * r ^ 2) * (κ ^ 2 * r ^ 2) := by
      ring
    have hk2 : 0 ≤ κ ^ 2 * r ^ 2 := by positivity
    have h1 : 40000 * (κ ^ 2 * r ^ 2) * (κ ^ 2 * r ^ 2) ≤ 4 * (κ ^ 2 * r ^ 2) := by nlinarith
    have h2 : 4 * (κ ^ 2 * r ^ 2) ≤ δ := by nlinarith
    have h3 : δ ≤ K * δ := by nlinarith
    rw [e]
    linarith
  have hmax : max ((N20 - N2) ^ 2) ((N2 - κ ^ 2 * (20 * r) ^ 2 / 2 - N2) ^ 2) ≤ K * δ :=
    max_le hm1 hm2
  have hE0 : 0 ≤ Real.exp (κ ^ 2 * (20 * r) ^ 2 / 8) := (Real.exp_pos _).le
  have hsum : 2 * (N20 - N2) + 2 * max ((N20 - N2) ^ 2)
      ((N2 - κ ^ 2 * (20 * r) ^ 2 / 2 - N2) ^ 2) ≤ 2 * δ + 2 * (K * δ) := by linarith
  have hsum0 : 0 ≤ 2 * (N20 - N2) + 2 * max ((N20 - N2) ^ 2)
      ((N2 - κ ^ 2 * (20 * r) ^ 2 / 2 - N2) ^ 2) := by
    have := le_max_left ((N20 - N2) ^ 2) ((N2 - κ ^ 2 * (20 * r) ^ 2 / 2 - N2) ^ 2)
    nlinarith [sq_nonneg (N20 - N2)]
  refine key.trans ?_
  calc Real.exp (κ ^ 2 * (20 * r) ^ 2 / 8) * ((20 * r) ^ (n + 2) * heightH u y (20 * r)) *
        (2 * (N20 - N2) + 2 * max ((N20 - N2) ^ 2) ((N2 - κ ^ 2 * (20 * r) ^ 2 / 2 - N2) ^ 2))
      ≤ 2 * ((20 * r) ^ (n + 2) * heightH u y (20 * r)) * (2 * δ + 2 * (K * δ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hE hP) hsum hsum0 (by positivity)
    _ = (20 * r) ^ (n + 2) * heightH u y (20 * r) * (4 + 4 * K) * δ := by ring

/-- **The estimate (6.23) with a Lipschitz coefficient**, at scale `r`: if
`x₀ ∈ B̄_r(x) ∩ Σ^H_{Q,r}`, `y ∈ B_r(x) ∩ Σ^H_{Q,r}` and `f(x₀) ≤ f(y)`, where
`f = Ñ(20r) − Ñ(r)`, then
`∫_{B_{18r}(x₀)∖B_{4r}(x₀)} ⟪∇u, y − x₀⟫² ≤ C (20r)^{n+2} H_{x₀}(10r) f(y)`. -/
theorem integral_annulus_sq_inner_le {x₀ y : Rn n} (hx₀ : x₀ ∈ closedBall x r)
    (hx₀H : x₀ ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r) (hy : y ∈ ball x r)
    (hyH : y ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r)
    (hmin : modFrequencyN (weissKappa L c C') Q u χ x₀ (20 * r) -
        modFrequencyN (weissKappa L c C') Q u χ x₀ r ≤
      modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
        modFrequencyN (weissKappa L c C') Q u χ y r) :
    ∫ z in ball x₀ (18 * r) \ ball x₀ (4 * r), ⟪gradient u z, y - x₀⟫ ^ 2 ≤
      twoPointConst n (modFrequencyNChangeConst n Np) *
        ((20 * r) ^ (n + 2) * (4 + 4 * modFrequencyNChangeConst n Np) *
          l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) *
            (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
              modFrequencyN (weissKappa L c C') Q u χ y r)) := by
  set κ := weissKappa L c C' with hκdef
  set K := modFrequencyNChangeConst n Np with hKdef
  have hy' : y ∈ closedBall x r := ball_subset_closedBall hy
  obtain ⟨hΩ₀, hmono₀, hfacts₀⟩ := h.frequency_facts hQ hr hκ hΩ hx hx₀ hx₀H
  obtain ⟨hΩy, hmonoy, hfactsy⟩ := h.frequency_facts hQ hr hκ hΩ hx hy' hyH
  have hK1 : 0 ≤ 4 + 4 * K := by linarith [two_le_modFrequencyNChangeConst n Np]
  have hH10 : 0 ≤ heightH u x₀ (10 * r) := heightH_nonneg _ _ (by positivity)
  have hCH := l2SubspaceHeightConst_pos n Np
  have hP : 0 ≤ (20 * r) ^ (n + 2) := by positivity
  -- the two annulus estimates, with a common right-hand side
  have hδ : ∀ w ∈ closedBall x r, w ∈ sigmaHQr Ω Q u χ κ r →
      modFrequencyN κ Q u χ w (20 * r) - modFrequencyN κ Q u χ w r ≤
        modFrequencyN κ Q u χ y (20 * r) - modFrequencyN κ Q u χ y r →
      ∫ z in ball w (10 * (2 * r)) \ ball w (2 * r),
          (⟪gradient u z, z - w⟫ - modFrequencyN κ Q u χ w (2 * r) * u z) ^ 2 ≤
        (20 * r) ^ (n + 2) * (4 + 4 * K) * l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) *
          (modFrequencyN κ Q u χ y (20 * r) - modFrequencyN κ Q u χ y r) := by
    intro w hw hwH hfw
    obtain ⟨-, hmonow, -⟩ := h.frequency_facts hQ hr hκ hΩ hx hw hwH
    have hfw₀ : 0 ≤ modFrequencyN κ Q u χ w (20 * r) - modFrequencyN κ Q u χ w r :=
      sub_nonneg.2 (hmonow ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith))
    rw [show 10 * (2 * r) = 20 * r by ring]
    refine (h.integral_annulus_le_of_mem hQ hr hκ hΩ hx hN hw hwH).trans ?_
    have hHw := h.heightH_twenty_le hQ hr hκ hΩ hx hN hw hx₀
    calc (20 * r) ^ (n + 2) * heightH u w (20 * r) * (4 + 4 * K) *
          (modFrequencyN κ Q u χ w (20 * r) - modFrequencyN κ Q u χ w r)
        ≤ (20 * r) ^ (n + 2) * (l2SubspaceHeightConst n Np * heightH u x₀ (10 * r)) *
            (4 + 4 * K) * (modFrequencyN κ Q u χ y (20 * r) - modFrequencyN κ Q u χ y r) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHw hP) hK1) hfw
            hfw₀ (mul_nonneg (mul_nonneg hP (mul_nonneg hCH.le hH10)) hK1)
      _ = _ := by ring
  have H₀ := hδ x₀ hx₀ hx₀H hmin
  have Hy := hδ y hy' hyH le_rfl
  have hN₀ : modFrequencyN κ Q u χ x₀ (2 * r) ∈ Icc 1 K :=
    ⟨(hfacts₀ _ ⟨by linarith, by linarith⟩).2.2.2,
      (hmono₀ ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)).trans
        (h.modFrequencyN_twenty_le hQ hr hκ hΩ hx hN hx₀)⟩
  have hNy : modFrequencyN κ Q u χ y (2 * r) ∈ Icc 1 K :=
    ⟨(hfactsy _ ⟨by linarith, by linarith⟩).2.2.2,
      (hmonoy ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)).trans
        (h.modFrequencyN_twenty_le hQ hr hκ hΩ hx hN hy')⟩
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

/-- **The lower bound in the proof of Theorem 6.1 with a Lipschitz coefficient**: if
`x₀ ∈ B̄_r(x) ∩ Σ^H_{Q,r}` and `Ñ_{x₀}(20r) − Ñ_{x₀}(r) ≤ δ₀`, then
`∫_{B_{10r}(x₀)∖B_{5r}(x₀)} |∇u|² ≥ (10r)ⁿ H_{x₀}(10r) / 4`. -/
theorem le_integral_annulus_norm_gradient_sq {x₀ : Rn n} (hx₀ : x₀ ∈ closedBall x r)
    (hx₀H : x₀ ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r)
    (hsmall : modFrequencyN (weissKappa L c C') Q u χ x₀ (20 * r) -
      modFrequencyN (weissKappa L c C') Q u χ x₀ r ≤ l2SubspaceDeltaQ n Np) :
    (10 * r) ^ n * heightH u x₀ (10 * r) / 4 ≤
      ∫ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ‖gradient u z‖ ^ 2 := by
  set κ := weissKappa L c C' with hκdef
  set K := modFrequencyNChangeConst n Np with hKdef
  set Cd := Abstract.RadialData.doublingConst (K + 1) with hCd
  have hCd0 : 0 < Cd := Abstract.RadialData.doublingConst_pos _
  have hk := hQ.weissKappa_nonneg hx.1
  obtain ⟨hΩ₀, hmono, hfacts⟩ := h.frequency_facts hQ hr hκ hΩ hx hx₀ hx₀H
  have hκ20 : κ * (20 * r) ≤ 1 / 2 := weissKappa_mul_le hQ hκ hx (by linarith)
  have hkr := weissKappa_sq_mul_sq_le hQ hr hκ hx
  have hball : ∀ s, s ≤ 20 * r → ball x₀ s ⊆ Ω := fun s hs =>
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hs).trans hΩ₀)
  -- (4.11) in the form `I_s = sⁿ H(s) (N(s) + V(s))`
  have hI : ∀ s, 0 < s → s ≤ 20 * r → 0 < heightH u x₀ s →
      ∫ z in ball x₀ s, ‖gradient u z‖ ^ 2 =
        s ^ n * heightH u x₀ s * (weightedFrequencyN Q u χ x₀ s + weightedVolumeV Q u χ x₀ s) := by
    intro s hs hs20 hH
    rw [h.weightedFrequencyN_add_weightedVolumeV hQ (hball s hs20)]
    field_simp
  have hH5 := (hfacts (5 * r) ⟨by linarith, by linarith⟩).1
  have hH10 := (hfacts (10 * r) ⟨by linarith, by linarith⟩).1
  -- `H(5r) ≤ E H(10r)` with `E ≤ 101/100`
  set E := Real.exp (κ ^ 2 * ((10 * r) ^ 2 - (5 * r) ^ 2) / 8) with hEdef
  have hHle : heightH u x₀ (5 * r) ≤ E * heightH u x₀ (10 * r) :=
    h.heightH_le_exp_mul hQ hx₀H.2.2.1 hr hx₀H.2.2.2 hκ20 hΩ₀ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  have hE1 : 1 ≤ E := Real.one_le_exp (by
    have : 0 ≤ κ ^ 2 * r ^ 2 := by positivity
    nlinarith)
  have hE : E ≤ 101 / 100 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_one_div_eight_hundred_le
    nlinarith
  -- `N(5r) ≤ N(10r) + 1/200` and `N(10r) ≥ 799/800`
  have hÑ : modFrequencyN κ Q u χ x₀ (5 * r) ≤ modFrequencyN κ Q u χ x₀ (10 * r) :=
    hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hNle : weightedFrequencyN Q u χ x₀ (5 * r) ≤
      weightedFrequencyN Q u χ x₀ (10 * r) + 1 / 200 := by
    have h1 := weightedFrequencyN_le_modFrequencyN κ Q u χ x₀ (5 * r)
    have e : modFrequencyN κ Q u χ x₀ (10 * r) =
        weightedFrequencyN Q u χ x₀ (10 * r) + 50 * (κ ^ 2 * r ^ 2) := by
      rw [modFrequencyN]; ring
    linarith
  have hN10 : 799 / 800 ≤ weightedFrequencyN Q u χ x₀ (10 * r) := by
    have := (hfacts (10 * r) ⟨by linarith, by linarith⟩).2.2.1
    nlinarith
  have hN5 : 799 / 800 ≤ weightedFrequencyN Q u χ x₀ (5 * r) := by
    have := (hfacts (5 * r) ⟨by linarith, by linarith⟩).2.2.1
    nlinarith
  have hV5 : 0 ≤ weightedVolumeV Q u χ x₀ (5 * r) :=
    h.weightedVolumeV_nonneg (by positivity) (hball _ (by linarith))
  have hV10 : 0 ≤ weightedVolumeV Q u χ x₀ (10 * r) :=
    h.weightedVolumeV_nonneg (by positivity) (hball _ (by linarith))
  -- Lemma 4.5: `V(5r) ≤ 1/4`
  have hV5le : weightedVolumeV Q u χ x₀ (5 * r) ≤ 1 / 4 := by
    have hδ₀ := l2SubspaceDeltaQ_pos n Np
    have hK : modFrequencyN κ Q u χ x₀ (20 * r) < K + 1 := by
      linarith [h.modFrequencyN_twenty_le hQ hr hκ hΩ hx hN hx₀]
    have hdrop : modFrequencyN κ Q u χ x₀ (20 * r) - modFrequencyN κ Q u χ x₀ (5 * r) <
        2 * l2SubspaceDeltaQ n Np := by
      have := hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith :
        r ≤ 5 * r)
      linarith
    have hZ5 := (hfacts (5 * r) ⟨by linarith, by linarith⟩).2.1
    have hV := h.weightedVolumeV_le_sqrt hQ hx₀H.2.2.1 (t := 5 * r) (r := 20 * r)
      (by positivity) (by linarith) hZ5 hκ20 hΩ₀ hK hdrop
    have hsq : √(3 * (2 * l2SubspaceDeltaQ n Np)) = 1 / (4 * 2 ^ n * Cd) := by
      rw [show 3 * (2 * l2SubspaceDeltaQ n Np) = (1 / (4 * 2 ^ n * Cd)) ^ 2 by
        rw [l2SubspaceDeltaQ, ← hKdef, ← hCd,
          show (4 : ℝ) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        field_simp
        ring]
      exact Real.sqrt_sq (by positivity)
    rw [hsq] at hV
    calc weightedVolumeV Q u χ x₀ (5 * r) ≤ 2 ^ n * Cd * (1 / (4 * 2 ^ n * Cd)) := hV
      _ = 1 / 4 := by field_simp
  -- the two integrals
  have hI5 := hI (5 * r) (by positivity) (by linarith) hH5
  have hI10 := hI (10 * r) (by positivity) (by linarith) hH10
  have hdiff : ∫ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ‖gradient u z‖ ^ 2 =
      (∫ z in ball x₀ (10 * r), ‖gradient u z‖ ^ 2) -
        ∫ z in ball x₀ (5 * r), ‖gradient u z‖ ^ 2 :=
    setIntegral_sdiff measurableSet_ball
      (h.integrableOn_norm_gradient_sq hQ (hball _ (by linarith)))
      (ball_subset_ball (by linarith))
  rw [hdiff, hI5, hI10]
  -- arithmetic, with `T = (10r)ⁿ`, `b = 2⁻ⁿ` and `p = b E`
  set N10 := weightedFrequencyN Q u χ x₀ (10 * r)
  set N5 := weightedFrequencyN Q u χ x₀ (5 * r)
  set V5 := weightedVolumeV Q u χ x₀ (5 * r)
  set V10 := weightedVolumeV Q u χ x₀ (10 * r)
  set H10 := heightH u x₀ (10 * r)
  set H5 := heightH u x₀ (5 * r)
  have hb0 : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  have hb2 : ((1 : ℝ) / 2) ^ n ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (NeZero.ne n)
  have h5 : (5 * r) ^ n = (1 / 2) ^ n * (10 * r) ^ n := by
    rw [← mul_pow]; ring_nf
  have hT0 : 0 ≤ (10 * r) ^ n := by positivity
  set T := (10 * r) ^ n
  have hQ0 : 0 ≤ T * H10 := mul_nonneg hT0 hH10.le
  set p := (1 / 2) ^ n * E with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 101 / 200 := by
    calc p ≤ 1 / 2 * (101 / 100) := mul_le_mul hb2 hE (by linarith) (by norm_num)
      _ = 101 / 200 := by norm_num
  have hup : (5 * r) ^ n * H5 * (N5 + V5) ≤ p * (T * H10) * (N10 + 1 / 200 + 1 / 4) := by
    rw [h5]
    have h1 : (1 / 2) ^ n * T * H5 ≤ (1 / 2) ^ n * T * (E * H10) :=
      mul_le_mul_of_nonneg_left hHle (mul_nonneg hb0 hT0)
    have h2 : N5 + V5 ≤ N10 + 1 / 200 + 1 / 4 := by linarith
    calc (1 / 2) ^ n * T * H5 * (N5 + V5) ≤ (1 / 2) ^ n * T * (E * H10) *
          (N10 + 1 / 200 + 1 / 4) :=
          mul_le_mul h1 h2 (by linarith) (mul_nonneg (mul_nonneg hb0 hT0)
            (mul_nonneg (by linarith) hH10.le))
      _ = p * (T * H10) * (N10 + 1 / 200 + 1 / 4) := by rw [hp]; ring
  have hlow : T * H10 * N10 ≤ T * H10 * (N10 + V10) := by
    have := mul_nonneg hQ0 hV10
    linarith
  have key : 1 / 4 ≤ N10 - p * (N10 + 1 / 200 + 1 / 4) := by
    have h1 : 799 / 800 * (1 - p) ≤ N10 * (1 - p) :=
      mul_le_mul_of_nonneg_right hN10 (by linarith)
    linarith
  have hkey := mul_le_mul_of_nonneg_left key hQ0
  linarith

/-! ### Step 5: the Fubini step -/

/-- **Steps 4–5 of the proof of Theorem 6.1 with a Lipschitz coefficient**: if `x₀` minimizes
`f = Ñ(20r) − Ñ(r)` over `B̄_r(x) ∩ Σ^H_{Q,r}` and `μ` is carried by `Σ^H_{Q,r}`, then with
`A = B_{10r}(x₀) ∖ B_{5r}(x₀)`,
`β²_μ(x, r) ∫_A |∇u|² ≤ C rⁿ H_{x₀}(10r) r^{1-n} ∫_{B_r(x)} f dμ`. -/
theorem jonesBetaSq_mul_lintegral_le_of_isMinOn (μ : Measure (Rn n)) [IsFiniteMeasure μ]
    (hμ : μ (sigmaHQr Ω Q u χ (weissKappa L c C') r)ᶜ = 0) {x₀ : Rn n}
    (hx₀ : x₀ ∈ closedBall x r) (hx₀H : x₀ ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r)
    (hmin : ∀ y ∈ closedBall x r ∩ sigmaHQr Ω Q u χ (weissKappa L c C') r,
      modFrequencyN (weissKappa L c C') Q u χ x₀ (20 * r) -
          modFrequencyN (weissKappa L c C') Q u χ x₀ r ≤
        modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
          modFrequencyN (weissKappa L c C') Q u χ y r) :
    jonesBetaSq μ x r *
        ∫⁻ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ENNReal.ofReal (‖gradient u z‖ ^ 2) ≤
      ENNReal.ofReal (l2SubspaceFubiniConstQ n Np * r ^ n * heightH u x₀ (10 * r)) *
        (∫⁻ y in ball x r, ENNReal.ofReal (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
          modFrequencyN (weissKappa L c C') Q u χ y r) ∂μ) /
          ENNReal.ofReal (r ^ (n - 1)) := by
  have hc0 : 0 ≤ l2SubspaceFubiniConstQ n Np * r ^ n * heightH u x₀ (10 * r) :=
    mul_nonneg (mul_nonneg (l2SubspaceFubiniConstQ_nonneg n Np) (by positivity))
      (heightH_nonneg _ _ (by positivity))
  refine (jonesBetaSq_mul_lintegral_le μ x r x₀ u).trans ?_
  gcongr ?_ / _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hae : ∀ᵐ y ∂(μ.restrict (ball x r)),
      y ∈ ball x r ∧ y ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r := by
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
      ?_).mono_set sdiff_subset
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
  have h63 := h.integral_annulus_sq_inner_le hQ hr hκ hΩ hx hN hx₀ hx₀H hy hyH
    (hmin y ⟨ball_subset_closedBall hy, hyH⟩)
  calc ∫⁻ z in ball x₀ (10 * r) \ ball x₀ (5 * r),
        ENNReal.ofReal (⟪gradient u z, y - x₀⟫ ^ 2 / r ^ 2)
      ≤ ∫⁻ z in ball x₀ (18 * r) \ ball x₀ (4 * r),
          ENNReal.ofReal (⟪gradient u z, y - x₀⟫ ^ 2 / r ^ 2) :=
        lintegral_mono_set (sdiff_subset_sdiff (ball_subset_ball (by linarith))
          (ball_subset_ball (by linarith)))
    _ = ENNReal.ofReal (∫ z in ball x₀ (18 * r) \ ball x₀ (4 * r),
          ⟪gradient u z, y - x₀⟫ ^ 2 / r ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hgint
          (ae_of_all _ fun z => div_nonneg (sq_nonneg _) (sq_nonneg _))).symm
    _ ≤ ENNReal.ofReal (l2SubspaceFubiniConstQ n Np * r ^ n * heightH u x₀ (10 * r) *
          (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
            modFrequencyN (weissKappa L c C') Q u χ y r)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_div]
        calc (∫ z in ball x₀ (18 * r) \ ball x₀ (4 * r), ⟪gradient u z, y - x₀⟫ ^ 2) / r ^ 2
            ≤ (twoPointConst n (modFrequencyNChangeConst n Np) *
                ((20 * r) ^ (n + 2) * (4 + 4 * modFrequencyNChangeConst n Np) *
                  l2SubspaceHeightConst n Np * heightH u x₀ (10 * r) *
                    (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
                      modFrequencyN (weissKappa L c C') Q u χ y r))) / r ^ 2 := by
              gcongr
          _ = _ := by
              rw [l2SubspaceFubiniConstQ, mul_pow]
              field_simp
              ring
    _ = _ := ENNReal.ofReal_mul hc0

end Setting

end IsVariationalSolutionQ

/-! ### Theorem 6.1 -/

/-- **Theorem 6.1 with a Lipschitz coefficient.** There is `C = C(N₊, n)` such that for every
variational solution `(u, χ)` for a coefficient `Q` with `QBounds Ω Q L c C'` on
`Ω ⊇ B̄_{50r}(x)` with `50 κ r ≤ 1/2` (`κ = weissKappa L c C'`), every finite measure `μ`
carried by `Σ^H_{Q,r}`, and every `x ∈ Σ^H_{Q,r}` with `Ñ_x(u; 50r) ≤ N₊`,
`β²_μ(x, r) ≤ C r^{1-n} ∫_{B_r(x)} (Ñ_y(u; 20r) − Ñ_y(u; r)) dμ(y)`.
The constant is `l2SubspaceConstQ n N₊`. -/
theorem jonesBetaSqQ_le (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ CJ : ℝ, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ) (x : Rn n)
      (r : ℝ) (μ : Measure (Rn n)), QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C Q u χ →
      0 < r → weissKappa L c C' * (50 * r) ≤ 1 / 2 → closedBall x (50 * r) ⊆ Ω →
      IsFiniteMeasure μ → μ (sigmaHQr Ω Q u χ (weissKappa L c C') r)ᶜ = 0 →
      x ∈ sigmaHQr Ω Q u χ (weissKappa L c C') r →
      modFrequencyN (weissKappa L c C') Q u χ x (50 * r) ≤ Np →
      jonesBetaSq μ x r ≤ ENNReal.ofReal (CJ / r ^ (n - 1)) *
        ∫⁻ y in ball x r, ENNReal.ofReal (modFrequencyN (weissKappa L c C') Q u χ y (20 * r) -
          modFrequencyN (weissKappa L c C') Q u χ y r) ∂μ := by
  refine ⟨l2SubspaceConstQ n Np, fun Ω C Q u χ L c C' x r μ hQ h hr hκ hΩ hμfin hμ hx hN => ?_⟩
  have := hμfin
  set κ := weissKappa L c C' with hκdef
  set S := closedBall x r ∩ sigmaHQr Ω Q u χ κ r with hS
  have hSsub : ∀ y ∈ S, closedBall y (20 * r) ⊆ Ω := fun y hy =>
    closedBall_subset_of_dist_le (mem_closedBall.1 hy.1) (by linarith) hΩ
  -- Step 2: the minimizer `x₀`
  have hSclosed : IsClosed S := by
    refine isClosed_of_closure_subset fun z hz => ?_
    have hz1 : z ∈ closedBall x r := closure_minimal inter_subset_left isClosed_closedBall hz
    have hz2 : z ∈ closure (sigmaHQr Ω Q u χ κ r) := closure_mono inter_subset_right hz
    exact ⟨hz1, h.closure_sigmaHQr_inter_subset hQ κ hr
      ⟨hz2, closedBall_subset_of_dist_le (mem_closedBall.1 hz1) (by linarith) hΩ⟩⟩
  have hScpt : IsCompact S :=
    (isCompact_closedBall x r).of_isClosed_subset hSclosed inter_subset_left
  have hpos : ∀ s, r ≤ s → s ≤ 20 * r → ∀ y ∈ S,
      closedBall y s ⊆ Ω ∧ 0 < heightH u y s := fun s hrs hs y hy => by
    have hΩs := (closedBall_subset_closedBall hs).trans (hSsub y hy)
    exact ⟨hΩs, h.heightH_pos hQ hy.2.2.2.1 (hr.trans_le hrs) hΩs⟩
  have hfcont : ContinuousOn
      (fun y => modFrequencyN κ Q u χ y (20 * r) - modFrequencyN κ Q u χ y r) S :=
    ((h.continuousOn_modFrequencyN hQ κ (by positivity : (0 : ℝ) < 20 * r)).mono
      fun y hy => hpos _ (by linarith) le_rfl y hy).sub
      ((h.continuousOn_modFrequencyN hQ κ hr).mono fun y hy => hpos r le_rfl (by linarith) y hy)
  obtain ⟨x₀, hx₀S, hmin⟩ := hScpt.exists_isMinOn ⟨x, mem_closedBall_self hr.le, hx⟩ hfcont
  have hmin' : ∀ y ∈ S, modFrequencyN κ Q u χ x₀ (20 * r) - modFrequencyN κ Q u χ x₀ r ≤
      modFrequencyN κ Q u χ y (20 * r) - modFrequencyN κ Q u χ y r := fun y hy => hmin hy
  set I := ∫⁻ y in ball x r,
    ENNReal.ofReal (modFrequencyN κ Q u χ y (20 * r) - modFrequencyN κ Q u χ y r) ∂μ with hI
  suffices H : ∃ c ≤ l2SubspaceConstQ n Np,
      jonesBetaSq μ x r ≤ ENNReal.ofReal c * I / ENNReal.ofReal (r ^ (n - 1)) by
    obtain ⟨c, hc, H⟩ := H
    exact H.trans (ofReal_mul_div_le_ofReal_div_mul hc hr I)
  by_cases hsmall : modFrequencyN κ Q u χ x₀ (20 * r) - modFrequencyN κ Q u χ x₀ r ≤
      l2SubspaceDeltaQ n Np
  · -- Steps 4–6: the main case
    refine ⟨4 * l2SubspaceFubiniConstQ n Np / 10 ^ n, le_max_right _ _, ?_⟩
    have hlow := h.le_integral_annulus_norm_gradient_sq hQ hr hκ hΩ hx hN hx₀S.1 hx₀S.2 hsmall
    have hE := h.jonesBetaSq_mul_lintegral_le_of_isMinOn hQ hr hκ hΩ hx hN μ hμ hx₀S.1 hx₀S.2
      hmin'
    have hH := (hpos (10 * r) (by linarith) (by linarith) x₀ hx₀S).2
    have ha0 : 0 < (10 * r) ^ n * heightH u x₀ (10 * r) / 4 := by positivity
    have hA : ENNReal.ofReal ((10 * r) ^ n * heightH u x₀ (10 * r) / 4) ≤
        ∫⁻ z in ball x₀ (10 * r) \ ball x₀ (5 * r), ENNReal.ofReal (‖gradient u z‖ ^ 2) := by
      have hint : IntegrableOn (fun z => ‖gradient u z‖ ^ 2)
          (ball x₀ (10 * r) \ ball x₀ (5 * r)) :=
        (h.integrableOn_norm_gradient_sq hQ (ball_subset_closedBall.trans
          (hpos (10 * r) (by linarith) (by linarith) x₀ hx₀S).1)).mono_set sdiff_subset
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hlow
    have hc0 : 0 ≤ 4 * l2SubspaceFubiniConstQ n Np / 10 ^ n :=
      div_nonneg (mul_nonneg (by norm_num) (l2SubspaceFubiniConstQ_nonneg n Np)) (by positivity)
    have hceq : l2SubspaceFubiniConstQ n Np * r ^ n * heightH u x₀ (10 * r) =
        4 * l2SubspaceFubiniConstQ n Np / 10 ^ n *
          ((10 * r) ^ n * heightH u x₀ (10 * r) / 4) := by
      rw [mul_pow]; field_simp
    rw [hceq, ENNReal.ofReal_mul hc0] at hE
    have h2 : jonesBetaSq μ x r * ENNReal.ofReal ((10 * r) ^ n * heightH u x₀ (10 * r) / 4) ≤
        ENNReal.ofReal (4 * l2SubspaceFubiniConstQ n Np / 10 ^ n) * I /
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
    refine ⟨(l2SubspaceDeltaQ n Np)⁻¹, le_max_left _ _, ?_⟩
    have hδ := l2SubspaceDeltaQ_pos n Np
    refine (jonesBetaSq_le_measure_ball (NeZero.pos n) μ x r).trans ?_
    gcongr ?_ / _
    have hae : ∀ᵐ y ∂(μ.restrict (ball x r)), y ∈ ball x r ∧ y ∈ sigmaHQr Ω Q u χ κ r := by
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hμ)] with y hy1 hy2
      exact ⟨hy1, by simpa using hy2⟩
    have hIδ : ENNReal.ofReal (l2SubspaceDeltaQ n Np) * μ (ball x r) ≤ I := by
      rw [hI, ← setLIntegral_const]
      refine lintegral_mono_ae (hae.mono fun y hy => ENNReal.ofReal_le_ofReal ?_)
      exact hsmall.le.trans (hmin' y ⟨ball_subset_closedBall hy.1, hy.2⟩)
    calc μ (ball x r) = ENNReal.ofReal (l2SubspaceDeltaQ n Np)⁻¹ *
          (ENNReal.ofReal (l2SubspaceDeltaQ n Np) * μ (ball x r)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), inv_mul_cancel₀ hδ.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (l2SubspaceDeltaQ n Np)⁻¹ * I := by gcongr

end InnerVariational
