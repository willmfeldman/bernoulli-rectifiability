/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.RadialQ
public import InnerVariational.Frequency.AbstractError.Doubling
public import InnerVariational.Frequency.AbstractError.Pinching
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal
import InnerVariational.Basic.Polar
import InnerVariational.Basic.LipschitzFTC

/-!
# The frequency formula with a Lipschitz coefficient (Lemmas 4.1–4.5)

Section 4 of Kriventsov–Weiss for variational solutions `(u, χ)` with a Lipschitz coefficient
`Q` (`IsVariationalSolutionQ` with `QBounds Ω Q L c C'`). The calculus of one variable is
`Abstract.RadialDataErr` (`Frequency/AbstractError.lean` and the files next to it), and the
radial data with error of `(u, χ)` at `x` are `IsVariationalSolutionQ.radialDataErr`
(`Monotonicity/RadialQ.lean`), with `ω = Q(x)² |B_1|` and `κ = 2 C' L / c²`
(`weissKappa L c C'`).

## The quantities

With `W_Q(s) = ∫_{B_s(x)} Q² (1 − χ)` and the weighted energy
`D^w_x(s) = s^{-n} (∫_{B_s(x)} |∇u|² − W_Q(s)) + Q(x)² |B_1|` (`weightedEnergyD`):
* `weightedFrequencyN Q u χ x s = (D^w_x(s) − Q(x)² |B_1|) / H_x(s)`, the frequency `N`;
* `weightedVolumeV Q u χ x s = s^{-n} W_Q(s) / H_x(s)`, the volume term `V`;
* `modFrequencyN κ Q u χ x s = N + κ² s² / 2`, the modified frequency `Ñ`;
* `modMonotonicityM κ Q u χ x s = M^w_x(s) − Q(x)² |B_1| + (κ² s² / 8) H_x(s)`, the shifted Weiss
  energy `Z = H (N − 1 + κ² s² / 8)`.
These are the fields `frequencyN`, `volumeV`, `modN`, `modM` of the radial data with error.
For `Q ≡ 1` they are the quantities `frequencyN`, `volumeV` of the paper, and `κ = 0`.

## Main results

The hypothesis `M_x(u; t) ≥ |B_1|` of the constant-coefficient theory is replaced by
`Z_x(t) ≥ 0` together with `κ R ≤ 1/2` on the radius interval `[t, R]`.
* Positivity of `H` and monotonicity of spherical means: `monotoneOn_sq_mul_heightH`,
  `heightH_pos`.
* Lemma 4.1: `monotoneOn_modFrequencyN`, `one_le_modFrequencyN`,
  `one_sub_le_weightedFrequencyN` (`N ≥ 1 − κ² s² / 8`), `modMonotonicityM_nonneg` (`Z ≥ 0`
  propagates outwards), `heightH_le_exp_mul` (`H(s) ≤ e^{κ² (r² − s²) / 8} H(r)`).
* Lemma 4.3: `heightH_doubling`; Lemma 4.4: `weightedVolumeV_doubling`; Lemma 4.5:
  `weightedVolumeV_le_sqrt`.
* The growth of `Ñ`: `sq_mul_sub_sq_le_modFrequencyN_sub`, `κ² (s₂² − s₁²) / 8 ≤ Ñ(s₂) − Ñ(s₁)`.
* The integrated form of (4.13): `integral_frequency_sq_term_le`, and the annulus estimate
  `integral_annulus_sq_inner_gradient_sub_le`.

## Differences from the paper

The paper treats `Q ≡ 1`. For a Lipschitz coefficient, `N` is only almost monotone; the
statements are for `Ñ = N + κ² s² / 2`, which is monotone and `≥ 1`. As in the constant-coefficient
files, `V` carries the factor `s^{-n}` and `N = 0` where `H = 0`.

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

/-! ### Elementary facts about `H` -/

/-- `H_x(u; r) ≥ 0` for `r ≥ 0`. -/
theorem heightH_nonneg (u : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ heightH u x r :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hr _)) (sphereIntegral_nonneg hr fun _ _ => sq_nonneg _)

/-- `∫_{∂B_s(x)} u² = s^{n+1} H_x(u; s)` for `s ≠ 0`. -/
theorem sphereIntegral_sq_eq (u : Rn n → ℝ) (x : Rn n) {s : ℝ} (hs : s ≠ 0) :
    sphereIntegral (fun y => u y ^ 2) x s = s ^ (n + 1) * heightH u x s := by
  rw [heightH, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs), one_mul]

/-- `s^{n+1} = s^{n-1} s²` for `n ≥ 1`. -/
theorem pow_succ_eq_pow_pred_mul_sq [NeZero n] (s : ℝ) : s ^ (n + 1) = s ^ (n - 1) * s ^ 2 := by
  rw [← pow_add]
  congr 1
  have := NeZero.pos n
  omega

/-- The constant `8 (8/5)^{n+1}` of the upper bound of Lemma 4.6 on `H`
(`IsVariationalSolution.heightH_change_of_point_le`). -/
def heightHChangeConst (n : ℕ) : ℝ := 8 * (8 / 5) ^ (n + 1)

theorem heightHChangeConst_pos (n : ℕ) : 0 < heightHChangeConst n := by
  unfold heightHChangeConst; positivity

/-- The constant `8 · 4^{n+1} C(N₊')²`, `N₊' = max N₊ 1 + 1`, of the lower bound of Lemma 4.6 on
`H` (`IsVariationalSolution.heightH_le_change_of_point`). `C` is the constant of Lemma 4.3. -/
def heightHChangeConst' (n : ℕ) (Np : ℝ) : ℝ :=
  8 * 4 ^ (n + 1) * Abstract.RadialData.doublingConst (max Np 1 + 1) ^ 2

theorem heightHChangeConst'_pos (n : ℕ) (Np : ℝ) : 0 < heightHChangeConst' n Np := by
  unfold heightHChangeConst'
  have := Abstract.RadialData.doublingConst_pos (max Np 1 + 1)
  positivity

/-- A function that is a.e.-measurable on `B_R(x)` and bounded there is integrable there. -/
theorem integrableOn_ball_of_abs_le {f : Rn n → ℝ} {x : Rn n} {R : ℝ} (A : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (ball x R))) (hb : ∀ y ∈ ball x R, |f y| ≤ A) :
    IntegrableOn f (ball x R) :=
  IntegrableOn.of_bound measure_ball_lt_top hf A
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact hb y hy))

/-! ### The quantities -/

/-- The frequency with a Lipschitz coefficient,
`N_x(s) = (D^w_x(s) − Q(x)² |B_1|) / H_x(s)`, with `N = 0` where `H = 0`. -/
def weightedFrequencyN (Q u χ : Rn n → ℝ) (x : Rn n) (s : ℝ) : ℝ :=
  (weightedEnergyD Q u χ x s - Q x ^ 2 * unitBallVolume n) / heightH u x s

/-- The volume term with a Lipschitz coefficient, `V_x(s) = s^{-n} ∫_{B_s(x)} Q² (1 − χ) / H_x(s)`.
-/
def weightedVolumeV (Q u χ : Rn n → ℝ) (x : Rn n) (s : ℝ) : ℝ :=
  (s ^ n)⁻¹ * (∫ y in ball x s, Q y ^ 2 * (1 - χ y)) / heightH u x s

/-- The modified frequency `Ñ_x(s) = N_x(s) + κ² s² / 2`. -/
def modFrequencyN (κ : ℝ) (Q u χ : Rn n → ℝ) (x : Rn n) (s : ℝ) : ℝ :=
  weightedFrequencyN Q u χ x s + κ ^ 2 * s ^ 2 / 2

/-- The shifted Weiss energy `Z_x(s) = M^w_x(s) − Q(x)² |B_1| + (κ² s² / 8) H_x(s)`. -/
def modMonotonicityM (κ : ℝ) (Q u χ : Rn n → ℝ) (x : Rn n) (s : ℝ) : ℝ :=
  weightedMonotonicityM Q u χ x s - Q x ^ 2 * unitBallVolume n + κ ^ 2 * s ^ 2 / 8 * heightH u x s

theorem weightedFrequencyN_le_modFrequencyN (κ : ℝ) (Q u χ : Rn n → ℝ) (x : Rn n) (s : ℝ) :
    weightedFrequencyN Q u χ x s ≤ modFrequencyN κ Q u χ x s := by
  have : 0 ≤ κ ^ 2 * s ^ 2 / 2 := by positivity
  rw [modFrequencyN]
  linarith

/-- `Z = H (N − 1 + κ² s² / 8)` when `H ≠ 0`. -/
theorem modMonotonicityM_eq {κ : ℝ} {Q u χ : Rn n → ℝ} {x : Rn n} {s : ℝ}
    (hH : heightH u x s ≠ 0) : modMonotonicityM κ Q u χ x s =
      heightH u x s * (weightedFrequencyN Q u χ x s - 1 + κ ^ 2 * s ^ 2 / 8) := by
  rw [modMonotonicityM, weightedMonotonicityM, weightedFrequencyN, mul_add, mul_sub,
    mul_div_cancel₀ _ hH]
  ring

/-- `e^{κ² r² / 8} ≤ e^{1/32}` when `0 ≤ κ`, `0 ≤ r` and `κ r ≤ 1/2`. -/
theorem exp_sq_mul_sq_div_eight_le {κ r : ℝ} (hk : 0 ≤ κ) (hr : 0 ≤ r) (hκ : κ * r ≤ 1 / 2) :
    Real.exp (κ ^ 2 * r ^ 2 / 8) ≤ Real.exp (1 / 32) := by
  refine Real.exp_le_exp.2 ?_
  have h0 : 0 ≤ κ * r := mul_nonneg hk hr
  have : (κ * r) ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ h0 hκ 2
  nlinarith

/-- `κ² s² ≤ 1/4` when `0 ≤ κ`, `0 ≤ s` and `κ s ≤ 1/2`. -/
theorem sq_mul_sq_le_of_mul_le {κ s : ℝ} (hk : 0 ≤ κ) (hs : 0 ≤ s) (hκ : κ * s ≤ 1 / 2) :
    κ ^ 2 * s ^ 2 ≤ 1 / 4 := by
  have h0 : 0 ≤ κ * s := mul_nonneg hk hs
  have : (κ * s) ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ h0 hκ 2
  rw [mul_pow] at this
  linarith

/-- `e^{1/32} ≤ 2`. -/
theorem exp_one_div_thirtyTwo_le_two : Real.exp (1 / 32) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 32) (by norm_num) (by norm_num)
  linarith

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-! ### The radial data -/

section RadialData

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ) {R : ℝ}
  (hR : ball x R ⊆ Ω) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R)

@[simp] theorem radialDataErr_frequencyN :
    (h.radialDataErr hQ hR ha hab hbR).frequencyN = weightedFrequencyN Q u χ x := rfl

@[simp] theorem radialDataErr_modN :
    (h.radialDataErr hQ hR ha hab hbR).modN = modFrequencyN (weissKappa L c C') Q u χ x := rfl

@[simp] theorem radialDataErr_modM :
    (h.radialDataErr hQ hR ha hab hbR).modM = modMonotonicityM (weissKappa L c C') Q u χ x :=
  rfl

theorem radialDataErr_volumeV {s : ℝ} (hs : 0 < s) :
    (h.radialDataErr hQ hR ha hab hbR).volumeV s = weightedVolumeV Q u χ x s := by
  simp only [Abstract.RadialDataErr.volumeV, radialDataErr, weightedVolumeV]
  congr 1
  have : s ^ n ≠ 0 := pow_ne_zero n hs.ne'
  field_simp
  ring

end RadialData

/-! ### Spherical means of `u²` and positivity of `H` -/

section Height

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
include hQ h

/-- **Spherical means of `u²` are nondecreasing**: `s ↦ s² H_x(u; s)` is nondecreasing on
`(0, R)` when `B_R(x) ⊆ Ω`. -/
theorem monotoneOn_sq_mul_heightH {R : ℝ} (hR : ball x R ⊆ Ω) :
    MonotoneOn (fun s => s ^ 2 * heightH u x s) (Ioo 0 R) := by
  intro s hs t ht hst
  exact (h.radialDataErr hQ hR hs.1 hst ht.2).monotoneOn_sq_mul_heightH
    (fun r _ => setIntegral_nonneg measurableSet_ball fun y _ => sq_nonneg _)
    ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

/-- `s ↦ s² H_x(u; s)` is nondecreasing on `(0, R]` when `B̄_R(x) ⊆ Ω`. -/
theorem monotoneOn_sq_mul_heightH_Ioc {R : ℝ} (hR : closedBall x R ⊆ Ω) :
    MonotoneOn (fun s => s ^ 2 * heightH u x s) (Ioc 0 R) := by
  intro s hs t ht hst
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.1.le.trans ht.2) hR
  exact h.monotoneOn_sq_mul_heightH hQ hR' ⟨hs.1, hs.2.trans_lt hRR'⟩ ⟨ht.1, ht.2.trans_lt hRR'⟩
    hst

/-- `s² H_x(s) ≤ t² H_x(t)` for `0 < s ≤ t` and `B̄_t(x) ⊆ Ω`. -/
theorem sq_mul_heightH_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : closedBall x t ⊆ Ω) :
    s ^ 2 * heightH u x s ≤ t ^ 2 * heightH u x t :=
  h.monotoneOn_sq_mul_heightH_Ioc hQ ht ⟨hs, hst⟩ ⟨hs.trans_le hst, le_rfl⟩ hst

/-- Positivity of `H` propagates outwards. -/
theorem heightH_pos_of_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : closedBall x t ⊆ Ω)
    (hH : 0 < heightH u x s) : 0 < heightH u x t := by
  have h1 : 0 < s ^ 2 * heightH u x s := by positivity
  exact pos_of_mul_pos_right (h1.trans_le (h.sq_mul_heightH_le hQ hs hst ht)) (sq_nonneg t)

omit [NeZero n] hQ in
theorem integrableOn_sq_of_closedBall {r : ℝ} (hΩ : closedBall x r ⊆ Ω) :
    IntegrableOn (fun y => u y ^ 2) (ball x r) :=
  (((h.continuousOn.mono hΩ).pow 2).integrableOn_compact (isCompact_closedBall x r)).mono_set
    ball_subset_closedBall

/-- **Positivity of `H`**: if `x ∈ closure {u > 0}`, `0 < r` and `B̄_r(x) ⊆ Ω`, then
`H_x(u; r) > 0`. -/
theorem heightH_pos (hx : x ∈ closure {y | 0 < u y}) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall x r ⊆ Ω) : 0 < heightH u x r := by
  by_contra hneg
  have hH0 : heightH u x r = 0 := le_antisymm (not_lt.1 hneg) (heightH_nonneg u x hr.le)
  have hS : ∀ s ∈ Ioc 0 r, sphereIntegral (fun y => u y ^ 2) x s = 0 := by
    intro s hs
    have hmono := h.sq_mul_heightH_le hQ hs.1 hs.2 hΩ
    rw [hH0, mul_zero] at hmono
    have hHs : heightH u x s = 0 := by
      have h0 := heightH_nonneg u x hs.1.le
      have hs2 : 0 < s ^ 2 := by have := hs.1; positivity
      nlinarith
    rw [sphereIntegral_sq_eq u x hs.1.ne', hHs, mul_zero]
  have hint := h.integrableOn_sq_of_closedBall hΩ
  have hball : ∫ y in ball x r, u y ^ 2 = 0 := by
    rw [integral_ball_eq hr.le hint, intervalIntegral.integral_of_le hr.le]
    exact setIntegral_eq_zero_of_forall_eq_zero hS
  have hae : (fun y => u y ^ 2) =ᵐ[volume.restrict (ball x r)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (.of_forall fun y => sq_nonneg (u y)) hint).1 hball
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_ball
    ((h.continuousOn.mono (ball_subset_closedBall.trans hΩ)).pow 2) continuousOn_const
  obtain ⟨z, hz, hzpos⟩ := mem_closure_iff_nhds.1 hx (ball x r) (ball_mem_nhds x hr)
  have := heq hz
  simp only [Pi.zero_apply] at this
  have : 0 < u z ^ 2 := by have := hzpos.out; positivity
  linarith

/-- `H_x(u; s) > 0` on `[t, R]` if `H_x(u; t) > 0` and `B̄_R(x) ⊆ Ω`. -/
theorem heightH_pos_of_mem_Icc {t R : ℝ} (ht : 0 < t) (hHt : 0 < heightH u x t)
    (hΩ : closedBall x R ⊆ Ω) {s : ℝ} (hs : s ∈ Icc t R) : 0 < heightH u x s :=
  h.heightH_pos_of_le hQ ht hs.1 ((closedBall_subset_closedBall hs.2).trans hΩ) hHt

end Height

/-! ### Identity (4.11) -/

section Identity

variable (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
include hQ h

/-- Identity (4.11): `N_x(s) + V_x(s) = s^{-n} ∫_{B_s(x)} |∇u|² / H_x(s)`. -/
theorem weightedFrequencyN_add_weightedVolumeV {s : ℝ} (hΩ : ball x s ⊆ Ω) :
    weightedFrequencyN Q u χ x s + weightedVolumeV Q u χ x s =
      (s ^ n)⁻¹ * (∫ y in ball x s, ‖gradient u y‖ ^ 2) / heightH u x s := by
  rw [weightedFrequencyN, weightedVolumeV, ← add_div, weightedEnergyD,
    h.integral_weightedEnergy_eq hQ hΩ]
  ring_nf

omit hQ in
/-- `V_x(s) ≥ 0`. -/
theorem weightedVolumeV_nonneg {s : ℝ} (hs : 0 ≤ s) (hΩ : ball x s ⊆ Ω) :
    0 ≤ weightedVolumeV Q u χ x s :=
  div_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hs _)) (h.integral_weight_nonneg hΩ))
    (heightH_nonneg u x hs)

end Identity

/-! ### Lemma 4.1 -/

section Frequency

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
include hQ h

/-- **Lemma 4.1 with a Lipschitz coefficient**, with the hypothesis `H_x(t) > 0` in place of
`x ∈ closure {u > 0}`: if `0 < t ≤ R`, `H_x(t) > 0`, `Z_x(t) ≥ 0`, `κ R ≤ 1/2` and
`B̄_R(x) ⊆ Ω`, then on `[t, R]`: `Ñ_x` is nondecreasing, `H_x > 0`, `Z_x ≥ 0`,
`N_x ≥ 1 − κ² s² / 8` and `Ñ_x ≥ 1`. -/
theorem monotoneOn_modFrequencyN_of_heightH_pos {t R : ℝ} (ht : 0 < t)
    (hHt : 0 < heightH u x t) (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (modFrequencyN (weissKappa L c C') Q u χ x) (Icc t R) ∧
      ∀ s ∈ Icc t R, 0 < heightH u x s ∧
        0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x s ∧
        1 - weissKappa L c C' ^ 2 * s ^ 2 / 8 ≤ weightedFrequencyN Q u χ x s ∧
        1 ≤ modFrequencyN (weissKappa L c C') Q u χ x s := by
  rcases lt_or_ge R t with hRt | htR
  · exact ⟨fun s hs _ _ _ => absurd (hs.1.trans hs.2) (not_le.2 hRt),
      fun s hs => absurd (hs.1.trans hs.2) (not_le.2 hRt)⟩
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htR) hΩ
  let d := h.radialDataErr hQ hR' ht htR hRR'
  have hH : ∀ s ∈ Icc t R, 0 < d.heightH s := fun s hs =>
    h.heightH_pos_of_mem_Icc hQ ht hHt hΩ hs
  exact ⟨d.monotoneOn_modN hH hZ hκ, fun s hs => ⟨hH s hs, d.modM_nonneg hH hκ hZ hs,
    d.one_sub_le_frequencyN hH hZ hκ hs, d.one_le_modN hH hZ hκ hs⟩⟩

/-- **Lemma 4.1 with a Lipschitz coefficient**: if `x ∈ closure {u > 0}`, `0 < t`,
`Z_x(t) ≥ 0`, `κ R ≤ 1/2` and `B̄_R(x) ⊆ Ω`, then `Ñ_x` is nondecreasing on `[t, R]`. -/
theorem monotoneOn_modFrequencyN (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (modFrequencyN (weissKappa L c C') Q u χ x) (Icc t R) := by
  rcases lt_or_ge R t with hRt | htR
  · exact fun s hs _ _ _ => absurd (hs.1.trans hs.2) (not_le.2 hRt)
  exact (h.monotoneOn_modFrequencyN_of_heightH_pos hQ ht
    (h.heightH_pos hQ hx ht ((closedBall_subset_closedBall htR).trans hΩ)) hZ hκ hΩ).1

/-- Under the hypotheses of `monotoneOn_modFrequencyN`, for `s ∈ [t, R]`: `H_x(s) > 0`,
`Z_x(s) ≥ 0`, `N_x(s) ≥ 1 − κ² s² / 8` and `Ñ_x(s) ≥ 1`. -/
theorem frequency_bounds (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) {s : ℝ}
    (hs : s ∈ Icc t R) : 0 < heightH u x s ∧
      0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x s ∧
      1 - weissKappa L c C' ^ 2 * s ^ 2 / 8 ≤ weightedFrequencyN Q u χ x s ∧
      1 ≤ modFrequencyN (weissKappa L c C') Q u χ x s :=
  (h.monotoneOn_modFrequencyN_of_heightH_pos hQ ht
    (h.heightH_pos hQ hx ht ((closedBall_subset_closedBall (hs.1.trans hs.2)).trans hΩ)) hZ hκ
    hΩ).2 s hs

/-- `Ñ_x(s) ≥ 1` on `[t, R]` (Lemma 4.1). -/
theorem one_le_modFrequencyN (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) {s : ℝ}
    (hs : s ∈ Icc t R) : 1 ≤ modFrequencyN (weissKappa L c C') Q u χ x s :=
  (h.frequency_bounds hQ hx ht hZ hκ hΩ hs).2.2.2

/-- `N_x(s) ≥ 1 − κ² s² / 8` on `[t, R]` (Lemma 4.1). -/
theorem one_sub_le_weightedFrequencyN (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) {s : ℝ}
    (hs : s ∈ Icc t R) : 1 - weissKappa L c C' ^ 2 * s ^ 2 / 8 ≤ weightedFrequencyN Q u χ x s :=
  (h.frequency_bounds hQ hx ht hZ hκ hΩ hs).2.2.1

/-- `Z_x ≥ 0` propagates outwards: `Z_x(s) ≥ 0` on `[t, R]`. -/
theorem modMonotonicityM_nonneg (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) {s : ℝ}
    (hs : s ∈ Icc t R) : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x s :=
  (h.frequency_bounds hQ hx ht hZ hκ hΩ hs).2.1

/-- **The lower half of Lemma 4.3 with a Lipschitz coefficient**: for `t ≤ s ≤ r ≤ R`,
`H_x(s) ≤ e^{κ² (r² − s²) / 8} H_x(r)`. -/
theorem heightH_le_exp_mul (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) {s r : ℝ}
    (hs : s ∈ Icc t R) (hr : r ∈ Icc t R) (hsr : s ≤ r) :
    heightH u x s ≤ Real.exp (weissKappa L c C' ^ 2 * (r ^ 2 - s ^ 2) / 8) * heightH u x r := by
  have htR : t ≤ R := hs.1.trans hs.2
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htR) hΩ
  let d := h.radialDataErr hQ hR' ht htR hRR'
  have hH : ∀ s ∈ Icc t R, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hQ hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  exact d.heightH_le_exp_mul hH hZ hκ hs hr hsr

/-- **The modified frequency grows at least quadratically**: for `t ≤ s₁ ≤ s₂ ≤ R`,
`κ² (s₂² − s₁²) / 8 ≤ Ñ_x(s₂) − Ñ_x(s₁)`. -/
theorem sq_mul_sub_sq_le_modFrequencyN_sub (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ}
    (ht : 0 < t) (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * R ≤ 1 / 2) (hΩ : closedBall x R ⊆ Ω) {s₁ s₂ : ℝ}
    (hs₁ : s₁ ∈ Icc t R) (hs₂ : s₂ ∈ Icc t R) (h12 : s₁ ≤ s₂) :
    weissKappa L c C' ^ 2 * (s₂ ^ 2 - s₁ ^ 2) / 8 ≤
      modFrequencyN (weissKappa L c C') Q u χ x s₂ -
        modFrequencyN (weissKappa L c C') Q u χ x s₁ := by
  have htR : t ≤ R := hs₁.1.trans hs₁.2
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htR) hΩ
  let d := h.radialDataErr hQ hR' ht htR hRR'
  have hH : ∀ s ∈ Icc t R, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hQ hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  exact d.sq_mul_sub_sq_le_modN_sub hH hZ hκ hs₁ hs₂ h12

/-! ### Lemmas 4.3–4.5 -/

/-- **Lemma 4.3 with a Lipschitz coefficient**, for `t ≤ s ≤ r ≤ 2t`: if
`x ∈ closure {u > 0}`, `Z_x(t) ≥ 0`, `κ r ≤ 1/2`, `B̄_r(x) ⊆ Ω` and `Ñ_x(r) ≤ N₊` with
`N₊ > 1`, then `H_x(s) ≤ e^{κ² r² / 8} H_x(r)` and `H_x(r) ≤ C H_x(s)` with
`C = exp(2(N₊ − 1) + 4√(N₊ − 1))`. -/
theorem heightH_doubling (hx : x ∈ closure {y | 0 < u y}) {t r : ℝ} (ht : 0 < t) (htr : t ≤ r)
    (hr2 : r ≤ 2 * t) (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * r ≤ 1 / 2) (hΩ : closedBall x r ⊆ Ω) {Np : ℝ} (hNp : 1 < Np)
    (hN : modFrequencyN (weissKappa L c C') Q u χ x r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    heightH u x s ≤ Real.exp (weissKappa L c C' ^ 2 * r ^ 2 / 8) * heightH u x r ∧
      heightH u x r ≤ Abstract.RadialData.doublingConst Np * heightH u x s := by
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htr) hΩ
  let d := h.radialDataErr hQ hR' ht htr hRR'
  have hH : ∀ s ∈ Icc t r, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hQ hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  exact d.heightH_doubling le_rfl htr le_rfl hr2 hH hZ hκ hNp hN hs

/-- **Lemma 4.4 with a Lipschitz coefficient**, for `t ≤ s ≤ r ≤ 2t`: under the hypotheses of
`heightH_doubling`, `V_x(s) ≤ 2ⁿ C V_x(r)`. -/
theorem weightedVolumeV_doubling (hx : x ∈ closure {y | 0 < u y}) {t r : ℝ} (ht : 0 < t)
    (htr : t ≤ r) (hr2 : r ≤ 2 * t) (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * r ≤ 1 / 2) (hΩ : closedBall x r ⊆ Ω) {Np : ℝ} (hNp : 1 < Np)
    (hN : modFrequencyN (weissKappa L c C') Q u χ x r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    weightedVolumeV Q u χ x s ≤
      2 ^ n * Abstract.RadialData.doublingConst Np * weightedVolumeV Q u χ x r := by
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htr) hΩ
  let d := h.radialDataErr hQ hR' ht htr hRR'
  have hH : ∀ s ∈ Icc t r, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hQ hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  have := d.volumeV_doubling le_rfl htr le_rfl hr2 hH hZ hκ hNp hN hs
  rwa [h.radialDataErr_volumeV hQ hR' ht htr hRR' (ht.trans_le hs.1),
    h.radialDataErr_volumeV hQ hR' ht htr hRR' (ht.trans_le htr)] at this

/-- **Lemma 4.5 with a Lipschitz coefficient**: if `x ∈ closure {u > 0}`, `0 < t`, `2t ≤ r`,
`Z_x(t) ≥ 0`, `κ r ≤ 1/2`, `B̄_r(x) ⊆ Ω`, `Ñ_x(r) < N₊` and `Ñ_x(r) − Ñ_x(t) < δ`, then
`V_x(t) ≤ 2ⁿ C(N₊) √(3δ)`. -/
theorem weightedVolumeV_le_sqrt (hx : x ∈ closure {y | 0 < u y}) {t r : ℝ} (ht : 0 < t)
    (htr : 2 * t ≤ r) (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * r ≤ 1 / 2) (hΩ : closedBall x r ⊆ Ω) {Np δ : ℝ}
    (hN : modFrequencyN (weissKappa L c C') Q u χ x r < Np)
    (hδ : modFrequencyN (weissKappa L c C') Q u χ x r -
      modFrequencyN (weissKappa L c C') Q u χ x t < δ) :
    weightedVolumeV Q u χ x t ≤ 2 ^ n * Abstract.RadialData.doublingConst Np * √(3 * δ) := by
  have htr' : t ≤ r := by linarith
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htr') hΩ
  let d := h.radialDataErr hQ hR' ht htr' hRR'
  have hH : ∀ s ∈ Icc t r, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hQ hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  have := d.volumeV_le_sqrt le_rfl htr le_rfl hH hZ hκ hN hδ
  rwa [h.radialDataErr_volumeV hQ hR' ht htr' hRR' ht] at this

end Frequency

/-! ### Integrated (4.13) and the annulus estimate -/

section Annulus

variable {R s : ℝ}

theorem sphereIntegral_inner_sub_mul_sq (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR : ball x R ⊆ Ω) (hs : 0 ≤ s) (hsR : s < R) (l : ℝ) :
    sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) x s =
      sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
        2 * l * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
        l ^ 2 * sphereIntegral (fun y => u y ^ 2) x s := by
  have e : (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) = fun y =>
      (⟪gradient u y, y - x⟫ ^ 2 - (2 * l) * (u y * ⟪gradient u y, y - x⟫)) + l ^ 2 * u y ^ 2 := by
    ext y; ring
  have hm : SphereIntegrable (fun y => (2 * l) * (u y * ⟪gradient u y, y - x⟫)) x s :=
    (h.sphereIntegrable_mix hR hs hsR).const_mul (2 * l)
  have hq : SphereIntegrable (fun y => l ^ 2 * u y ^ 2) x s :=
    (h.sphereIntegrable_u_sq hR hs hsR).const_mul (l ^ 2)
  have hd : SphereIntegrable
      (fun y => ⟪gradient u y, y - x⟫ ^ 2 - (2 * l) * (u y * ⟪gradient u y, y - x⟫)) x s :=
    (h.sphereIntegrable_inner_sq hR hs hsR).sub hm
  rw [e, sphereIntegral_add hd hq, sphereIntegral_sub (h.sphereIntegrable_inner_sq hR hs hsR) hm,
    sphereIntegral_const_mul, sphereIntegral_const_mul]

theorem sphereIntegrable_inner_sub_mul_sq (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR : ball x R ⊆ Ω) (hs : 0 ≤ s) (hsR : s < R) (l : ℝ) :
    SphereIntegrable (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) x s := by
  have e : (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) = fun y =>
      (⟪gradient u y, y - x⟫ ^ 2 - (2 * l) * (u y * ⟪gradient u y, y - x⟫)) + l ^ 2 * u y ^ 2 := by
    ext y; ring
  rw [e]
  exact ((h.sphereIntegrable_inner_sq hR hs hsR).sub
    ((h.sphereIntegrable_mix hR hs hsR).const_mul (2 * l))).add
    ((h.sphereIntegrable_u_sq hR hs hsR).const_mul (l ^ 2))

/-- The integrands `u ∇u·(y−x)`, `(∇u·(y−x))²` and `(∇u·(y−x) − l u)²` are integrable on
`B_R(x)` when `B̄_R(x) ⊆ Ω`. -/
theorem integrableOn_ball_inner_gradient (h : IsVariationalSolutionQ Ω C Q u χ)
    (hΩ : closedBall x R ⊆ Ω) :
    IntegrableOn (fun y => u y * ⟪gradient u y, y - x⟫) (ball x R) ∧
      IntegrableOn (fun y => ⟪gradient u y, y - x⟫ ^ 2) (ball x R) ∧
      ∀ l : ℝ, IntegrableOn (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) (ball x R) := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn
    (h.continuousOn.mono hΩ)
  have hu : AEStronglyMeasurable u (volume.restrict (ball x R)) :=
    (h.continuousOn.mono (ball_subset_closedBall.trans hΩ)).aestronglyMeasurable measurableSet_ball
  have hg : AEStronglyMeasurable (fun y => ⟪gradient u y, y - x⟫) (volume.restrict (ball x R)) :=
    ((measurable_gradient u).inner (measurable_id.sub_const x)).aestronglyMeasurable
  have hub : ∀ y ∈ ball x R, |u y| ≤ A := fun y hy => by
    rw [← Real.norm_eq_abs]; exact hA y (ball_subset_closedBall hy)
  have hgb : ∀ y ∈ ball x R, |⟪gradient u y, y - x⟫| ≤ C * R := fun y hy => by
    rw [← Real.norm_eq_abs]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul (h.norm_gradient_le (hΩ (ball_subset_closedBall hy))) (mem_ball.1 hy).le
      dist_nonneg C.2
  refine ⟨integrableOn_ball_of_abs_le (A * (C * R)) (hu.mul hg) fun y hy => ?_,
    integrableOn_ball_of_abs_le ((C * R) ^ 2) (hg.pow 2) fun y hy => ?_, fun l =>
      integrableOn_ball_of_abs_le ((C * R + |l| * A) ^ 2) ((hg.sub (hu.const_mul l)).pow 2)
        fun y hy => ?_⟩
  · rw [abs_mul]
    exact mul_le_mul (hub y hy) (hgb y hy) (abs_nonneg _) ((abs_nonneg _).trans (hub y hy))
  · rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hgb y hy) 2
  · rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hgb y hy) ?_)) 2
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hub y hy) (abs_nonneg l)

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
include hQ h

/-- **Integrated form of (4.13) with a Lipschitz coefficient**: for `0 < t ≤ s₁ ≤ s₂`, if
`x ∈ closure {u > 0}`, `Z_x(t) ≥ 0`, `κ s₂ ≤ 1/2` and `B̄_{s₂}(x) ⊆ Ω`, then
`∫_{s₁}^{s₂} (1 / (H_x(s) s^{n+2})) ∫_{∂B_s(x)} (∇u·(y−x) − N_x(s) u)² ds ≤ Ñ_x(s₂) − Ñ_x(s₁)`. -/
theorem integral_frequency_sq_term_le (hx : x ∈ closure {y | 0 < u y}) {t s₁ s₂ : ℝ}
    (ht : 0 < t) (hts : t ≤ s₁) (hs : s₁ ≤ s₂)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * s₂ ≤ 1 / 2) (hΩ : closedBall x s₂ ⊆ Ω) :
    ∫ s in s₁..s₂, 1 / (heightH u x s * s ^ (n + 2)) *
        sphereIntegral (fun y => (⟪gradient u y, y - x⟫ -
          weightedFrequencyN Q u χ x s * u y) ^ 2) x s ≤
      modFrequencyN (weissKappa L c C') Q u χ x s₂ -
        modFrequencyN (weissKappa L c C') Q u χ x s₁ := by
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans (hts.trans hs)) hΩ
  let d := h.radialDataErr hQ hR' ht (hts.trans hs) hRR'
  have hH : ∀ s ∈ Icc t s₂, 0 < d.heightH s := fun s hs' =>
    h.heightH_pos hQ hx (ht.trans_le hs'.1) ((closedBall_subset_closedBall hs'.2).trans hΩ)
  refine AbsolutelyContinuousOnInterval.integral_le_sub_of_ae_le hs
    ((d.absolutelyContinuousOnInterval_modN hH).mono_Icc d.le ⟨hts, hs⟩ ⟨hts.trans hs, le_rfl⟩)
    (ae_mem_Ioo_imp_mono hts le_rfl (d.ae_hasDerivAt_deriv_modN hH)) ?_ ?_
  · refine .of_forall fun s hs' => ?_
    have hs0 : 0 < s := ht.trans_le (hts.trans hs'.1.le)
    have hHs := hH s ⟨hts.trans hs'.1.le, hs'.2.le⟩
    exact mul_nonneg (by positivity) (sphereIntegral_nonneg hs0.le fun y _ => sq_nonneg _)
  · filter_upwards [ae_mem_Ioo_imp_mono hts le_rfl
      (d.ae_frequency_sq_term_le_deriv_modN hH hZ hκ)] with s hs1 hs'
    refine le_of_eq_of_le ?_ (hs1 hs')
    have hs0 : 0 < s := ht.trans_le (hts.trans hs'.1.le)
    rw [h.sphereIntegral_inner_sub_mul_sq hR' hs0.le (hs'.2.trans hRR')]
    rfl

/-- **The annulus homogeneity estimate with a Lipschitz coefficient** (proofs of Theorems 6.1
and 6.3), for any degree `λ`: if `x ∈ closure {u > 0}`, `Z_x(t) ≥ 0`, `0 < t ≤ s₁ ≤ s₂`,
`κ s₂ ≤ 1/2` and `B̄_{s₂}(x) ⊆ Ω`, then with `E = e^{κ² s₂² / 8}`,
`∫_{B_{s₂}(x)∖B_{s₁}(x)} (∇u·(y−x) − λu)² ≤ E s₂^{n+2} H_x(s₂)
  (2 (Ñ_x(s₂) − Ñ_x(s₁)) + 2 max((Ñ_x(s₂) − λ)², (Ñ_x(s₁) − κ² s₂² / 2 − λ)²))`.

On `∂B_s(x)`, `(∇u·(y−x) − λu)² ≤ 2(∇u·(y−x) − N(s)u)² + 2(N(s) − λ)²u²`, and
`N(s) ∈ [Ñ(s₁) − κ² s₂² / 2, Ñ(s₂)]` since `Ñ` is nondecreasing and `N = Ñ − κ² s² / 2`. -/
theorem integral_annulus_sq_inner_gradient_sub_le (hx : x ∈ closure {y | 0 < u y})
    {t s₁ s₂ : ℝ} (ht : 0 < t) (hts : t ≤ s₁) (hs : s₁ ≤ s₂)
    (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ x t)
    (hκ : weissKappa L c C' * s₂ ≤ 1 / 2) (hΩ : closedBall x s₂ ⊆ Ω) (l : ℝ) :
    ∫ y in ball x s₂ \ ball x s₁, (⟪gradient u y, y - x⟫ - l * u y) ^ 2 ≤
      Real.exp (weissKappa L c C' ^ 2 * s₂ ^ 2 / 8) * (s₂ ^ (n + 2) * heightH u x s₂) *
        (2 * (modFrequencyN (weissKappa L c C') Q u χ x s₂ -
            modFrequencyN (weissKappa L c C') Q u χ x s₁) +
          2 * max ((modFrequencyN (weissKappa L c C') Q u χ x s₂ - l) ^ 2)
            ((modFrequencyN (weissKappa L c C') Q u χ x s₁ -
              weissKappa L c C' ^ 2 * s₂ ^ 2 / 2 - l) ^ 2)) := by
  set κ := weissKappa L c C' with hκdef
  have hs₁ : 0 < s₁ := ht.trans_le hts
  have hs₂ : 0 < s₂ := hs₁.trans_le hs
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen hs₂.le hΩ
  have hmonoN : MonotoneOn (modFrequencyN κ Q u χ x) (Icc t s₂) :=
    h.monotoneOn_modFrequencyN hQ hx ht hZ hκ hΩ
  set N := weightedFrequencyN Q u χ x with hN
  set Nt := modFrequencyN κ Q u χ x with hNt
  set H := heightH u x with hHdef
  set E := Real.exp (κ ^ 2 * s₂ ^ 2 / 8) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hHpos : ∀ s ∈ Icc t s₂, 0 < H s := fun s hs' =>
    (h.frequency_bounds hQ hx ht hZ hκ hΩ hs').1
  have hHle : ∀ s ∈ Icc s₁ s₂, H s ≤ E * H s₂ := by
    intro s hs'
    have h1 := h.heightH_le_exp_mul hQ hx ht hZ hκ hΩ ⟨hts.trans hs'.1, hs'.2⟩
      ⟨hts.trans hs, le_rfl⟩ hs'.2
    refine h1.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hHpos s₂
      ⟨hts.trans hs, le_rfl⟩).le)
    have : 0 ≤ κ ^ 2 * s ^ 2 := by positivity
    nlinarith
  set m := max ((Nt s₂ - l) ^ 2) ((Nt s₁ - κ ^ 2 * s₂ ^ 2 / 2 - l) ^ 2) with hm
  have hm0 : 0 ≤ m := (sq_nonneg _).trans (le_max_left _ _)
  obtain ⟨hIMix, hIRad, hIF⟩ := h.integrableOn_ball_inner_gradient hΩ
  have hISq := h.integrableOn_sq_of_closedBall hΩ
  have hsub : uIcc s₁ s₂ ⊆ uIcc 0 s₂ := by
    rw [uIcc_of_le hs, uIcc_of_le hs₂.le]; exact Icc_subset_Icc hs₁.le le_rfl
  have hIIF := (intervalIntegrable_sphereIntegral hs₂.le (hIF l)).mono_set hsub
  have hIIRad := (intervalIntegrable_sphereIntegral hs₂.le hIRad).mono_set hsub
  have hIIMix := (intervalIntegrable_sphereIntegral hs₂.le hIMix).mono_set hsub
  have hIISq := (intervalIntegrable_sphereIntegral hs₂.le hISq).mono_set hsub
  set F : ℝ → ℝ := fun s =>
    sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - N s * u y) ^ 2) x s with hF
  set S : ℝ → ℝ := fun s => sphereIntegral (fun y => u y ^ 2) x s with hS
  have hmem : ∀ s ∈ Icc s₁ s₂, 0 ≤ s ∧ s < R' := fun s hs' =>
    ⟨hs₁.le.trans hs'.1, hs'.2.trans_lt hRR'⟩
  have hFeq : ∀ s ∈ Icc s₁ s₂, F s =
      sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
        2 * N s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
        N s ^ 2 * sphereIntegral (fun y => u y ^ 2) x s :=
    fun s hs' => h.sphereIntegral_inner_sub_mul_sq hR' (hmem s hs').1 (hmem s hs').2 (N s)
  have hNc : ContinuousOn N (uIcc s₁ s₂) := by
    let d := h.radialDataErr hQ hR' ht (hts.trans hs) hRR'
    have hH' : ∀ s ∈ Icc t s₂, 0 < d.heightH s := hHpos
    obtain ⟨K, hK⟩ := d.exists_lipschitzOnWith_frequencyN hH'
    rw [uIcc_of_le hs]
    exact hK.continuousOn.mono (Icc_subset_Icc hts le_rfl)
  have hIIQ : IntervalIntegrable F volume s₁ s₂ := by
    have h1 : IntervalIntegrable (fun s =>
        sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
          2 * N s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
          N s ^ 2 * sphereIntegral (fun y => u y ^ 2) x s) volume s₁ s₂ := by
      have h2 := (hIIMix.continuousOn_mul hNc).const_mul 2
      have h3 := hIISq.continuousOn_mul (hNc.pow 2)
      refine ((hIIRad.sub h2).add h3).congr fun s _ => ?_
      ring
    refine h1.congr fun s hs' => (hFeq s ?_).symm
    rw [uIoc_of_le hs] at hs'
    exact Ioc_subset_Icc_self hs'
  -- pointwise bound on each sphere
  have hpt : ∀ s ∈ Icc s₁ s₂,
      sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) x s ≤
        2 * F s + 2 * m * S s := by
    intro s hs'
    obtain ⟨hs0, hsR⟩ := hmem s hs'
    have hN1 : Nt s₁ ≤ Nt s := hmonoN ⟨hts, hs⟩ ⟨hts.trans hs'.1, hs'.2⟩ hs'.1
    have hN2 : Nt s ≤ Nt s₂ := hmonoN ⟨hts.trans hs'.1, hs'.2⟩ ⟨hts.trans hs, le_rfl⟩ hs'.2
    have hNs1 : N s ≤ Nt s₂ := (weightedFrequencyN_le_modFrequencyN κ Q u χ x s).trans hN2
    have hNs2 : Nt s₁ - κ ^ 2 * s₂ ^ 2 / 2 ≤ N s := by
      have e : N s = Nt s - κ ^ 2 * s ^ 2 / 2 := by rw [hNt, modFrequencyN]; ring
      have : κ ^ 2 * s ^ 2 ≤ κ ^ 2 * s₂ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hs'.2 2) (sq_nonneg κ)
      linarith
    have hNs : (N s - l) ^ 2 ≤ m := by
      rcases le_total l (N s) with hl | hl
      · exact (pow_le_pow_left₀ (sub_nonneg.2 hl) (by linarith) 2).trans (le_max_left _ _)
      · have : (N s - l) ^ 2 ≤ (Nt s₁ - κ ^ 2 * s₂ ^ 2 / 2 - l) ^ 2 := by nlinarith
        exact this.trans (le_max_right _ _)
    have hI1 : SphereIntegrable (fun y => 2 * (⟪gradient u y, y - x⟫ - N s * u y) ^ 2) x s :=
      (h.sphereIntegrable_inner_sub_mul_sq hR' hs0 hsR (N s)).const_mul 2
    have hI2 : SphereIntegrable (fun y => 2 * m * u y ^ 2) x s :=
      (h.sphereIntegrable_u_sq hR' hs0 hsR).const_mul (2 * m)
    calc sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) x s
        ≤ sphereIntegral (fun y => 2 * (⟪gradient u y, y - x⟫ - N s * u y) ^ 2 +
            2 * m * u y ^ 2) x s := by
          refine sphereIntegral_mono hs0 (h.sphereIntegrable_inner_sub_mul_sq hR' hs0 hsR l)
            (hI1.add hI2) fun y _ => ?_
          have hq : (N s - l) ^ 2 * u y ^ 2 ≤ m * u y ^ 2 :=
            mul_le_mul_of_nonneg_right hNs (sq_nonneg _)
          nlinarith [sq_nonneg (⟪gradient u y, y - x⟫ - N s * u y - (N s - l) * u y)]
      _ = 2 * F s + 2 * m * S s := by
          rw [sphereIntegral_add hI1 hI2,
            sphereIntegral_const_mul, sphereIntegral_const_mul]
  -- the `F` term, from (4.13)
  have hH₂ : 0 < H s₂ := hHpos s₂ ⟨hts.trans hs, le_rfl⟩
  have hP : 0 < E * (s₂ ^ (n + 2) * H s₂) := by positivity
  have hQint : ∫ s in s₁..s₂, F s ≤ E * (s₂ ^ (n + 2) * H s₂) * (Nt s₂ - Nt s₁) := by
    let d := h.radialDataErr hQ hR' ht (hts.trans hs) hRR'
    have hH' : ∀ s ∈ Icc t s₂, 0 < d.heightH s := hHpos
    set c₀ := (E * (s₂ ^ (n + 2) * H s₂))⁻¹ with hc₀
    have hc₀0 : 0 < c₀ := inv_pos.2 hP
    have key : ∫ s in s₁..s₂, c₀ * F s ≤ Nt s₂ - Nt s₁ := by
      refine AbsolutelyContinuousOnInterval.integral_le_sub_of_ae_le hs
        ((d.absolutelyContinuousOnInterval_modN hH').mono_Icc d.le ⟨hts, hs⟩
          ⟨hts.trans hs, le_rfl⟩)
        (ae_mem_Ioo_imp_mono hts le_rfl (d.ae_hasDerivAt_deriv_modN hH')) ?_ ?_
      · refine .of_forall fun s hs' => mul_nonneg hc₀0.le ?_
        exact sphereIntegral_nonneg (hs₁.le.trans hs'.1.le) fun y _ => sq_nonneg _
      · filter_upwards [ae_mem_Ioo_imp_mono hts le_rfl
          (d.ae_frequency_sq_term_le_deriv_modN hH' hZ hκ)] with s hs1 hs'
        refine le_trans ?_ (hs1 hs')
        have hs'' : s ∈ Icc s₁ s₂ := Ioo_subset_Icc_self hs'
        have hs0 : 0 < s := hs₁.trans hs'.1
        have hHs : 0 < H s := hHpos s ⟨hts.trans hs''.1, hs''.2⟩
        have hF0 : 0 ≤ F s := sphereIntegral_nonneg hs0.le fun y _ => sq_nonneg _
        rw [show d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s =
          F s from (hFeq s hs'').symm]
        refine mul_le_mul_of_nonneg_right ?_ hF0
        rw [hc₀, one_div]
        refine inv_anti₀ (by positivity) ?_
        calc d.heightH s * s ^ (n + 2) = H s * s ^ (n + 2) := rfl
          _ ≤ (E * H s₂) * s₂ ^ (n + 2) :=
            mul_le_mul (hHle s hs'') (pow_le_pow_left₀ hs0.le hs''.2 _) (by positivity)
              (by positivity)
          _ = E * (s₂ ^ (n + 2) * H s₂) := by ring
    rw [intervalIntegral.integral_const_mul, hc₀, inv_mul_le_iff₀ hP] at key
    exact key
  -- the `u²` term
  have hSint : ∫ s in s₁..s₂, S s ≤ E * (s₂ ^ (n + 2) * H s₂) := by
    calc ∫ s in s₁..s₂, S s ≤ ∫ _ in s₁..s₂, s₂ ^ (n + 1) * (E * H s₂) := by
          refine intervalIntegral.integral_mono_on hs hIISq intervalIntegrable_const
            fun s hs' => ?_
          have hs0 : 0 < s := hs₁.trans_le hs'.1
          simp only [hS]
          rw [sphereIntegral_sq_eq u x hs0.ne']
          exact mul_le_mul (pow_le_pow_left₀ hs0.le hs'.2 _) (hHle s hs')
            (heightH_nonneg u x hs0.le) (by positivity)
      _ = (s₂ - s₁) * (s₂ ^ (n + 1) * (E * H s₂)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ s₂ * (s₂ ^ (n + 1) * (E * H s₂)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = E * (s₂ ^ (n + 2) * H s₂) := by ring
  -- combine
  rw [integral_ball_diff_ball hs₁.le hs (hIF l)]
  calc ∫ s in s₁..s₂, sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) x s
      ≤ ∫ s in s₁..s₂, (2 * F s + 2 * m * S s) :=
        intervalIntegral.integral_mono_on hs hIIF ((hIIQ.const_mul 2).add (hIISq.const_mul _)) hpt
    _ = 2 * (∫ s in s₁..s₂, F s) + 2 * m * ∫ s in s₁..s₂, S s := by
        rw [intervalIntegral.integral_add (hIIQ.const_mul 2) (hIISq.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * (E * (s₂ ^ (n + 2) * H s₂) * (Nt s₂ - Nt s₁)) +
          2 * m * (E * (s₂ ^ (n + 2) * H s₂)) :=
        add_le_add (mul_le_mul_of_nonneg_left hQint zero_le_two)
          (mul_le_mul_of_nonneg_left hSint (mul_nonneg zero_le_two hm0))
    _ = E * (s₂ ^ (n + 2) * H s₂) * (2 * (Nt s₂ - Nt s₁) + 2 * m) := by ring

end Annulus

end IsVariationalSolutionQ

/-! ### The coefficient `Q ≡ 1` -/

theorem weissKappa_zero (c C' : ℝ) : weissKappa 0 c C' = 0 := by
  simp [weissKappa]

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- For `Q ≡ 1`, the weighted energy is `D`: `D^w_x(s) = D_x(s)` for `s > 0`. -/
theorem weightedEnergyD_one (h : IsVariationalSolution Ω C u χ) {s : ℝ} (hs : 0 < s)
    (hΩ : ball x s ⊆ Ω) : weightedEnergyD (fun _ => 1) u χ x s = energyD u χ x s := by
  have hG := h.integrableOn_norm_gradient_sq hΩ
  have hχ := h.integrableOn_chi hΩ
  have h1 : IntegrableOn (fun _ : Rn n => (1 : ℝ)) (ball x s) :=
    integrableOn_const measure_ball_lt_top.ne
  have hone : (∫ y in ball x s, (1 : ℝ)) = s ^ n * unitBallVolume n := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, volume_ball_toReal x hs]
  have e : ∫ y in ball x s, (‖gradient u y‖ ^ 2 - (1 : ℝ) ^ 2 * (1 - χ y)) =
      (∫ y in ball x s, (‖gradient u y‖ ^ 2 + χ y)) - ∫ y in ball x s, (1 : ℝ) := by
    have hGχ : IntegrableOn (fun y => ‖gradient u y‖ ^ 2 + χ y) (ball x s) := hG.add hχ
    rw [← integral_sub hGχ h1]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only
    ring
  have hsn : s ^ n ≠ 0 := pow_ne_zero n hs.ne'
  rw [weightedEnergyD, energyD, e, hone, mul_sub, ← mul_assoc, inv_mul_cancel₀ hsn]
  ring

/-- For `Q ≡ 1`, the weighted frequency is `N`. -/
theorem weightedFrequencyN_one (h : IsVariationalSolution Ω C u χ) {s : ℝ} (hs : 0 < s)
    (hΩ : ball x s ⊆ Ω) : weightedFrequencyN (fun _ => 1) u χ x s = frequencyN u χ x s := by
  rw [weightedFrequencyN, frequencyN, h.weightedEnergyD_one hs hΩ, one_pow, one_mul]

/-- For `Q ≡ 1` and `κ = 0`, the modified frequency is `N`. -/
theorem modFrequencyN_one (h : IsVariationalSolution Ω C u χ) {s : ℝ} (hs : 0 < s)
    (hΩ : ball x s ⊆ Ω) : modFrequencyN 0 (fun _ => 1) u χ x s = frequencyN u χ x s := by
  rw [modFrequencyN, h.weightedFrequencyN_one hs hΩ]
  ring

/-- For `Q ≡ 1` and `κ = 0`, the shifted Weiss energy is `M − |B_1|`. -/
theorem modMonotonicityM_one (h : IsVariationalSolution Ω C u χ) {s : ℝ} (hs : 0 < s)
    (hΩ : ball x s ⊆ Ω) :
    modMonotonicityM 0 (fun _ => 1) u χ x s = monotonicityM u χ x s - unitBallVolume n := by
  rw [modMonotonicityM, weightedMonotonicityM, monotonicityM, h.weightedEnergyD_one hs hΩ]
  ring

end IsVariationalSolution

end InnerVariational
