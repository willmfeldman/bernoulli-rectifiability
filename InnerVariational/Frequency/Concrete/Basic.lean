/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Radial
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal
public import InnerVariational.Defs.Quantities
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
public import InnerVariational.Frequency.Abstract
import InnerVariational.Basic.LipschitzFTC

/-!
# The frequency formula for a variational solution (Lemmas 4.1–4.5)

Section 4 of Kriventsov–Weiss, up to Lemma 4.5. The calculus of one variable behind Section 4 is
proved for abstract radial data in `Frequency/Abstract.lean`, and the radial data of a
variational solution are constructed in `Monotonicity/Radial.lean`
(`IsVariationalSolution.radialData`). This file states the results for `frequencyN`, `heightH`
and `volumeV` of a variational solution, up to the annulus estimate.

## Main results

* `IsVariationalSolution.monotoneOn_sq_mul_heightH`: `s ↦ s² H_x(u; s)` is nondecreasing on
  `(0, R)` when `B_R(x) ⊆ Ω`. Up to the factor `n |B_1|` this is the spherical mean of `u²`.
  It follows from `H' = −(2/s) H + (2/s^{n+2}) ∫_{∂B_s} u ∇u·(y−x)` and the energy identity (3.8),
  so the sub-mean-value property of subharmonic functions is not needed.
* `IsVariationalSolution.heightH_pos` (beginning of §4): `H_x(u; r) > 0` if
  `x ∈ closure {u > 0}` and `B̄_r(x) ⊆ Ω`.
* Lemma 4.1: `IsVariationalSolution.monotoneOn_frequencyN`,
  `IsVariationalSolution.one_le_frequencyN`, and `IsVariationalSolution.monotoneOn_heightH`.
* Lemma 4.3: `IsVariationalSolution.heightH_doubling`.
* Lemma 4.4: `IsVariationalSolution.volumeV_doubling`.
* Lemma 4.5: `IsVariationalSolution.volumeV_le_sqrt`.
* The integrated form of (4.13): `IsVariationalSolution.integral_frequency_sq_term_le`, and the
  annulus estimate `IsVariationalSolution.integral_annulus_sq_inner_gradient_sub_le` (used in
  the proofs of Theorems 6.1 and 6.3), with its special case
  `IsVariationalSolution.integral_annulus_homogeneity_le` (`λ = N_x(s₁)`).

## Differences from the paper

* `V` carries the factor `r^{-n}`, which the paper's printed definition omits and (4.11) uses
  (the two agree at `r = 1`); the constant in Lemma 4.4 is `2ⁿ C(N₊)` because of this factor.
* Lemmas 4.3–4.5 are stated with `M_x(t) ≥ |B_1|` at the inner endpoint `t` of the interval.
  This covers the paper's case and is what the proof of Lemma 4.5 actually needs.
* `N_x(r) = 0` where `H_x(r) = 0` (the paper sets `N = −∞`). Every statement about `N` has
  `H > 0` available, from `heightH_pos` or as a hypothesis.
* We assume `Q ≡ 1`, as the paper does.

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

/-! ### Complements to the abstract radial calculus -/

namespace Abstract.RadialData

variable {ω a b : ℝ} (d : RadialData n ω a b)

/-- `(s² H)' = 2 s ∫_{B_s} |∇u|² / sⁿ` for a.e. `s`, from the derivative of `H` and the energy
identity (3.8). -/
theorem hasDerivAt_sq_mul_heightH : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt (fun s => s ^ 2 * d.heightH s) (2 * s * d.gradInt s / s ^ n) s := by
  filter_upwards [d.hasDerivAt_heightH, d.gradInt_eq] with s hH hG hs
  have hs0 : s ≠ 0 := (d.pos.trans hs.1).ne'
  refine ((hasDerivAt_pow 2 s).mul (hH hs)).congr_deriv ?_
  rw [hG hs]
  field_simp
  ring

theorem absolutelyContinuousOnInterval_sq_mul_heightH :
    AbsolutelyContinuousOnInterval (fun s => s ^ 2 * d.heightH s) a b :=
  (ContDiffOn.absolutelyContinuousOnInterval (f := fun s : ℝ => s ^ 2)
    (contDiff_id.pow 2).contDiffOn).fun_mul d.absolutelyContinuousOnInterval_heightH

/-- The spherical mean of `u²` is nondecreasing: `s ↦ s² H(s)` is nondecreasing on `[a, b]` when
`∫_{B_s} |∇u|² ≥ 0`. -/
theorem monotoneOn_sq_mul_heightH (hG : ∀ s ∈ Ioo a b, 0 ≤ d.gradInt s) :
    MonotoneOn (fun s => s ^ 2 * d.heightH s) (Icc a b) :=
  d.absolutelyContinuousOnInterval_sq_mul_heightH.monotoneOn_of_ae_hasDerivAt_nonneg
    d.hasDerivAt_sq_mul_heightH (.of_forall fun s hs => by
      have hs0 : 0 < s := d.pos.trans hs.1
      exact div_nonneg (mul_nonneg (by positivity) (hG s hs)) (by positivity))

/-- A radius with small `V`: if `H > 0` on `[t₁, t₂]`, `M(t₁) ≥ ω`, `0 ≤ v` and
`N(t₂) − N(t₁) < 2 v² log(t₂ / t₁)`, then `V(σ) < v` for some `σ ∈ (t₁, t₂)`. This is the
pigeonhole step of the proof of Lemma 4.5, from `∫ (2/s) V² ≤ N(t₂) − N(t₁)`. -/
theorem exists_volumeV_lt {t₁ t₂ : ℝ} (ht₁ : a ≤ t₁) (ht : t₁ < t₂) (ht₂ : t₂ ≤ b)
    (hH : ∀ s ∈ Icc t₁ t₂, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t₁) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : d.frequencyN t₂ - d.frequencyN t₁ < 2 * v ^ 2 * (Real.log t₂ - Real.log t₁)) :
    ∃ σ ∈ Ioo t₁ t₂, d.volumeV σ < v := by
  by_contra hcon
  push Not at hcon
  have ht₁0 : 0 < t₁ := d.pos.trans_le ht₁
  let d' := d.restrict ht₁ ht.le ht₂
  have hfAC : AbsolutelyContinuousOnInterval (fun s => 2 * v ^ 2 * Real.log s) t₁ t₂ := by
    obtain ⟨K, hK⟩ := (LipschitzWith.id.lipschitzOnWith (s := Icc t₁ t₂)).exists_log
      (g := fun s => s) ht₁0 fun x hx => hx.1
    exact (hK.absolutelyContinuousOnInterval_of_Icc ht.le).const_mul (2 * v ^ 2)
  have hf' : ∀ᵐ x, x ∈ Ioo t₁ t₂ →
      HasDerivAt (fun s => 2 * v ^ 2 * Real.log s) (2 * v ^ 2 * x⁻¹) x :=
    Eventually.of_forall fun x hx =>
      (Real.hasDerivAt_log (ht₁0.trans hx.1).ne').const_mul (2 * v ^ 2)
  have hle : ∀ᵐ x, x ∈ Ioo t₁ t₂ → 2 * v ^ 2 * x⁻¹ ≤
      2 / (d.heightH x * x ^ (n + 2)) *
          (d.sphRad x - 2 * (d.frequencyN x + d.volumeV x) * d.sphMix x +
            (d.frequencyN x + d.volumeV x) ^ 2 * d.sphSq x) +
        2 / x * (d.volumeV x ^ 2 + d.volumeV x * (d.frequencyN x - 1)) := by
    filter_upwards [d'.ae_volumeV_sq_le hH hM] with x hx hmem
    have hx0 : 0 < x := ht₁0.trans hmem.1
    refine le_trans ?_ (hx hmem)
    have hV2 : v ^ 2 ≤ d.volumeV x ^ 2 := pow_le_pow_left₀ hv0 (hcon x hmem) 2
    calc 2 * v ^ 2 * x⁻¹ = 2 / x * v ^ 2 := by ring
      _ ≤ 2 / x * d.volumeV x ^ 2 := mul_le_mul_of_nonneg_left hV2 (by positivity)
  have hcomp : 2 * v ^ 2 * Real.log t₂ - 2 * v ^ 2 * Real.log t₁ ≤
      d.frequencyN t₂ - d.frequencyN t₁ :=
    hfAC.sub_le_sub_of_ae_hasDerivAt_le (d'.absolutelyContinuousOnInterval_frequencyN hH) hf'
      (d'.hasDerivAt_frequencyN hH) hle (left_mem_Icc.2 ht.le) (right_mem_Icc.2 ht.le) ht.le
  linarith

end Abstract.RadialData

/-- `H_x(u; r) ≥ 0` for `r ≥ 0`. -/
theorem heightH_nonneg (u : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ heightH u x r :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hr _)) (sphereIntegral_nonneg hr fun _ _ => sq_nonneg _)

/-- `N_x(u; r) = 0` where `H_x(u; r) = 0` (Lean's `x / 0 = 0`; the paper sets `N = −∞`). -/
theorem frequencyN_of_heightH_eq_zero {u χ : Rn n → ℝ} {x : Rn n} {r : ℝ}
    (hH : heightH u x r = 0) : frequencyN u χ x r = 0 := by
  rw [frequencyN, hH, div_zero]

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

/-- The constant `K(n, N₊) = max{1, (8/5)ⁿ (3 N₊' + 1) heightHChangeConst' n N₊}`,
`N₊' = max N₊ 1`, of Lemma 4.6 on `N`, in the corrected form
`IsVariationalSolution.frequencyN_change_of_point_le`. -/
def frequencyNChangeConst (n : ℕ) (Np : ℝ) : ℝ :=
  max 1 ((8 / 5) ^ n * (max Np 1 + (2 * max Np 1 + 1)) * heightHChangeConst' n Np)

theorem one_le_frequencyNChangeConst (n : ℕ) (Np : ℝ) : 1 ≤ frequencyNChangeConst n Np :=
  le_max_left _ _

/-- A function that is a.e.-measurable on `B_R(x)` and bounded there is integrable there. -/
theorem integrableOn_ball_of_abs_le {f : Rn n → ℝ} {x : Rn n} {R : ℝ} (A : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (ball x R))) (hb : ∀ y ∈ ball x R, |f y| ≤ A) :
    IntegrableOn f (ball x R) :=
  IntegrableOn.of_bound measure_ball_lt_top hf A
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact hb y hy))

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Integrability helpers -/

theorem integrableOn_sq_of_closedBall (h : IsVariationalSolution Ω C u χ) {r : ℝ}
    (hΩ : closedBall x r ⊆ Ω) : IntegrableOn (fun y => u y ^ 2) (ball x r) :=
  (((h.continuousOn.mono hΩ).pow 2).integrableOn_compact (isCompact_closedBall x r)).mono_set
    ball_subset_closedBall

/-- `∫_{∂B_s(x)} (∇u·(y−x) − c u)² = ∫ (∇u·(y−x))² − 2c ∫ u ∇u·(y−x) + c² ∫ u²`. -/
theorem sphereIntegral_inner_sub_mul_sq (h : IsVariationalSolution Ω C u χ) {R s : ℝ}
    (hR : ball x R ⊆ Ω) (hs : 0 ≤ s) (hsR : s < R) (c : ℝ) :
    sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - c * u y) ^ 2) x s =
      sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
        2 * c * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
        c ^ 2 * sphereIntegral (fun y => u y ^ 2) x s := by
  have e : (fun y => (⟪gradient u y, y - x⟫ - c * u y) ^ 2) = fun y =>
      (⟪gradient u y, y - x⟫ ^ 2 - (2 * c) * (u y * ⟪gradient u y, y - x⟫)) + c ^ 2 * u y ^ 2 := by
    ext y; ring
  have hm : SphereIntegrable (fun y => (2 * c) * (u y * ⟪gradient u y, y - x⟫)) x s :=
    (h.sphereIntegrable_mix hR hs hsR).const_mul (2 * c)
  have hq : SphereIntegrable (fun y => c ^ 2 * u y ^ 2) x s :=
    (h.sphereIntegrable_u_sq hR hs hsR).const_mul (c ^ 2)
  have hd : SphereIntegrable
      (fun y => ⟪gradient u y, y - x⟫ ^ 2 - (2 * c) * (u y * ⟪gradient u y, y - x⟫)) x s :=
    (h.sphereIntegrable_inner_sq hR hs hsR).sub hm
  rw [e, sphereIntegral_add hd hq, sphereIntegral_sub (h.sphereIntegrable_inner_sq hR hs hsR) hm,
    sphereIntegral_const_mul, sphereIntegral_const_mul]

theorem sphereIntegrable_inner_sub_mul_sq (h : IsVariationalSolution Ω C u χ) {R s : ℝ}
    (hR : ball x R ⊆ Ω) (hs : 0 ≤ s) (hsR : s < R) (c : ℝ) :
    SphereIntegrable (fun y => (⟪gradient u y, y - x⟫ - c * u y) ^ 2) x s := by
  have e : (fun y => (⟪gradient u y, y - x⟫ - c * u y) ^ 2) = fun y =>
      (⟪gradient u y, y - x⟫ ^ 2 - (2 * c) * (u y * ⟪gradient u y, y - x⟫)) + c ^ 2 * u y ^ 2 := by
    ext y; ring
  rw [e]
  exact ((h.sphereIntegrable_inner_sq hR hs hsR).sub
    ((h.sphereIntegrable_mix hR hs hsR).const_mul (2 * c))).add
    ((h.sphereIntegrable_u_sq hR hs hsR).const_mul (c ^ 2))

/-! ### Spherical means of `u²` and positivity of `H` -/

/-- **Spherical means of `u²` are nondecreasing**: `s ↦ s² H_x(u; s)` is nondecreasing on
`(0, R)` when `B_R(x) ⊆ Ω`. Here `s² H_x(s) = s^{1-n} ∫_{∂B_s(x)} u²`. This follows from
`(s² H)' = 2 s^{1-n} ∫_{B_s(x)} |∇u|² ≥ 0`, a consequence of the energy identity (3.8). -/
theorem monotoneOn_sq_mul_heightH [NeZero n] (h : IsVariationalSolution Ω C u χ) {R : ℝ}
    (hR : ball x R ⊆ Ω) : MonotoneOn (fun s => s ^ 2 * heightH u x s) (Ioo 0 R) := by
  intro s hs t ht hst
  exact (h.radialData hR hs.1 hst ht.2).monotoneOn_sq_mul_heightH
    (fun r _ => setIntegral_nonneg measurableSet_ball fun y _ => sq_nonneg _)
    ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

/-- `s ↦ s² H_x(u; s)` is nondecreasing on `(0, R]` when `B̄_R(x) ⊆ Ω`. -/
theorem monotoneOn_sq_mul_heightH_Ioc [NeZero n] (h : IsVariationalSolution Ω C u χ) {R : ℝ}
    (hR : closedBall x R ⊆ Ω) : MonotoneOn (fun s => s ^ 2 * heightH u x s) (Ioc 0 R) := by
  intro s hs t ht hst
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.1.le.trans ht.2) hR
  exact h.monotoneOn_sq_mul_heightH hR' ⟨hs.1, hs.2.trans_lt hRR'⟩ ⟨ht.1, ht.2.trans_lt hRR'⟩ hst

/-- `s² H_x(s) ≤ t² H_x(t)` for `0 < s ≤ t` and `B̄_t(x) ⊆ Ω`. -/
theorem sq_mul_heightH_le [NeZero n] (h : IsVariationalSolution Ω C u χ) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (ht : closedBall x t ⊆ Ω) :
    s ^ 2 * heightH u x s ≤ t ^ 2 * heightH u x t :=
  h.monotoneOn_sq_mul_heightH_Ioc ht ⟨hs, hst⟩ ⟨hs.trans_le hst, le_rfl⟩ hst

/-- Positivity of `H` propagates outwards: if `H_x(s) > 0`, `s ≤ t` and `B̄_t(x) ⊆ Ω`, then
`H_x(t) > 0`. -/
theorem heightH_pos_of_le [NeZero n] (h : IsVariationalSolution Ω C u χ) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (ht : closedBall x t ⊆ Ω) (hH : 0 < heightH u x s) :
    0 < heightH u x t := by
  have h1 : 0 < s ^ 2 * heightH u x s := by positivity
  exact pos_of_mul_pos_right (h1.trans_le (h.sq_mul_heightH_le hs hst ht)) (sq_nonneg t)

/-- **Positivity of `H`** (§4): if `x ∈ closure {u > 0}`, `0 < r` and `B̄_r(x) ⊆ Ω`, then
`H_x(u; r) > 0`. If `H_x(r) = 0`, the monotonicity of spherical means gives `H_x(s) = 0` for
`s ≤ r`, so `∫_{B_r(x)} u² = 0` and `u ≡ 0` on `B_r(x)`, contradicting `x ∈ closure {u > 0}`. -/
theorem heightH_pos [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ closure {y | 0 < u y}) {r : ℝ} (hr : 0 < r) (hΩ : closedBall x r ⊆ Ω) :
    0 < heightH u x r := by
  by_contra hneg
  have hH0 : heightH u x r = 0 := le_antisymm (not_lt.1 hneg) (heightH_nonneg u x hr.le)
  have hS : ∀ s ∈ Ioc 0 r, sphereIntegral (fun y => u y ^ 2) x s = 0 := by
    intro s hs
    have hmono := h.sq_mul_heightH_le hs.1 hs.2 hΩ
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
theorem heightH_pos_of_mem_Icc [NeZero n] (h : IsVariationalSolution Ω C u χ) {t R : ℝ}
    (ht : 0 < t) (hHt : 0 < heightH u x t) (hΩ : closedBall x R ⊆ Ω) {s : ℝ}
    (hs : s ∈ Icc t R) : 0 < heightH u x s :=
  h.heightH_pos_of_le ht hs.1 ((closedBall_subset_closedBall hs.2).trans hΩ) hHt

/-! ### Lemma 4.1 -/

section Frequency

variable [NeZero n] (h : IsVariationalSolution Ω C u χ)
include h

/-- **Lemma 4.1** with the hypothesis `H_x(t) > 0` in place of
`x ∈ closure {u > 0}`: if `0 < t ≤ R`, `H_x(t) > 0`, `M_x(t) ≥ |B_1|` and `B̄_R(x) ⊆ Ω`, then
`N_x` is nondecreasing on `[t, R]` and `N_x ≥ 1` there. This form applies at points `y` that
need not lie in `closure {u > 0}` (Lemma 4.6). -/
theorem monotoneOn_frequencyN_of_heightH_pos {t R : ℝ} (ht : 0 < t) (hHt : 0 < heightH u x t)
    (hM : unitBallVolume n ≤ monotonicityM u χ x t) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (frequencyN u χ x) (Icc t R) ∧ ∀ s ∈ Icc t R, 1 ≤ frequencyN u χ x s := by
  rcases lt_or_ge R t with hRt | htR
  · exact ⟨fun s hs _ _ _ => absurd (hs.1.trans hs.2) (not_le.2 hRt),
      fun s hs => absurd (hs.1.trans hs.2) (not_le.2 hRt)⟩
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htR) hΩ
  let d := h.radialData hR' ht htR hRR'
  have hH : ∀ s ∈ Icc t R, 0 < d.heightH s := fun s hs => h.heightH_pos_of_mem_Icc ht hHt hΩ hs
  exact ⟨d.monotoneOn_frequencyN hH hM, fun s hs => d.one_le_frequencyN hH hM hs⟩

/-- **Lemma 4.1**: if `x ∈ closure {u > 0}`, `0 < t`, `M_x(u; t) ≥ |B_1|` and
`B̄_R(x) ⊆ Ω`, then `s ↦ N_x(u; s)` is nondecreasing on `[t, R]`. -/
theorem monotoneOn_frequencyN (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hM : unitBallVolume n ≤ monotonicityM u χ x t) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (frequencyN u χ x) (Icc t R) := by
  rcases lt_or_ge R t with hRt | htR
  · exact fun s hs _ _ _ => absurd (hs.1.trans hs.2) (not_le.2 hRt)
  exact (h.monotoneOn_frequencyN_of_heightH_pos ht
    (h.heightH_pos hx ht ((closedBall_subset_closedBall htR).trans hΩ)) hM hΩ).1

/-- **Lemma 4.1**: under the hypotheses of `monotoneOn_frequencyN`,
`N_x(u; s) ≥ 1` for `s ∈ [t, R]`. -/
theorem one_le_frequencyN (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hM : unitBallVolume n ≤ monotonicityM u χ x t) (hΩ : closedBall x R ⊆ Ω) {s : ℝ}
    (hs : s ∈ Icc t R) : 1 ≤ frequencyN u χ x s :=
  (h.monotoneOn_frequencyN_of_heightH_pos ht
    (h.heightH_pos hx ht ((closedBall_subset_closedBall (hs.1.trans hs.2)).trans hΩ)) hM hΩ).2
    s hs

/-- The lower bound of Lemma 4.3: if `x ∈ closure {u > 0}`, `0 < t`,
`M_x(u; t) ≥ |B_1|` and `B̄_R(x) ⊆ Ω`, then `H_x` is nondecreasing on `[t, R]`. -/
theorem monotoneOn_heightH (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hM : unitBallVolume n ≤ monotonicityM u χ x t) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (heightH u x) (Icc t R) := by
  rcases lt_or_ge R t with hRt | htR
  · exact fun s hs _ _ _ => absurd (hs.1.trans hs.2) (not_le.2 hRt)
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htR) hΩ
  let d := h.radialData hR' ht htR hRR'
  have hH : ∀ s ∈ Icc t R, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  exact d.monotoneOn_heightH hH hM

omit [NeZero n] in
/-- `N_x(u; s) + V_x(u; s) = s^{-n} ∫_{B_s(x)} |∇u|² / H_x(u; s)`, identity (4.11), for a
variational solution. -/
theorem frequencyN_add_volumeV_eq {s : ℝ} (hs : 0 < s) (hΩ : ball x s ⊆ Ω) :
    frequencyN u χ x s + volumeV u χ x s =
      (s ^ n)⁻¹ * (∫ y in ball x s, ‖gradient u y‖ ^ 2) / heightH u x s :=
  InnerVariational.frequencyN_add_volumeV hs (h.integrableOn_norm_gradient_sq hΩ)
    (h.integrableOn_chi hΩ)

omit [NeZero n] in
/-- `V_x(u; s) ≥ 0` for a variational solution. -/
theorem volumeV_nonneg {s : ℝ} (hs : 0 < s) (hΩ : ball x s ⊆ Ω) : 0 ≤ volumeV u χ x s := by
  rw [volumeV]
  refine div_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg hs.le _))
    (setIntegral_nonneg measurableSet_ball fun y hy => ?_)) (heightH_nonneg u x hs.le)
  exact sub_nonneg.2 (abs_le.1 (h.abs_chi_le_one (hΩ hy))).2

/-! ### Lemmas 4.3–4.5 -/

/-- **Lemma 4.3**, for `t ≤ s ≤ r ≤ 2t` (the paper's case is `t = r/2`; the hypothesis
`M ≥ |B_1|` sits at the inner endpoint, which is what the proof of Lemma 4.5 needs): if
`x ∈ closure {u > 0}`, `M_x(u; t) ≥ |B_1|`, `B̄_r(x) ⊆ Ω` and `N_x(u; r) ≤ N₊` with `N₊ > 1`,
then `H_x(s) ≤ H_x(r) ≤ C H_x(s)` with `C = exp(2(N₊ − 1) + 4√(N₊ − 1))`. -/
theorem heightH_doubling (hx : x ∈ closure {y | 0 < u y}) {t r : ℝ} (ht : 0 < t) (htr : t ≤ r)
    (hr2 : r ≤ 2 * t) (hM : unitBallVolume n ≤ monotonicityM u χ x t)
    (hΩ : closedBall x r ⊆ Ω) {Np : ℝ} (hNp : 1 < Np) (hN : frequencyN u χ x r ≤ Np) {s : ℝ}
    (hs : s ∈ Icc t r) :
    heightH u x s ≤ heightH u x r ∧
      heightH u x r ≤ Abstract.RadialData.doublingConst Np * heightH u x s := by
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htr) hΩ
  let d := h.radialData hR' ht htr hRR'
  have hH : ∀ s ∈ Icc t r, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  exact d.heightH_doubling le_rfl htr le_rfl hr2 hH hM hNp hN hs

/-- **Lemma 4.4**, for `t ≤ s ≤ r ≤ 2t`: under the hypotheses of `heightH_doubling`,
`V_x(s) ≤ 2ⁿ C V_x(r)`. The constant is `2ⁿ C` because of the factor `r^{-n}` in `V`,
which the paper's printed definition omits. -/
theorem volumeV_doubling (hx : x ∈ closure {y | 0 < u y}) {t r : ℝ} (ht : 0 < t) (htr : t ≤ r)
    (hr2 : r ≤ 2 * t) (hM : unitBallVolume n ≤ monotonicityM u χ x t)
    (hΩ : closedBall x r ⊆ Ω) {Np : ℝ} (hNp : 1 < Np) (hN : frequencyN u χ x r ≤ Np) {s : ℝ}
    (hs : s ∈ Icc t r) :
    volumeV u χ x s ≤ 2 ^ n * Abstract.RadialData.doublingConst Np * volumeV u χ x r := by
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htr) hΩ
  let d := h.radialData hR' ht htr hRR'
  have hH : ∀ s ∈ Icc t r, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  have := d.volumeV_doubling le_rfl htr le_rfl hr2 hH hM hNp hN hs
  rwa [h.radialData_volumeV hR' ht htr hRR' hs,
    h.radialData_volumeV hR' ht htr hRR' (right_mem_Icc.2 htr)] at this

/-- **Lemma 4.5**: if `x ∈ closure {u > 0}`, `0 < t`,
`2t ≤ r`, `M_x(u; t) ≥ |B_1|`, `B̄_r(x) ⊆ Ω`, `N_x(u; r) < N₊` and
`N_x(u; r) − N_x(u; t) < δ`, then `V_x(u; t) ≤ 2ⁿ C(N₊) √δ`. -/
theorem volumeV_le_sqrt (hx : x ∈ closure {y | 0 < u y}) {t r : ℝ} (ht : 0 < t)
    (htr : 2 * t ≤ r) (hM : unitBallVolume n ≤ monotonicityM u χ x t)
    (hΩ : closedBall x r ⊆ Ω) {Np δ : ℝ} (hN : frequencyN u χ x r < Np)
    (hδ : frequencyN u χ x r - frequencyN u χ x t < δ) :
    volumeV u χ x t ≤ 2 ^ n * Abstract.RadialData.doublingConst Np * √δ := by
  have htr' : t ≤ r := by linarith
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans htr') hΩ
  let d := h.radialData hR' ht htr' hRR'
  have hH : ∀ s ∈ Icc t r, 0 < d.heightH s := fun s hs =>
    h.heightH_pos hx (ht.trans_le hs.1) ((closedBall_subset_closedBall hs.2).trans hΩ)
  have := d.volumeV_le_sqrt le_rfl htr le_rfl hH hM hN hδ
  rwa [h.radialData_volumeV hR' ht htr' hRR' (left_mem_Icc.2 htr')] at this

end Frequency

/-! ### Integrated (4.13) and the annulus estimate -/

section Annulus

variable [NeZero n] (h : IsVariationalSolution Ω C u χ)
include h

omit [NeZero n] in
/-- The integrands `u ∇u·(y−x)`, `(∇u·(y−x))²` and `(∇u·(y−x) − l u)²` are integrable on
`B_R(x)` when `B̄_R(x) ⊆ Ω`. -/
theorem integrableOn_ball_inner_gradient {R : ℝ} (hΩ : closedBall x R ⊆ Ω) :
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

/-- **Integrated form of (4.13)** (as in the proof of Theorem 6.1): for `0 < t ≤ s₁ ≤ s₂`, if
`x ∈ closure {u > 0}`, `M_x(u; t) ≥ |B_1|` and `B̄_{s₂}(x) ⊆ Ω`, then
`∫_{s₁}^{s₂} (2 / (H_x(s) s^{n+2})) ∫_{∂B_s(x)} (∇u·(y−x) − N_x(s) u)² ds ≤ N_x(s₂) − N_x(s₁)`. -/
theorem integral_frequency_sq_term_le (hx : x ∈ closure {y | 0 < u y}) {t s₁ s₂ : ℝ}
    (ht : 0 < t) (hts : t ≤ s₁) (hs : s₁ ≤ s₂) (hM : unitBallVolume n ≤ monotonicityM u χ x t)
    (hΩ : closedBall x s₂ ⊆ Ω) :
    ∫ s in s₁..s₂, 2 / (heightH u x s * s ^ (n + 2)) *
        sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - frequencyN u χ x s * u y) ^ 2) x s ≤
      frequencyN u χ x s₂ - frequencyN u χ x s₁ := by
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.le.trans (hts.trans hs)) hΩ
  let d := h.radialData hR' ht (hts.trans hs) hRR'
  have hH : ∀ s ∈ Icc t s₂, 0 < d.heightH s := fun s hs' =>
    h.heightH_pos hx (ht.trans_le hs'.1) ((closedBall_subset_closedBall hs'.2).trans hΩ)
  refine Eq.trans_le ?_ (d.integral_frequency_sq_term_le hH hM ⟨hts, hs⟩
    ⟨hts.trans hs, le_rfl⟩ hs)
  refine intervalIntegral.integral_congr fun s hs' => ?_
  rw [uIcc_of_le hs] at hs'
  rw [h.sphereIntegral_inner_sub_mul_sq hR' (ht.le.trans (hts.trans hs'.1))
    (hs'.2.trans_lt hRR')]
  rfl

/-- **The annulus homogeneity estimate** (proofs of Theorems 6.1 and 6.3), the integrated form
of (4.13) on an annulus, for any `λ`: if `x ∈ closure {u > 0}`, `M_x(u; t) ≥ |B_1|`,
`0 < t ≤ s₁ ≤ s₂` and `B̄_{s₂}(x) ⊆ Ω`, then
`∫_{B_{s₂}(x)∖B_{s₁}(x)} (∇u·(y−x) − λu)² ≤
  s₂^{n+2} H_x(s₂) ((N_x(s₂) − N_x(s₁)) + 2 max((N_x(s₂) − λ)², (N_x(s₁) − λ)²))`.

Proof: on `∂B_s(x)`, `(∇u·(y−x) − λu)² ≤ 2(∇u·(y−x) − N(s)u)² + 2(N(s) − λ)²u²`. The first term
integrates to at most `s₂^{n+2} H(s₂)(N(s₂) − N(s₁))` by (4.13) (since `V(N − 1) ≥ 0` and `H` is
nondecreasing), and `∫_{B_{s₂}∖B_{s₁}} u² ≤ s₂^{n+2} H(s₂)`. -/
theorem integral_annulus_sq_inner_gradient_sub_le (hx : x ∈ closure {y | 0 < u y})
    {t s₁ s₂ : ℝ} (ht : 0 < t) (hts : t ≤ s₁) (hs : s₁ ≤ s₂)
    (hM : unitBallVolume n ≤ monotonicityM u χ x t) (hΩ : closedBall x s₂ ⊆ Ω) (l : ℝ) :
    ∫ y in ball x s₂ \ ball x s₁, (⟪gradient u y, y - x⟫ - l * u y) ^ 2 ≤
      s₂ ^ (n + 2) * heightH u x s₂ * ((frequencyN u χ x s₂ - frequencyN u χ x s₁) +
        2 * max ((frequencyN u χ x s₂ - l) ^ 2) ((frequencyN u χ x s₁ - l) ^ 2)) := by
  have hs₁ : 0 < s₁ := ht.trans_le hts
  have hs₂ : 0 < s₂ := hs₁.trans_le hs
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen hs₂.le hΩ
  let d := h.radialData hR' ht (hts.trans hs) hRR'
  have hH : ∀ s ∈ Icc t s₂, 0 < d.heightH s := fun s hs' =>
    h.heightH_pos hx (ht.trans_le hs'.1) ((closedBall_subset_closedBall hs'.2).trans hΩ)
  have hmonoN : MonotoneOn (frequencyN u χ x) (Icc t s₂) := h.monotoneOn_frequencyN hx ht hM hΩ
  have hmonoH : MonotoneOn (heightH u x) (Icc t s₂) := h.monotoneOn_heightH hx ht hM hΩ
  set N := frequencyN u χ x with hN
  set H := heightH u x with hHdef
  set m := max ((N s₂ - l) ^ 2) ((N s₁ - l) ^ 2) with hm
  have hm0 : 0 ≤ m := (sq_nonneg _).trans (le_max_left _ _)
  obtain ⟨hIMix, hIRad, hIF⟩ := h.integrableOn_ball_inner_gradient hΩ
  have hISq := h.integrableOn_sq_of_closedBall hΩ
  have hsub : uIcc s₁ s₂ ⊆ uIcc 0 s₂ := by
    rw [uIcc_of_le hs, uIcc_of_le hs₂.le]; exact Icc_subset_Icc hs₁.le le_rfl
  have hIIF := (intervalIntegrable_sphereIntegral hs₂.le (hIF l)).mono_set hsub
  have hIIRad := (intervalIntegrable_sphereIntegral hs₂.le hIRad).mono_set hsub
  have hIIMix := (intervalIntegrable_sphereIntegral hs₂.le hIMix).mono_set hsub
  have hIISq := (intervalIntegrable_sphereIntegral hs₂.le hISq).mono_set hsub
  set Q : ℝ → ℝ := fun s =>
    sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - N s * u y) ^ 2) x s with hQ
  set S : ℝ → ℝ := fun s => sphereIntegral (fun y => u y ^ 2) x s with hS
  have hmem : ∀ s ∈ Icc s₁ s₂, 0 ≤ s ∧ s < R' := fun s hs' =>
    ⟨hs₁.le.trans hs'.1, hs'.2.trans_lt hRR'⟩
  have hQeq : ∀ s ∈ Icc s₁ s₂, Q s =
      sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
        2 * N s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
        N s ^ 2 * sphereIntegral (fun y => u y ^ 2) x s :=
    fun s hs' => h.sphereIntegral_inner_sub_mul_sq hR' (hmem s hs').1 (hmem s hs').2 (N s)
  have hNc : ContinuousOn N (uIcc s₁ s₂) := by
    obtain ⟨K, hK⟩ := d.exists_lipschitzOnWith_frequencyN hH
    rw [uIcc_of_le hs]
    exact hK.continuousOn.mono (Icc_subset_Icc hts le_rfl)
  have hIIQ : IntervalIntegrable Q volume s₁ s₂ := by
    have h1 : IntervalIntegrable (fun s =>
        sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
          2 * N s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
          N s ^ 2 * sphereIntegral (fun y => u y ^ 2) x s) volume s₁ s₂ := by
      have h2 := (hIIMix.continuousOn_mul hNc).const_mul 2
      have h3 := hIISq.continuousOn_mul (hNc.pow 2)
      refine ((hIIRad.sub h2).add h3).congr fun s _ => ?_
      ring
    refine h1.congr fun s hs' => (hQeq s ?_).symm
    rw [uIoc_of_le hs] at hs'
    exact Ioc_subset_Icc_self hs'
  -- pointwise bound on each sphere
  have hpt : ∀ s ∈ Icc s₁ s₂,
      sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) x s ≤
        2 * Q s + 2 * m * S s := by
    intro s hs'
    obtain ⟨hs0, hsR⟩ := hmem s hs'
    have hN1 : N s₁ ≤ N s := hmonoN ⟨hts, hs⟩ ⟨hts.trans hs'.1, hs'.2⟩ hs'.1
    have hN2 : N s ≤ N s₂ := hmonoN ⟨hts.trans hs'.1, hs'.2⟩ ⟨hts.trans hs, le_rfl⟩ hs'.2
    have hNs : (N s - l) ^ 2 ≤ m := by
      rcases le_total l (N s) with hl | hl
      · exact (pow_le_pow_left₀ (sub_nonneg.2 hl) (by linarith) 2).trans (le_max_left _ _)
      · have : (N s - l) ^ 2 ≤ (N s₁ - l) ^ 2 := by nlinarith
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
      _ = 2 * Q s + 2 * m * S s := by
          rw [sphereIntegral_add hI1 hI2,
            sphereIntegral_const_mul, sphereIntegral_const_mul]
  -- the `Q` term, from (4.13)
  have hH₂ : 0 < H s₂ := hH s₂ ⟨hts.trans hs, le_rfl⟩
  have hQint : ∫ s in s₁..s₂, Q s ≤ s₂ ^ (n + 2) * H s₂ * (N s₂ - N s₁) / 2 := by
    set c := 2 / (s₂ ^ (n + 2) * H s₂) with hc
    have hc0 : 0 < c := by positivity
    have key : ∫ s in s₁..s₂, c * Q s ≤ N s₂ - N s₁ := by
      refine AbsolutelyContinuousOnInterval.integral_le_sub_of_ae_le hs
        ((d.absolutelyContinuousOnInterval_frequencyN hH).mono_Icc d.le ⟨hts, hs⟩
          ⟨hts.trans hs, le_rfl⟩)
        (ae_mem_Ioo_imp_mono hts le_rfl (d.hasDerivAt_frequencyN' hH)) ?_ ?_
      · refine .of_forall fun s hs' => mul_nonneg hc0.le ?_
        exact sphereIntegral_nonneg (hs₁.le.trans hs'.1.le) fun y _ => sq_nonneg _
      · filter_upwards [ae_mem_Ioo_imp_mono hts le_rfl (d.ae_frequency_sq_term_le hH hM)]
          with s hs1 hs'
        refine le_trans ?_ (hs1 hs')
        have hs'' : s ∈ Icc s₁ s₂ := Ioo_subset_Icc_self hs'
        have hs0 : 0 < s := hs₁.trans hs'.1
        have hHs : 0 < H s := hH s ⟨hts.trans hs''.1, hs''.2⟩
        have hQ0 : 0 ≤ Q s := sphereIntegral_nonneg hs0.le fun y _ => sq_nonneg _
        rw [show d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s =
          Q s from (hQeq s hs'').symm]
        refine mul_le_mul_of_nonneg_right ?_ hQ0
        refine div_le_div_of_nonneg_left zero_le_two (by positivity) ?_
        rw [mul_comm]
        exact mul_le_mul (pow_le_pow_left₀ hs0.le hs''.2 _)
          (hmonoH ⟨hts.trans hs''.1, hs''.2⟩ ⟨hts.trans hs, le_rfl⟩ hs''.2) hHs.le (by positivity)
    rw [intervalIntegral.integral_const_mul] at key
    have hpos : 0 < s₂ ^ (n + 2) * H s₂ := by positivity
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ hpos] at key
    linarith
  -- the `u²` term
  have hSint : ∫ s in s₁..s₂, S s ≤ s₂ ^ (n + 2) * H s₂ := by
    calc ∫ s in s₁..s₂, S s ≤ ∫ _ in s₁..s₂, s₂ ^ (n + 1) * H s₂ := by
          refine intervalIntegral.integral_mono_on hs hIISq intervalIntegrable_const
            fun s hs' => ?_
          have hs0 : 0 < s := hs₁.trans_le hs'.1
          simp only [hS]
          rw [sphereIntegral_sq_eq u x hs0.ne']
          exact mul_le_mul (pow_le_pow_left₀ hs0.le hs'.2 _)
            (hmonoH ⟨hts.trans hs'.1, hs'.2⟩ ⟨hts.trans hs, le_rfl⟩ hs'.2)
            (heightH_nonneg u x hs0.le) (by positivity)
      _ = (s₂ - s₁) * (s₂ ^ (n + 1) * H s₂) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ s₂ * (s₂ ^ (n + 1) * H s₂) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = s₂ ^ (n + 2) * H s₂ := by ring
  -- combine
  rw [integral_ball_diff_ball hs₁.le hs (hIF l)]
  calc ∫ s in s₁..s₂, sphereIntegral (fun y => (⟪gradient u y, y - x⟫ - l * u y) ^ 2) x s
      ≤ ∫ s in s₁..s₂, (2 * Q s + 2 * m * S s) :=
        intervalIntegral.integral_mono_on hs hIIF ((hIIQ.const_mul 2).add (hIISq.const_mul _)) hpt
    _ = 2 * (∫ s in s₁..s₂, Q s) + 2 * m * ∫ s in s₁..s₂, S s := by
        rw [intervalIntegral.integral_add (hIIQ.const_mul 2) (hIISq.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * (s₂ ^ (n + 2) * H s₂ * (N s₂ - N s₁) / 2) + 2 * m * (s₂ ^ (n + 2) * H s₂) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hQint zero_le_two)
          (mul_le_mul_of_nonneg_left hSint (mul_nonneg zero_le_two hm0))
    _ = s₂ ^ (n + 2) * H s₂ * ((N s₂ - N s₁) + 2 * m) := by ring

/-- **The annulus homogeneity estimate** with `λ = N_x(s₁)` (proof of Theorem 6.1): under the
hypotheses of `integral_annulus_sq_inner_gradient_sub_le`,
`∫_{B_{s₂}(x)∖B_{s₁}(x)} (∇u·(y−x) − N_x(s₁) u)² ≤
  s₂^{n+2} H_x(s₂) (1 + 2 (N_x(s₂) − N_x(s₁))) (N_x(s₂) − N_x(s₁))`. -/
theorem integral_annulus_homogeneity_le (hx : x ∈ closure {y | 0 < u y}) {t s₁ s₂ : ℝ}
    (ht : 0 < t) (hts : t ≤ s₁) (hs : s₁ ≤ s₂) (hM : unitBallVolume n ≤ monotonicityM u χ x t)
    (hΩ : closedBall x s₂ ⊆ Ω) :
    ∫ y in ball x s₂ \ ball x s₁,
        (⟪gradient u y, y - x⟫ - frequencyN u χ x s₁ * u y) ^ 2 ≤
      s₂ ^ (n + 2) * heightH u x s₂ *
        (1 + 2 * (frequencyN u χ x s₂ - frequencyN u χ x s₁)) *
        (frequencyN u χ x s₂ - frequencyN u χ x s₁) := by
  have := h.integral_annulus_sq_inner_gradient_sub_le hx ht hts hs hM hΩ (frequencyN u χ x s₁)
  rw [sub_self, zero_pow two_ne_zero, max_eq_left (sq_nonneg _)] at this
  exact this.trans_eq (by ring)

end Annulus

end IsVariationalSolution

end InnerVariational
