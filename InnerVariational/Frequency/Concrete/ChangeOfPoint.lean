/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Radial
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal
public import InnerVariational.Defs.Quantities
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
public import InnerVariational.Frequency.Abstract
import InnerVariational.Basic.LipschitzFTC
public import InnerVariational.Frequency.Concrete.Basic
public import InnerVariational.Frequency.ConcreteQ.ChangeOfPoint

/-!
# The frequency formula for a variational solution: Lemma 4.6 (change of point)

Lemma 4.6 of Kriventsov–Weiss (change of point), the continuity of `frequencyN` in the centre
(used in the proof of Theorem 6.1), and the forms of the results of Section 4 used in Sections 6
and 7.

## Main results

* Lemma 4.6: `IsVariationalSolution.heightH_change_of_point_le`,
  `IsVariationalSolution.heightH_le_change_of_point` (the two bounds on `H`) and
  `IsVariationalSolution.frequencyN_change_of_point_le` (the bound on `N`), with the
  existential forms `heightH_change_of_point`, `frequencyN_change_of_point`.
* `IsVariationalSolution.continuousOn_frequencyN`: `y ↦ N_y(u; r)` is continuous where
  `B̄_r(y) ⊆ Ω` and `H_y(u; r) > 0`.

## Differences from the paper

* Lemma 4.6 states `N_y(s) ≤ max{1, C N_x(r)}` with `C = C(n)`. The step
  `D_y(5/8) ≤ (8/5)ⁿ D_0(1)` in its proof leaves a term of order `|B_1| / H_y` that `N_0` does
  not control. We prove `N_y(s) ≤ K(n, N₊)` via (4.11), (4.12) and Lemma 4.3, which is what the
  later applications use: bound `N_y ≤ N_y + V_y`, which by (4.11) involves only `∫|∇u|²`, and
  control `∫_{B_σ(x)} |∇u|² = σⁿ H_x(σ) (N_x + V_x)(σ)` at a radius `σ ∈ (7r/8, r)` where
  `V_x(σ)` is bounded, which exists by (4.12).
* H-part of Lemma 4.6. The proof as written ends with `C H_y(5/8) ≥ H_0(1)`, the reverse of the
  stated `H_y(5r/8) ≤ C H_x(r)`. Both bounds hold and Theorems 6.1 and 6.3 use both. We prove
  both: the upper bound with `C = C(n)` (it needs only the monotonicity of spherical means of
  `u²`), and the lower bound with `C = C(n, N₊)` (it uses Lemma 4.3).

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

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Lemma 4.6: change of point -/

section ChangeOfPoint

variable [NeZero n] (h : IsVariationalSolution Ω C u χ)
include h

/-- `∫_{B_r(x)} u² ≤ r^{n+2} H_x(u; r)` when `B̄_r(x) ⊆ Ω`, since the spherical means of `u²` are
nondecreasing. -/
theorem integral_ball_sq_le {r : ℝ} (hr : 0 < r) (hΩ : closedBall x r ⊆ Ω) :
    ∫ y in ball x r, u y ^ 2 ≤ r ^ (n + 2) * heightH u x r :=
  IsVariationalSolutionQ.integral_ball_sq_le (QBounds.one Ω) h.toQ hr hΩ

/-- If `c ≤ ∫_{∂B_s(x)} u²` for every `s ∈ [ρ, ρ']`, then
`(ρ' − ρ) c ≤ ∫_{B_{ρ'}(x) ∖ B_ρ(x)} u²`. -/
theorem mul_le_integral_annulus_sq {ρ ρ' c : ℝ} (hρ : 0 ≤ ρ) (hρρ' : ρ ≤ ρ')
    (hΩ : closedBall x ρ' ⊆ Ω) (hc : ∀ s ∈ Icc ρ ρ', c ≤ sphereIntegral (fun y => u y ^ 2) x s) :
    (ρ' - ρ) * c ≤ ∫ y in ball x ρ' \ ball x ρ, u y ^ 2 :=
  h.toQ.mul_le_integral_annulus_sq hρ hρρ' hΩ hc

/-- **Lemma 4.6, upper bound on `H`**: if `0 < r`, `B̄_r(x) ⊆ Ω` and
`y ∈ B_{r/4}(x)`, then `H_y(u; 5r/8) ≤ 8 (8/5)^{n+1} H_x(u; r)`. The constant depends only on
`n`, and no hypothesis on `x` is needed: `∫_{B_{3r/4}(y) ∖ B_{5r/8}(y)} u²` is bounded below by
`H_y(5r/8)` and above by `∫_{B_r(x)} u² ≤ r^{n+2} H_x(r)`, both by the monotonicity of spherical
means of `u²`. (The proof of Lemma 4.6 as written ends with the reverse inequality; see
`heightH_le_change_of_point`.) -/
theorem heightH_change_of_point_le {r : ℝ} (hr : 0 < r) (hΩ : closedBall x r ⊆ Ω) {y : Rn n}
    (hy : y ∈ ball x (r / 4)) :
    heightH u y (5 / 8 * r) ≤ heightHChangeConst n * heightH u x r :=
  IsVariationalSolutionQ.heightH_change_of_point_le (QBounds.one Ω) h.toQ hr hΩ hy

/-- **Lemma 4.6, lower bound on `H`**: if `x ∈ closure {u > 0}`,
`0 < r`, `B̄_r(x) ⊆ Ω`, `M_x(u; r/4) ≥ |B_1|` and `N_x(u; r) ≤ N₊`, then
`H_x(u; r) ≤ K H_y(u; 5r/8)` for every `y ∈ B_{r/4}(x)`, with `K = heightHChangeConst' n N₊`.
The proof of Lemma 4.6 as written ends with `C H_y(5/8) ≥ H_0(1)`, the reverse of the stated
`H_y(5r/8) ≤ C H_x(r)`; both bounds hold and we prove both. The constant depends on `N₊`
through Lemma 4.3. -/
theorem heightH_le_change_of_point (hx : x ∈ closure {y | 0 < u y}) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall x r ⊆ Ω) (hM : unitBallVolume n ≤ monotonicityM u χ x (r / 4)) {Np : ℝ}
    (hN : frequencyN u χ x r ≤ Np) {y : Rn n} (hy : y ∈ ball x (r / 4)) :
    heightH u x r ≤ heightHChangeConst' n Np * heightH u y (5 / 8 * r) := by
  have hr4 : 0 < r / 4 := by positivity
  refine IsVariationalSolutionQ.heightH_le_change_of_point (QBounds.one Ω) h.toQ hx hr hΩ ?_
    (by simp [weissKappa_zero]) ?_ hy
  · rw [weissKappa_zero, h.modMonotonicityM_one hr4
      (ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hΩ))]
    linarith
  · rwa [weissKappa_zero, h.modFrequencyN_one hr (ball_subset_closedBall.trans hΩ)]

/-- **Lemma 4.6, bound on `N`**: if
`x ∈ closure {u > 0}`, `0 < r`, `B̄_r(x) ⊆ Ω`, `M_x(u; r/4) ≥ |B_1|` and `N_x(u; r) ≤ N₊`, then
`N_y(u; s) ≤ K(n, N₊)` for every `y ∈ B_{r/4}(x)` and `0 < s < r/2`,
`K = frequencyNChangeConst n N₊`.

The paper states `N_y(s) ≤ max{1, C N_x(r)}` with `C = C(n)`. The step
`D_y(5/8) ≤ (8/5)ⁿ D_0(1)` in its proof leaves a term of order `|B_1| / H_y` that `N_0` does
not control; we prove the bound with `K = K(n, N₊)` via (4.11), (4.12) and Lemma 4.3, which is
what the later applications use. The argument is:
* if `N_y(s) ≤ 1` there is nothing to prove (this includes `H_y(s) = 0`, where `N_y(s) = 0`);
* otherwise `M_y(s) > |B_1|` and `H_y(s) > 0`, so `N_y` is nondecreasing on `[s, 5r/8]`
  (Lemma 4.1 at `y`, which need not lie in `closure {u > 0}`), and
  `N_y(s) ≤ N_y(5r/8) ≤ (N_y + V_y)(5r/8) = (5r/8)^{-n} ∫_{B_{5r/8}(y)} |∇u|² / H_y(5r/8)`;
* `B_{5r/8}(y) ⊆ B_σ(x)` for `σ ∈ (7r/8, r)`, and
  `∫_{B_σ(x)} |∇u|² = σⁿ H_x(σ) (N_x + V_x)(σ) ≤ rⁿ H_x(r) (N₊ + V_x(σ))`;
* by (4.12), `∫_{7r/8}^r (2/s) V_x² ≤ N_x(r) − N_x(7r/8) ≤ N₊ − 1`, so some `σ ∈ (7r/8, r)` has
  `V_x(σ) < 2 N₊ + 1` (`Abstract.RadialData.exists_volumeV_lt`);
* `H_x(r) ≤ K' H_y(5r/8)` (`heightH_le_change_of_point`). -/
theorem frequencyN_change_of_point_le (hx : x ∈ closure {y | 0 < u y}) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall x r ⊆ Ω) (hM : unitBallVolume n ≤ monotonicityM u χ x (r / 4)) {Np : ℝ}
    (hN : frequencyN u χ x r ≤ Np) {y : Rn n} (hy : y ∈ ball x (r / 4)) {s : ℝ} (hs : 0 < s)
    (hsr : s < r / 2) : frequencyN u χ y s ≤ frequencyNChangeConst n Np := by
  rcases le_or_gt (frequencyN u χ y s) 1 with hN1 | hN1
  · exact hN1.trans (one_le_frequencyNChangeConst n Np)
  have hHs : 0 < heightH u y s := by
    rcases (heightH_nonneg u y hs.le).lt_or_eq with hpos | hzero
    · exact hpos
    · rw [frequencyN_of_heightH_eq_zero hzero.symm] at hN1; linarith
  have hMy : unitBallVolume n < monotonicityM u χ y s := (one_lt_frequencyN_iff hHs).1 hN1
  have hyx : dist y x < r / 4 := hy
  set ρ := 5 / 8 * r with hρdef
  have hρ : 0 < ρ := by positivity
  have hclρ : closedBall y ρ ⊆ Ω := fun z hz => hΩ (by
    rw [mem_closedBall] at hz ⊢; linarith [dist_triangle z y x])
  have hsρ : s ≤ ρ := by linarith
  -- `N_y(s) ≤ N_y(ρ) ≤ (N_y + V_y)(ρ)`
  have hmono := (h.monotoneOn_frequencyN_of_heightH_pos (x := y) hs hHs hMy.le hclρ).1
    ⟨le_rfl, hsρ⟩ ⟨hsρ, le_rfl⟩ hsρ
  have hHρ : 0 < heightH u y ρ := h.heightH_pos_of_le hs hsρ hclρ hHs
  have hballρ : ball y ρ ⊆ Ω := ball_subset_closedBall.trans hclρ
  have hNV := h.frequencyN_add_volumeV_eq (x := y) hρ hballρ
  have hV := h.volumeV_nonneg (x := y) hρ hballρ
  -- a radius `σ ∈ (7r/8, r)` with `V_x(σ) < v`
  set Mp := max Np 1 with hMp
  set v := 2 * Mp + 1 with hv
  have hMp1 : 1 ≤ Mp := le_max_right _ _
  have hNpM : Np ≤ Mp := le_max_left _ _
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen hr.le hΩ
  have hr4 : 0 < r / 4 := by positivity
  let d := h.radialData hR' hr4 (by linarith : r / 4 ≤ r) hRR'
  have hHx : ∀ s ∈ Icc (r / 4) r, 0 < d.heightH s := fun s hs' =>
    h.heightH_pos hx (hr4.trans_le hs'.1) ((closedBall_subset_closedBall hs'.2).trans hΩ)
  have h78 : closedBall x (7 / 8 * r) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hΩ
  have hM78 : unitBallVolume n ≤ d.monotonicityM (7 / 8 * r) :=
    hM.trans (h.monotonicityM_le hr4 (by linarith) h78)
  have hN78 : 1 ≤ frequencyN u χ x (7 / 8 * r) :=
    h.one_le_frequencyN hx hr4 hM hΩ ⟨by linarith, by linarith⟩
  have hlog : 1 / 8 ≤ Real.log r - Real.log (7 / 8 * r) := by
    rw [← Real.log_div hr.ne' (by positivity)]
    have e : r / (7 / 8 * r) = 8 / 7 := by field_simp
    rw [e]
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 8 / 7)
    norm_num at this ⊢
    linarith
  obtain ⟨σ, hσ, hVσ⟩ := d.exists_volumeV_lt (t₁ := 7 / 8 * r) (t₂ := r) (by linarith)
    (by linarith) le_rfl (fun s hs' => hHx s ⟨by linarith [hs'.1], hs'.2⟩) hM78 (v := v)
    (by positivity) (by
      change frequencyN u χ x r - frequencyN u χ x (7 / 8 * r) <
        2 * v ^ 2 * (Real.log r - Real.log (7 / 8 * r))
      have hv2 : 4 * Mp < v ^ 2 := by nlinarith
      have hv0 : 0 ≤ v ^ 2 := sq_nonneg v
      nlinarith)
  have hσmem : σ ∈ Icc (r / 4) r := ⟨by linarith [hσ.1], hσ.2.le⟩
  rw [h.radialData_volumeV hR' hr4 _ hRR' hσmem] at hVσ
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hclσ : closedBall x σ ⊆ Ω := (closedBall_subset_closedBall hσ.2.le).trans hΩ
  have hballσ : ball x σ ⊆ Ω := ball_subset_closedBall.trans hclσ
  have hHσ : 0 < heightH u x σ := h.heightH_pos hx hσ0 hclσ
  have hNσ : frequencyN u χ x σ ≤ Mp :=
    ((h.monotoneOn_frequencyN hx hr4 hM hΩ hσmem ⟨by linarith, le_rfl⟩ hσ.2.le).trans hN).trans
      hNpM
  have hN1σ : 1 ≤ frequencyN u χ x σ := h.one_le_frequencyN hx hr4 hM hΩ hσmem
  have hVσ0 : 0 ≤ volumeV u χ x σ := h.volumeV_nonneg hσ0 hballσ
  have hHσr : heightH u x σ ≤ heightH u x r :=
    h.monotoneOn_heightH hx hr4 hM hΩ hσmem ⟨by linarith, le_rfl⟩ hσ.2.le
  -- `∫_{B_σ(x)} |∇u|² ≤ rⁿ H_x(r) (Mp + v)`
  have hNVσ := h.frequencyN_add_volumeV_eq hσ0 hballσ
  set Gx := ∫ z in ball x σ, ‖gradient u z‖ ^ 2 with hGx
  have hGxeq : Gx = σ ^ n * heightH u x σ * (frequencyN u χ x σ + volumeV u χ x σ) := by
    rw [hNVσ]
    field_simp
  have hGx_le : Gx ≤ r ^ n * heightH u x r * (Mp + v) := by
    rw [hGxeq]
    have h1 : σ ^ n * heightH u x σ ≤ r ^ n * heightH u x r :=
      mul_le_mul (pow_le_pow_left₀ hσ0.le hσ.2.le _) hHσr hHσ.le (by positivity)
    have h2 : frequencyN u χ x σ + volumeV u χ x σ ≤ Mp + v := by linarith
    exact mul_le_mul h1 h2 (by linarith)
      (mul_nonneg (pow_nonneg hr.le _) (heightH_nonneg u x hr.le))
  -- `∫_{B_ρ(y)} |∇u|² ≤ ∫_{B_σ(x)} |∇u|²`
  have hsubσ : ball y ρ ⊆ ball x σ := fun z hz => by
    rw [mem_ball] at hz ⊢; linarith [dist_triangle z y x, hσ.1]
  have hGy_le : ∫ z in ball y ρ, ‖gradient u z‖ ^ 2 ≤ Gx :=
    setIntegral_mono_set (h.integrableOn_norm_gradient_sq hballσ)
      (.of_forall fun z => sq_nonneg _) hsubσ.eventuallyLE
  -- `H_x(r) ≤ K' H_y(ρ)`
  have hlowH := h.heightH_le_change_of_point hx hr hΩ hM hN hy
  have hK' := heightHChangeConst'_pos n Np
  have hGy : ∫ z in ball y ρ, ‖gradient u z‖ ^ 2 ≤
      r ^ n * (Mp + v) * heightHChangeConst' n Np * heightH u y ρ := by
    calc ∫ z in ball y ρ, ‖gradient u z‖ ^ 2 ≤ r ^ n * heightH u x r * (Mp + v) :=
          hGy_le.trans hGx_le
      _ = r ^ n * (Mp + v) * heightH u x r := by ring
      _ ≤ r ^ n * (Mp + v) * (heightHChangeConst' n Np * heightH u y ρ) :=
          mul_le_mul_of_nonneg_left hlowH (by positivity)
      _ = _ := by ring
  have hfin : (ρ ^ n)⁻¹ * (∫ z in ball y ρ, ‖gradient u z‖ ^ 2) / heightH u y ρ ≤
      (8 / 5) ^ n * (Mp + v) * heightHChangeConst' n Np := by
    rw [div_le_iff₀ hHρ]
    have e : (ρ ^ n)⁻¹ * r ^ n = (8 / 5) ^ n := by
      rw [hρdef, mul_pow, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), mul_one,
        ← inv_pow]
      norm_num
    calc (ρ ^ n)⁻¹ * (∫ z in ball y ρ, ‖gradient u z‖ ^ 2)
        ≤ (ρ ^ n)⁻¹ * (r ^ n * (Mp + v) * heightHChangeConst' n Np * heightH u y ρ) :=
          mul_le_mul_of_nonneg_left hGy (by positivity)
      _ = (ρ ^ n)⁻¹ * r ^ n * (Mp + v) * heightHChangeConst' n Np * heightH u y ρ := by ring
      _ = _ := by rw [e]
  calc frequencyN u χ y s ≤ frequencyN u χ y ρ := hmono
    _ ≤ frequencyN u χ y ρ + volumeV u χ y ρ := le_add_of_nonneg_right hV
    _ = (ρ ^ n)⁻¹ * (∫ z in ball y ρ, ‖gradient u z‖ ^ 2) / heightH u y ρ := hNV
    _ ≤ (8 / 5) ^ n * (Mp + v) * heightHChangeConst' n Np := hfin
    _ ≤ frequencyNChangeConst n Np := le_max_right _ _

end ChangeOfPoint

end IsVariationalSolution

/-! ### Continuity in the centre (used in the proof of Theorem 6.1) -/

/-- If `B̄_r(x) ⊆ Ω` with `Ω` open and `r ≥ 0`, then `B̄_r(y) ⊆ Ω` for every `y` near `x`. -/
theorem eventually_closedBall_subset {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {x : Rn n} {r : ℝ}
    (hr : 0 ≤ r) (hx : closedBall x r ⊆ Ω) : ∀ᶠ y in 𝓝 x, closedBall y r ⊆ Ω := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall x r).exists_thickening_subset_open hΩ hx
  rw [thickening_closedBall hδ hr] at hsub
  filter_upwards [ball_mem_nhds x hδ] with y hy z hz
  refine hsub ?_
  rw [mem_ball] at hy ⊢
  rw [mem_closedBall] at hz
  linarith [dist_triangle z y x]

/-- `Ω_r = {x : B̄_r(x) ⊆ Ω}` is open. -/
theorem isOpen_setOf_closedBall_subset {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {r : ℝ} (hr : 0 ≤ r) :
    IsOpen {x : Rn n | closedBall x r ⊆ Ω} :=
  isOpen_iff_mem_nhds.2 fun _ hx => eventually_closedBall_subset hΩ hr hx

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- `Ω.indicator (|∇u|² + χ)` is locally integrable. -/
theorem locallyIntegrable_indicator_energy (h : IsVariationalSolution Ω C u χ) :
    LocallyIntegrable (Ω.indicator fun z => ‖gradient u z‖ ^ 2 + χ z) := by
  have e : (Ω.indicator fun z => ‖gradient u z‖ ^ 2 + χ z) =
      fun z => Ω.indicator (fun z => ‖gradient u z‖ ^ 2) z + Ω.indicator χ z := by
    ext z; by_cases hz : z ∈ Ω <;> simp [hz]
  have hm : Measurable (Ω.indicator fun z => ‖gradient u z‖ ^ 2 + χ z) := by
    rw [e]
    exact (((measurable_gradient u).norm.pow_const 2).indicator h.isOpen.measurableSet).add
      h.measurable_chi
  rw [locallyIntegrable_iff]
  intro K hK
  refine IntegrableOn.of_bound hK.measure_lt_top hm.aestronglyMeasurable ((C : ℝ) ^ 2 + 1)
    (.of_forall fun z => ?_)
  by_cases hz : z ∈ Ω
  · rw [indicator_of_mem hz, Real.norm_eq_abs]
    have a1 := h.sq_norm_gradient_le hz
    have a2 := h.abs_chi_le_one hz
    have a3 : 0 ≤ ‖gradient u z‖ ^ 2 := sq_nonneg _
    rw [abs_le] at a2 ⊢
    constructor <;> linarith
  · rw [indicator_of_notMem hz, norm_zero]
    positivity

/-- `y ↦ D_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω`. -/
theorem continuousAt_energyD [NeZero n] (h : IsVariationalSolution Ω C u χ) {r : ℝ} (hr : 0 < r)
    (hx : closedBall x r ⊆ Ω) : ContinuousAt (fun y => energyD u χ y r) x := by
  have hc : ContinuousAt (fun y => (r ^ n)⁻¹ *
      ∫ z in ball y r, Ω.indicator (fun z => ‖gradient u z‖ ^ 2 + χ z) z) x :=
    continuousAt_const.mul
      (continuous_integral_ball h.locallyIntegrable_indicator_energy r).continuousAt
  refine hc.congr ?_
  filter_upwards [eventually_closedBall_subset h.isOpen hr.le hx] with y hy
  simp only [energyD]
  congr 1
  exact setIntegral_congr_fun measurableSet_ball fun z hz =>
    indicator_of_mem (hy (ball_subset_closedBall hz)) _

/-- `y ↦ H_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω`. -/
theorem continuousAt_heightH (h : IsVariationalSolution Ω C u χ) {r : ℝ} (hr : 0 < r)
    (hx : closedBall x r ⊆ Ω) : ContinuousAt (fun y => heightH u y r) x :=
  h.toQ.continuousAt_heightH hr hx

/-- `y ↦ M_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω`. -/
theorem continuousAt_monotonicityM [NeZero n] (h : IsVariationalSolution Ω C u χ) {r : ℝ}
    (hr : 0 < r) (hx : closedBall x r ⊆ Ω) : ContinuousAt (fun y => monotonicityM u χ y r) x :=
  (h.continuousAt_energyD hr hx).sub (h.continuousAt_heightH hr hx)

/-- **Continuity of the frequency in the centre** (used in the proof of Theorem 6.1):
`y ↦ N_y(u; r)` is continuous at `x` when `B̄_r(x) ⊆ Ω` and `H_x(u; r) ≠ 0`. -/
theorem continuousAt_frequencyN [NeZero n] (h : IsVariationalSolution Ω C u χ) {r : ℝ}
    (hr : 0 < r) (hx : closedBall x r ⊆ Ω) (hH : heightH u x r ≠ 0) :
    ContinuousAt (fun y => frequencyN u χ y r) x :=
  ((h.continuousAt_energyD hr hx).sub continuousAt_const).div (h.continuousAt_heightH hr hx) hH

/-- **Continuity of the frequency in the centre**: for fixed `r > 0`,
`y ↦ N_y(u; r)` is continuous on `{y : B̄_r(y) ⊆ Ω, H_y(u; r) > 0}`. -/
theorem continuousOn_frequencyN [NeZero n] (h : IsVariationalSolution Ω C u χ) {r : ℝ}
    (hr : 0 < r) :
    ContinuousOn (fun y => frequencyN u χ y r) {y | closedBall y r ⊆ Ω ∧ 0 < heightH u y r} :=
  fun _ hy => (h.continuousAt_frequencyN hr hy.1 hy.2.ne').continuousWithinAt

end IsVariationalSolution

/-! ### Forms used in Sections 6 and 7 -/

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- **Lemma 4.1** on `(t, R]` (the form restated as
`NaberValtorta.Inputs.frequencyN_monotoneOn`). -/
theorem monotoneOn_frequencyN_Ioc [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ} (ht : 0 < t)
    (hM : unitBallVolume n ≤ monotonicityM u χ x t) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (frequencyN u χ x) (Ioc t R) ∧ ∀ s ∈ Ioc t R, 1 ≤ frequencyN u χ x s :=
  ⟨(h.monotoneOn_frequencyN hx ht hM hΩ).mono Ioc_subset_Icc_self,
    fun _ hs => h.one_le_frequencyN hx ht hM hΩ (Ioc_subset_Icc_self hs)⟩

end IsVariationalSolution

/-- **Lemma 4.6, bound on `N`**, existential form: for every `N₊` there is
`K = K(n, N₊)` such that `N_y(u; s) ≤ K` for `y ∈ B_{r/4}(x)` and `0 < s < r/2`, whenever
`x ∈ closure {u > 0}`, `B̄_r(x) ⊆ Ω`, `M_x(u; r/4) ≥ |B_1|` and `N_x(u; r) ≤ N₊`. This is the
statement of `NaberValtorta.Inputs.frequencyN_change_of_point`. -/
theorem frequencyN_change_of_point (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ K : ℝ, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ),
      IsVariationalSolution Ω C u χ → 0 < r → closedBall x r ⊆ Ω →
      x ∈ closure {y | 0 < u y} → unitBallVolume n ≤ monotonicityM u χ x (r / 4) →
      frequencyN u χ x r ≤ Np → ∀ y ∈ ball x (r / 4), ∀ s, 0 < s → s < r / 2 →
        frequencyN u χ y s ≤ K :=
  ⟨frequencyNChangeConst n Np, fun _ _ _ _ _ _ h hr hΩ hx hM hN _ hy _ hs hsr =>
    h.frequencyN_change_of_point_le hx hr hΩ hM hN hy hs hsr⟩

/-- **Lemma 4.6, bounds on `H`**, existential form: there is `K = K(n, N₊) > 0`
with `K⁻¹ H_x(u; r) ≤ H_y(u; 5r/8) ≤ K H_x(u; r)` for `y ∈ B_{r/4}(x)`, under the hypotheses of
`frequencyN_change_of_point`. The proof of Lemma 4.6 as written ends with
`C H_y(5/8) ≥ H_0(1)`, the reverse of the stated upper bound; both bounds hold and Theorems 6.1
and 6.3 use both. -/
theorem heightH_change_of_point (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ),
      IsVariationalSolution Ω C u χ → 0 < r → closedBall x r ⊆ Ω →
      x ∈ closure {y | 0 < u y} → unitBallVolume n ≤ monotonicityM u χ x (r / 4) →
      frequencyN u χ x r ≤ Np → ∀ y ∈ ball x (r / 4),
        heightH u y (5 / 8 * r) ≤ K * heightH u x r ∧
          heightH u x r ≤ K * heightH u y (5 / 8 * r) := by
  refine ⟨max (heightHChangeConst n) (heightHChangeConst' n Np),
    (heightHChangeConst_pos n).trans_le (le_max_left _ _),
    fun Ω C u χ x r h hr hΩ hx hM hN y hy => ⟨?_, ?_⟩⟩
  · exact (h.heightH_change_of_point_le hr hΩ hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (heightH_nonneg u x hr.le))
  · exact (h.heightH_le_change_of_point hx hr hΩ hM hN hy).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (heightH_nonneg u y (by positivity)))

end InnerVariational
