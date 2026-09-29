/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Concrete
public import InnerVariational.Kernel.BV
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Real.Hom
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.Quantities
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Basic.Polar
public import InnerVariational.Frequency.Abstract
import InnerVariational.Defs.Calculus

/-!
# Frequency input for the renormalized blow-up sequence (Section 5)

The estimates of Section 4 of Kriventsov–Weiss (full reference below), as proved in
`Frequency/Concrete.lean`, applied at the scales `[1/2, 2]` of the standing assumptions of
Section 5: `(u, χ)` is a variational solution on `Ω ⊇ B̄_2`, `0 ∈ closure {u > 0}`,
`M_0(u; 1/2) ≥ |B_1|`, `N_0(u; 2) ≤ N₊`. (We write `M_0(u_k; 1/2)` with the index `k` for each
member of the sequence, where the paper writes `M_0(u; 1/2)`; we also use
`0 ∈ closure {u_k > 0}` and `B̄_2 ⊆ Ω` where the paper writes `0 ∈ {u_k > 0}` and `B_2 ⊆ Ω`.)
These are the inputs to the proofs of Lemma 5.1 and Theorem 5.3 for `v = u / √H_0(u; 1)`.

## Main results

* `IsVariationalSolution.frequencyN_half_le_one_le_two`: `1 ≤ N(1/2) ≤ N(1) ≤ N(2)`.
* `IsVariationalSolution.volumeV_one_le`: Lemma 4.5 at `t = 1`, `r = 2`.
* `IsVariationalSolution.integral_ball_one_norm_gradient_sq_eq`: identity (4.11) at `r = 1`.
* `IsVariationalSolution.integral_annulus_euler_le`: equation (4.13) integrated over
  `A = B_1 \ B̄_{1/2}`, as in the proof of Lemma 5.1.
* `IsVariationalSolution.mul_heightH_le_integral_annulus_sq`: the mass lower bound on `A`, from
  Lemma 4.3 (it replaces the normalization `∫_{∂B_1} v² = 1`, so that no trace is needed).
* `IsVariationalSolution.integral_annulus_sq_mem_Icc`: `∫_A u² / H_0(u; 1)` lies between
  `m / C(N₊)` and `m`, `m = ∫_{1/2}^1 s^{n+1} ds` (the radial mass identity in the limit `N → 1`).
* `IsVariationalSolution.abs_integral_gradVariation_le_volumeV`: the domain-variation defect is
  bounded by `V_0(u; 1)` (used in the proof of Theorem 5.3 before equation (5.15)).
* `gradient_const_mul`: `∇(c u) = c ∇u`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- `∇(c f) = c ∇f`, with no differentiability hypothesis. -/
theorem gradient_const_mul (c : ℝ) (f : Rn n → ℝ) (y : Rn n) :
    gradient (fun z => c * f z) y = c • gradient f y := by
  have e : (fun z => c * f z) = c • f := rfl
  rw [e, gradient, gradient, fderiv_const_smul_field, Pi.smul_apply, map_smulₛₗ]
  simp

theorem closedBall_one_subset_of_two {Ω : Set (Rn n)} (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω) :
    closedBall (0 : Rn n) 1 ⊆ Ω :=
  (closedBall_subset_closedBall (by norm_num)).trans hΩ

/-- `B_1 \ B̄_{1/2}` and `B_1 \ B_{1/2}` differ by the null sphere `∂B_{1/2}`. -/
theorem setIntegral_annulus_closedBall_eq (f : Rn n → ℝ) :
    ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), f y =
      ∫ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2), f y := by
  refine setIntegral_congr_set ((ae_eq_refl _).diff ?_)
  refine ae_eq_set.2 ⟨?_, by simp [diff_eq_empty.2 ball_subset_closedBall]⟩
  rw [closedBall_diff_ball]
  exact Measure.addHaar_sphere_of_ne_zero volume 0 (by norm_num)

namespace IsVariationalSolution

variable [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

section Setting

variable (h : IsVariationalSolution Ω C u χ) (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
  (hcl : (0 : Rn n) ∈ closure {y | 0 < u y})
  (hM : unitBallVolume n ≤ monotonicityM u χ 0 (1 / 2))
include h hΩ hcl hM

omit hM in
/-- `H_0(u; 1) > 0`. -/
theorem heightH_one_pos : 0 < heightH u 0 1 :=
  h.heightH_pos hcl one_pos (closedBall_one_subset_of_two hΩ)

/-- `1 ≤ N(1/2) ≤ N(1) ≤ N(2)` (Lemma 4.1). -/
theorem frequencyN_half_le_one_le_two :
    1 ≤ frequencyN u χ 0 (1 / 2) ∧ frequencyN u χ 0 (1 / 2) ≤ frequencyN u χ 0 1 ∧
      frequencyN u χ 0 1 ≤ frequencyN u χ 0 2 := by
  have hmono := h.monotoneOn_frequencyN hcl (t := 1 / 2) (R := 2) (by norm_num) hM hΩ
  refine ⟨h.one_le_frequencyN hcl (t := 1 / 2) (R := 2) (by norm_num) hM hΩ
    (by norm_num : (1 / 2 : ℝ) ∈ Icc (1 / 2) 2), ?_, ?_⟩
  · exact hmono (by norm_num) (by norm_num) (by norm_num)
  · exact hmono (by norm_num) (by norm_num) (by norm_num)

/-- `M_0(u; 1) ≥ |B_1|`, from `N_0(u; 1) ≥ 1` and `H_0(u; 1) > 0`. -/
theorem unitBallVolume_le_monotonicityM_one : unitBallVolume n ≤ monotonicityM u χ 0 1 := by
  have hH := heightH_one_pos h hΩ hcl
  have h1 : 1 ≤ frequencyN u χ 0 1 :=
    (frequencyN_half_le_one_le_two h hΩ hcl hM).1.trans
      (frequencyN_half_le_one_le_two h hΩ hcl hM).2.1
  rw [frequencyN, le_div_iff₀ hH, one_mul] at h1
  rw [monotonicityM]
  linarith

/-- **Lemma 4.5 at `t = 1`, `r = 2`**: if `N_0(u; 2) < N₊` and `N_0(u; 2) − N_0(u; 1) < δ`, then
`V_0(u; 1) ≤ 2ⁿ C(N₊) √δ`. -/
theorem volumeV_one_le {Np δ : ℝ} (hN : frequencyN u χ 0 2 < Np)
    (hδ : frequencyN u χ 0 2 - frequencyN u χ 0 1 < δ) :
    volumeV u χ 0 1 ≤ 2 ^ n * Abstract.RadialData.doublingConst Np * √δ :=
  h.volumeV_le_sqrt hcl one_pos (by norm_num) (unitBallVolume_le_monotonicityM_one h hΩ hcl hM)
    hΩ hN hδ

omit hcl hM in
/-- `∫_{B_1} u² ≤ H_0(u; 1)`. -/
theorem integral_ball_one_sq_le : ∫ y in ball (0 : Rn n) 1, u y ^ 2 ≤ heightH u 0 1 := by
  have := h.integral_ball_sq_le one_pos (closedBall_one_subset_of_two hΩ)
  simpa using this

omit [NeZero n] hcl hM in
/-- Identity (4.11) at `r = 1`: `∫_{B_1} |∇u|² = (N_0(u; 1) + V_0(u; 1)) H_0(u; 1)`. -/
theorem integral_ball_one_norm_gradient_sq_eq (hH : 0 < heightH u 0 1) :
    ∫ y in ball (0 : Rn n) 1, ‖gradient u y‖ ^ 2 =
      (frequencyN u χ 0 1 + volumeV u χ 0 1) * heightH u 0 1 := by
  rw [h.frequencyN_add_volumeV_eq one_pos (ball_subset_closedBall.trans
    (closedBall_one_subset_of_two hΩ))]
  field_simp
  simp

/-- **Equation (4.13) integrated over `A = B_1 \ B̄_{1/2}`** (as in the proof of Lemma 5.1):
for every `l`,
`∫_A (∇u·y − l u)² ≤ H_0(u; 1) ((N(1) − N(1/2)) + 2 max((N(1) − l)², (N(1/2) − l)²))`. -/
theorem integral_annulus_euler_le (l : ℝ) :
    ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), (⟪gradient u y, y⟫ - l * u y) ^ 2 ≤
      heightH u 0 1 * ((frequencyN u χ 0 1 - frequencyN u χ 0 (1 / 2)) +
        2 * max ((frequencyN u χ 0 1 - l) ^ 2) ((frequencyN u χ 0 (1 / 2) - l) ^ 2)) := by
  have hΩ1 := closedBall_one_subset_of_two hΩ
  have key := h.integral_annulus_sq_inner_gradient_sub_le hcl (t := 1 / 2) (s₁ := 1 / 2)
    (s₂ := 1) (by norm_num) le_rfl (by norm_num) hM hΩ1 l
  simp only [sub_zero, one_pow, one_mul] at key
  refine le_trans ?_ key
  have hint := (h.integrableOn_ball_inner_gradient (x := 0) hΩ1).2.2 l
  simp only [sub_zero] at hint
  refine setIntegral_mono_set (hint.mono_set diff_subset)
    (Eventually.of_forall fun y => sq_nonneg _) ?_
  exact (diff_subset_diff_right ball_subset_closedBall).eventuallyLE

/-- **Mass lower bound on `A`** (from Lemma 4.3): if `N_0(u; 1) ≤ N₊` with `N₊ > 1`, then
`(1/4) (3/4)^{n+1} H_0(u; 1) / C(N₊) ≤ ∫_A u²`. -/
theorem mul_heightH_le_integral_annulus_sq {Np : ℝ} (hNp : 1 < Np)
    (hN : frequencyN u χ 0 1 ≤ Np) :
    1 / 4 * ((3 / 4) ^ (n + 1) * heightH u 0 1 / Abstract.RadialData.doublingConst Np) ≤
      ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), u y ^ 2 := by
  have hΩ1 := closedBall_one_subset_of_two hΩ
  have hK := Abstract.RadialData.doublingConst_pos Np
  have key := h.mul_le_integral_annulus_sq (x := 0) (ρ := 3 / 4) (ρ' := 1)
    (c := (3 / 4) ^ (n + 1) * heightH u 0 1 / Abstract.RadialData.doublingConst Np)
    (by norm_num) (by norm_num) hΩ1 (fun s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      have hd := (h.heightH_doubling hcl (t := 1 / 2) (r := 1) (by norm_num) (by norm_num)
        (by norm_num) hM hΩ1 hNp hN (s := s) ⟨by linarith [hs.1], hs.2⟩).2
      have e : sphereIntegral (fun y => u y ^ 2) 0 s = s ^ (n + 1) * heightH u 0 s := by
        rw [heightH, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs0.ne'), one_mul]
      rw [e, div_le_iff₀ hK]
      have hH0 : 0 ≤ heightH u 0 s := heightH_nonneg u 0 hs0.le
      calc (3 / 4) ^ (n + 1) * heightH u 0 1
          ≤ s ^ (n + 1) * (Abstract.RadialData.doublingConst Np * heightH u 0 s) :=
            mul_le_mul (pow_le_pow_left₀ (by norm_num) hs.1 _) hd
              (heightH_nonneg u 0 zero_le_one) (by positivity)
        _ = s ^ (n + 1) * heightH u 0 s * Abstract.RadialData.doublingConst Np := by ring)
  norm_num at key ⊢
  refine key.trans (setIntegral_mono_set ?_ (Eventually.of_forall fun y => sq_nonneg _) ?_)
  · exact (h.integrableOn_sq_of_closedBall hΩ1).mono_set diff_subset
  · refine (diff_subset_diff_right fun y hy => ?_).eventuallyLE
    rw [mem_closedBall_zero_iff] at hy
    rw [mem_ball_zero_iff]
    linarith

/-- **Radial mass bounds on `A = B_1 \ B̄_{1/2}`** (Lemma 4.3): if `N_0(u; 1) ≤ N₊` with `N₊ > 1`,
then `H_0(u; 1) m / C(N₊) ≤ ∫_A u² ≤ H_0(u; 1) m`, where `m = ∫_{1/2}^1 s^{n+1} ds`. Since
`C(N₊) → 1` as `N₊ → 1`, this gives the radial mass identity in the limit `N → 1`:
`∫_A u² / H_0(u; 1) → m`. It replaces the normalization `∫_{∂B_1} v² = 1` of Lemma 5.1. -/
theorem integral_annulus_sq_mem_Icc {Np : ℝ} (hNp : 1 < Np) (hN : frequencyN u χ 0 1 ≤ Np) :
    heightH u 0 1 * (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)) / Abstract.RadialData.doublingConst Np ≤
      ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), u y ^ 2 ∧
    ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), u y ^ 2 ≤
      heightH u 0 1 * ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) := by
  have hΩ1 := closedBall_one_subset_of_two hΩ
  have hK := Abstract.RadialData.doublingConst_pos Np
  have hint := h.integrableOn_sq_of_closedBall hΩ1
  have hI := integral_ball_diff_ball (x := (0 : Rn n)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hint
  have hJ : ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), u y ^ 2 =
      ∫ s in (1 / 2 : ℝ)..1, sphereIntegral (fun y => u y ^ 2) 0 s :=
    (setIntegral_annulus_closedBall_eq _).trans hI
  rw [hJ]
  have hII : IntervalIntegrable (sphereIntegral (fun y => u y ^ 2) 0) volume (1 / 2) 1 :=
    (intervalIntegrable_sphereIntegral zero_le_one hint).mono_set (by
      rw [uIcc_of_le (by norm_num), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have hpow : IntervalIntegrable (fun s : ℝ => s ^ (n + 1)) volume (1 / 2) 1 :=
    (continuous_pow _).intervalIntegrable _ _
  have he : ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      sphereIntegral (fun y => u y ^ 2) 0 s = s ^ (n + 1) * heightH u 0 s := fun s hs => by
    have hs0 : 0 < s := by linarith [hs.1]
    rw [heightH, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs0.ne'), one_mul]
  have hd : ∀ s ∈ Icc (1 / 2 : ℝ) 1, heightH u 0 s ≤ heightH u 0 1 ∧
      heightH u 0 1 ≤ Abstract.RadialData.doublingConst Np * heightH u 0 s := fun s hs =>
    h.heightH_doubling hcl (t := 1 / 2) (r := 1) (by norm_num) (by norm_num) (by norm_num) hM
      hΩ1 hNp hN hs
  constructor
  · calc heightH u 0 1 * (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)) /
          Abstract.RadialData.doublingConst Np
        = ∫ s in (1 / 2 : ℝ)..1,
            heightH u 0 1 / Abstract.RadialData.doublingConst Np * s ^ (n + 1) := by
          rw [intervalIntegral.integral_const_mul]
          ring
      _ ≤ ∫ s in (1 / 2 : ℝ)..1, sphereIntegral (fun y => u y ^ 2) 0 s := by
          refine intervalIntegral.integral_mono_on (by norm_num) (hpow.const_mul _) hII
            fun s hs => ?_
          rw [he s hs]
          have hs0 : 0 ≤ s ^ (n + 1) := pow_nonneg (by linarith [hs.1]) _
          have h1 : heightH u 0 1 / Abstract.RadialData.doublingConst Np ≤ heightH u 0 s := by
            rw [div_le_iff₀ hK, mul_comm]
            exact (hd s hs).2
          calc heightH u 0 1 / Abstract.RadialData.doublingConst Np * s ^ (n + 1)
              ≤ heightH u 0 s * s ^ (n + 1) := mul_le_mul_of_nonneg_right h1 hs0
            _ = s ^ (n + 1) * heightH u 0 s := mul_comm _ _
  · calc ∫ s in (1 / 2 : ℝ)..1, sphereIntegral (fun y => u y ^ 2) 0 s
        ≤ ∫ s in (1 / 2 : ℝ)..1, heightH u 0 1 * s ^ (n + 1) := by
          refine intervalIntegral.integral_mono_on (by norm_num) hII (hpow.const_mul _)
            fun s hs => ?_
          rw [he s hs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hd s hs).1 (pow_nonneg (by linarith [hs.1]) _)
      _ = heightH u 0 1 * ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) :=
          intervalIntegral.integral_const_mul _ _

omit [NeZero n] hcl hM in
/-- **The domain-variation defect is controlled by `V`** (the step "using that
`V_0(u_k; 1) → 0`" in the proof of Theorem 5.3, before equation (5.15)). For a Lipschitz test
field `ξ` supported in `B_1` with Lipschitz constant `D`,
`|∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)| ≤ n D V_0(u; 1) H_0(u; 1)`. The proof writes the quadratic part
as `−∫ χ div ξ = ∫ (1 − χ) div ξ`, using `∫ div ξ = 0`. -/
theorem abs_integral_gradVariation_le_volumeV (hH : 0 < heightH u 0 1) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField (ball 0 1) ξ) {D : ℝ≥0} (hD : LipschitzWith D ξ) :
    |∫ y, Kernel.gradVariation u ξ y| ≤ n * D * (volumeV u χ 0 1 * heightH u 0 1) := by
  have hB1 : ball (0 : Rn n) 1 ⊆ Ω := ball_subset_closedBall.trans (closedBall_one_subset_of_two hΩ)
  have hξΩ : IsLipTestField Ω ξ := hξ.mono hB1
  have hsupp : ∀ y ∉ ball (0 : Rn n) 1, divergence ξ y = 0 := fun y hy =>
    divergence_eq_zero_of_notMem_tsupport fun h' => hy (hξ.2.2 h')
  have hdivB1 : IntegrableOn (divergence ξ) (ball (0 : Rn n) 1) :=
    (Kernel.integrable_divergence hD hξ.2.1).integrableOn
  have hχint : IntegrableOn χ (ball (0 : Rn n) 1) := h.integrableOn_chi hB1
  have hdm : AEStronglyMeasurable (divergence ξ) (volume.restrict (ball (0 : Rn n) 1)) :=
    (Kernel.measurable_divergence ξ).aestronglyMeasurable
  have hdb : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), ‖divergence ξ y‖ ≤ n * D :=
    Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact Kernel.abs_divergence_le hD y
  have hχdiv : IntegrableOn (fun y => χ y * divergence ξ y) (ball (0 : Rn n) 1) :=
    hχint.mul_bdd hdm hdb
  have hχ1 : IntegrableOn (fun y => 1 - χ y) (ball (0 : Rn n) 1) :=
    (integrableOn_const measure_ball_lt_top.ne).sub hχint
  have hI : IntegrableOn (fun y => (1 - χ y) * divergence ξ y) (ball (0 : Rn n) 1) :=
    hχ1.mul_bdd hdm hdb
  -- `∫ gradVariation = ∫_{B_1} (1 − χ) div ξ`.
  have e1 : ∫ y, Kernel.gradVariation u ξ y =
      ∫ y in ball (0 : Rn n) 1, (1 - χ y) * divergence ξ y := by
    have h1 := h.integral_chi_mul_divergence_eq hξΩ
    have h2 := Kernel.integral_divergence_eq_zero isOpen_ball hξ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Rn n) 1)
      (fun y hy => by rw [hsupp y hy, mul_zero])] at h1
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Rn n) 1) hsupp] at h2
    have e2 : ∫ y in ball (0 : Rn n) 1, (1 - χ y) * divergence ξ y =
        (∫ y in ball (0 : Rn n) 1, divergence ξ y) -
          ∫ y in ball (0 : Rn n) 1, χ y * divergence ξ y := by
      rw [← integral_sub hdivB1 hχdiv]
      congr 1
      funext y
      ring
    rw [e2, h1, h2]
    ring
  rw [e1]
  have hbd : ∀ y ∈ ball (0 : Rn n) 1, |(1 - χ y) * divergence ξ y| ≤ n * D * (1 - χ y) := by
    intro y hy
    have h01 : 0 ≤ 1 - χ y := sub_nonneg.2 (abs_le.1 (h.abs_chi_le_one (hB1 hy))).2
    rw [abs_mul, abs_of_nonneg h01, mul_comm]
    exact mul_le_mul_of_nonneg_right (Kernel.abs_divergence_le hD y) h01
  calc |∫ y in ball (0 : Rn n) 1, (1 - χ y) * divergence ξ y|
      ≤ ∫ y in ball (0 : Rn n) 1, |(1 - χ y) * divergence ξ y| := abs_integral_le_integral_abs
    _ ≤ ∫ y in ball (0 : Rn n) 1, n * D * (1 - χ y) :=
        setIntegral_mono_on hI.abs (hχ1.const_mul _) measurableSet_ball hbd
    _ = n * D * ∫ y in ball (0 : Rn n) 1, (1 - χ y) := integral_const_mul _ _
    _ = n * D * (volumeV u χ 0 1 * heightH u 0 1) := by
        rw [volumeV]
        field_simp
        simp

end Setting

end IsVariationalSolution

end InnerVariational
