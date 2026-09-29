/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.ConcreteQ.ChangeOfPoint
public import InnerVariational.Kernel.BV
import Mathlib.Data.Real.Hom
import InnerVariational.Defs.Calculus
public import InnerVariational.Kernel.VariationalQ
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InnerVariational.Basic.Polar

/-!
# Frequency input for the renormalized blow-up sequence with a Lipschitz coefficient

The estimates of Section 4 with a Lipschitz coefficient (`Frequency/ConcreteQ/`), applied at the
scales `[1/2, 2]` of the standing assumptions of Section 5: `(u, χ)` is a variational solution for
a coefficient `Q` with `QBounds Ω Q L c C'` on `Ω ⊇ B̄_2`, `κ = 2 C' L / c²` with `2κ ≤ 1/2`,
`0 ∈ closure {u > 0}`, `Z_0(u; 1/2) ≥ 0`, `Ñ_0(u; 2) ≤ N₊`. These are the inputs to the proofs of
Lemma 5.1 and Theorem 5.3 for `v = u / √H_0(u; 1)`.

Compared with the constant-coefficient file `Blowup/Renormalization.lean`, every estimate carries
an error controlled by `κ`: the factor `e^{κ²/8}` in the comparison of `H` at different radii, the
shift `κ²/2` between `Ñ` and `N`, and the term `κ M V H` in the domain-variation defect. Along a
sequence with frequency pinching `Ñ(2) − Ñ(1/2) → 0` these errors vanish, since
`(15/32) κ² ≤ Ñ(2) − Ñ(1/2)` (`weissKappa_sq_le_modFrequencyN_sub`).

## Main results

* `IsVariationalSolutionQ.modFrequencyN_half_le_one_le_two`: `1 ≤ Ñ(1/2) ≤ Ñ(1) ≤ Ñ(2)`.
* `IsVariationalSolutionQ.weissKappa_sq_le_modFrequencyN_sub`: `(15/32) κ² ≤ Ñ(2) − Ñ(1/2)`.
* `IsVariationalSolutionQ.weightedVolumeV_one_le`: Lemma 4.5 at `t = 1`, `r = 2`.
* `IsVariationalSolutionQ.integral_ball_one_norm_gradient_sq_eq`: identity (4.11) at `r = 1`.
* `IsVariationalSolutionQ.integral_annulus_euler_le`: (4.13) integrated over
  `A = B_1 \ B̄_{1/2}`.
* `IsVariationalSolutionQ.mul_heightH_le_integral_annulus_sq`,
  `IsVariationalSolutionQ.integral_annulus_sq_mem_Icc`: mass bounds on `A`.
* `IsVariationalSolutionQ.abs_integral_gradVariation_le_weightedVolumeV`: the domain-variation
  defect `|∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)| ≤ (n D + κ M) V_0(1) H_0(1)`.

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

namespace IsVariationalSolutionQ

variable [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

section Setting

variable (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
  (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω) (hκ : weissKappa L c C' * 2 ≤ 1 / 2)
  (hcl : (0 : Rn n) ∈ closure {y | 0 < u y})
  (hZ : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ 0 (1 / 2))
include hQ h hΩ hκ hcl hZ

omit hκ hZ in
/-- `H_0(u; 1) > 0`. -/
theorem heightH_one_pos : 0 < heightH u 0 1 :=
  h.heightH_pos hQ hcl one_pos (closedBall_one_subset_of_two hΩ)

omit [NeZero n] h hκ hcl hZ in
theorem weissKappa_nonneg' : 0 ≤ weissKappa L c C' :=
  hQ.weissKappa_nonneg (hΩ (mem_closedBall_self zero_le_two))

omit [NeZero n] h hcl hZ in
theorem weissKappa_mul_one_le : weissKappa L c C' * 1 ≤ 1 / 2 := by
  have := weissKappa_nonneg' hQ hΩ
  linarith

/-- `1 ≤ Ñ(1/2) ≤ Ñ(1) ≤ Ñ(2)` (Lemma 4.1). -/
theorem modFrequencyN_half_le_one_le_two :
    1 ≤ modFrequencyN (weissKappa L c C') Q u χ 0 (1 / 2) ∧
      modFrequencyN (weissKappa L c C') Q u χ 0 (1 / 2) ≤
        modFrequencyN (weissKappa L c C') Q u χ 0 1 ∧
      modFrequencyN (weissKappa L c C') Q u χ 0 1 ≤
        modFrequencyN (weissKappa L c C') Q u χ 0 2 := by
  have hmono := h.monotoneOn_modFrequencyN hQ hcl (t := 1 / 2) (R := 2) (by norm_num) hZ hκ hΩ
  refine ⟨h.one_le_modFrequencyN hQ hcl (t := 1 / 2) (R := 2) (by norm_num) hZ hκ hΩ
    (by norm_num : (1 / 2 : ℝ) ∈ Icc (1 / 2) 2), ?_, ?_⟩
  · exact hmono (by norm_num) (by norm_num) (by norm_num)
  · exact hmono (by norm_num) (by norm_num) (by norm_num)

/-- `Z_0(u; 1) ≥ 0`. -/
theorem modMonotonicityM_one_nonneg : 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ 0 1 :=
  h.modMonotonicityM_nonneg hQ hcl (t := 1 / 2) (R := 2) (by norm_num) hZ hκ hΩ
    (by norm_num : (1 : ℝ) ∈ Icc (1 / 2) 2)

/-- `N_0(u; s) ≥ 1 − κ² s² / 8` for `s ∈ [1/2, 2]`. -/
theorem one_sub_le_weightedFrequencyN_of_mem {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 2) :
    1 - weissKappa L c C' ^ 2 * s ^ 2 / 8 ≤ weightedFrequencyN Q u χ 0 s :=
  h.one_sub_le_weightedFrequencyN hQ hcl (t := 1 / 2) (R := 2) (by norm_num) hZ hκ hΩ hs

/-- **The pinching controls `κ`**: `(15/32) κ² ≤ Ñ(2) − Ñ(1/2)`. -/
theorem weissKappa_sq_le_modFrequencyN_sub :
    15 / 32 * weissKappa L c C' ^ 2 ≤
      modFrequencyN (weissKappa L c C') Q u χ 0 2 -
        modFrequencyN (weissKappa L c C') Q u χ 0 (1 / 2) := by
  have := h.sq_mul_sub_sq_le_modFrequencyN_sub hQ hcl (t := 1 / 2) (R := 2) (by norm_num) hZ hκ
    hΩ (s₁ := 1 / 2) (s₂ := 2) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- **Lemma 4.5 at `t = 1`, `r = 2`**: if `Ñ_0(u; 2) < N₊` and `Ñ_0(u; 2) − Ñ_0(u; 1) < δ`, then
`V_0(u; 1) ≤ 2ⁿ C(N₊) √(3δ)`. -/
theorem weightedVolumeV_one_le {Np δ : ℝ} (hN : modFrequencyN (weissKappa L c C') Q u χ 0 2 < Np)
    (hδ : modFrequencyN (weissKappa L c C') Q u χ 0 2 -
      modFrequencyN (weissKappa L c C') Q u χ 0 1 < δ) :
    weightedVolumeV Q u χ 0 1 ≤ 2 ^ n * Abstract.RadialData.doublingConst Np * √(3 * δ) :=
  h.weightedVolumeV_le_sqrt hQ hcl one_pos (by norm_num)
    (modMonotonicityM_one_nonneg hQ h hΩ hκ hcl hZ) hκ hΩ hN hδ

omit hκ hcl hZ in
/-- `∫_{B_1} u² ≤ H_0(u; 1)`. -/
theorem integral_ball_one_sq_le : ∫ y in ball (0 : Rn n) 1, u y ^ 2 ≤ heightH u 0 1 := by
  have := h.integral_ball_sq_le hQ one_pos (closedBall_one_subset_of_two hΩ)
  simpa using this

omit [NeZero n] hκ hcl hZ in
/-- Identity (4.11) at `r = 1`: `∫_{B_1} |∇u|² = (N_0(u; 1) + V_0(u; 1)) H_0(u; 1)`. -/
theorem integral_ball_one_norm_gradient_sq_eq (hH : 0 < heightH u 0 1) :
    ∫ y in ball (0 : Rn n) 1, ‖gradient u y‖ ^ 2 =
      (weightedFrequencyN Q u χ 0 1 + weightedVolumeV Q u χ 0 1) * heightH u 0 1 := by
  rw [h.weightedFrequencyN_add_weightedVolumeV hQ (ball_subset_closedBall.trans
    (closedBall_one_subset_of_two hΩ))]
  field_simp
  simp

/-- **Equation (4.13) integrated over `A = B_1 \ B̄_{1/2}`**: for every `l`,
`∫_A (∇u·y − l u)² ≤ e^{κ²/8} H_0(u; 1) (2 (Ñ(1) − Ñ(1/2)) +
  2 max((Ñ(1) − l)², (Ñ(1/2) − κ²/2 − l)²))`. -/
theorem integral_annulus_euler_le (l : ℝ) :
    ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), (⟪gradient u y, y⟫ - l * u y) ^ 2 ≤
      Real.exp (weissKappa L c C' ^ 2 / 8) * heightH u 0 1 *
        (2 * (modFrequencyN (weissKappa L c C') Q u χ 0 1 -
            modFrequencyN (weissKappa L c C') Q u χ 0 (1 / 2)) +
          2 * max ((modFrequencyN (weissKappa L c C') Q u χ 0 1 - l) ^ 2)
            ((modFrequencyN (weissKappa L c C') Q u χ 0 (1 / 2) -
              weissKappa L c C' ^ 2 / 2 - l) ^ 2)) := by
  have hΩ1 := closedBall_one_subset_of_two hΩ
  have key := h.integral_annulus_sq_inner_gradient_sub_le hQ hcl (t := 1 / 2) (s₁ := 1 / 2)
    (s₂ := 1) (by norm_num) le_rfl (by norm_num) hZ (weissKappa_mul_one_le hQ hΩ hκ) hΩ1 l
  simp only [sub_zero, one_pow, one_mul, mul_one] at key
  refine le_trans ?_ key
  have hint := (h.integrableOn_ball_inner_gradient (x := 0) hΩ1).2.2 l
  simp only [sub_zero] at hint
  refine setIntegral_mono_set (hint.mono_set diff_subset)
    (Eventually.of_forall fun y => sq_nonneg _) ?_
  exact (diff_subset_diff_right ball_subset_closedBall).eventuallyLE

/-- **Mass lower bound on `A`** (from Lemma 4.3): if `Ñ_0(u; 1) ≤ N₊` with `N₊ > 1`, then
`(1/4) (3/4)^{n+1} H_0(u; 1) / C(N₊) ≤ ∫_A u²`. -/
theorem mul_heightH_le_integral_annulus_sq {Np : ℝ} (hNp : 1 < Np)
    (hN : modFrequencyN (weissKappa L c C') Q u χ 0 1 ≤ Np) :
    1 / 4 * ((3 / 4) ^ (n + 1) * heightH u 0 1 / Abstract.RadialData.doublingConst Np) ≤
      ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), u y ^ 2 := by
  have hΩ1 := closedBall_one_subset_of_two hΩ
  have hK := Abstract.RadialData.doublingConst_pos Np
  have key := h.mul_le_integral_annulus_sq (x := 0) (ρ := 3 / 4) (ρ' := 1)
    (c₀ := (3 / 4) ^ (n + 1) * heightH u 0 1 / Abstract.RadialData.doublingConst Np)
    (by norm_num) (by norm_num) hΩ1 (fun s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      have hd := (h.heightH_doubling hQ hcl (t := 1 / 2) (r := 1) (by norm_num) (by norm_num)
        (by norm_num) hZ (weissKappa_mul_one_le hQ hΩ hκ) hΩ1 hNp hN (s := s)
        ⟨by linarith [hs.1], hs.2⟩).2
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

/-- **Radial mass bounds on `A = B_1 \ B̄_{1/2}`** (Lemma 4.3): if `Ñ_0(u; 1) ≤ N₊` with
`N₊ > 1`, then `H_0(u; 1) m / C(N₊) ≤ ∫_A u² ≤ e^{κ²/8} H_0(u; 1) m`, where
`m = ∫_{1/2}^1 s^{n+1} ds`. -/
theorem integral_annulus_sq_mem_Icc {Np : ℝ} (hNp : 1 < Np)
    (hN : modFrequencyN (weissKappa L c C') Q u χ 0 1 ≤ Np) :
    heightH u 0 1 * (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)) / Abstract.RadialData.doublingConst Np ≤
      ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), u y ^ 2 ∧
    ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), u y ^ 2 ≤
      Real.exp (weissKappa L c C' ^ 2 / 8) * heightH u 0 1 *
        ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) := by
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
  have hd : ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      heightH u 0 s ≤ Real.exp (weissKappa L c C' ^ 2 / 8) * heightH u 0 1 ∧
      heightH u 0 1 ≤ Abstract.RadialData.doublingConst Np * heightH u 0 s := fun s hs => by
    have := h.heightH_doubling hQ hcl (t := 1 / 2) (r := 1) (by norm_num) (by norm_num)
      (by norm_num) hZ (weissKappa_mul_one_le hQ hΩ hκ) hΩ1 hNp hN hs
    simpa only [one_pow, mul_one] using this
  have hE : 0 ≤ Real.exp (weissKappa L c C' ^ 2 / 8) := (Real.exp_pos _).le
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
        ≤ ∫ s in (1 / 2 : ℝ)..1,
            Real.exp (weissKappa L c C' ^ 2 / 8) * heightH u 0 1 * s ^ (n + 1) := by
          refine intervalIntegral.integral_mono_on (by norm_num) hII (hpow.const_mul _)
            fun s hs => ?_
          rw [he s hs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hd s hs).1 (pow_nonneg (by linarith [hs.1]) _)
      _ = Real.exp (weissKappa L c C' ^ 2 / 8) * heightH u 0 1 *
            ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) :=
          intervalIntegral.integral_const_mul _ _

omit [NeZero n] hκ hcl hZ in
/-- **The domain-variation defect is controlled by `V`**, with a Lipschitz coefficient. For a
Lipschitz test field `ξ` supported in `B_1` with Lipschitz constant `D` and `|ξ| ≤ M`,
`|∫ (|∇u|² div ξ − 2 ∇u·Dξ∇u)| ≤ (n D + κ M) V_0(u; 1) H_0(u; 1)`. The proof writes the
quadratic part as `∫ (1 − χ)(Q² div ξ + ∇(Q²)·ξ)` and uses `|∇(Q²)| ≤ 2 C' L = κ c² ≤ κ Q²`. -/
theorem abs_integral_gradVariation_le_weightedVolumeV (hH : 0 < heightH u 0 1)
    {ξ : Rn n → Rn n} (hξ : IsLipTestField (ball 0 1) ξ) {D : ℝ≥0} (hD : LipschitzWith D ξ)
    {M : ℝ} (hM : ∀ y, ‖ξ y‖ ≤ M) :
    |∫ y, Kernel.gradVariation u ξ y| ≤
      (n * D + weissKappa L c C' * M) * (weightedVolumeV Q u χ 0 1 * heightH u 0 1) := by
  have hB1 : ball (0 : Rn n) 1 ⊆ Ω := ball_subset_closedBall.trans (closedBall_one_subset_of_two hΩ)
  have hξΩ : IsLipTestField Ω ξ := hξ.mono hB1
  have h0Ω : (0 : Rn n) ∈ Ω := hB1 (mem_ball_self one_pos)
  have hk : 0 ≤ weissKappa L c C' := hQ.weissKappa_nonneg h0Ω
  have hc2 : 0 < c ^ 2 := pow_pos hQ.pos 2
  set F : Rn n → ℝ := fun y => (1 - χ y) * (Q y ^ 2 * divergence ξ y +
    fderiv ℝ (fun z => Q z ^ 2) y (ξ y)) with hF
  have hsupp : ∀ y ∉ ball (0 : Rn n) 1, F y = 0 := fun y hy => by
    rw [hF]
    dsimp only
    rw [QBounds.sq_mul_divergence_add_eq_zero_of_notMem ξ (fun h' => hy (hξ.2.2 h')), mul_zero]
  have e1 : ∫ y, Kernel.gradVariation u ξ y = ∫ y in ball (0 : Rn n) 1, F y := by
    rw [h.integral_gradVariation_eq hQ hξΩ,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Rn n) 1) hsupp]
  have hW := h.integrableOn_weight (x := 0) hQ hB1
  have hM0 : ∀ y, 0 ≤ M := fun y => (norm_nonneg _).trans (hM y)
  have hbd : ∀ y ∈ ball (0 : Rn n) 1,
      |F y| ≤ (n * D + weissKappa L c C' * M) * (Q y ^ 2 * (1 - χ y)) := by
    intro y hy
    have hyΩ := hB1 hy
    have h01 : 0 ≤ 1 - χ y := h.one_sub_chi_nonneg hyΩ
    have hQ2 : c ^ 2 ≤ Q y ^ 2 := hQ.sq_le_sq hyΩ
    have hC' := hQ.nonneg_of_mem hyΩ
    have hdiv := Kernel.abs_divergence_le hD y
    have hder := hQ.abs_fderiv_sq_apply_le h.isOpen hyΩ (ξ y)
    have hκQ : 2 * C' * L ≤ weissKappa L c C' * Q y ^ 2 := by
      rw [weissKappa]
      rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
      exact mul_le_mul_of_nonneg_left hQ2 (by positivity)
    rw [hF]
    dsimp only
    rw [abs_mul, abs_of_nonneg h01]
    have h2 : |Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y)| ≤
        (n * D + weissKappa L c C' * M) * Q y ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      have h3 : 2 * C' * L * ‖ξ y‖ ≤ weissKappa L c C' * Q y ^ 2 * M :=
        mul_le_mul hκQ (hM y) (norm_nonneg _) (by positivity)
      have h4 : Q y ^ 2 * |divergence ξ y| ≤ Q y ^ 2 * (n * D) :=
        mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
      nlinarith
    calc (1 - χ y) * |Q y ^ 2 * divergence ξ y + fderiv ℝ (fun z => Q z ^ 2) y (ξ y)|
        ≤ (1 - χ y) * ((n * D + weissKappa L c C' * M) * Q y ^ 2) :=
          mul_le_mul_of_nonneg_left h2 h01
      _ = (n * D + weissKappa L c C' * M) * (Q y ^ 2 * (1 - χ y)) := by ring
  have hFint : IntegrableOn F (ball (0 : Rn n) 1) := by
    have hI := hQ.integrable_sq_mul_divergence_add h.isOpen hξΩ
    have hχ := h.integrable_chi_mul_sq_mul_divergence_add hQ hξΩ
    refine (hI.sub hχ).integrableOn.congr_fun (fun y _ => ?_) measurableSet_ball
    simp only [hF, Pi.sub_apply]
    ring
  have hVH : weightedVolumeV Q u χ 0 1 * heightH u 0 1 =
      ∫ y in ball (0 : Rn n) 1, Q y ^ 2 * (1 - χ y) := by
    rw [weightedVolumeV, div_mul_cancel₀ _ hH.ne']
    simp
  rw [e1, hVH, ← integral_const_mul]
  calc |∫ y in ball (0 : Rn n) 1, F y| ≤ ∫ y in ball (0 : Rn n) 1, |F y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y in ball (0 : Rn n) 1, (n * D + weissKappa L c C' * M) * (Q y ^ 2 * (1 - χ y)) :=
        setIntegral_mono_on hFint.abs (hW.const_mul _) measurableSet_ball hbd

end Setting

end IsVariationalSolutionQ

end InnerVariational
