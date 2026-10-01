/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.SphereIntegral
public import InnerVariational.Defs.Quantities
public import InnerVariational.Homogeneity.RayCalculus

/-!
# Scaling of the frequency quantities under the one-homogeneous rescaling

For `ρ > 0` and the rescaling `ũ = u_{a,ρ}`, `ũ(y) = u(a + ρ y)/ρ`, `χ̃(y) = χ(a + ρ y)`
(equation (3.6) of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131, numbering of arXiv v2), every quantity of
Section 4 of the paper at the origin and radius `s` is the quantity of `u` at
`a` and radius `ρ s`:

* `energyD_oneHomRescale`: `D_0(ũ; s) = D_a(u; ρ s)`;
* `heightH_oneHomRescale`: `H_0(ũ; s) = H_a(u; ρ s)`;
* `monotonicityM_oneHomRescale`, `frequencyN_oneHomRescale`: the same for `M` and `N`.

Also `zero_mem_closure_oneHomRescale_iff` (the free boundary condition) and
`setIntegral_tangential_oneHomRescale`, the change of variables for the tangential energy that
appears in the direction-free form of Theorem 5.3 (`approx1D_limit_frequency_eq_one`). These are
used in the proof of Theorem 6.3 to apply Theorem 5.3 at the scale `ρ = 10 r` (we use `10 r`
rather than the paper's `18 r`, since the frequency pinching is available on `[r, 20r]`).
-/

open MeasureTheory Metric Set Filter
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Dichotomy

variable {n : ℕ}

theorem oneHomRescale_eq (u : Rn n → ℝ) (a : Rn n) (ρ : ℝ) :
    oneHomRescale u a ρ = fun y => u (a + ρ • y) / ρ := rfl

theorem gradient_oneHomRescale (u : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : ρ ≠ 0) (y : Rn n) :
    gradient (oneHomRescale u a ρ) y = gradient u (a + ρ • y) := by
  rw [oneHomRescale_eq]
  exact gradient_comp_add_smul_div u a hρ y

/-- `D_0(u_{a,ρ}; s) = D_a(u; ρ s)`. -/
theorem energyD_oneHomRescale (u χ : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    energyD (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s = energyD u χ a (ρ * s) := by
  simp only [energyD]
  have h := setIntegral_ball_comp_add_smul (fun w => ‖gradient u w‖ ^ 2 + χ w) a 0 hρ s
  simp only [smul_zero, add_zero] at h
  have e : ∫ y in ball (0 : Rn n) s,
      (‖gradient (oneHomRescale u a ρ) y‖ ^ 2 + chiRescale χ a ρ y) =
      ∫ y in ball (0 : Rn n) s, (‖gradient u (a + ρ • y)‖ ^ 2 + χ (a + ρ • y)) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [gradient_oneHomRescale u a hρ.ne', chiRescale_apply]
  rw [e, h, mul_pow, mul_inv]
  ring

/-- `H_0(u_{a,ρ}; s) = H_a(u; ρ s)`. -/
theorem heightH_oneHomRescale [NeZero n] (u : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ)
    (s : ℝ) : heightH (oneHomRescale u a ρ) 0 s = heightH u a (ρ * s) := by
  simp only [heightH]
  have e : sphereIntegral (fun y => oneHomRescale u a ρ y ^ 2) 0 s =
      (ρ ^ 2)⁻¹ * sphereIntegral (fun y => u (a + ρ • y) ^ 2) 0 s := by
    rw [← sphereIntegral_const_mul]
    congr 1
    ext y
    rw [oneHomRescale_apply, div_pow, div_eq_inv_mul]
  rw [e, sphereIntegral_comp_add_smul' (fun w => u w ^ 2) a hρ.ne' s]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  simp only [Nat.add_sub_cancel]
  have hpow : (ρ * s) ^ (m + 1 + 1) = s ^ (m + 1 + 1) * (ρ ^ 2 * ρ ^ m) := by ring
  rw [hpow, mul_inv, mul_inv]
  ring

/-- `M_0(u_{a,ρ}; s) = M_a(u; ρ s)`. -/
theorem monotonicityM_oneHomRescale [NeZero n] (u χ : Rn n → ℝ) (a : Rn n) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) :
    monotonicityM (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s = monotonicityM u χ a (ρ * s) := by
  rw [monotonicityM, monotonicityM, energyD_oneHomRescale u χ a hρ,
    heightH_oneHomRescale u a hρ]

/-- `N_0(u_{a,ρ}; s) = N_a(u; ρ s)`. -/
theorem frequencyN_oneHomRescale [NeZero n] (u χ : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ)
    (s : ℝ) :
    frequencyN (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s = frequencyN u χ a (ρ * s) := by
  rw [frequencyN, frequencyN, energyD_oneHomRescale u χ a hρ, heightH_oneHomRescale u a hρ]

/-- The affine map `y ↦ a + ρ y` as a homeomorphism. -/
def affineHomeomorph (a : Rn n) {ρ : ℝ} (hρ : ρ ≠ 0) : Rn n ≃ₜ Rn n :=
  (Homeomorph.smulOfNeZero ρ hρ).trans (Homeomorph.addLeft a)

@[simp] theorem affineHomeomorph_apply (a : Rn n) {ρ : ℝ} (hρ : ρ ≠ 0) (y : Rn n) :
    affineHomeomorph a hρ y = a + ρ • y := rfl

/-- `0 ∈ closure {u_{a,ρ} > 0}` if and only if `a ∈ closure {u > 0}`. -/
theorem zero_mem_closure_oneHomRescale_iff (u : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ) :
    (0 : Rn n) ∈ closure {y | 0 < oneHomRescale u a ρ y} ↔ a ∈ closure {y | 0 < u y} := by
  have hset : {y | 0 < oneHomRescale u a ρ y} = affineHomeomorph a hρ.ne' ⁻¹' {y | 0 < u y} := by
    ext y
    simp only [mem_ofPred_eq, oneHomRescale_apply, mem_preimage, affineHomeomorph_apply]
    exact div_pos_iff_of_pos_right hρ
  rw [hset, ← Homeomorph.preimage_closure, mem_preimage, affineHomeomorph_apply, smul_zero,
    add_zero]

/-- `B_1 ∖ B̄_{1/2}` and `B_1 ∖ B_{1/2}` differ by a null set. -/
theorem ball_diff_closedBall_ae_eq (x : Rn n) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    (ball x b \ closedBall x a : Set (Rn n)) =ᵐ[volume] (ball x b \ ball x a : Set (Rn n)) := by
  refine (EventuallyEqSet.refl _ (ball x b)).diff ?_
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · rw [closedBall_sdiff_ball]
    exact Measure.addHaar_sphere_of_ne_zero volume x ha
  · rw [sdiff_eq_empty.2 ball_subset_closedBall, measure_empty]

/-- The tangential energy of `u_{a,ρ}` on `B_1 ∖ B̄_{1/2}` is `ρ^{-n}` times the tangential
energy of `u` on `B_ρ(a) ∖ B_{ρ/2}(a)`. -/
theorem setIntegral_tangential_oneHomRescale (u : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ)
    (ν : Rn n) :
    ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (oneHomRescale u a ρ) y - ⟪gradient (oneHomRescale u a ρ) y, ν⟫ • ν‖ ^ 2 =
      (ρ ^ n)⁻¹ * ∫ y in ball a ρ \ ball a (ρ / 2), ‖gradient u y - ⟪gradient u y, ν⟫ • ν‖ ^ 2 := by
  rw [setIntegral_congr_set (ball_diff_closedBall_ae_eq 0 (by norm_num) 1)]
  have h := setIntegral_annulus_comp_add_smul
    (fun w => ‖gradient u w - ⟪gradient u w, ν⟫ • ν‖ ^ 2) a hρ (1 / 2) 1
  rw [mul_one, mul_one_div] at h
  rw [← h, annulus_def]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [gradient_oneHomRescale u a hρ.ne']

end InnerVariational.Dichotomy
