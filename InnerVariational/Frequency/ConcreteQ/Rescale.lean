/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.ConcreteQ.Basic
public import InnerVariational.Estimates.Dichotomy.Rescale

/-!
# Scaling of the frequency quantities with a Lipschitz coefficient

For `ρ > 0`, the rescaling `ũ(y) = u(a + ρ y)/ρ`, `χ̃(y) = χ(a + ρ y)` of a variational solution
for the coefficient `Q` is a variational solution for the coefficient `Q̃(y) = Q(a + ρ y)`
(`IsVariationalSolutionQ.rescale`). If `Q` is `L`-Lipschitz, then `Q̃` is `ρ L`-Lipschitz with the
same bounds (`QBounds.rescale`), so `κ̃ = ρ κ` (`weissKappa_toNNReal_mul`). Every quantity at the
origin and radius `s` is the quantity of `u` at `a` and radius `ρ s`:

* `weightedEnergyD_oneHomRescale`, `weightedMonotonicityM_oneHomRescale`,
  `weightedFrequencyN_oneHomRescale`, `weightedVolumeV_oneHomRescale`;
* `modFrequencyN_oneHomRescale`: `Ñ` with `κ̃ = ρ κ` at radius `s` is `Ñ` with `κ` at `ρ s`;
* `modMonotonicityM_oneHomRescale`: the same for the shifted Weiss energy `Z`.

These are used to apply Theorem 5.3 with Lipschitz coefficients (`approx1DQ_limit_frequency_eq_one`)
at the scale of the proof of Theorem 6.3.
-/

open MeasureTheory Metric Set Filter
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- `κ` scales linearly with the Lipschitz constant of the coefficient. -/
theorem weissKappa_toNNReal_mul {r : ℝ} (hr : 0 ≤ r) (L : ℝ≥0) (c C' : ℝ) :
    weissKappa (Real.toNNReal r * L) c C' = r * weissKappa L c C' := by
  simp only [weissKappa, NNReal.coe_mul, Real.coe_toNNReal _ hr]
  ring

open Dichotomy

variable (Q u χ : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ)
include hρ

/-- `D^w_0(ũ; s) = D^w_a(u; ρ s)`, with the rescaled coefficient `Q(a + ρ ·)`. -/
theorem weightedEnergyD_oneHomRescale (s : ℝ) :
    weightedEnergyD (fun y => Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s =
      weightedEnergyD Q u χ a (ρ * s) := by
  simp only [weightedEnergyD, smul_zero, add_zero]
  have h := setIntegral_ball_comp_add_smul
    (fun w => ‖gradient u w‖ ^ 2 - Q w ^ 2 * (1 - χ w)) a 0 hρ s
  simp only [smul_zero, add_zero] at h
  have e : ∫ y in ball (0 : Rn n) s,
      (‖gradient (oneHomRescale u a ρ) y‖ ^ 2 - Q (a + ρ • y) ^ 2 * (1 - chiRescale χ a ρ y)) =
      ∫ y in ball (0 : Rn n) s,
        (‖gradient u (a + ρ • y)‖ ^ 2 - Q (a + ρ • y) ^ 2 * (1 - χ (a + ρ • y))) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [gradient_oneHomRescale u a hρ.ne', chiRescale_apply]
  rw [e, h, mul_pow, mul_inv]
  ring

/-- `M^w_0(ũ; s) = M^w_a(u; ρ s)`. -/
theorem weightedMonotonicityM_oneHomRescale [NeZero n] (s : ℝ) :
    weightedMonotonicityM (fun y => Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s =
      weightedMonotonicityM Q u χ a (ρ * s) := by
  rw [weightedMonotonicityM, weightedMonotonicityM, weightedEnergyD_oneHomRescale Q u χ a hρ,
    heightH_oneHomRescale u a hρ]

/-- `N_0(ũ; s) = N_a(u; ρ s)`. -/
theorem weightedFrequencyN_oneHomRescale [NeZero n] (s : ℝ) :
    weightedFrequencyN (fun y => Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s =
      weightedFrequencyN Q u χ a (ρ * s) := by
  rw [weightedFrequencyN, weightedFrequencyN, weightedEnergyD_oneHomRescale Q u χ a hρ,
    heightH_oneHomRescale u a hρ, smul_zero, add_zero]

/-- `V_0(ũ; s) = V_a(u; ρ s)`. -/
theorem weightedVolumeV_oneHomRescale [NeZero n] (s : ℝ) :
    weightedVolumeV (fun y => Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s =
      weightedVolumeV Q u χ a (ρ * s) := by
  simp only [weightedVolumeV]
  rw [heightH_oneHomRescale u a hρ]
  have h := setIntegral_ball_comp_add_smul (fun w => Q w ^ 2 * (1 - χ w)) a 0 hρ s
  simp only [smul_zero, add_zero] at h
  have e : ∫ y in ball (0 : Rn n) s, Q (a + ρ • y) ^ 2 * (1 - chiRescale χ a ρ y) =
      ∫ y in ball (0 : Rn n) s, Q (a + ρ • y) ^ 2 * (1 - χ (a + ρ • y)) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [chiRescale_apply]
  rw [e, h, mul_pow, mul_inv]
  ring

/-- `Ñ_0(ũ; s)` with `κ̃ = ρ κ` is `Ñ_a(u; ρ s)` with `κ`. -/
theorem modFrequencyN_oneHomRescale [NeZero n] (κ s : ℝ) :
    modFrequencyN (ρ * κ) (fun y => Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ) 0 s =
      modFrequencyN κ Q u χ a (ρ * s) := by
  rw [modFrequencyN, modFrequencyN, weightedFrequencyN_oneHomRescale Q u χ a hρ]
  ring

/-- `Z_0(ũ; s)` with `κ̃ = ρ κ` is `Z_a(u; ρ s)` with `κ`. -/
theorem modMonotonicityM_oneHomRescale [NeZero n] (κ s : ℝ) :
    modMonotonicityM (ρ * κ) (fun y => Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ)
      0 s = modMonotonicityM κ Q u χ a (ρ * s) := by
  rw [modMonotonicityM, modMonotonicityM, weightedMonotonicityM_oneHomRescale Q u χ a hρ,
    heightH_oneHomRescale u a hρ, smul_zero, add_zero]
  ring

end InnerVariational
