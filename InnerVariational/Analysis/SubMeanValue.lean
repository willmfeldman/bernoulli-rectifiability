/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import InnerVariational.Vendor.SubMeanValue

/-!
# The sub-mean-value property of continuous weakly subharmonic functions

`IsWeaklySubharmonicOn.le_average`: a continuous weakly subharmonic function on an open `Ω`
satisfies `u(x) ≤ ⨍_{∂B_r(x)} u` and `u(x) ≤ ⨍_{B_r(x)} u` whenever `closedBall x r ⊆ Ω`,
`r > 0` (Gilbarg–Trudinger, Theorem 2.1, for `C²` subharmonic functions).

This file has exactly the statement of `InnerVariational.Registry.IsWeaklySubharmonicOn.le_average`
(`Registry/Harmonic.lean`) and does not import the registry, so that the registry entry can
delegate to it.

## Proof

`Vendor.integral_toSphere_ge_of_weaklySubharmonic` and
`Vendor.mul_le_setIntegral_ball_of_weaklySubharmonic` (adapted from TauCeti's mean-value
property, see `Vendor/SubMeanValue.lean`), with `σ(S^{n-1}) = n |B_1|` and `|B_r| = r^n |B_1|`.
No mollification is needed.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001 (reprint of the 1998 edition).
-/

open MeasureTheory Metric Set Module

@[expose] public noncomputable section

namespace InnerVariational.Analysis

variable {n : ℕ}

/-- **Sub-mean-value property** (cf. Gilbarg–Trudinger, Theorem 2.1). A continuous weakly
subharmonic function on an open `Ω` satisfies `u(x) ≤ ⨍_{∂B_r(x)} u` and `u(x) ≤ ⨍_{B_r(x)} u`
whenever `closedBall x r ⊆ Ω`, `r > 0`. Here `|∂B_r| = n |B_1| r^{n-1}` and
`|B_r| = r^n |B_1|`. -/
theorem IsWeaklySubharmonicOn.le_average [NeZero n] {Ω : Set (Rn n)} (hΩ : IsOpen Ω)
    {u : Rn n → ℝ} (hu : ContinuousOn u Ω) (hsub : IsWeaklySubharmonicOn Ω u) {x : Rn n}
    {r : ℝ} (hr : 0 < r) (hball : closedBall x r ⊆ Ω) :
    u x * (n * unitBallVolume n * r ^ (n - 1)) ≤ sphereIntegral u x r ∧
      u x * (r ^ n * unitBallVolume n) ≤ ∫ y in ball x r, u y := by
  have hw : Vendor.WeaklySubharmonicOn volume u Ω := fun χ hχ hχc hχU hχ0 ↦
    hsub χ ⟨hχ, hχc, hχU⟩ hχ0
  have hB : unitBallVolume n = volume.real (ball (0 : Rn n) 1) := rfl
  constructor
  · have h := Vendor.integral_toSphere_ge_of_weaklySubharmonic hΩ hu hw hball hr.le
    rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, ← hB] at h
    rw [sphereIntegral, sphereMeasure]
    calc u x * (n * unitBallVolume n * r ^ (n - 1))
        = r ^ (n - 1) * (n * unitBallVolume n * u x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  · have h := Vendor.mul_le_setIntegral_ball_of_weaklySubharmonic hΩ hu hw hball
    rw [measureReal_def, Measure.addHaar_ball _ _ hr.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, ← measureReal_def,
      ← hB] at h
    linarith

end InnerVariational.Analysis
