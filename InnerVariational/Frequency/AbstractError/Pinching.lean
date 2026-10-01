/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.AbstractError.ModN
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# A lower bound on the growth of the modified frequency

For radial data with error (`RadialDataErr`) under the standing hypotheses `H > 0` on `[a, b]`,
`Z(a) ≥ 0` and `κ b ≤ 1/2`, the derivative bound for the modified frequency `Ñ = N + κ² s² / 2`
has some room to spare: the quadratic form in `V` that is absorbed in
`RadialDataErr.ae_modN_deriv_ge` is bounded below by a positive multiple of `κ² s`. We record

`Ñ' ≥ κ² s / 4 + V² / (2s)`,

and its integrated form `Ñ(s₂) − Ñ(s₁) ≥ κ² (s₂² − s₁²) / 8`. The frequency pinching
`Ñ(s₂) − Ñ(s₁)` therefore controls `κ² s₂²` when `s₁ ≤ s₂ / 2`. This is how the additive errors of
order `κ² s²` in the passage from the modified frequency `Ñ` to the frequency `N` are absorbed
in the estimates of Section 6 and in the blow-up arguments of Section 5.

We also record the monotonicity of the spherical means `s² H(s)` for radial data with error,
exactly as for `RadialData`: it only uses the formula for `H'` and the energy identity.

## Main results

* `RadialDataErr.ae_sq_div_four_add_volumeV_sq_le_deriv_modN`: `Ñ' ≥ κ² s / 4 + V² / (2s)`.
* `RadialDataErr.sq_mul_sub_sq_le_modN_sub`: `κ² (s₂² − s₁²) / 8 ≤ Ñ(s₂) − Ñ(s₁)`.
* `RadialDataErr.monotoneOn_sq_mul_heightH`: `s ↦ s² H(s)` is nondecreasing.
-/

open MeasureTheory Set Filter
open scoped NNReal

@[expose] public noncomputable section

namespace InnerVariational.Abstract

namespace RadialDataErr

variable {n : ℕ} {ω κ a b : ℝ} (d : RadialDataErr n ω κ a b)

/-! ### Spherical means -/

/-- `(s² H)' = 2 s ∫_{B_s} |∇u|² / sⁿ` for a.e. `s`. -/
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

/-! ### Growth of the modified frequency -/

section Growth

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s) (hZ : 0 ≤ d.modM a) (hκ : κ * b ≤ 1 / 2)
include hH hZ hκ

/-- `κ² s / 4 + V² / (2s) ≤ Ñ'` for a.e. `s`. -/
theorem ae_sq_div_four_add_volumeV_sq_le_deriv_modN : ∀ᵐ s, s ∈ Ioo a b →
    κ ^ 2 * s / 4 + d.volumeV s ^ 2 / (2 * s) ≤ deriv d.modN s := by
  filter_upwards [d.hasDerivAt_modN hH, d.ae_neg_le_err, d.sphSq_nonneg, d.sphRad_nonneg,
    d.sq_sphMix_le] with s hd he h1 h2 h3 hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 := d.pos_of_mem hs'
  have hh := hH s hs'
  have hk := d.kappa_nonneg
  have hks : κ * s ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hs.2.le hk).trans hκ
  have hks0 : 0 ≤ κ * s := mul_nonneg hk hs0.le
  have hN := d.one_sub_le_frequencyN hH hZ hκ hs'
  have hV := d.volumeV_nonneg hs' hh
  have herr := he hs
  rw [d.sub_chiInt_div_eq hh.ne'] at herr
  have hc : 0 ≤ 2 / (d.heightH s * s ^ (n + 2)) := by positivity
  have q1 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s + d.volumeV s))
  have q2 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s))
  rw [(hd hs).deriv]
  set N := d.frequencyN s
  set V := d.volumeV s
  set H := d.heightH s
  have herr' : -(κ * V) ≤ d.err s / H := by
    rw [le_div_iff₀ hh]
    linarith
  have h1' : 0 ≤ 2 / s * (V * (N - 1 + κ ^ 2 * s ^ 2 / 8)) :=
    mul_nonneg (by positivity) (mul_nonneg hV (by linarith))
  have e2 : 2 / s * (V * (κ ^ 2 * s ^ 2 / 8)) = κ ^ 2 * s * V / 4 := by
    field_simp
    ring
  have e3 : 2 / s * (V ^ 2 / 2) = V ^ 2 / (2 * s) + V ^ 2 / (2 * s) := by
    field_simp
    ring
  have hpoly : κ ^ 2 * s / 4 ≤ V ^ 2 / (2 * s) - κ * V - κ ^ 2 * s * V / 4 + κ ^ 2 * s := by
    set t := κ * s with ht
    have ht2 : (1 + t / 4) ^ 2 ≤ 81 / 64 := by nlinarith
    have hnum : 0 ≤ V ^ 2 - (2 * t + t ^ 2 / 2) * V + 3 / 2 * t ^ 2 := by
      nlinarith [sq_nonneg (V - (t + t ^ 2 / 4)), mul_nonneg (sq_nonneg t)
        (by linarith : (0 : ℝ) ≤ 81 / 64 - (1 + t / 4) ^ 2)]
    have e : V ^ 2 / (2 * s) - κ * V - κ ^ 2 * s * V / 4 + κ ^ 2 * s - κ ^ 2 * s / 4 =
        (V ^ 2 - (2 * t + t ^ 2 / 2) * V + 3 / 2 * t ^ 2) / (2 * s) := by
      rw [ht]
      field_simp
      ring
    have : 0 ≤ (V ^ 2 - (2 * t + t ^ 2 / 2) * V + 3 / 2 * t ^ 2) / (2 * s) := by positivity
    linarith
  have hsplit : 2 / s * (V ^ 2 / 2 + V * (N - 1)) =
      2 / s * (V ^ 2 / 2) + 2 / s * (V * (N - 1 + κ ^ 2 * s ^ 2 / 8)) -
        2 / s * (V * (κ ^ 2 * s ^ 2 / 8)) := by ring
  have hdist : 2 / (H * s ^ (n + 2)) *
      (1 / 2 * (d.sphRad s - 2 * (N + V) * d.sphMix s + (N + V) ^ 2 * d.sphSq s) +
        1 / 2 * (d.sphRad s - 2 * N * d.sphMix s + N ^ 2 * d.sphSq s)) =
      1 / 2 * (2 / (H * s ^ (n + 2)) *
        (d.sphRad s - 2 * (N + V) * d.sphMix s + (N + V) ^ 2 * d.sphSq s)) +
      1 / 2 * (2 / (H * s ^ (n + 2)) *
        (d.sphRad s - 2 * N * d.sphMix s + N ^ 2 * d.sphSq s)) := by ring
  rw [hdist, hsplit, e2, e3]
  linarith

/-- The square term of (4.13) is bounded by the derivative of `Ñ`: for a.e. `s`,
`(1 / (H s^{n+2})) ∫_{∂B_s} (∇u·y − N u)² ≤ Ñ'`. -/
theorem ae_frequency_sq_term_le_deriv_modN : ∀ᵐ s, s ∈ Ioo a b →
    1 / (d.heightH s * s ^ (n + 2)) *
        (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) ≤
      deriv d.modN s := by
  filter_upwards [d.hasDerivAt_modN hH, d.ae_modN_deriv_ge hH hZ hκ, d.sphSq_nonneg,
    d.sphRad_nonneg, d.sq_sphMix_le] with s hd hle h1 h2 h3 hs
  have hs0 := d.pos_of_mem (Ioo_subset_Icc_self hs)
  have hh := hH s (Ioo_subset_Icc_self hs)
  have hc : 0 ≤ 2 / (d.heightH s * s ^ (n + 2)) := by positivity
  have q1 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s + d.volumeV s))
  have q3 : 0 ≤ d.volumeV s ^ 2 / (2 * s) := by positivity
  have e : 1 / (d.heightH s * s ^ (n + 2)) *
      (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) =
      1 / 2 * (2 / (d.heightH s * s ^ (n + 2)) *
        (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s)) := by
    ring
  rw [(hd hs).deriv, e]
  have := hle hs
  linarith

/-- **The modified frequency grows at least quadratically**: for `a ≤ s₁ ≤ s₂ ≤ b`,
`κ² (s₂² − s₁²) / 8 ≤ Ñ(s₂) − Ñ(s₁)`. -/
theorem sq_mul_sub_sq_le_modN_sub {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc a b) (hs₂ : s₂ ∈ Icc a b)
    (h12 : s₁ ≤ s₂) : κ ^ 2 * (s₂ ^ 2 - s₁ ^ 2) / 8 ≤ d.modN s₂ - d.modN s₁ := by
  have hfAC : AbsolutelyContinuousOnInterval (fun s => κ ^ 2 * s ^ 2 / 8) a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (by fun_prop : ContDiff ℝ 1 fun s : ℝ => κ ^ 2 * s ^ 2 / 8).contDiffOn
  have hf' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun s => κ ^ 2 * s ^ 2 / 8) (κ ^ 2 * x / 4) x := by
    refine Eventually.of_forall fun x _ => ?_
    have := ((hasDerivAt_pow 2 x).const_mul (κ ^ 2)).div_const 8
    convert this using 1
    push_cast
    ring
  have hle : ∀ᵐ x, x ∈ Ioo a b → κ ^ 2 * x / 4 ≤ deriv d.modN x := by
    filter_upwards [d.ae_sq_div_four_add_volumeV_sq_le_deriv_modN hH hZ hκ] with x hx hmem
    have hx0 := d.pos_of_mem (Ioo_subset_Icc_self hmem)
    have : 0 ≤ d.volumeV x ^ 2 / (2 * x) := by positivity
    linarith [hx hmem]
  have h := hfAC.sub_le_sub_of_ae_hasDerivAt_le (d.absolutelyContinuousOnInterval_modN hH) hf'
    (d.ae_hasDerivAt_deriv_modN hH) hle hs₁ hs₂ h12
  have e : κ ^ 2 * s₂ ^ 2 / 8 - κ ^ 2 * s₁ ^ 2 / 8 = κ ^ 2 * (s₂ ^ 2 - s₁ ^ 2) / 8 := by ring
  linarith

/-- For `s₁ ≤ s₂ / 2`: `(3/32) κ² s₂² ≤ Ñ(s₂) − Ñ(s₁)`. -/
theorem sq_mul_le_modN_sub {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc a b) (hs₂ : s₂ ∈ Icc a b)
    (h12 : 2 * s₁ ≤ s₂) : 3 / 32 * (κ ^ 2 * s₂ ^ 2) ≤ d.modN s₂ - d.modN s₁ := by
  have hs0 := d.pos_of_mem hs₁
  have h := d.sq_mul_sub_sq_le_modN_sub hH hZ hκ hs₁ hs₂ (by linarith)
  have h1 : s₁ ^ 2 ≤ s₂ ^ 2 / 4 := by nlinarith
  have hk : 0 ≤ κ ^ 2 := sq_nonneg κ
  nlinarith

end Growth

/-- Subinterval version of `sq_mul_sub_sq_le_modN_sub`: if `H > 0` on `[t, r]`, `Z(t) ≥ 0` and
`κ r ≤ 1/2`, then `κ² (s₂² − s₁²) / 8 ≤ Ñ(s₂) − Ñ(s₁)` for `t ≤ s₁ ≤ s₂ ≤ r`. -/
theorem sq_mul_sub_sq_le_modN_sub_of_le {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hZ : 0 ≤ d.modM t) (hκ : κ * r ≤ 1 / 2)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc t r) (hs₂ : s₂ ∈ Icc t r) (h12 : s₁ ≤ s₂) :
    κ ^ 2 * (s₂ ^ 2 - s₁ ^ 2) / 8 ≤ d.modN s₂ - d.modN s₁ :=
  (d.restrict ht htr hr).sq_mul_sub_sq_le_modN_sub hH hZ hκ hs₁ hs₂ h12

end RadialDataErr

end InnerVariational.Abstract
