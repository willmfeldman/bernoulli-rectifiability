/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.AbstractError
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The modified frequency `Ñ = N + κ² s² / 2`

For radial data with error (`RadialDataErr`), with `H > 0` on `[a, b]`, `κ b ≤ 1/2` and a
nonnegative shifted Weiss energy `Z(a) ≥ 0` at the inner endpoint, the first-crossing bound
`RadialDataErr.modM_ge` gives `N ≥ 1 - κ² s² / 8` on `[a, b]`. Averaging the two forms (4.12)
and (4.13) of the derivative of `N`, and absorbing the error `|err| / H ≤ κ V` into the `V²`
term, we obtain `Ñ' ≥ ½ sq₁₂ + ½ sq₁₃ + V² / (2s)`, where `sq₁₂` and `sq₁₃` are the square terms
of (4.12) and (4.13). In particular `Ñ` is nondecreasing and `Ñ ≥ 1`.

## Main results

* `RadialDataErr.one_sub_le_frequencyN`: `N ≥ 1 - κ² s² / 8`.
* `RadialDataErr.one_le_modN`: `Ñ ≥ 1`.
* `RadialDataErr.ae_modN_deriv_ge`, `RadialDataErr.monotoneOn_modN`: `Ñ` is nondecreasing.
* `RadialDataErr.heightH_le_exp_mul`: `H(s) ≤ e^{κ² (r² - s²) / 8} H(r)` for `s ≤ r`.
* `RadialDataErr.integral_frequency_sq_term_le`, `RadialDataErr.integral_volumeV_sq_le`: the
  integrated forms.
* `RadialData.monotoneOn_frequencyN_of_toErr`, `RadialData.one_le_frequencyN_of_toErr`: for
  `κ = 0` these recover Lemma 4.1.
-/

open MeasureTheory Set Filter
open scoped NNReal

@[expose] public noncomputable section

namespace InnerVariational.Abstract

namespace RadialDataErr

variable {n : ℕ} {ω κ a b : ℝ} (d : RadialDataErr n ω κ a b)

section ModN

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s) (hZ : 0 ≤ d.modM a) (hκ : κ * b ≤ 1 / 2)
include hH hZ hκ


variable (hZ : 0 ≤ d.modM a) (hκ : κ * b ≤ 1 / 2)
include hZ hκ

/-- **Lower bound for the frequency**: `N ≥ 1 - κ² s² / 8` on `[a, b]`. -/
theorem one_sub_le_frequencyN {s : ℝ} (hs : s ∈ Icc a b) :
    1 - κ ^ 2 * s ^ 2 / 8 ≤ d.frequencyN s := by
  have h := d.modM_nonneg hH hκ hZ hs
  rw [d.modM_eq (hH s hs).ne', mul_nonneg_iff_of_pos_left (hH s hs)] at h
  linarith

/-- The modified frequency is at least one: `Ñ ≥ 1` on `[a, b]`. -/
theorem one_le_modN {s : ℝ} (hs : s ∈ Icc a b) : 1 ≤ d.modN s := by
  have h := d.one_sub_le_frequencyN hH hZ hκ hs
  have : 0 ≤ κ ^ 2 * s ^ 2 := by positivity
  rw [modN]
  linarith

omit hZ hκ in
theorem absolutelyContinuousOnInterval_modN : AbsolutelyContinuousOnInterval d.modN a b :=
  (d.absolutelyContinuousOnInterval_frequencyN hH).fun_add
    (ContDiffOn.absolutelyContinuousOnInterval
      (by fun_prop : ContDiff ℝ 1 fun s : ℝ => κ ^ 2 * s ^ 2 / 2).contDiffOn)

omit hZ hκ in
/-- **Derivative of the modified frequency**, as the average of (4.12) and (4.13): for a.e. `s`,
`Ñ' = (2 / (H s^{n+2})) (½ ∫(∇u·y - (N+V) u)² + ½ ∫(∇u·y - N u)²) + (2/s)(V²/2 + V (N - 1))
+ err / H + κ² s`. -/
theorem hasDerivAt_modN : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.modN
      (2 / (d.heightH s * s ^ (n + 2)) *
          (1 / 2 * (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
          1 / 2 * (d.sphRad s - 2 * d.frequencyN s * d.sphMix s +
            d.frequencyN s ^ 2 * d.sphSq s)) +
        2 / s * (d.volumeV s ^ 2 / 2 + d.volumeV s * (d.frequencyN s - 1)) +
        d.err s / d.heightH s + κ ^ 2 * s) s := by
  filter_upwards [d.hasDerivAt_frequencyN hH, d.hasDerivAt_frequencyN' hH] with s h12 h13 hs
  have hq : HasDerivAt (fun s => κ ^ 2 * s ^ 2 / 2) (κ ^ 2 * s) s := by
    have := ((hasDerivAt_pow 2 s).const_mul (κ ^ 2)).div_const 2
    convert this using 1
    push_cast
    ring
  have heq := (h12 hs).unique (h13 hs)
  refine ((h12 hs).add hq).congr_deriv ?_
  linear_combination (1 / 2 : ℝ) * heq

/-- **Almost-monotonicity of the frequency**: for a.e. `s`,
`Ñ' ≥ ½ (2 / (H s^{n+2})) ∫(∇u·y - (N+V) u)² + ½ (2 / (H s^{n+2})) ∫(∇u·y - N u)² + V² / (2s)`.
-/
theorem ae_modN_deriv_ge : ∀ᵐ s, s ∈ Ioo a b →
    1 / 2 * (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s)) +
        1 / 2 * (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s)) +
        d.volumeV s ^ 2 / (2 * s) ≤
      2 / (d.heightH s * s ^ (n + 2)) *
          (1 / 2 * (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
          1 / 2 * (d.sphRad s - 2 * d.frequencyN s * d.sphMix s +
            d.frequencyN s ^ 2 * d.sphSq s)) +
        2 / s * (d.volumeV s ^ 2 / 2 + d.volumeV s * (d.frequencyN s - 1)) +
        d.err s / d.heightH s + κ ^ 2 * s := by
  filter_upwards [d.ae_neg_le_err] with s he hs
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
  set N := d.frequencyN s
  set V := d.volumeV s
  set H := d.heightH s
  have herr' : -(κ * V) ≤ d.err s / H := by
    rw [le_div_iff₀ hh]
    linarith
  have h1 : 0 ≤ 2 / s * (V * (N - 1 + κ ^ 2 * s ^ 2 / 8)) :=
    mul_nonneg (by positivity) (mul_nonneg hV (by linarith))
  have h2 : 2 / s * (V * (κ ^ 2 * s ^ 2 / 8)) = κ ^ 2 * s * V / 4 := by
    field_simp
    ring
  have h3 : 2 / s * (V ^ 2 / 2) = V ^ 2 / (2 * s) + V ^ 2 / (2 * s) := by
    field_simp
    ring
  have hpoly : 0 ≤ V ^ 2 / (2 * s) - κ * V - κ ^ 2 * s * V / 4 + κ ^ 2 * s := by
    have ht : 0 ≤ (κ * s) ^ 2 * (1 - κ * s / 2 - (κ * s) ^ 2 / 16) :=
      mul_nonneg (sq_nonneg _) (by nlinarith)
    have hnum : 0 ≤ V ^ 2 - (2 * (κ * s) + (κ * s) ^ 2 / 2) * V + 2 * (κ * s) ^ 2 := by
      nlinarith [sq_nonneg (V - (κ * s + (κ * s) ^ 2 / 4))]
    have e : V ^ 2 / (2 * s) - κ * V - κ ^ 2 * s * V / 4 + κ ^ 2 * s =
        (V ^ 2 - (2 * (κ * s) + (κ * s) ^ 2 / 2) * V + 2 * (κ * s) ^ 2) / (2 * s) := by
      field_simp
      ring
    rw [e]
    positivity
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
  rw [hdist, hsplit, h2, h3]
  linarith

omit hZ hκ in
/-- Both square terms and the `V²` term in `ae_modN_deriv_ge` are nonnegative. -/
theorem ae_modN_deriv_lower_nonneg : ∀ᵐ s, s ∈ Ioo a b →
    0 ≤ 1 / 2 * (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s)) +
        1 / 2 * (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s)) +
        d.volumeV s ^ 2 / (2 * s) := by
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 := d.pos_of_mem hs'
  have hh := hH s hs'
  have hc : 0 ≤ 2 / (d.heightH s * s ^ (n + 2)) := by positivity
  have q1 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s + d.volumeV s))
  have q2 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s))
  have q3 : 0 ≤ d.volumeV s ^ 2 / (2 * s) := by positivity
  linarith

omit hZ hκ in
/-- `Ñ` has derivative `deriv Ñ` at a.e. point of `(a, b)`. -/
theorem ae_hasDerivAt_deriv_modN : ∀ᵐ s, s ∈ Ioo a b → HasDerivAt d.modN (deriv d.modN s) s := by
  filter_upwards [d.hasDerivAt_modN hH] with s h hs
  exact (h hs).differentiableAt.hasDerivAt

/-- `V² / (2s) ≤ Ñ'` for a.e. `s`. -/
theorem ae_volumeV_sq_le_deriv_modN : ∀ᵐ s, s ∈ Ioo a b →
    d.volumeV s ^ 2 / (2 * s) ≤ deriv d.modN s := by
  filter_upwards [d.hasDerivAt_modN hH, d.ae_modN_deriv_ge hH hZ hκ, d.sphSq_nonneg,
    d.sphRad_nonneg, d.sq_sphMix_le] with s hd hle h1 h2 h3 hs
  have hs0 := d.pos_of_mem (Ioo_subset_Icc_self hs)
  have hh := hH s (Ioo_subset_Icc_self hs)
  have hc : 0 ≤ 2 / (d.heightH s * s ^ (n + 2)) := by positivity
  have q1 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s + d.volumeV s))
  have q2 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s))
  rw [(hd hs).deriv]
  have := hle hs
  linarith

/-- **The modified frequency `Ñ = N + κ² s² / 2` is nondecreasing** on `[a, b]`. -/
theorem monotoneOn_modN : MonotoneOn d.modN (Icc a b) :=
  (d.absolutelyContinuousOnInterval_modN hH).monotoneOn_of_ae_hasDerivAt_nonneg
    (d.hasDerivAt_modN hH) (by
      filter_upwards [d.ae_modN_deriv_ge hH hZ hκ, d.ae_modN_deriv_lower_nonneg hH] with
        s h1 h2 hs
      exact (h2 hs).trans (h1 hs))

/-- **Almost-monotonicity of `H`** (replacing the lower bound of Lemma 4.3): for
`a ≤ s ≤ r ≤ b`, `H(s) ≤ e^{κ² (r² - s²) / 8} H(r)`. -/
theorem heightH_le_exp_mul {s r : ℝ} (hs : s ∈ Icc a b) (hr : r ∈ Icc a b) (hsr : s ≤ r) :
    d.heightH s ≤ Real.exp (κ ^ 2 * (r ^ 2 - s ^ 2) / 8) * d.heightH r := by
  have hfAC : AbsolutelyContinuousOnInterval (fun s => -(κ ^ 2 * s ^ 2 / 8)) a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (by fun_prop : ContDiff ℝ 1 fun s : ℝ => -(κ ^ 2 * s ^ 2 / 8)).contDiffOn
  have hgAC : AbsolutelyContinuousOnInterval (fun s => Real.log (d.heightH s)) a b :=
    let ⟨_, hK⟩ := d.exists_lipschitzOnWith_log_heightH hH
    hK.absolutelyContinuousOnInterval_of_Icc d.le
  have hf' : ∀ᵐ x, x ∈ Ioo a b →
      HasDerivAt (fun s => -(κ ^ 2 * s ^ 2 / 8)) (-(κ ^ 2 * x / 4)) x := by
    refine Eventually.of_forall fun x _ => ?_
    have := (((hasDerivAt_pow 2 x).const_mul (κ ^ 2)).div_const 8).neg
    convert this using 1
    push_cast
    ring
  have hle : ∀ᵐ x, x ∈ Ioo a b →
      -(κ ^ 2 * x / 4) ≤ 2 / x * (d.frequencyN x + d.volumeV x - 1) := by
    refine Eventually.of_forall fun x hx => ?_
    have hx' := Ioo_subset_Icc_self hx
    have hx0 := d.pos_of_mem hx'
    have hN := d.one_sub_le_frequencyN hH hZ hκ hx'
    have hV := d.volumeV_nonneg hx' (hH x hx')
    have h1 : 0 ≤ 2 / x * (d.frequencyN x + d.volumeV x - 1 + κ ^ 2 * x ^ 2 / 8) :=
      mul_nonneg (by positivity) (by linarith)
    have h2 : 2 / x * (κ ^ 2 * x ^ 2 / 8) = κ ^ 2 * x / 4 := by
      field_simp
      ring
    have h3 : 2 / x * (d.frequencyN x + d.volumeV x - 1 + κ ^ 2 * x ^ 2 / 8) =
        2 / x * (d.frequencyN x + d.volumeV x - 1) + 2 / x * (κ ^ 2 * x ^ 2 / 8) := by ring
    linarith
  have hcomp := hfAC.sub_le_sub_of_ae_hasDerivAt_le hgAC hf' (d.hasDerivAt_log_heightH hH) hle
    hs hr hsr
  have hHs := hH s hs
  have hHr := hH r hr
  calc d.heightH s = Real.exp (Real.log (d.heightH s)) := (Real.exp_log hHs).symm
    _ ≤ Real.exp (κ ^ 2 * (r ^ 2 - s ^ 2) / 8 + Real.log (d.heightH r)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (κ ^ 2 * (r ^ 2 - s ^ 2) / 8) * d.heightH r := by
        rw [Real.exp_add, Real.exp_log hHr]


end ModN

/-! ### Integrated forms of the almost-monotonicity of `Ñ` -/

section Integrated

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s) (hZ : 0 ≤ d.modM a) (hκ : κ * b ≤ 1 / 2)
include hH hZ hκ

/-- Integrated form of (4.13) for `Ñ`:
`∫_{s₁}^{s₂} ½ (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - N u)² ≤ Ñ(s₂) - Ñ(s₁)`. -/
theorem integral_frequency_sq_term_le {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc a b) (hs₂ : s₂ ∈ Icc a b)
    (h12 : s₁ ≤ s₂) :
    ∫ s in s₁..s₂, 1 / 2 * (2 / (d.heightH s * s ^ (n + 2)) *
        (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s)) ≤
      d.modN s₂ - d.modN s₁ := by
  have hsub₁ : a ≤ s₁ := hs₁.1
  have hsub₂ : s₂ ≤ b := hs₂.2
  refine ((d.absolutelyContinuousOnInterval_modN hH).mono_Icc d.le hs₁ hs₂
    ).integral_le_sub_of_ae_le h12 (ae_mem_Ioo_imp_mono hsub₁ hsub₂ (d.hasDerivAt_modN hH))
    (ae_mem_Ioo_imp_mono hsub₁ hsub₂ ?_) (ae_mem_Ioo_imp_mono hsub₁ hsub₂ ?_)
  · filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
    have hs0 := d.pos_of_mem (Ioo_subset_Icc_self hs)
    have hh := hH s (Ioo_subset_Icc_self hs)
    exact mul_nonneg (by norm_num) (mul_nonneg (by positivity)
      (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs) (d.frequencyN s)))
  · filter_upwards [d.ae_modN_deriv_ge hH hZ hκ, d.sphSq_nonneg, d.sphRad_nonneg,
      d.sq_sphMix_le] with s hle h1 h2 h3 hs
    have hs0 := d.pos_of_mem (Ioo_subset_Icc_self hs)
    have hh := hH s (Ioo_subset_Icc_self hs)
    have q1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / (d.heightH s * s ^ (n + 2)))
      (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
        (d.frequencyN s + d.volumeV s))
    have q3 : 0 ≤ d.volumeV s ^ 2 / (2 * s) := by positivity
    have := hle hs
    linarith

/-- Integrated form of (4.12) for `Ñ`: `∫_{s₁}^{s₂} V² / (2s) ≤ Ñ(s₂) - Ñ(s₁)`. -/
theorem integral_volumeV_sq_le {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc a b) (hs₂ : s₂ ∈ Icc a b)
    (h12 : s₁ ≤ s₂) :
    ∫ s in s₁..s₂, d.volumeV s ^ 2 / (2 * s) ≤ d.modN s₂ - d.modN s₁ := by
  have hsub₁ : a ≤ s₁ := hs₁.1
  have hsub₂ : s₂ ≤ b := hs₂.2
  refine ((d.absolutelyContinuousOnInterval_modN hH).mono_Icc d.le hs₁ hs₂
    ).integral_le_sub_of_ae_le h12 (ae_mem_Ioo_imp_mono hsub₁ hsub₂ (d.hasDerivAt_modN hH))
    (ae_mem_Ioo_imp_mono hsub₁ hsub₂ ?_) (ae_mem_Ioo_imp_mono hsub₁ hsub₂ ?_)
  · refine Eventually.of_forall fun s hs => ?_
    have hs0 := d.pos_of_mem (Ioo_subset_Icc_self hs)
    positivity
  · filter_upwards [d.ae_modN_deriv_ge hH hZ hκ, d.sphSq_nonneg, d.sphRad_nonneg,
      d.sq_sphMix_le] with s hle h1 h2 h3 hs
    have hs0 := d.pos_of_mem (Ioo_subset_Icc_self hs)
    have hh := hH s (Ioo_subset_Icc_self hs)
    have hc : 0 ≤ 2 / (d.heightH s * s ^ (n + 2)) := by positivity
    have q1 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
      (d.frequencyN s + d.volumeV s))
    have q2 := mul_nonneg hc (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
      (d.frequencyN s))
    have := hle hs
    linarith

end Integrated

/-! ### Subinterval versions -/

/-- `Z ≥ 0` on a subinterval `[t, r]`, if `H > 0` on `[t, r]`, `κ r ≤ 1/2` and `Z(t) ≥ 0`. -/
theorem modM_nonneg_of_le {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hκ : κ * r ≤ 1 / 2) (hZ : 0 ≤ d.modM t) {s : ℝ}
    (hs : s ∈ Icc t r) : 0 ≤ d.modM s :=
  (d.restrict ht htr hr).modM_nonneg hH hκ hZ hs

/-- `N ≥ 1 - κ² s² / 8` on a subinterval `[t, r]`. -/
theorem one_sub_le_frequencyN_of_le {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hZ : 0 ≤ d.modM t) (hκ : κ * r ≤ 1 / 2) {s : ℝ}
    (hs : s ∈ Icc t r) : 1 - κ ^ 2 * s ^ 2 / 8 ≤ d.frequencyN s :=
  (d.restrict ht htr hr).one_sub_le_frequencyN hH hZ hκ hs

/-- `Ñ ≥ 1` on a subinterval `[t, r]`. -/
theorem one_le_modN_of_le {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hZ : 0 ≤ d.modM t) (hκ : κ * r ≤ 1 / 2) {s : ℝ}
    (hs : s ∈ Icc t r) : 1 ≤ d.modN s :=
  (d.restrict ht htr hr).one_le_modN hH hZ hκ hs

/-- `Ñ` is nondecreasing on a subinterval `[t, r]`. -/
theorem monotoneOn_modN_of_le {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hZ : 0 ≤ d.modM t) (hκ : κ * r ≤ 1 / 2) :
    MonotoneOn d.modN (Icc t r) :=
  (d.restrict ht htr hr).monotoneOn_modN hH hZ hκ

end RadialDataErr

namespace RadialData

variable {n : ℕ} {ω a b : ℝ} (d : RadialData n ω a b)

/-- Regression check: for `κ = 0` the monotonicity of `Ñ` is the monotonicity of `N`. -/
theorem monotoneOn_frequencyN_of_toErr (hH : ∀ s ∈ Icc a b, 0 < d.heightH s)
    (hM : ω ≤ d.monotonicityM a) : MonotoneOn d.frequencyN (Icc a b) := by
  have h := d.toErr.monotoneOn_modN hH (by rw [toErr_modM]; linarith)
    (by rw [zero_mul]; norm_num)
  rwa [toErr_modN] at h

/-- Regression check: for `κ = 0` the lower bound on `N` is `N ≥ 1` from `M(a) ≥ ω`. -/
theorem one_le_frequencyN_of_toErr (hH : ∀ s ∈ Icc a b, 0 < d.heightH s)
    (hM : ω ≤ d.monotonicityM a) {s : ℝ} (hs : s ∈ Icc a b) : 1 ≤ d.frequencyN s := by
  have h := d.toErr.one_sub_le_frequencyN hH (by rw [toErr_modM]; linarith)
    (by rw [zero_mul]; norm_num) hs
  simpa using h


end RadialData

end InnerVariational.Abstract
