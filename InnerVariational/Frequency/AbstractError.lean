/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Abstract.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The almost-monotone frequency calculus with an error term

This file generalises `Frequency/Abstract.lean` to variational solutions of the Bernoulli
problem with a Lipschitz coefficient `Q`, i.e. critical points of `∫ |∇u|² + Q² χ` with respect
to inner variations. The geometric input is again packaged in a structure, `RadialDataErr`, which
has every field of `RadialData` except that the derivative of `D` gains an error term `e(s)`.

## The `Q²`-weighted normalisation

With `G(s) = ∫_{B_s} |∇u|²` and `W_Q(s) = ∫_{B_s} Q² (1 - χ)`, the Rellich identity with `Q`
suggests the quantities
* `P(s) = s^{-n} (G(s) - W_Q(s))`, which plays the role of `D - ω`,
* `N = P / H` and `V = s^{-n} W_Q / H`,
where `H(s) = s^{-(n+1)} ∫_{∂B_s} u²` as before. In the abstract setting `ω` is any real
constant, `chiInt s = ω sⁿ - W_Q(s)` and `energyD = (gradInt + chiInt) / sⁿ = P + ω`, so that
`frequencyN = (energyD - ω) / H` and `volumeV = (ω - chiInt / sⁿ) / H` have the same formulas as
for `Q ≡ 1`. In this normalisation the sphere terms coming from `Q²(1 - χ)` cancel exactly, and
`P' = (2 / s^{n+2}) ∫_{∂B_s} ((∇u·y)² - u ∇u·y) + e(s)` with
`e(s) = -s^{-n-1} ∫_{B_s} (1 - χ) ∇(Q²)·y`. The error satisfies `|e| ≤ κ V H`, where
`κ = ‖∇(Q²)‖_∞ / inf Q²`; this is the hypothesis `abs_err_le`. The identity `N + V = s^{-n} G / H`
and the formula for `H'` are unchanged. For `Q ≡ 1` we have `e = 0` and `κ = 0`
(`RadialData.toErr`).

## The shifted Weiss quantity

The lower bound `N ≥ 1` of the constant-coefficient theory is replaced by
`N ≥ 1 - κ² s² / 8`. The key quantity is the shifted Weiss energy
`Z(s) = M(s) - ω + (κ² s² / 8) H(s) = H(s) (N(s) - 1 + κ² s² / 8)`, which satisfies
`Z' ≥ 2 κ Z` almost everywhere on `{Z < 0}` as long as `κ s ≤ 1/2`. A first-crossing argument
then gives `Z(s) ≥ e^{2κ(s-a)} min(Z(a), 0)`, so `Z ≥ 0` propagates from `a` to the right. The
modified frequency `Ñ(s) = N(s) + κ² s² / 2` is then nondecreasing and `Ñ ≥ 1`, and Lemmas 4.3–4.5
of the constant-coefficient theory hold for `Ñ`.

The paper treats `Q ≡ 1`, where `κ = 0`, `Z = M - ω` and `Ñ = N`, and all statements reduce to
those of `Frequency/Abstract.lean`.

## Main results

* `RadialDataErr.hasDerivAt_monotonicityM`, `RadialDataErr.monotoneOn_monotonicityM_add`,
  `RadialDataErr.integral_monotonicityM_sq_term_le`: the Weiss formula with error; `M + κ Λ s`
  is nondecreasing when `V H ≤ Λ`.
* `RadialDataErr.hasDerivAt_monotonicityM_refined`: with `l = N + V`,
  `M' = (2 / s^{n+2}) ∫_{∂B_s} (∇u·y - l u)² + (2/s) H (l - 1)² + err`.
* `RadialDataErr.hasDerivAt_frequencyN`, `RadialDataErr.hasDerivAt_frequencyN'`: (4.12) and
  (4.13) with the additional term `err / H`.
* `RadialDataErr.ae_two_mul_modM_le_deriv`: `Z' ≥ 2κZ` a.e. on `{Z < 0}`.
* `RadialDataErr.modM_ge` (first crossing for `Z`) and `RadialDataErr.modM_nonneg`.

The modified frequency is treated in `Frequency/AbstractError/ModN.lean`, the doubling lemmas in
`Frequency/AbstractError/Doubling.lean`.

## Implementation notes

As in `Frequency/Abstract.lean`, a.e. hypotheses are stated as `∀ᵐ s, s ∈ Ioo a b → _`, every
statement about `N` assumes `H > 0` on the relevant interval, and every lemma is stated for a
general subinterval of the data interval. Hypotheses `M(a) ≥ ω` of the constant-coefficient theory
become `Z(a) ≥ 0` together with `κ b ≤ 1/2`.
-/

open MeasureTheory Set Filter
open scoped NNReal

@[expose] public noncomputable section

namespace InnerVariational.Abstract

/-- **Radial data with an error term** of a variational solution at a point, on the radius
interval `[a, b]`.

The fields are those of `RadialData`, except that the derivative of `D` is
`(2 / s^{n+2}) (sphRad - sphMix) + err`, where the error satisfies
`|err s| ≤ κ (ω - s^{-n} chiInt s) = κ V(s) H(s)`. For a variational solution with coefficient
`Q`, `chiInt s = ω sⁿ - ∫_{B_s} Q² (1 - χ)` and `κ = ‖∇(Q²)‖_∞ / inf Q²`. -/
structure RadialDataErr (n : ℕ) (ω κ a b : ℝ) where
  /-- `s ↦ ∫_{B_s} |∇u|²`. -/
  gradInt : ℝ → ℝ
  /-- `s ↦ ω sⁿ - ∫_{B_s} Q² (1 - χ)`. -/
  chiInt : ℝ → ℝ
  /-- `s ↦ ∫_{∂B_s} u²`. -/
  sphSq : ℝ → ℝ
  /-- `s ↦ ∫_{∂B_s} u ∇u·y`. -/
  sphMix : ℝ → ℝ
  /-- `s ↦ ∫_{∂B_s} (∇u·y)²`. -/
  sphRad : ℝ → ℝ
  /-- `D(s) = s^{-n} (gradInt + chiInt)`. -/
  energyD : ℝ → ℝ
  /-- `H(s) = s^{-(n+1)} ∫_{∂B_s} u²`. -/
  heightH : ℝ → ℝ
  /-- The error term in the derivative of `D`. -/
  err : ℝ → ℝ
  pos : 0 < a
  le : a ≤ b
  kappa_nonneg : 0 ≤ κ
  energyD_eq : ∀ s ∈ Icc a b, energyD s = (gradInt s + chiInt s) / s ^ n
  heightH_eq : ∀ s ∈ Icc a b, heightH s = sphSq s / s ^ (n + 1)
  lipschitzOnWith_energyD : ∃ K, LipschitzOnWith K energyD (Icc a b)
  lipschitzOnWith_heightH : ∃ K, LipschitzOnWith K heightH (Icc a b)
  /-- `chiInt s ≤ ω sⁿ`. -/
  chiInt_le : ∀ s ∈ Icc a b, chiInt s ≤ ω * s ^ n
  /-- `s ↦ ω sⁿ - chiInt s` is nondecreasing. -/
  monotoneOn_sub_chiInt : MonotoneOn (fun s => ω * s ^ n - chiInt s) (Icc a b)
  /-- The energy identity: `∫_{B_s}|∇u|² = ∫_{∂B_s} u ∇u·y/|y|`. -/
  gradInt_eq : ∀ᵐ s, s ∈ Ioo a b → gradInt s = sphMix s / s
  /-- `D' = (2 / s^(n+2)) ∫_{∂B_s} ((∇u·y)² - u ∇u·y) + err`. -/
  hasDerivAt_energyD : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt energyD (2 / s ^ (n + 2) * (sphRad s - sphMix s) + err s) s
  /-- `|err| ≤ κ (ω - s^{-n} chiInt) = κ V H`. -/
  abs_err_le : ∀ᵐ s, s ∈ Ioo a b → |err s| ≤ κ * (ω - chiInt s / s ^ n)
  /-- `H' = -(2/s) H + (2 / s^(n+2)) ∫_{∂B_s} u ∇u·y`. -/
  hasDerivAt_heightH : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt heightH (-(2 / s) * heightH s + 2 / s ^ (n + 2) * sphMix s) s
  sphSq_nonneg : ∀ᵐ s, s ∈ Ioo a b → 0 ≤ sphSq s
  sphRad_nonneg : ∀ᵐ s, s ∈ Ioo a b → 0 ≤ sphRad s
  /-- Cauchy–Schwarz on `∂B_s`. -/
  sq_sphMix_le : ∀ᵐ s, s ∈ Ioo a b → sphMix s ^ 2 ≤ sphSq s * sphRad s

namespace RadialDataErr

variable {n : ℕ} {ω κ a b : ℝ} (d : RadialDataErr n ω κ a b)

/-- The Weiss energy `M = D - H`. -/
def monotonicityM (s : ℝ) : ℝ := d.energyD s - d.heightH s

/-- The frequency `N = (D - ω) / H`, with `N = 0` when `H = 0`. -/
def frequencyN (s : ℝ) : ℝ := (d.energyD s - ω) / d.heightH s

/-- The volume term `V = (ω - s^{-n} chiInt) / H`. -/
def volumeV (s : ℝ) : ℝ := (ω - d.chiInt s / s ^ n) / d.heightH s

/-- The shifted Weiss energy `Z = M - ω + (κ² s² / 8) H = H (N - 1 + κ² s² / 8)`. -/
def modM (s : ℝ) : ℝ := d.monotonicityM s - ω + κ ^ 2 * s ^ 2 / 8 * d.heightH s

/-- The modified frequency `Ñ = N + κ² s² / 2`. -/
def modN (s : ℝ) : ℝ := d.frequencyN s + κ ^ 2 * s ^ 2 / 2

/-- Restriction of radial data with error to a subinterval. -/
def restrict {c e : ℝ} (hc : a ≤ c) (hce : c ≤ e) (he : e ≤ b) : RadialDataErr n ω κ c e where
  gradInt := d.gradInt
  chiInt := d.chiInt
  sphSq := d.sphSq
  sphMix := d.sphMix
  sphRad := d.sphRad
  energyD := d.energyD
  heightH := d.heightH
  err := d.err
  pos := d.pos.trans_le hc
  le := hce
  kappa_nonneg := d.kappa_nonneg
  energyD_eq s hs := d.energyD_eq s ⟨hc.trans hs.1, hs.2.trans he⟩
  heightH_eq s hs := d.heightH_eq s ⟨hc.trans hs.1, hs.2.trans he⟩
  lipschitzOnWith_energyD :=
    let ⟨K, hK⟩ := d.lipschitzOnWith_energyD
    ⟨K, hK.mono (Icc_subset_Icc hc he)⟩
  lipschitzOnWith_heightH :=
    let ⟨K, hK⟩ := d.lipschitzOnWith_heightH
    ⟨K, hK.mono (Icc_subset_Icc hc he)⟩
  chiInt_le s hs := d.chiInt_le s ⟨hc.trans hs.1, hs.2.trans he⟩
  monotoneOn_sub_chiInt := d.monotoneOn_sub_chiInt.mono (Icc_subset_Icc hc he)
  gradInt_eq := ae_mem_Ioo_imp_mono hc he d.gradInt_eq
  hasDerivAt_energyD := ae_mem_Ioo_imp_mono hc he d.hasDerivAt_energyD
  abs_err_le := ae_mem_Ioo_imp_mono hc he d.abs_err_le
  hasDerivAt_heightH := ae_mem_Ioo_imp_mono hc he d.hasDerivAt_heightH
  sphSq_nonneg := ae_mem_Ioo_imp_mono hc he d.sphSq_nonneg
  sphRad_nonneg := ae_mem_Ioo_imp_mono hc he d.sphRad_nonneg
  sq_sphMix_le := ae_mem_Ioo_imp_mono hc he d.sq_sphMix_le

section Restrict

variable {c e : ℝ} (hc : a ≤ c) (hce : c ≤ e) (he : e ≤ b)

@[simp] theorem restrict_energyD : (d.restrict hc hce he).energyD = d.energyD := rfl
@[simp] theorem restrict_heightH : (d.restrict hc hce he).heightH = d.heightH := rfl
@[simp] theorem restrict_chiInt : (d.restrict hc hce he).chiInt = d.chiInt := rfl
@[simp] theorem restrict_gradInt : (d.restrict hc hce he).gradInt = d.gradInt := rfl
@[simp] theorem restrict_sphSq : (d.restrict hc hce he).sphSq = d.sphSq := rfl
@[simp] theorem restrict_sphMix : (d.restrict hc hce he).sphMix = d.sphMix := rfl
@[simp] theorem restrict_sphRad : (d.restrict hc hce he).sphRad = d.sphRad := rfl
@[simp] theorem restrict_err : (d.restrict hc hce he).err = d.err := rfl
@[simp] theorem restrict_monotonicityM :
    (d.restrict hc hce he).monotonicityM = d.monotonicityM := rfl
@[simp] theorem restrict_frequencyN : (d.restrict hc hce he).frequencyN = d.frequencyN := rfl
@[simp] theorem restrict_volumeV : (d.restrict hc hce he).volumeV = d.volumeV := rfl
@[simp] theorem restrict_modM : (d.restrict hc hce he).modM = d.modM := rfl
@[simp] theorem restrict_modN : (d.restrict hc hce he).modN = d.modN := rfl

end Restrict

/-! ### Basic properties -/

include d in
theorem pos_of_mem {s : ℝ} (hs : s ∈ Icc a b) : 0 < s := d.pos.trans_le hs.1

theorem absolutelyContinuousOnInterval_energyD : AbsolutelyContinuousOnInterval d.energyD a b :=
  let ⟨_, hK⟩ := d.lipschitzOnWith_energyD
  hK.absolutelyContinuousOnInterval_of_Icc d.le

theorem absolutelyContinuousOnInterval_heightH : AbsolutelyContinuousOnInterval d.heightH a b :=
  let ⟨_, hK⟩ := d.lipschitzOnWith_heightH
  hK.absolutelyContinuousOnInterval_of_Icc d.le

theorem continuousOn_heightH : ContinuousOn d.heightH (Icc a b) :=
  let ⟨_, hK⟩ := d.lipschitzOnWith_heightH
  hK.continuousOn

/-- `∫_{∂B_s} u² = s^{n+1} H(s)`. -/
theorem sphSq_eq {s : ℝ} (hs : s ∈ Icc a b) : d.sphSq s = s ^ (n + 1) * d.heightH s := by
  have hs0 : s ^ (n + 1) ≠ 0 := (pow_pos (d.pos_of_mem hs) _).ne'
  rw [d.heightH_eq s hs, mul_div_cancel₀ _ hs0]

/-- `V = (ω sⁿ - chiInt) / (sⁿ H)`. -/
theorem volumeV_eq {s : ℝ} (hs : s ∈ Icc a b) :
    d.volumeV s = (ω * s ^ n - d.chiInt s) / (s ^ n * d.heightH s) := by
  have hs0 : s ^ n ≠ 0 := (pow_pos (d.pos_of_mem hs) _).ne'
  have h1 : ω - d.chiInt s / s ^ n = (ω * s ^ n - d.chiInt s) / s ^ n := by
    rw [sub_div, mul_div_cancel_right₀ _ hs0]
  rw [volumeV, h1, div_div]

theorem volumeV_nonneg {s : ℝ} (hs : s ∈ Icc a b) (hH : 0 < d.heightH s) : 0 ≤ d.volumeV s := by
  have hs0 := d.pos_of_mem hs
  refine div_nonneg ?_ hH.le
  rw [sub_nonneg, div_le_iff₀ (pow_pos hs0 n)]
  exact d.chiInt_le s hs

/-- Identity (4.11): `N + V = s^{-n} ∫_{B_s}|∇u|² / H`. -/
theorem frequencyN_add_volumeV {s : ℝ} (hs : s ∈ Icc a b) :
    d.frequencyN s + d.volumeV s = d.gradInt s / s ^ n / d.heightH s := by
  rw [frequencyN, volumeV, ← add_div]
  congr 1
  rw [d.energyD_eq s hs, add_div]
  ring

/-- `∫_{∂B_s} u ∇u·y = s^{n+1} H (N + V)` for a.e. `s`. -/
theorem ae_sphMix_eq : ∀ᵐ s, s ∈ Ioo a b → d.heightH s ≠ 0 →
    d.sphMix s = s ^ (n + 1) * d.heightH s * (d.frequencyN s + d.volumeV s) := by
  filter_upwards [d.gradInt_eq] with s hI hs hH
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  rw [d.frequencyN_add_volumeV hs', hI hs]
  field_simp
  ring

/-- `N ≥ 1` if and only if `M ≥ ω` (when `H > 0`). -/
theorem one_le_frequencyN_iff {s : ℝ} (hH : 0 < d.heightH s) :
    1 ≤ d.frequencyN s ↔ ω ≤ d.monotonicityM s := by
  rw [frequencyN, monotonicityM, le_div_iff₀ hH]
  constructor <;> intro h <;> linarith

/-- `N > 1` if and only if `M > ω` (when `H > 0`). -/
theorem one_lt_frequencyN_iff {s : ℝ} (hH : 0 < d.heightH s) :
    1 < d.frequencyN s ↔ ω < d.monotonicityM s := by
  rw [frequencyN, monotonicityM, lt_div_iff₀ hH]
  constructor <;> intro h <;> linarith

theorem lt_monotonicityM_of_one_lt_frequencyN {s : ℝ} (hH : 0 < d.heightH s)
    (hN : 1 < d.frequencyN s) : ω < d.monotonicityM s :=
  (d.one_lt_frequencyN_iff hH).1 hN

/-- `ω - s^{-n} chiInt = V H` (when `H ≠ 0`). -/
theorem sub_chiInt_div_eq {s : ℝ} (hH : d.heightH s ≠ 0) :
    ω - d.chiInt s / s ^ n = d.volumeV s * d.heightH s := by
  rw [volumeV, div_mul_cancel₀ _ hH]

/-- `M - ω = H (N - 1)` (when `H ≠ 0`). -/
theorem monotonicityM_sub_eq {s : ℝ} (hH : d.heightH s ≠ 0) :
    d.monotonicityM s - ω = d.heightH s * (d.frequencyN s - 1) := by
  rw [monotonicityM, frequencyN, mul_sub, mul_div_cancel₀ _ hH]
  ring

/-- `Z = H (N - 1 + κ² s² / 8)` (when `H ≠ 0`). -/
theorem modM_eq {s : ℝ} (hH : d.heightH s ≠ 0) :
    d.modM s = d.heightH s * (d.frequencyN s - 1 + κ ^ 2 * s ^ 2 / 8) := by
  rw [modM, d.monotonicityM_sub_eq hH]
  ring

theorem frequencyN_le_modN (s : ℝ) : d.frequencyN s ≤ d.modN s := by
  have : 0 ≤ κ ^ 2 * s ^ 2 / 2 := by positivity
  rw [modN]
  linarith

/-- The error is bounded below by `-κ (ω - s^{-n} chiInt) = -κ V H`. -/
theorem ae_neg_le_err : ∀ᵐ s, s ∈ Ioo a b → -(κ * (ω - d.chiInt s / s ^ n)) ≤ d.err s := by
  filter_upwards [d.abs_err_le] with s h hs
  exact neg_le_of_abs_le (h hs)

/-! ### The Weiss energy -/

/-- **Derivative of `M`**: for a.e. `s`,
`M' = (2 / s^{n+2}) ∫_{∂B_s} (u - ∇u·y)² + err`. -/
theorem hasDerivAt_monotonicityM : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.monotonicityM
      (2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) + d.err s) s := by
  filter_upwards [d.hasDerivAt_energyD, d.hasDerivAt_heightH] with s hD hH hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  refine ((hD hs).sub (hH hs)).congr_deriv ?_
  rw [d.sphSq_eq hs']
  field_simp
  ring

theorem ae_monotonicityM_sq_term_nonneg : ∀ᵐ s, s ∈ Ioo a b →
    0 ≤ 2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) := by
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
  have hs0 : 0 < s := d.pos.trans hs.1
  have hq := Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs) 1
  simp only [mul_one, one_pow, one_mul] at hq
  exact mul_nonneg (by positivity) hq

/-- The derivative of `M` is at least `(2 / s^{n+2}) ∫_{∂B_s} (u - ∇u·y)² - κ V H`. -/
theorem ae_monotonicityM_deriv_ge : ∀ᵐ s, s ∈ Ioo a b →
    2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) -
        κ * (ω - d.chiInt s / s ^ n) ≤
      2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) + d.err s := by
  filter_upwards [d.ae_neg_le_err] with s h hs
  linarith [h hs]

theorem absolutelyContinuousOnInterval_monotonicityM :
    AbsolutelyContinuousOnInterval d.monotonicityM a b :=
  d.absolutelyContinuousOnInterval_energyD.fun_sub d.absolutelyContinuousOnInterval_heightH

section WeissBound

variable {Λ : ℝ} (hΛ : ∀ s ∈ Ioo a b, ω - d.chiInt s / s ^ n ≤ Λ)
include hΛ

theorem ae_monotonicityM_deriv_add_nonneg : ∀ᵐ s, s ∈ Ioo a b →
    2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) ≤
      2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) + d.err s + κ * Λ := by
  filter_upwards [d.ae_neg_le_err] with s h hs
  have := mul_le_mul_of_nonneg_left (hΛ s hs) d.kappa_nonneg
  linarith [h hs]

/-- **Almost-monotonicity of `M`**: if `ω - s^{-n} chiInt ≤ Λ` (that is, `V H ≤ Λ`) on
`(a, b)`, then `M(s) + κ Λ s` is nondecreasing on `[a, b]`. -/
theorem monotoneOn_monotonicityM_add :
    MonotoneOn (fun s => d.monotonicityM s + κ * Λ * s) (Icc a b) := by
  have hAC : AbsolutelyContinuousOnInterval (fun s => κ * Λ * s) a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (by fun_prop : ContDiff ℝ 1 fun s : ℝ => κ * Λ * s).contDiffOn
  refine (d.absolutelyContinuousOnInterval_monotonicityM.fun_add hAC
    ).monotoneOn_of_ae_hasDerivAt_nonneg
    (f' := fun s => 2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) + d.err s +
      κ * Λ) ?_ ?_
  · filter_upwards [d.hasDerivAt_monotonicityM] with s h hs
    exact (h hs).add (((hasDerivAt_id s).const_mul (κ * Λ)).congr_deriv (mul_one _))
  · filter_upwards [d.ae_monotonicityM_sq_term_nonneg, d.ae_monotonicityM_deriv_add_nonneg hΛ]
      with s h1 h2 hs
    exact (h1 hs).trans (h2 hs)

/-- **Integrated Weiss formula**: if `V H ≤ Λ` on `(a, b)`, then
`∫_{s₁}^{s₂} (2 / s^{n+2}) ∫_{∂B_s} (u - ∇u·y)² ≤ M(s₂) - M(s₁) + κ Λ (s₂ - s₁)`. -/
theorem integral_monotonicityM_sq_term_le {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc a b) (hs₂ : s₂ ∈ Icc a b)
    (h12 : s₁ ≤ s₂) :
    ∫ s in s₁..s₂, 2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) ≤
      d.monotonicityM s₂ - d.monotonicityM s₁ + κ * Λ * (s₂ - s₁) := by
  have hAC : AbsolutelyContinuousOnInterval (fun s => κ * Λ * s) a b :=
    ContDiffOn.absolutelyContinuousOnInterval
      (by fun_prop : ContDiff ℝ 1 fun s : ℝ => κ * Λ * s).contDiffOn
  have h := ((d.absolutelyContinuousOnInterval_monotonicityM.fun_add hAC).mono_Icc d.le hs₁ hs₂
    ).integral_le_sub_of_ae_le h12
    (f' := fun s => 2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) + d.err s +
      κ * Λ)
    (ae_mem_Ioo_imp_mono hs₁.1 hs₂.2 (by
      filter_upwards [d.hasDerivAt_monotonicityM] with s h hs
      exact (h hs).add (((hasDerivAt_id s).const_mul (κ * Λ)).congr_deriv (mul_one _))))
    (ae_mem_Ioo_imp_mono hs₁.1 hs₂.2 d.ae_monotonicityM_sq_term_nonneg)
    (ae_mem_Ioo_imp_mono hs₁.1 hs₂.2 (d.ae_monotonicityM_deriv_add_nonneg hΛ))
  linarith

end WeissBound

/-- `β W - β² s / 8 ≤ (2 / s) W²` for `s > 0`. -/
theorem mul_sub_sq_mul_le_two_div_mul_sq {s : ℝ} (hs : 0 < s) (β W : ℝ) :
    β * W - β ^ 2 * s / 8 ≤ 2 / s * W ^ 2 := by
  have h : 0 ≤ (4 * W - β * s) ^ 2 / (8 * s) := by positivity
  have e : (4 * W - β * s) ^ 2 / (8 * s) = 2 / s * W ^ 2 - (β * W - β ^ 2 * s / 8) := by
    field_simp
    ring
  linarith

/-! ### The frequency and the shifted Weiss energy -/

section Frequency

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s)
include hH

theorem exists_pos_le_heightH : ∃ c, 0 < c ∧ ∀ s ∈ Icc a b, c ≤ d.heightH s :=
  d.continuousOn_heightH.exists_pos_le_of_isCompact isCompact_Icc hH

/-- `N` is Lipschitz on `[a, b]` when `H > 0` there. -/
theorem exists_lipschitzOnWith_frequencyN : ∃ K, LipschitzOnWith K d.frequencyN (Icc a b) := by
  obtain ⟨c, hc, hcH⟩ := d.exists_pos_le_heightH hH
  obtain ⟨KD, hKD⟩ := d.lipschitzOnWith_energyD
  obtain ⟨KH, hKH⟩ := d.lipschitzOnWith_heightH
  have hD' : LipschitzOnWith KD (fun s => d.energyD s - ω) (Icc a b) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      change dist (d.energyD x - ω) (d.energyD y - ω) ≤ KD * dist x y
      rw [dist_sub_right]
      exact hKD.dist_le_mul x hx y hy
  obtain ⟨A, hA⟩ := hD'.exists_abs_le isCompact_Icc
  obtain ⟨Kinv, hKinv⟩ := hKH.exists_inv hc hcH
  have hB : ∀ s ∈ Icc a b, |(d.heightH s)⁻¹| ≤ c⁻¹ := fun s hs => by
    rw [abs_inv, abs_of_pos (hc.trans_le (hcH s hs))]
    exact inv_anti₀ hc (hcH s hs)
  obtain ⟨K, hK⟩ := hD'.exists_mul hKinv hA hB
  refine ⟨K, ?_⟩
  have heq : d.frequencyN = fun s => (d.energyD s - ω) * (d.heightH s)⁻¹ := by
    funext s
    rw [frequencyN, div_eq_mul_inv]
  rw [heq]
  exact hK

theorem absolutelyContinuousOnInterval_frequencyN :
    AbsolutelyContinuousOnInterval d.frequencyN a b :=
  let ⟨_, hK⟩ := d.exists_lipschitzOnWith_frequencyN hH
  hK.absolutelyContinuousOnInterval_of_Icc d.le

/-- `log H` is Lipschitz on `[a, b]` when `H > 0` there. -/
theorem exists_lipschitzOnWith_log_heightH :
    ∃ K, LipschitzOnWith K (fun s => Real.log (d.heightH s)) (Icc a b) := by
  obtain ⟨c, hc, hcH⟩ := d.exists_pos_le_heightH hH
  obtain ⟨KH, hKH⟩ := d.lipschitzOnWith_heightH
  exact hKH.exists_log hc hcH

/-- **Refined Weiss identity**: for a.e. `s`, with `l = N + V`,
`M' = (2 / s^{n+2}) ∫_{∂B_s} (∇u·y - l u)² + (2/s) H (l - 1)² + err`. -/
theorem hasDerivAt_monotonicityM_refined : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.monotonicityM
      (2 / s ^ (n + 2) * (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
          (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
        2 / s * d.heightH s * (d.frequencyN s + d.volumeV s - 1) ^ 2 + d.err s) s := by
  filter_upwards [d.hasDerivAt_monotonicityM, d.ae_sphMix_eq] with s hM hQ hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  have hh : d.heightH s ≠ 0 := (hH s hs').ne'
  refine (hM hs).congr_deriv ?_
  rw [hQ hs hh, d.sphSq_eq hs']
  field_simp
  ring

/-- Formula (4.13) with error: for a.e. `s`,
`N' = (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - N u)² + (2/s) V (N - 1) + err / H`. -/
theorem hasDerivAt_frequencyN' : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.frequencyN
      (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s * (d.frequencyN s - 1)) + d.err s / d.heightH s) s := by
  filter_upwards [d.hasDerivAt_energyD, d.hasDerivAt_heightH, d.ae_sphMix_eq] with
    s hD hHd hQ hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  have hh : d.heightH s ≠ 0 := (hH s hs').ne'
  have hder := ((hD hs).sub_const ω).div (hHd hs) hh
  refine hder.congr_deriv ?_
  have hN : d.energyD s - ω = d.frequencyN s * d.heightH s := by
    rw [frequencyN, div_mul_cancel₀ _ hh]
  rw [hN, hQ hs hh, d.sphSq_eq hs']
  field_simp
  ring

/-- Formula (4.12) with error: for a.e. `s`,
`N' = (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - (N+V) u)² + (2/s)(V² + V (N - 1)) + err / H`. -/
theorem hasDerivAt_frequencyN : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.frequencyN
      (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s ^ 2 + d.volumeV s * (d.frequencyN s - 1)) +
          d.err s / d.heightH s) s := by
  filter_upwards [d.hasDerivAt_frequencyN' hH, d.ae_sphMix_eq] with s hN hQ hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  have hh : d.heightH s ≠ 0 := (hH s hs').ne'
  refine (hN hs).congr_deriv ?_
  rw [hQ hs hh, d.sphSq_eq hs']
  field_simp
  ring

/-- `H' = (2/s) H (N + V - 1)` for a.e. `s`. -/
theorem hasDerivAt_heightH' : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.heightH (2 / s * d.heightH s * (d.frequencyN s + d.volumeV s - 1)) s := by
  filter_upwards [d.hasDerivAt_heightH, d.ae_sphMix_eq] with s hHd hQ hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  have hh : d.heightH s ≠ 0 := (hH s hs').ne'
  refine (hHd hs).congr_deriv ?_
  rw [hQ hs hh]
  field_simp
  ring

/-- `(log H)' = (2/s)(N + V - 1)` for a.e. `s`. -/
theorem hasDerivAt_log_heightH : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt (fun s => Real.log (d.heightH s))
      (2 / s * (d.frequencyN s + d.volumeV s - 1)) s := by
  filter_upwards [d.hasDerivAt_heightH' hH] with s hHd hs
  have hs' := Ioo_subset_Icc_self hs
  have hh : d.heightH s ≠ 0 := (hH s hs').ne'
  refine ((hHd hs).log hh).congr_deriv ?_
  rw [mul_comm (2 / s) (d.heightH s), mul_assoc, mul_div_cancel_left₀ _ hh]

omit hH in
theorem absolutelyContinuousOnInterval_modM : AbsolutelyContinuousOnInterval d.modM a b :=
  (d.absolutelyContinuousOnInterval_monotonicityM.fun_sub
    (ContDiffOn.absolutelyContinuousOnInterval (f := fun _ : ℝ => ω) contDiffOn_const)).fun_add
    ((ContDiffOn.absolutelyContinuousOnInterval
      (by fun_prop : ContDiff ℝ 1 fun s : ℝ => κ ^ 2 * s ^ 2 / 8).contDiffOn).fun_mul
      d.absolutelyContinuousOnInterval_heightH)

/-- **Derivative of the shifted Weiss energy**: for a.e. `s`, with `l = N + V`,
`Z' = (2 / s^{n+2}) ∫_{∂B_s} (∇u·y - l u)² + H ((2/s)(l - 1)² + (κ² s / 4)(l - 1) + κ² s / 4)
+ err`. -/
theorem hasDerivAt_modM : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.modM
      (2 / s ^ (n + 2) * (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
          (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
        d.heightH s * (2 / s * (d.frequencyN s + d.volumeV s - 1) ^ 2 +
          κ ^ 2 * s / 4 * (d.frequencyN s + d.volumeV s - 1) + κ ^ 2 * s / 4) + d.err s) s := by
  filter_upwards [d.hasDerivAt_monotonicityM_refined hH, d.hasDerivAt_heightH' hH] with
    s hM hHd hs
  have hs0 : s ≠ 0 := (d.pos.trans hs.1).ne'
  have hq : HasDerivAt (fun s => κ ^ 2 * s ^ 2 / 8) (κ ^ 2 * s / 4) s := by
    have := ((hasDerivAt_pow 2 s).const_mul (κ ^ 2)).div_const 8
    convert this using 1
    push_cast
    ring
  refine (((hM hs).sub_const ω).add (hq.mul (hHd hs))).congr_deriv ?_
  field_simp
  ring

/-- The key differential inequality for the shifted Weiss energy: if `κ b ≤ 1/2`, then
`Z' ≥ 2 κ Z` for a.e. `s` with `Z(s) < 0`. -/
theorem ae_two_mul_modM_le_deriv (hκ : κ * b ≤ 1 / 2) : ∀ᵐ s, s ∈ Ioo a b → d.modM s < 0 →
    2 * κ * d.modM s ≤
      2 / s ^ (n + 2) * (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
          (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
        d.heightH s * (2 / s * (d.frequencyN s + d.volumeV s - 1) ^ 2 +
          κ ^ 2 * s / 4 * (d.frequencyN s + d.volumeV s - 1) + κ ^ 2 * s / 4) + d.err s := by
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le, d.ae_neg_le_err] with
    s h1 h2 h3 he hs hZ
  have hs' := Ioo_subset_Icc_self hs
  have hs0 := d.pos_of_mem hs'
  have hh := hH s hs'
  have hk := d.kappa_nonneg
  have hks : κ * s ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hs.2.le hk).trans hκ
  have hks0 : 0 ≤ κ * s := mul_nonneg hk hs0.le
  have hq := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / s ^ (n + 2))
    (Abstract.sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
      (d.frequencyN s + d.volumeV s))
  have herr := he hs
  rw [d.sub_chiInt_div_eq hh.ne'] at herr
  rw [d.modM_eq hh.ne'] at hZ ⊢
  set N := d.frequencyN s
  set V := d.volumeV s
  set H := d.heightH s
  have hx : N - 1 + κ ^ 2 * s ^ 2 / 8 < 0 := by
    by_contra hc
    push Not at hc
    exact absurd hZ (not_lt.2 (mul_nonneg hh.le hc))
  have hA := mul_sub_sq_mul_le_two_div_mul_sq hs0 (κ * (1 - κ * s / 4)) (N + V - 1)
  have hkx := mul_nonpos_of_nonneg_of_nonpos hk hx.le
  have hpoly : 0 ≤ κ ^ 2 * s / 8 * (1 - κ * s / 2 - (κ * s) ^ 2 / 16) :=
    mul_nonneg (by positivity) (by nlinarith)
  have key : 0 ≤ 2 / s * (N + V - 1) ^ 2 + κ ^ 2 * s / 4 * (N + V - 1) + κ ^ 2 * s / 4 -
      κ * V - 2 * κ * (N - 1 + κ ^ 2 * s ^ 2 / 8) := by
    linarith
  have := mul_nonneg hh.le key
  linarith

/-- **First crossing for the shifted Weiss energy**: if `H > 0` on `[a, b]` and `κ b ≤ 1/2`, then
`Z(s) ≥ e^{2κ(s-a)} min(Z(a), 0)` for `s ∈ [a, b]`. -/
theorem modM_ge (hκ : κ * b ≤ 1 / 2) {s : ℝ} (hs : s ∈ Icc a b) :
    Real.exp (2 * κ * (s - a)) * min (d.modM a) 0 ≤ d.modM s := by
  set m := min (d.modM a) 0 with hm
  set G : ℝ → ℝ := fun s => Real.exp (-(2 * κ * (s - a))) * d.modM s with hG
  have hGAC : AbsolutelyContinuousOnInterval G a b :=
    (ContDiffOn.absolutelyContinuousOnInterval (by fun_prop :
      ContDiff ℝ 1 fun s : ℝ => Real.exp (-(2 * κ * (s - a)))).contDiffOn).fun_mul
      d.absolutelyContinuousOnInterval_modM
  have hGcont : ContinuousOn G (Icc a b) := by
    have := hGAC.continuousOn
    rwa [uIcc_of_le d.le] at this
  have hG' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt G (Real.exp (-(2 * κ * (x - a))) *
      ((2 / x ^ (n + 2) * (d.sphRad x - 2 * (d.frequencyN x + d.volumeV x) * d.sphMix x +
          (d.frequencyN x + d.volumeV x) ^ 2 * d.sphSq x) +
        d.heightH x * (2 / x * (d.frequencyN x + d.volumeV x - 1) ^ 2 +
          κ ^ 2 * x / 4 * (d.frequencyN x + d.volumeV x - 1) + κ ^ 2 * x / 4) + d.err x) -
        2 * κ * d.modM x)) x := by
    filter_upwards [d.hasDerivAt_modM hH] with x hx hmem
    have he : HasDerivAt (fun s => Real.exp (-(2 * κ * (s - a))))
        (Real.exp (-(2 * κ * (x - a))) * (-(2 * κ * 1))) x :=
      ((((hasDerivAt_id x).sub_const a).const_mul (2 * κ)).neg).exp
    exact (he.mul (hx hmem)).congr_deriv (by ring)
  have hG'0 : ∀ᵐ x, x ∈ Ioo a b → d.modM x < 0 → 0 ≤ Real.exp (-(2 * κ * (x - a))) *
      ((2 / x ^ (n + 2) * (d.sphRad x - 2 * (d.frequencyN x + d.volumeV x) * d.sphMix x +
          (d.frequencyN x + d.volumeV x) ^ 2 * d.sphSq x) +
        d.heightH x * (2 / x * (d.frequencyN x + d.volumeV x - 1) ^ 2 +
          κ ^ 2 * x / 4 * (d.frequencyN x + d.volumeV x - 1) + κ ^ 2 * x / 4) + d.err x) -
        2 * κ * d.modM x) := by
    filter_upwards [d.ae_two_mul_modM_le_deriv hH hκ] with x hx hmem hneg
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (hx hmem hneg))
  have key : ∀ s ∈ Icc a b, m ≤ G s := by
    intro s₀ hs₀
    by_contra hlt
    push Not at hlt
    set S := Icc a s₀ ∩ G ⁻¹' Ici m with hS
    have hSc : IsClosed S :=
      (hGcont.mono (Icc_subset_Icc_right hs₀.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have haS : a ∈ S := ⟨left_mem_Icc.2 hs₀.1, by simp [G, m]⟩
    have hbdd : BddAbove S := ⟨s₀, fun x hx => hx.1.2⟩
    have hs₁S : sSup S ∈ S := hSc.csSup_mem ⟨a, haS⟩ hbdd
    have hs₁lt : sSup S < s₀ := by
      refine lt_of_le_of_ne hs₁S.1.2 fun h => ?_
      have := hs₁S.2
      rw [h] at this
      exact absurd (mem_Ici.1 this) (not_le.2 hlt)
    have hneg : ∀ x ∈ Ioc (sSup S) s₀, G x < m := fun x hx => by
      by_contra hc
      push Not at hc
      have : x ≤ sSup S := le_csSup hbdd ⟨⟨hs₁S.1.1.trans hx.1.le, hx.2⟩, hc⟩
      linarith [hx.1]
    have hs₁ab : sSup S ∈ Icc a b := ⟨hs₁S.1.1, hs₁lt.le.trans hs₀.2⟩
    have hmono : MonotoneOn G (Icc (sSup S) s₀) := by
      refine (hGAC.mono_Icc d.le hs₁ab hs₀).monotoneOn_of_ae_hasDerivAt_nonneg
        (ae_mem_Ioo_imp_mono hs₁ab.1 hs₀.2 hG') ?_
      filter_upwards [hG'0] with x hx hmem
      have hmem' : x ∈ Ioo a b := ⟨hs₁ab.1.trans_lt hmem.1, hmem.2.trans_le hs₀.2⟩
      refine hx hmem' ?_
      have hGx : G x < 0 := (hneg x ⟨hmem.1, hmem.2.le⟩).trans_le (min_le_right _ _)
      by_contra hc
      push Not at hc
      exact absurd hGx (not_lt.2 (mul_nonneg (Real.exp_pos _).le hc))
    have := hmono (left_mem_Icc.2 hs₁lt.le) (right_mem_Icc.2 hs₁lt.le) hs₁lt.le
    have h1 : m ≤ G (sSup S) := hs₁S.2
    linarith
  have hZ : d.modM s = Real.exp (2 * κ * (s - a)) * G s := by
    simp only [G]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [hZ]
  exact mul_le_mul_of_nonneg_left (key s hs) (Real.exp_pos _).le

/-- `Z ≥ 0` propagates to the right: if `H > 0` on `[a, b]`, `κ b ≤ 1/2` and `Z(a) ≥ 0`, then
`Z ≥ 0` on `[a, b]`. -/
theorem modM_nonneg (hκ : κ * b ≤ 1 / 2) (hZ : 0 ≤ d.modM a) {s : ℝ} (hs : s ∈ Icc a b) :
    0 ≤ d.modM s := by
  have := d.modM_ge hH hκ hs
  rwa [min_eq_right hZ, mul_zero] at this

end Frequency

end RadialDataErr

namespace RadialData

variable {n : ℕ} {ω a b : ℝ} (d : RadialData n ω a b)

/-- Radial data for `Q ≡ 1` are radial data with error `0` and `κ = 0`. -/
def toErr : RadialDataErr n ω 0 a b where
  gradInt := d.gradInt
  chiInt := d.chiInt
  sphSq := d.sphSq
  sphMix := d.sphMix
  sphRad := d.sphRad
  energyD := d.energyD
  heightH := d.heightH
  err := 0
  pos := d.pos
  le := d.le
  kappa_nonneg := le_rfl
  energyD_eq := d.energyD_eq
  heightH_eq := d.heightH_eq
  lipschitzOnWith_energyD := d.lipschitzOnWith_energyD
  lipschitzOnWith_heightH := d.lipschitzOnWith_heightH
  chiInt_le := d.chiInt_le
  monotoneOn_sub_chiInt := d.monotoneOn_sub_chiInt
  gradInt_eq := d.gradInt_eq
  hasDerivAt_energyD := by
    filter_upwards [d.hasDerivAt_energyD] with s hs hmem
    simpa using hs hmem
  abs_err_le := .of_forall fun s _ => by simp
  hasDerivAt_heightH := d.hasDerivAt_heightH
  sphSq_nonneg := d.sphSq_nonneg
  sphRad_nonneg := d.sphRad_nonneg
  sq_sphMix_le := d.sq_sphMix_le

section ToErr

@[simp] theorem toErr_gradInt : d.toErr.gradInt = d.gradInt := rfl
@[simp] theorem toErr_chiInt : d.toErr.chiInt = d.chiInt := rfl
@[simp] theorem toErr_sphSq : d.toErr.sphSq = d.sphSq := rfl
@[simp] theorem toErr_sphMix : d.toErr.sphMix = d.sphMix := rfl
@[simp] theorem toErr_sphRad : d.toErr.sphRad = d.sphRad := rfl
@[simp] theorem toErr_energyD : d.toErr.energyD = d.energyD := rfl
@[simp] theorem toErr_heightH : d.toErr.heightH = d.heightH := rfl
@[simp] theorem toErr_err : d.toErr.err = 0 := rfl
@[simp] theorem toErr_monotonicityM : d.toErr.monotonicityM = d.monotonicityM := rfl
@[simp] theorem toErr_frequencyN : d.toErr.frequencyN = d.frequencyN := rfl
@[simp] theorem toErr_volumeV : d.toErr.volumeV = d.volumeV := rfl

/-- For `κ = 0` the shifted Weiss energy is `M - ω`. -/
@[simp] theorem toErr_modM (s : ℝ) : d.toErr.modM s = d.monotonicityM s - ω := by
  simp [RadialDataErr.modM]

/-- For `κ = 0` the modified frequency is `N`. -/
@[simp] theorem toErr_modN : d.toErr.modN = d.frequencyN := by
  funext s
  simp [RadialDataErr.modN]

end ToErr

end RadialData

end InnerVariational.Abstract
