/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.LipschitzFTC
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The abstract monotonicity and frequency calculus (Sections 3.3 and 4, one-dimensional part)

This file proves every statement of Sections 3.3 and 4 of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2), that is calculus of one real variable. The geometric input (derivative
formulas, the energy identity, Cauchy–Schwarz) enters as hypotheses, packaged in the structure
`RadialData`. `Monotonicity/Radial.lean` instantiates the package for a variational solution at a
point, and `Frequency/Concrete.lean` restates the results with the concrete names.

## The radial data

Fix `n : ℕ`, a real number `ω` (in applications `ω = |B_1|`) and a closed interval `[a, b]` with
`0 < a`. For a variational solution `(u, χ)` centred at a point, the radial data consist of
(`s` the radius, `y` the position relative to the centre)
* `gradInt s = ∫_{B_s} |∇u|²` (the paper's `∫_{B_s}|∇u|²`),
* `chiInt s = ∫_{B_s} χ`,
* `sphSq s = ∫_{∂B_s} u²`,
* `sphMix s = ∫_{∂B_s} u ∇u·y`,
* `sphRad s = ∫_{∂B_s} (∇u·y)²`,
together with `energyD = s^{-n} (gradInt + chiInt)` and `heightH = s^{-(n+1)} sphSq`
(§3.3 of the paper). We then define `monotonicityM = D - H`, `frequencyN = (D - ω) / H` and
`volumeV = (ω - s^{-n} chiInt) / H`. Since `∫_{B_s} 1 = ω s^n`, the latter is
`s^{-n} ∫_{B_s}(1 - χ) / H`. The paper (beginning of §4) defines `V = ∫_{B_s}(1 - χ) / H`,
**without the factor `s^{-n}`**; with that definition the identity (4.11),
`N + V = s ∫_{B_s}|∇u|² / ∫_{∂B_s} u²`, fails for `s ≠ 1`, and the frequency derivative (4.12)
rests on (4.11). We include the factor. The proofs are unaffected up to constants.

## Main results

* `RadialData.hasDerivAt_monotonicityM`, `RadialData.monotoneOn_monotonicityM`: the derivative
  of `M` (Proposition 3.4 and its proof) and its monotonicity.
* `RadialData.frequencyN_add_volumeV`: identity (4.11).
* `RadialData.hasDerivAt_frequencyN` and `RadialData.hasDerivAt_frequencyN'`: the derivative of
  the frequency, in the forms (4.12) and (4.13) (Lemma 4.1 and Remark 4.2).
* `RadialData.one_le_frequencyN`, `RadialData.monotoneOn_frequencyN`: Lemma 4.1.
* `RadialData.heightH_doubling`: Lemma 4.3.
* `RadialData.volumeV_doubling`: Lemma 4.4, with constant `2^n C` (the factor `2^n` comes from
  the `s^{-n}` in `V`).
* `RadialData.volumeV_le_sqrt`: Lemma 4.5.
* `RadialData.integral_frequency_sq_term_le`, `RadialData.integral_volumeV_sq_le`: the integrated
  forms of Lemma 4.1 used in the proofs of Theorems 6.1 and 6.3.

Every lemma is stated for a general subinterval of the data interval, since radial data cannot
be rescaled cheaply.

## Implementation notes

* A.e. hypotheses are stated as `∀ᵐ s, s ∈ Ioo a b → _`; conclusions are pointwise.
* The paper's convention `N = -∞` when `H = 0` is replaced by Lean's `x / 0 = 0`; every
  statement about `N` assumes `H > 0` on the relevant interval.
* Lemma 4.3 is proved without integrating `V`: the paper's Cauchy–Schwarz step is replaced by the
  pointwise inequality `2V ≤ V²/ε + ε` and a comparison of derivatives. This avoids any
  measurability assumption on the radial data and gives the paper's constant.
-/

open MeasureTheory Set Filter
open scoped NNReal

@[expose] public noncomputable section

namespace InnerVariational.Abstract

/-- The discriminant form of Cauchy–Schwarz: if `Q² ≤ P R` with `P, R ≥ 0`, then
`R - 2 λ Q + λ² P ≥ 0` for every `λ` (it is `∫ (∇u·y - λ u)²` in the application). -/
theorem sub_two_mul_add_sq_mul_nonneg {P Q R : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R)
    (hQ : Q ^ 2 ≤ P * R) (l : ℝ) : 0 ≤ R - 2 * l * Q + l ^ 2 * P := by
  rcases hP.eq_or_lt with rfl | hP
  · have hQ2 : Q ^ 2 = 0 := le_antisymm (by simpa using hQ) (sq_nonneg Q)
    have hQ0 : Q = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hQ2
    subst hQ0
    simpa using hR
  · have h : 0 ≤ P * (R - 2 * l * Q + l ^ 2 * P) := by nlinarith [sq_nonneg (l * P - Q)]
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_pos_of_neg hP hneg]

/-- **Radial data** of a variational solution at a point, on the radius interval `[a, b]`.

The fields `gradInt`, `chiInt`, `sphSq`, `sphMix`, `sphRad` are the radial integrals
`∫_{B_s}|∇u|²`, `∫_{B_s}χ`, `∫_{∂B_s}u²`, `∫_{∂B_s}u∇u·y`, `∫_{∂B_s}(∇u·y)²`, and `energyD`,
`heightH` are `D_x(u;s)` and `H_x(u;s)` (§3.3). The hypotheses are the one-dimensional
consequences of the variational-solution property used in Sections 3.3 and 4:
the energy identity (3.8), the derivative formulas for `D` and `H` (proof of Proposition 3.4),
Cauchy–Schwarz on the sphere, and the Lipschitz bounds on `D` and `H` (ibid.). -/
structure RadialData (n : ℕ) (ω a b : ℝ) where
  /-- `s ↦ ∫_{B_s} |∇u|²`. -/
  gradInt : ℝ → ℝ
  /-- `s ↦ ∫_{B_s} χ`. -/
  chiInt : ℝ → ℝ
  /-- `s ↦ ∫_{∂B_s} u²`. -/
  sphSq : ℝ → ℝ
  /-- `s ↦ ∫_{∂B_s} u ∇u·y`. -/
  sphMix : ℝ → ℝ
  /-- `s ↦ ∫_{∂B_s} (∇u·y)²`. -/
  sphRad : ℝ → ℝ
  /-- `D(s) = s^{-n} ∫_{B_s} (|∇u|² + χ)`. -/
  energyD : ℝ → ℝ
  /-- `H(s) = s^{-(n+1)} ∫_{∂B_s} u²`. -/
  heightH : ℝ → ℝ
  pos : 0 < a
  le : a ≤ b
  energyD_eq : ∀ s ∈ Icc a b, energyD s = (gradInt s + chiInt s) / s ^ n
  heightH_eq : ∀ s ∈ Icc a b, heightH s = sphSq s / s ^ (n + 1)
  lipschitzOnWith_energyD : ∃ K, LipschitzOnWith K energyD (Icc a b)
  lipschitzOnWith_heightH : ∃ K, LipschitzOnWith K heightH (Icc a b)
  /-- `∫_{B_s} χ ≤ |B_s| = ω s^n`. -/
  chiInt_le : ∀ s ∈ Icc a b, chiInt s ≤ ω * s ^ n
  /-- `s ↦ ∫_{B_s} (1 - χ)` is nondecreasing. -/
  monotoneOn_sub_chiInt : MonotoneOn (fun s => ω * s ^ n - chiInt s) (Icc a b)
  /-- The energy identity (3.8): `∫_{B_s}|∇u|² = ∫_{∂B_s} u ∇u·y/|y|`. -/
  gradInt_eq : ∀ᵐ s, s ∈ Ioo a b → gradInt s = sphMix s / s
  /-- `D' = (2 / s^(n+2)) ∫_{∂B_s} ((∇u·y)² - u ∇u·y)` (proof of Proposition 3.4). -/
  hasDerivAt_energyD : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt energyD (2 / s ^ (n + 2) * (sphRad s - sphMix s)) s
  /-- `H' = -(2/s) H + (2 / s^(n+2)) ∫_{∂B_s} u ∇u·y` (proof of Proposition 3.4). -/
  hasDerivAt_heightH : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt heightH (-(2 / s) * heightH s + 2 / s ^ (n + 2) * sphMix s) s
  sphSq_nonneg : ∀ᵐ s, s ∈ Ioo a b → 0 ≤ sphSq s
  sphRad_nonneg : ∀ᵐ s, s ∈ Ioo a b → 0 ≤ sphRad s
  /-- Cauchy–Schwarz on `∂B_s`. -/
  sq_sphMix_le : ∀ᵐ s, s ∈ Ioo a b → sphMix s ^ 2 ≤ sphSq s * sphRad s

namespace RadialData

variable {n : ℕ} {ω a b : ℝ} (d : RadialData n ω a b)

/-- The monotonicity formula `M = D - H` (§3.3). -/
def monotonicityM (s : ℝ) : ℝ := d.energyD s - d.heightH s

/-- The frequency `N = (D - ω) / H` (§4), with `N = 0` when `H = 0` (the paper sets
`N = -∞` there). -/
def frequencyN (s : ℝ) : ℝ := (d.energyD s - ω) / d.heightH s

/-- The volume term `V = s^{-n} ∫_{B_s}(1 - χ) / H = (ω - s^{-n} ∫_{B_s} χ) / H`
(§4; the paper's printed definition omits the factor `s^{-n}`, see the module docstring). -/
def volumeV (s : ℝ) : ℝ := (ω - d.chiInt s / s ^ n) / d.heightH s

/-- Restriction of radial data to a subinterval. -/
def restrict {c e : ℝ} (hc : a ≤ c) (hce : c ≤ e) (he : e ≤ b) : RadialData n ω c e where
  gradInt := d.gradInt
  chiInt := d.chiInt
  sphSq := d.sphSq
  sphMix := d.sphMix
  sphRad := d.sphRad
  energyD := d.energyD
  heightH := d.heightH
  pos := d.pos.trans_le hc
  le := hce
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
  hasDerivAt_heightH := ae_mem_Ioo_imp_mono hc he d.hasDerivAt_heightH
  sphSq_nonneg := ae_mem_Ioo_imp_mono hc he d.sphSq_nonneg
  sphRad_nonneg := ae_mem_Ioo_imp_mono hc he d.sphRad_nonneg
  sq_sphMix_le := ae_mem_Ioo_imp_mono hc he d.sq_sphMix_le

section Restrict

variable {c e : ℝ} (hc : a ≤ c) (hce : c ≤ e) (he : e ≤ b)

@[simp] theorem restrict_energyD : (d.restrict hc hce he).energyD = d.energyD := rfl
@[simp] theorem restrict_heightH : (d.restrict hc hce he).heightH = d.heightH := rfl
@[simp] theorem restrict_chiInt : (d.restrict hc hce he).chiInt = d.chiInt := rfl
@[simp] theorem restrict_sphSq : (d.restrict hc hce he).sphSq = d.sphSq := rfl
@[simp] theorem restrict_sphMix : (d.restrict hc hce he).sphMix = d.sphMix := rfl
@[simp] theorem restrict_sphRad : (d.restrict hc hce he).sphRad = d.sphRad := rfl
@[simp] theorem restrict_monotonicityM :
    (d.restrict hc hce he).monotonicityM = d.monotonicityM := rfl
@[simp] theorem restrict_frequencyN : (d.restrict hc hce he).frequencyN = d.frequencyN := rfl
@[simp] theorem restrict_volumeV : (d.restrict hc hce he).volumeV = d.volumeV := rfl

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

/-- `V = s^{-n} ∫_{B_s}(1-χ) / H`. -/
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

/-- **Identity (4.11)**: `N + V = s^{-n} ∫_{B_s}|∇u|² / H`. -/
theorem frequencyN_add_volumeV {s : ℝ} (hs : s ∈ Icc a b) :
    d.frequencyN s + d.volumeV s = d.gradInt s / s ^ n / d.heightH s := by
  rw [frequencyN, volumeV, ← add_div]
  congr 1
  rw [d.energyD_eq s hs, add_div]
  ring

/-- Consequence of (3.8) and (4.11): `∫_{∂B_s} u ∇u·y = s^{n+1} H (N + V)` for a.e. `s`. -/
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

/-- A key observation: `N > 1` if and only if `M > ω` (when `H > 0`). -/
theorem one_lt_frequencyN_iff {s : ℝ} (hH : 0 < d.heightH s) :
    1 < d.frequencyN s ↔ ω < d.monotonicityM s := by
  rw [frequencyN, monotonicityM, lt_div_iff₀ hH]
  constructor <;> intro h <;> linarith

theorem lt_monotonicityM_of_one_lt_frequencyN {s : ℝ} (hH : 0 < d.heightH s)
    (hN : 1 < d.frequencyN s) : ω < d.monotonicityM s :=
  (d.one_lt_frequencyN_iff hH).1 hN

/-! ### Result 1: the monotonicity formula -/

/-- **Derivative of `M`** (Proposition 3.4): for a.e. `s`,
`M' = (2 / s^{n+2}) (R - 2Q + P) = (2 / s^{n+2}) ∫_{∂B_s} (u - ∇u·y)²`. -/
theorem hasDerivAt_monotonicityM : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.monotonicityM (2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s)) s := by
  filter_upwards [d.hasDerivAt_energyD, d.hasDerivAt_heightH] with s hD hH hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  refine ((hD hs).sub (hH hs)).congr_deriv ?_
  rw [d.sphSq_eq hs']
  field_simp
  ring

theorem ae_monotonicityM_deriv_nonneg : ∀ᵐ s, s ∈ Ioo a b →
    0 ≤ 2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) := by
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
  have hs0 : 0 < s := d.pos.trans hs.1
  have hq := sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs) 1
  simp only [mul_one, one_pow, one_mul] at hq
  exact mul_nonneg (by positivity) hq

theorem absolutelyContinuousOnInterval_monotonicityM :
    AbsolutelyContinuousOnInterval d.monotonicityM a b :=
  d.absolutelyContinuousOnInterval_energyD.fun_sub d.absolutelyContinuousOnInterval_heightH

/-- **`M` is nondecreasing** (Proposition 3.4). -/
theorem monotoneOn_monotonicityM : MonotoneOn d.monotonicityM (Icc a b) :=
  d.absolutelyContinuousOnInterval_monotonicityM.monotoneOn_of_ae_hasDerivAt_nonneg
    d.hasDerivAt_monotonicityM d.ae_monotonicityM_deriv_nonneg

/-! ### Result 3: the frequency formula (Lemma 4.1) -/

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

/-- **Remark 4.2, formula (4.13)**: for a.e. `s`,
`N' = (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - N u)² + (2/s) V (N - 1)`. -/
theorem hasDerivAt_frequencyN' : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.frequencyN
      (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s * (d.frequencyN s - 1))) s := by
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

/-- **Lemma 4.1, formula (4.12)**: for a.e. `s`,
`N' = (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - (N+V) u)² + (2/s)(V² + V (N - 1))`. -/
theorem hasDerivAt_frequencyN : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.frequencyN
      (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s ^ 2 + d.volumeV s * (d.frequencyN s - 1))) s := by
  filter_upwards [d.hasDerivAt_frequencyN' hH, d.ae_sphMix_eq] with s hN hQ hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 : s ≠ 0 := (d.pos_of_mem hs').ne'
  have hh : d.heightH s ≠ 0 := (hH s hs').ne'
  refine (hN hs).congr_deriv ?_
  rw [hQ hs hh, d.sphSq_eq hs']
  field_simp
  ring

/-- `H' = (2/s) H (N + V - 1)` for a.e. `s` (proof of Lemma 4.3). -/
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

/-- `(log H)' = (2/s)(N + V - 1)` for a.e. `s` (proof of Lemma 4.3). -/
theorem hasDerivAt_log_heightH : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt (fun s => Real.log (d.heightH s))
      (2 / s * (d.frequencyN s + d.volumeV s - 1)) s := by
  filter_upwards [d.hasDerivAt_heightH' hH] with s hHd hs
  have hs' := Ioo_subset_Icc_self hs
  have hh : d.heightH s ≠ 0 := (hH s hs').ne'
  refine ((hHd hs).log hh).congr_deriv ?_
  rw [mul_comm (2 / s) (d.heightH s), mul_assoc, mul_div_cancel_left₀ _ hh]

variable (hM : ω ≤ d.monotonicityM a)
include hM

/-- **Lemma 4.1**: `N ≥ 1` on `[a, b]` if `M(a) ≥ ω`. -/
theorem one_le_frequencyN {s : ℝ} (hs : s ∈ Icc a b) : 1 ≤ d.frequencyN s :=
  (d.one_le_frequencyN_iff (hH s hs)).2
    (hM.trans (d.monotoneOn_monotonicityM (left_mem_Icc.2 d.le) hs hs.1))

theorem ae_frequencyN_deriv_nonneg : ∀ᵐ s, s ∈ Ioo a b →
    0 ≤ 2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s * (d.frequencyN s - 1)) := by
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 := d.pos_of_mem hs'
  have hh := hH s hs'
  have hq := sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs) (d.frequencyN s)
  have hN1 := d.one_le_frequencyN hH hM hs'
  have hV := d.volumeV_nonneg hs' hh
  have hc1 : 0 ≤ 2 / (d.heightH s * s ^ (n + 2)) := by positivity
  have hc2 : 0 ≤ 2 / s := by positivity
  exact add_nonneg (mul_nonneg hc1 hq) (mul_nonneg hc2 (mul_nonneg hV (by linarith)))

/-- **Lemma 4.1**: `N` is nondecreasing on `[a, b]` if `M(a) ≥ ω`. -/
theorem monotoneOn_frequencyN : MonotoneOn d.frequencyN (Icc a b) :=
  (d.absolutelyContinuousOnInterval_frequencyN hH).monotoneOn_of_ae_hasDerivAt_nonneg
    (d.hasDerivAt_frequencyN' hH) (d.ae_frequencyN_deriv_nonneg hH hM)

/-- The first term of (4.13) is bounded by `N'`. -/
theorem ae_frequency_sq_term_le : ∀ᵐ s, s ∈ Ioo a b →
    2 / (d.heightH s * s ^ (n + 2)) *
        (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) ≤
      2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s * (d.frequencyN s - 1)) := by
  filter_upwards with s hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 := d.pos_of_mem hs'
  have hN1 := d.one_le_frequencyN hH hM hs'
  have hV := d.volumeV_nonneg hs' (hH s hs')
  have hc2 : 0 ≤ 2 / s := by positivity
  have := mul_nonneg hc2 (mul_nonneg hV (by linarith : 0 ≤ d.frequencyN s - 1))
  linarith

/-- The `V²` term of (4.12) is bounded by `N'`. -/
theorem ae_volumeV_sq_le : ∀ᵐ s, s ∈ Ioo a b →
    2 / s * d.volumeV s ^ 2 ≤
      2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s ^ 2 + d.volumeV s * (d.frequencyN s - 1)) := by
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
  have hs' := Ioo_subset_Icc_self hs
  have hs0 := d.pos_of_mem hs'
  have hh := hH s hs'
  have hq := sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs)
    (d.frequencyN s + d.volumeV s)
  have hN1 := d.one_le_frequencyN hH hM hs'
  have hV := d.volumeV_nonneg hs' hh
  have hc1 : 0 ≤ 2 / (d.heightH s * s ^ (n + 2)) := by positivity
  have hc2 : 0 ≤ 2 / s := by positivity
  have h4 := mul_nonneg hc1 hq
  have h5 := mul_nonneg hc2 (mul_nonneg hV (by linarith : 0 ≤ d.frequencyN s - 1))
  have h6 : 2 / s * (d.volumeV s ^ 2 + d.volumeV s * (d.frequencyN s - 1)) =
      2 / s * d.volumeV s ^ 2 + 2 / s * (d.volumeV s * (d.frequencyN s - 1)) := by ring
  linarith

/-- `H` is nondecreasing on `[a, b]` if `M(a) ≥ ω` (the lower bound of Lemma 4.3). -/
theorem monotoneOn_heightH : MonotoneOn d.heightH (Icc a b) := by
  refine d.absolutelyContinuousOnInterval_heightH.monotoneOn_of_ae_hasDerivAt_nonneg
    (d.hasDerivAt_heightH' hH) (Eventually.of_forall fun s hs => ?_)
  have hs' := Ioo_subset_Icc_self hs
  have hs0 := d.pos_of_mem hs'
  have hh := hH s hs'
  have hN1 := d.one_le_frequencyN hH hM hs'
  have hV := d.volumeV_nonneg hs' hh
  have hc : 0 ≤ 2 / s * d.heightH s := by positivity
  exact mul_nonneg hc (by linarith)

end Frequency

/-! ### Result 7: integrated forms of Lemma 4.1 -/

/-- If `0 ≤ g ≤ f'` a.e. on `(a, b)` for an absolutely continuous `f`, then
`∫_a^b g ≤ f b - f a`. No integrability of `g` is needed: a non-integrable `g` has integral `0`. -/
theorem _root_.AbsolutelyContinuousOnInterval.integral_le_sub_of_ae_le {f f' g : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (f' x) x) (hg0 : ∀ᵐ x, x ∈ Ioo a b → 0 ≤ g x)
    (hle : ∀ᵐ x, x ∈ Ioo a b → g x ≤ f' x) : ∫ x in a..b, g x ≤ f b - f a := by
  have hf'' := ae_mem_uIcc_imp_of_ae_mem_Ioo hab hf'
  have hint := hf.intervalIntegrable_of_ae_hasDerivAt hf''
  rw [← hf.integral_eq_sub_of_ae_hasDerivAt hf'']
  by_cases hg : IntervalIntegrable g volume a b
  · refine intervalIntegral.integral_mono_ae_restrict hab hg hint ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (ae_mem_Icc_imp_of_ae_mem_Ioo hle)
  · rw [intervalIntegral.integral_undef hg]
    refine intervalIntegral.integral_nonneg_of_ae_restrict hab ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_mem_Icc_imp_of_ae_mem_Ioo ?_)
    filter_upwards [hg0, hle] with x h1 h2 hx
    exact (h1 hx).trans (h2 hx)

section Integrated

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM a)
include hH hM

/-- Integrated form of (4.13):
`∫_{s₁}^{s₂} (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - N u)² ≤ N s₂ - N s₁`. -/
theorem integral_frequency_sq_term_le {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc a b) (hs₂ : s₂ ∈ Icc a b)
    (h12 : s₁ ≤ s₂) :
    ∫ s in s₁..s₂, 2 / (d.heightH s * s ^ (n + 2)) *
        (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) ≤
      d.frequencyN s₂ - d.frequencyN s₁ := by
  have hsub₁ : a ≤ s₁ := hs₁.1
  have hsub₂ : s₂ ≤ b := hs₂.2
  refine ((d.absolutelyContinuousOnInterval_frequencyN hH).mono_Icc d.le hs₁ hs₂
    ).integral_le_sub_of_ae_le h12 (ae_mem_Ioo_imp_mono hsub₁ hsub₂
      (d.hasDerivAt_frequencyN' hH)) ?_ (ae_mem_Ioo_imp_mono hsub₁ hsub₂
      (d.ae_frequency_sq_term_le hH hM))
  refine ae_mem_Ioo_imp_mono hsub₁ hsub₂ ?_
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
  have hs0 := d.pos_of_mem (Ioo_subset_Icc_self hs)
  have hh := hH s (Ioo_subset_Icc_self hs)
  exact mul_nonneg (by positivity)
    (sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs) (d.frequencyN s))

/-- Integrated form of (4.12): `∫_{s₁}^{s₂} (2/s) V² ≤ N s₂ - N s₁`. -/
theorem integral_volumeV_sq_le {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc a b) (hs₂ : s₂ ∈ Icc a b)
    (h12 : s₁ ≤ s₂) :
    ∫ s in s₁..s₂, 2 / s * d.volumeV s ^ 2 ≤ d.frequencyN s₂ - d.frequencyN s₁ := by
  have hsub₁ : a ≤ s₁ := hs₁.1
  have hsub₂ : s₂ ≤ b := hs₂.2
  refine ((d.absolutelyContinuousOnInterval_frequencyN hH).mono_Icc d.le hs₁ hs₂
    ).integral_le_sub_of_ae_le h12 (ae_mem_Ioo_imp_mono hsub₁ hsub₂
      (d.hasDerivAt_frequencyN hH)) ?_ (ae_mem_Ioo_imp_mono hsub₁ hsub₂
      (d.ae_volumeV_sq_le hH hM))
  refine Eventually.of_forall fun s hs => ?_
  have hs0 : 0 < s := d.pos.trans_le (hsub₁.trans hs.1.le)
  positivity

end Integrated

/-! ### Results 4–6: doubling of `H` and `V`, vanishing of `V` -/

/-- The constant `C(N₊) = exp(2(N₊ - 1) + 4 √(N₊ - 1))` of Lemma 4.3. -/
def doublingConst (Np : ℝ) : ℝ := Real.exp (2 * (Np - 1) + 4 * √(Np - 1))

theorem doublingConst_pos (Np : ℝ) : 0 < doublingConst Np := Real.exp_pos _

section Doubling

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM a)
include hH hM

/-- Upper bound of Lemma 4.3 on the whole data interval, assuming `b ≤ 2a`. -/
theorem heightH_le_doublingConst_mul (hb : b ≤ 2 * a) {Np : ℝ} (hNp : 1 < Np)
    (hN : d.frequencyN b ≤ Np) {s : ℝ} (hs : s ∈ Icc a b) :
    d.heightH b ≤ doublingConst Np * d.heightH s := by
  have hbmem : b ∈ Icc a b := right_mem_Icc.2 d.le
  set e := √(Np - 1) with he_def
  have he0 : 0 < e := Real.sqrt_pos.2 (by linarith)
  have he2 : e ^ 2 = Np - 1 := Real.sq_sqrt (by linarith)
  set c := 2 * (Np - 1) + e with hc_def
  have hc0 : 0 ≤ c := by rw [hc_def]; linarith
  -- absolute continuity of the two sides of the comparison
  have hfAC : AbsolutelyContinuousOnInterval (fun s => Real.log (d.heightH s)) a b :=
    let ⟨_, hK⟩ := d.exists_lipschitzOnWith_log_heightH hH
    hK.absolutelyContinuousOnInterval_of_Icc d.le
  have hlogAC : AbsolutelyContinuousOnInterval (fun s => Real.log s) a b := by
    obtain ⟨K, hK⟩ := (LipschitzWith.id.lipschitzOnWith (s := Icc a b)).exists_log
      (g := fun s => s) d.pos fun x hx => hx.1
    exact hK.absolutelyContinuousOnInterval_of_Icc d.le
  have hgAC : AbsolutelyContinuousOnInterval
      (fun s => (2 * e)⁻¹ * d.frequencyN s + c * Real.log s) a b :=
    ((d.absolutelyContinuousOnInterval_frequencyN hH).const_mul (2 * e)⁻¹).fun_add
      (hlogAC.const_mul c)
  -- the derivatives
  have hg' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt
      (fun s => (2 * e)⁻¹ * d.frequencyN s + c * Real.log s)
      ((2 * e)⁻¹ * (2 / (d.heightH x * x ^ (n + 2)) *
          (d.sphRad x - 2 * (d.frequencyN x + d.volumeV x) * d.sphMix x +
            (d.frequencyN x + d.volumeV x) ^ 2 * d.sphSq x) +
        2 / x * (d.volumeV x ^ 2 + d.volumeV x * (d.frequencyN x - 1))) + c * x⁻¹) x := by
    filter_upwards [d.hasDerivAt_frequencyN hH] with x hx hmem
    have hx0 : x ≠ 0 := (d.pos.trans hmem.1).ne'
    exact ((hx hmem).const_mul (2 * e)⁻¹).add ((Real.hasDerivAt_log hx0).const_mul c)
  have hle : ∀ᵐ x, x ∈ Ioo a b →
      2 / x * (d.frequencyN x + d.volumeV x - 1) ≤
      (2 * e)⁻¹ * (2 / (d.heightH x * x ^ (n + 2)) *
          (d.sphRad x - 2 * (d.frequencyN x + d.volumeV x) * d.sphMix x +
            (d.frequencyN x + d.volumeV x) ^ 2 * d.sphSq x) +
        2 / x * (d.volumeV x ^ 2 + d.volumeV x * (d.frequencyN x - 1))) + c * x⁻¹ := by
    filter_upwards [d.ae_volumeV_sq_le hH hM] with x hx hmem
    have hmem' := Ioo_subset_Icc_self hmem
    have hx0 : 0 < x := d.pos_of_mem hmem'
    set v := d.volumeV x
    set N' := 2 / (d.heightH x * x ^ (n + 2)) *
          (d.sphRad x - 2 * (d.frequencyN x + v) * d.sphMix x +
            (d.frequencyN x + v) ^ 2 * d.sphSq x) +
        2 / x * (v ^ 2 + v * (d.frequencyN x - 1))
    have hNx : d.frequencyN x ≤ Np :=
      (d.monotoneOn_frequencyN hH hM hmem' hbmem hmem.2.le).trans hN
    have h1 : 2 / x * (d.frequencyN x - 1) ≤ 2 / x * (Np - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have key : 2 * v * e ≤ v ^ 2 + e ^ 2 := by nlinarith [sq_nonneg (v - e)]
    have h2 : 2 / x * v ≤ (2 * e)⁻¹ * (2 / x * v ^ 2) + e / x := by
      calc 2 / x * v = (2 * v * e) / (x * e) := by
            rw [mul_div_mul_right _ _ he0.ne']
            ring
        _ ≤ (v ^ 2 + e ^ 2) / (x * e) := by gcongr
        _ = (2 * e)⁻¹ * (2 / x * v ^ 2) + e / x := by
            have hx0' : x ≠ 0 := hx0.ne'
            have he0' : e ≠ 0 := he0.ne'
            field_simp
    have h3 : (2 * e)⁻¹ * (2 / x * v ^ 2) ≤ (2 * e)⁻¹ * N' :=
      mul_le_mul_of_nonneg_left (hx hmem) (by positivity)
    have h4 : c * x⁻¹ = 2 / x * (Np - 1) + e / x := by rw [hc_def]; ring
    have h5 : 2 / x * (d.frequencyN x + v - 1) = 2 / x * (d.frequencyN x - 1) + 2 / x * v := by
      ring
    linarith
  have hcomp : Real.log (d.heightH b) - Real.log (d.heightH s) ≤
      ((2 * e)⁻¹ * d.frequencyN b + c * Real.log b) -
        ((2 * e)⁻¹ * d.frequencyN s + c * Real.log s) :=
    hfAC.sub_le_sub_of_ae_hasDerivAt_le hgAC (d.hasDerivAt_log_heightH hH) hg' hle hs hbmem hs.2
  -- estimate the right-hand side
  have hs0 : 0 < s := d.pos_of_mem hs
  have hNs := d.one_le_frequencyN hH hM hs
  have hNdiff : (2 * e)⁻¹ * d.frequencyN b - (2 * e)⁻¹ * d.frequencyN s ≤ e / 2 := by
    have : (2 * e)⁻¹ * (d.frequencyN b - d.frequencyN s) ≤ (2 * e)⁻¹ * e ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h' : (2 * e)⁻¹ * e ^ 2 = e / 2 := by
      have he0' : e ≠ 0 := he0.ne'
      field_simp
    linarith [mul_sub ((2 * e)⁻¹) (d.frequencyN b) (d.frequencyN s)]
  have hlog : Real.log b - Real.log s ≤ 1 := by
    have h2s : b ≤ 2 * s := hb.trans (by linarith [hs.1])
    have : Real.log b ≤ Real.log (2 * s) := Real.log_le_log (hs0.trans_le hs.2) h2s
    rw [Real.log_mul two_ne_zero hs0.ne'] at this
    linarith [Real.log_two_lt_d9]
  have hclog : c * Real.log b - c * Real.log s ≤ c := by
    have := mul_le_mul_of_nonneg_left hlog hc0
    linarith [mul_sub c (Real.log b) (Real.log s)]
  have hfinal : Real.log (d.heightH b) ≤ Real.log (d.heightH s) + (2 * (Np - 1) + 4 * e) := by
    linarith
  have hHb := hH b hbmem
  have hHs := hH s hs
  calc d.heightH b = Real.exp (Real.log (d.heightH b)) := (Real.exp_log hHb).symm
    _ ≤ Real.exp (2 * (Np - 1) + 4 * e + Real.log (d.heightH s)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = doublingConst Np * d.heightH s := by
        rw [Real.exp_add, Real.exp_log hHs, doublingConst, he_def]

/-- `V` doubling on the whole data interval, assuming `b ≤ 2a`. -/
theorem volumeV_le_doublingConst_mul (hb : b ≤ 2 * a) {Np : ℝ} (hNp : 1 < Np)
    (hN : d.frequencyN b ≤ Np) {s : ℝ} (hs : s ∈ Icc a b) :
    d.volumeV s ≤ 2 ^ n * doublingConst Np * d.volumeV b := by
  have hbmem : b ∈ Icc a b := right_mem_Icc.2 d.le
  have hs0 := d.pos_of_mem hs
  have hb0 := d.pos_of_mem hbmem
  have hHs := hH s hs
  have hHb := hH b hbmem
  have hC := doublingConst_pos Np
  have hHdb := d.heightH_le_doublingConst_mul hH hM hb hNp hN hs
  rw [d.volumeV_eq hs, d.volumeV_eq hbmem]
  set X := ω * b ^ n - d.chiInt b
  have hXs : ω * s ^ n - d.chiInt s ≤ X := d.monotoneOn_sub_chiInt hs hbmem hs.2
  have hX0 : 0 ≤ X := by
    have := d.chiInt_le b hbmem
    linarith
  have hbs : b ^ n ≤ 2 ^ n * s ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hb0.le (hb.trans (by linarith [hs.1])) n
  have hden : b ^ n * d.heightH b ≤ 2 ^ n * doublingConst Np * (s ^ n * d.heightH s) := by
    calc b ^ n * d.heightH b ≤ (2 ^ n * s ^ n) * (doublingConst Np * d.heightH s) :=
          mul_le_mul hbs hHdb hHb.le (by positivity)
      _ = 2 ^ n * doublingConst Np * (s ^ n * d.heightH s) := by ring
  have hbH0 : b ^ n * d.heightH b ≠ 0 := by positivity
  calc (ω * s ^ n - d.chiInt s) / (s ^ n * d.heightH s) ≤ X / (s ^ n * d.heightH s) := by
        gcongr
    _ = X / (b ^ n * d.heightH b) * ((b ^ n * d.heightH b) / (s ^ n * d.heightH s)) := by
        rw [div_mul_div_comm, mul_comm X, mul_div_mul_left _ _ hbH0]
    _ ≤ X / (b ^ n * d.heightH b) * (2 ^ n * doublingConst Np) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hX0 (by positivity))
        rw [div_le_iff₀ (by positivity)]
        exact hden
    _ = 2 ^ n * doublingConst Np * (X / (b ^ n * d.heightH b)) := by ring

end Doubling

/-- **Lemma 4.3 (H-doubling)**, for `t ≤ s ≤ r ≤ 2t` inside the data interval
(the paper's case is `t = r/2`): if `H > 0` on `[t, r]`, `M(t) ≥ ω` and `N(r) ≤ N₊` with
`N₊ > 1`, then `H(s) ≤ H(r) ≤ C H(s)` with `C = exp(2(N₊ - 1) + 4√(N₊ - 1))`.
The hypothesis `M ≥ ω` is placed at the inner endpoint `t`, and `r ≤ 2t` is allowed. This
generality is what Lemma 4.5 needs (see `volumeV_le_sqrt`). -/
theorem heightH_doubling {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b) (hr2 : r ≤ 2 * t)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t) {Np : ℝ}
    (hNp : 1 < Np) (hN : d.frequencyN r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    d.heightH s ≤ d.heightH r ∧ d.heightH r ≤ doublingConst Np * d.heightH s := by
  let d' := d.restrict ht htr hr
  exact ⟨d'.monotoneOn_heightH hH hM hs (right_mem_Icc.2 htr) hs.2,
    d'.heightH_le_doublingConst_mul hH hM hr2 hNp hN hs⟩

/-- **Lemma 4.4 (V-doubling)**, for `t ≤ s ≤ r ≤ 2t` inside the data interval:
`V(s) ≤ 2^n C V(r)`. The constant is `2^n C` because of the factor `s^{-n}` in `V`,
which the paper's printed definition omits (see the module docstring). As in `heightH_doubling`,
`M ≥ ω` is assumed at the inner endpoint `t`. -/
theorem volumeV_doubling {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b) (hr2 : r ≤ 2 * t)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t) {Np : ℝ}
    (hNp : 1 < Np) (hN : d.frequencyN r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    d.volumeV s ≤ 2 ^ n * doublingConst Np * d.volumeV r :=
  (d.restrict ht htr hr).volumeV_le_doublingConst_mul hH hM hr2 hNp hN hs

/-- **Lemma 4.1 on a subinterval**: if `H > 0` on `[t, r]` and `M(t) ≥ ω`, then `N ≥ 1` and `N`
is nondecreasing on `[t, r]`. -/
theorem one_le_frequencyN_of_le {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t) {s : ℝ}
    (hs : s ∈ Icc t r) : 1 ≤ d.frequencyN s :=
  (d.restrict ht htr hr).one_le_frequencyN hH hM hs

theorem monotoneOn_frequencyN_of_le {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t) :
    MonotoneOn d.frequencyN (Icc t r) :=
  (d.restrict ht htr hr).monotoneOn_frequencyN hH hM

/-- **Lemma 4.5 (V-vanishing)**: if `2t ≤ r` inside the data interval, `H > 0` on
`[t, r]`, `M(t) ≥ ω`, `N(r) - N(t) < δ` and `N(r) < N₊`, then `V(t) ≤ 2^n C √δ`.

The paper's proof applies Lemma 4.4 on `[σ/2, σ]` for some `σ ∈ [t, 2t]`, which uses
`M(σ/2) ≥ ω`, while only `M(t) ≥ ω` is assumed. We apply `volumeV_doubling` on `[t, σ]`
instead, which needs `M ≥ ω` only at `t`. -/
theorem volumeV_le_sqrt {t r : ℝ} (ht : a ≤ t) (htr : 2 * t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t) {Np δ : ℝ}
    (hN : d.frequencyN r < Np) (hδ : d.frequencyN r - d.frequencyN t < δ) :
    d.volumeV t ≤ 2 ^ n * doublingConst Np * √δ := by
  have ht0 : 0 < t := d.pos.trans_le ht
  have htr' : t ≤ r := by linarith
  let d' := d.restrict ht htr' hr
  have htmem : t ∈ Icc t r := left_mem_Icc.2 htr'
  have hrmem : r ∈ Icc t r := right_mem_Icc.2 htr'
  have h2tmem : 2 * t ∈ Icc t r := ⟨by linarith, htr⟩
  have hmono := d'.monotoneOn_frequencyN hH hM
  have hNp : 1 < Np := (d'.one_le_frequencyN hH hM hrmem).trans_lt hN
  -- there is `σ ∈ (t, 2t)` with `V σ < √δ`
  obtain ⟨σ, hσ, hVσ⟩ : ∃ σ ∈ Ioo t (2 * t), d.volumeV σ < √δ := by
    by_contra hcon
    push Not at hcon
    let d'' := d.restrict ht (by linarith : t ≤ 2 * t) (by linarith)
    have hH'' : ∀ s ∈ Icc t (2 * t), 0 < d.heightH s := fun s hs => hH s ⟨hs.1, hs.2.trans htr⟩
    set δ' := √δ ^ 2
    have hδ'0 : 0 ≤ δ' := sq_nonneg _
    have hfAC : AbsolutelyContinuousOnInterval (fun s => 2 * δ' * Real.log s) t (2 * t) := by
      obtain ⟨K, hK⟩ := (LipschitzWith.id.lipschitzOnWith (s := Icc t (2 * t))).exists_log
        (g := fun s => s) ht0 fun x hx => hx.1
      exact (hK.absolutelyContinuousOnInterval_of_Icc (by linarith)).const_mul (2 * δ')
    have hf' : ∀ᵐ x, x ∈ Ioo t (2 * t) →
        HasDerivAt (fun s => 2 * δ' * Real.log s) (2 * δ' * x⁻¹) x :=
      Eventually.of_forall fun x hx =>
        (Real.hasDerivAt_log (ht0.trans hx.1).ne').const_mul (2 * δ')
    have hle : ∀ᵐ x, x ∈ Ioo t (2 * t) → 2 * δ' * x⁻¹ ≤
        2 / (d.heightH x * x ^ (n + 2)) *
          (d.sphRad x - 2 * (d.frequencyN x + d.volumeV x) * d.sphMix x +
            (d.frequencyN x + d.volumeV x) ^ 2 * d.sphSq x) +
        2 / x * (d.volumeV x ^ 2 + d.volumeV x * (d.frequencyN x - 1)) := by
      filter_upwards [d''.ae_volumeV_sq_le hH'' hM] with x hx hmem
      have hx0 : 0 < x := ht0.trans hmem.1
      refine le_trans ?_ (hx hmem)
      have hV : √δ ≤ d.volumeV x := hcon x hmem
      have hV2 : δ' ≤ d.volumeV x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hV 2
      calc 2 * δ' * x⁻¹ = 2 / x * δ' := by ring
        _ ≤ 2 / x * d.volumeV x ^ 2 :=
          mul_le_mul_of_nonneg_left hV2 (by positivity)
    have hcomp : 2 * δ' * Real.log (2 * t) - 2 * δ' * Real.log t ≤
        d.frequencyN (2 * t) - d.frequencyN t :=
      hfAC.sub_le_sub_of_ae_hasDerivAt_le
        (d''.absolutelyContinuousOnInterval_frequencyN hH'') hf'
        (d''.hasDerivAt_frequencyN hH'') hle (left_mem_Icc.2 (by linarith))
        (right_mem_Icc.2 (by linarith)) (by linarith)
    have hlog2 : Real.log (2 * t) - Real.log t = Real.log 2 := by
      rw [Real.log_mul two_ne_zero ht0.ne']
      ring
    have hmid : d.frequencyN (2 * t) ≤ d.frequencyN r := hmono h2tmem hrmem htr
    have hδδ' : δ ≤ δ' := by
      rcases le_or_gt 0 δ with h | h
      · exact (Real.sq_sqrt h).ge
      · linarith
    have hlhs : 2 * δ' * Real.log (2 * t) - 2 * δ' * Real.log t = 2 * δ' * Real.log 2 := by
      rw [← hlog2]
      ring
    have : δ' ≤ 2 * δ' * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
    linarith
  -- apply V-doubling on `[t, σ]`
  have hσmem : σ ∈ Icc t r := ⟨hσ.1.le, hσ.2.le.trans htr⟩
  have hNσ : d.frequencyN σ ≤ Np := (hmono hσmem hrmem hσmem.2).trans hN.le
  have hdoub := d.volumeV_doubling ht hσ.1.le (hσmem.2.trans hr) (by linarith [hσ.2])
    (fun s hs => hH s ⟨hs.1, hs.2.trans hσmem.2⟩) hM hNp hNσ (left_mem_Icc.2 hσ.1.le)
  have hC : 0 ≤ 2 ^ n * doublingConst Np := by
    have := doublingConst_pos Np
    positivity
  calc d.volumeV t ≤ 2 ^ n * doublingConst Np * d.volumeV σ := hdoub
    _ ≤ 2 ^ n * doublingConst Np * √δ := mul_le_mul_of_nonneg_left hVσ.le hC

end RadialData

end InnerVariational.Abstract
