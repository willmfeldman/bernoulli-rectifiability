/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Abstract.Basic
public import InnerVariational.Frequency.AbstractError.Doubling
public import InnerVariational.Basic.LipschitzFTC
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
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
* `RadialData.hasDerivAt_frequencyN` and `RadialData.hasDerivAt_frequencyN'`: the derivative of
  the frequency, in the forms (4.12) and (4.13) (Lemma 4.1 and Remark 4.2).
* `RadialData.one_le_frequencyN`, `RadialData.monotoneOn_frequencyN`: Lemma 4.1.
* `RadialData.heightH_doubling`: Lemma 4.3.
* `RadialData.volumeV_doubling`: Lemma 4.4, with constant `2^n C` (the factor `2^n` comes from
  the `s^{-n}` in `V`).
* `RadialData.volumeV_le_sqrt`: Lemma 4.5.

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

namespace RadialData

variable {n : ℕ} {ω a b : ℝ} (d : RadialData n ω a b)

/-! ### Basic properties -/

theorem absolutelyContinuousOnInterval_heightH : AbsolutelyContinuousOnInterval d.heightH a b :=
  d.toErr.absolutelyContinuousOnInterval_heightH

theorem volumeV_nonneg {s : ℝ} (hs : s ∈ Icc a b) (hH : 0 < d.heightH s) : 0 ≤ d.volumeV s :=
  d.toErr.volumeV_nonneg hs hH

/-! ### Result 1: the monotonicity formula -/

/-- **Derivative of `M`** (Proposition 3.4): for a.e. `s`,
`M' = (2 / s^{n+2}) (R - 2Q + P) = (2 / s^{n+2}) ∫_{∂B_s} (u - ∇u·y)²`. -/
theorem hasDerivAt_monotonicityM : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.monotonicityM (2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s)) s := by
  filter_upwards [d.toErr.hasDerivAt_monotonicityM] with s h hs
  simpa using h hs

theorem ae_monotonicityM_deriv_nonneg : ∀ᵐ s, s ∈ Ioo a b →
    0 ≤ 2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) := by
  filter_upwards [d.sphSq_nonneg, d.sphRad_nonneg, d.sq_sphMix_le] with s h1 h2 h3 hs
  have hs0 : 0 < s := d.pos.trans hs.1
  have hq := sub_two_mul_add_sq_mul_nonneg (h1 hs) (h2 hs) (h3 hs) 1
  simp only [mul_one, one_pow, one_mul] at hq
  exact mul_nonneg (by positivity) hq

theorem absolutelyContinuousOnInterval_monotonicityM :
    AbsolutelyContinuousOnInterval d.monotonicityM a b :=
  d.toErr.absolutelyContinuousOnInterval_monotonicityM

/-- **`M` is nondecreasing** (Proposition 3.4). -/
theorem monotoneOn_monotonicityM : MonotoneOn d.monotonicityM (Icc a b) :=
  d.absolutelyContinuousOnInterval_monotonicityM.monotoneOn_of_ae_hasDerivAt_nonneg
    d.hasDerivAt_monotonicityM d.ae_monotonicityM_deriv_nonneg

/-! ### Result 3: the frequency formula (Lemma 4.1) -/

section Frequency

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s)
include hH

/-- `N` is Lipschitz on `[a, b]` when `H > 0` there. -/
theorem exists_lipschitzOnWith_frequencyN : ∃ K, LipschitzOnWith K d.frequencyN (Icc a b) :=
  d.toErr.exists_lipschitzOnWith_frequencyN hH

theorem absolutelyContinuousOnInterval_frequencyN :
    AbsolutelyContinuousOnInterval d.frequencyN a b :=
  d.toErr.absolutelyContinuousOnInterval_frequencyN hH

/-- **Remark 4.2, formula (4.13)**: for a.e. `s`,
`N' = (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - N u)² + (2/s) V (N - 1)`. -/
theorem hasDerivAt_frequencyN' : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.frequencyN
      (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * d.frequencyN s * d.sphMix s + d.frequencyN s ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s * (d.frequencyN s - 1))) s := by
  filter_upwards [d.toErr.hasDerivAt_frequencyN' hH] with s h hs
  simpa using h hs

/-- **Lemma 4.1, formula (4.12)**: for a.e. `s`,
`N' = (2 / (H s^{n+2})) ∫_{∂B_s}(∇u·y - (N+V) u)² + (2/s)(V² + V (N - 1))`. -/
theorem hasDerivAt_frequencyN : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.frequencyN
      (2 / (d.heightH s * s ^ (n + 2)) *
          (d.sphRad s - 2 * (d.frequencyN s + d.volumeV s) * d.sphMix s +
            (d.frequencyN s + d.volumeV s) ^ 2 * d.sphSq s) +
        2 / s * (d.volumeV s ^ 2 + d.volumeV s * (d.frequencyN s - 1))) s := by
  filter_upwards [d.toErr.hasDerivAt_frequencyN hH] with s h hs
  simpa using h hs

/-- `H' = (2/s) H (N + V - 1)` for a.e. `s` (proof of Lemma 4.3). -/
theorem hasDerivAt_heightH' : ∀ᵐ s, s ∈ Ioo a b →
    HasDerivAt d.heightH (2 / s * d.heightH s * (d.frequencyN s + d.volumeV s - 1)) s :=
  d.toErr.hasDerivAt_heightH' hH

variable (hM : ω ≤ d.monotonicityM a)
include hM

/-- **Lemma 4.1**: `N ≥ 1` on `[a, b]` if `M(a) ≥ ω`. -/
theorem one_le_frequencyN {s : ℝ} (hs : s ∈ Icc a b) : 1 ≤ d.frequencyN s :=
  d.one_le_frequencyN_of_toErr hH hM hs

/-- **Lemma 4.1**: `N` is nondecreasing on `[a, b]` if `M(a) ≥ ω`. -/
theorem monotoneOn_frequencyN : MonotoneOn d.frequencyN (Icc a b) :=
  d.monotoneOn_frequencyN_of_toErr hH hM

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

/-! ### Results 4–6: doubling of `H` and `V`, vanishing of `V` -/

/-- **Lemma 4.3 (H-doubling)**, for `t ≤ s ≤ r ≤ 2t` inside the data interval
(the paper's case is `t = r/2`): if `H > 0` on `[t, r]`, `M(t) ≥ ω` and `N(r) ≤ N₊` with
`N₊ > 1`, then `H(s) ≤ H(r) ≤ C H(s)` with `C = exp(2(N₊ - 1) + 4√(N₊ - 1))`.
The hypothesis `M ≥ ω` is placed at the inner endpoint `t`, and `r ≤ 2t` is allowed. This
generality is what Lemma 4.5 needs (see `volumeV_le_sqrt`). -/
theorem heightH_doubling {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b) (hr2 : r ≤ 2 * t)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t) {Np : ℝ}
    (hNp : 1 < Np) (hN : d.frequencyN r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    d.heightH s ≤ d.heightH r ∧ d.heightH r ≤ doublingConst Np * d.heightH s := by
  simpa using d.toErr.heightH_doubling ht htr hr hr2 hH
    (by rw [toErr_modM]; linarith) (by rw [zero_mul]; norm_num)
    hNp (by rwa [toErr_modN]) hs

/-- **Lemma 4.4 (V-doubling)**, for `t ≤ s ≤ r ≤ 2t` inside the data interval:
`V(s) ≤ 2^n C V(r)`. The constant is `2^n C` because of the factor `s^{-n}` in `V`,
which the paper's printed definition omits (see the module docstring). As in `heightH_doubling`,
`M ≥ ω` is assumed at the inner endpoint `t`. -/
theorem volumeV_doubling {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b) (hr2 : r ≤ 2 * t)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hM : ω ≤ d.monotonicityM t) {Np : ℝ}
    (hNp : 1 < Np) (hN : d.frequencyN r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    d.volumeV s ≤ 2 ^ n * doublingConst Np * d.volumeV r :=
  d.toErr.volumeV_doubling ht htr hr hr2 hH
    (by rw [toErr_modM]; linarith) (by rw [zero_mul]; norm_num) hNp
    (by rwa [toErr_modN]) hs

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
