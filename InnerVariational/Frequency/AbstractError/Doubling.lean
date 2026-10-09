/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.AbstractError.ModN
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Doubling of `H` and `V`, and vanishing of `V`, with an error term

Lemmas 4.3–4.5 of the constant-coefficient theory, for radial data with error
(`RadialDataErr`). The frequency `N` is replaced by the modified frequency
`Ñ = N + κ² s² / 2`, which is nondecreasing and at least one as soon as the shifted Weiss energy
`Z` is nonnegative at the inner endpoint and `κ r ≤ 1/2` at the outer endpoint `r`.

* Lemma 4.3: the upper bound `H(r) ≤ C(N₊) H(s)` holds with the same constant
  `C(N₊) = exp(2(N₊ - 1) + 4 √(N₊ - 1))`, now under `Ñ(r) ≤ N₊`. Since `H` is no longer
  nondecreasing, the lower bound becomes `H(s) ≤ e^{κ² r² / 8} H(r)` (and `e^{κ² r² / 8} ≤ e^{1/32}`
  when `κ r ≤ 1/2`).
* Lemma 4.4: `V(s) ≤ 2ⁿ C(N₊) V(r)`, unchanged.
* Lemma 4.5: `V(t) ≤ 2ⁿ C(N₊) √(3δ)` when the pinching of `Ñ` on `[t, r]` is less than `δ`; the
  factor `3` comes from the weaker bound `Ñ' ≥ V² / (2s)` (instead of `N' ≥ 2V² / s`).
-/

open MeasureTheory Set Filter
open scoped NNReal

@[expose] public noncomputable section

namespace InnerVariational.Abstract

namespace RadialDataErr

variable {n : ℕ} {ω κ a b : ℝ} (d : RadialDataErr n ω κ a b)

section Doubling

variable (hH : ∀ s ∈ Icc a b, 0 < d.heightH s) (hZ : 0 ≤ d.modM a) (hκ : κ * b ≤ 1 / 2)
include hH hZ hκ

/-- Upper bound of Lemma 4.3 on the whole data interval, assuming `b ≤ 2a`. -/
theorem heightH_le_doublingConst_mul (hb : b ≤ 2 * a) {Np : ℝ} (hNp : 1 < Np)
    (hN : d.modN b ≤ Np) {s : ℝ} (hs : s ∈ Icc a b) :
    d.heightH b ≤ RadialData.doublingConst Np * d.heightH s := by
  have hbmem : b ∈ Icc a b := right_mem_Icc.2 d.le
  set e := √(Np - 1) with he_def
  have he0 : 0 < e := Real.sqrt_pos.2 (by linarith)
  have he2 : e ^ 2 = Np - 1 := Real.sq_sqrt (by linarith)
  set c := 2 * (Np - 1) + 2 * e with hc_def
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
      (fun s => e⁻¹ * d.modN s + c * Real.log s) a b :=
    ((d.absolutelyContinuousOnInterval_modN hH).const_mul e⁻¹).fun_add (hlogAC.const_mul c)
  -- the derivatives
  have hg' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun s => e⁻¹ * d.modN s + c * Real.log s)
      (e⁻¹ * deriv d.modN x + c * x⁻¹) x := by
    filter_upwards [d.ae_hasDerivAt_deriv_modN hH] with x hx hmem
    have hx0 : x ≠ 0 := (d.pos.trans hmem.1).ne'
    exact ((hx hmem).const_mul e⁻¹).add ((Real.hasDerivAt_log hx0).const_mul c)
  have hle : ∀ᵐ x, x ∈ Ioo a b →
      2 / x * (d.frequencyN x + d.volumeV x - 1) ≤ e⁻¹ * deriv d.modN x + c * x⁻¹ := by
    filter_upwards [d.ae_volumeV_sq_le_deriv_modN hH hZ hκ] with x hx hmem
    have hmem' := Ioo_subset_Icc_self hmem
    have hx0 : 0 < x := d.pos_of_mem hmem'
    set v := d.volumeV x
    have hNx : d.frequencyN x ≤ Np :=
      ((d.frequencyN_le_modN x).trans
        (d.monotoneOn_modN hH hZ hκ hmem' hbmem hmem.2.le)).trans hN
    have h1 : 2 / x * (d.frequencyN x - 1) ≤ 2 / x * (Np - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 2 / x * v ≤ e⁻¹ * (v ^ 2 / (2 * x)) + 2 * e / x := by
      have hsq : 0 ≤ (v - 2 * e) ^ 2 / (2 * e * x) := by positivity
      have heq : e⁻¹ * (v ^ 2 / (2 * x)) + 2 * e / x - 2 / x * v =
          (v - 2 * e) ^ 2 / (2 * e * x) := by
        field_simp
        ring
      linarith
    have h3 : e⁻¹ * (v ^ 2 / (2 * x)) ≤ e⁻¹ * deriv d.modN x :=
      mul_le_mul_of_nonneg_left (hx hmem) (by positivity)
    have h4 : c * x⁻¹ = 2 / x * (Np - 1) + 2 * e / x := by rw [hc_def]; ring
    have h5 : 2 / x * (d.frequencyN x + v - 1) = 2 / x * (d.frequencyN x - 1) + 2 / x * v := by
      ring
    linarith
  have hcomp : Real.log (d.heightH b) - Real.log (d.heightH s) ≤
      (e⁻¹ * d.modN b + c * Real.log b) - (e⁻¹ * d.modN s + c * Real.log s) :=
    hfAC.sub_le_sub_of_ae_hasDerivAt_le hgAC (d.hasDerivAt_log_heightH hH) hg' hle hs hbmem hs.2
  -- estimate the right-hand side
  have hs0 : 0 < s := d.pos_of_mem hs
  have hNs := d.one_le_modN hH hZ hκ hs
  have hNdiff : e⁻¹ * d.modN b - e⁻¹ * d.modN s ≤ e := by
    have : e⁻¹ * (d.modN b - d.modN s) ≤ e⁻¹ * e ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h' : e⁻¹ * e ^ 2 = e := by
      have he0' : e ≠ 0 := he0.ne'
      field_simp
    linarith [mul_sub e⁻¹ (d.modN b) (d.modN s)]
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
    _ = RadialData.doublingConst Np * d.heightH s := by
        rw [Real.exp_add, Real.exp_log hHs, RadialData.doublingConst, he_def]

/-- `V` doubling on the whole data interval, assuming `b ≤ 2a`. -/
theorem volumeV_le_doublingConst_mul (hb : b ≤ 2 * a) {Np : ℝ} (hNp : 1 < Np)
    (hN : d.modN b ≤ Np) {s : ℝ} (hs : s ∈ Icc a b) :
    d.volumeV s ≤ 2 ^ n * RadialData.doublingConst Np * d.volumeV b := by
  have hbmem : b ∈ Icc a b := right_mem_Icc.2 d.le
  have hs0 := d.pos_of_mem hs
  have hb0 := d.pos_of_mem hbmem
  have hHs := hH s hs
  have hHb := hH b hbmem
  have hC := RadialData.doublingConst_pos Np
  have hHdb := d.heightH_le_doublingConst_mul hH hZ hκ hb hNp hN hs
  rw [d.volumeV_eq hs, d.volumeV_eq hbmem]
  set X := ω * b ^ n - d.chiInt b
  have hXs : ω * s ^ n - d.chiInt s ≤ X := d.monotoneOn_sub_chiInt hs hbmem hs.2
  have hX0 : 0 ≤ X := by
    have := d.chiInt_le b hbmem
    linarith
  have hbs : b ^ n ≤ 2 ^ n * s ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hb0.le (hb.trans (by linarith [hs.1])) n
  have hden : b ^ n * d.heightH b ≤
      2 ^ n * RadialData.doublingConst Np * (s ^ n * d.heightH s) := by
    calc b ^ n * d.heightH b ≤ (2 ^ n * s ^ n) * (RadialData.doublingConst Np * d.heightH s) :=
          mul_le_mul hbs hHdb hHb.le (by positivity)
      _ = 2 ^ n * RadialData.doublingConst Np * (s ^ n * d.heightH s) := by ring
  have hbH0 : b ^ n * d.heightH b ≠ 0 := by positivity
  calc (ω * s ^ n - d.chiInt s) / (s ^ n * d.heightH s) ≤ X / (s ^ n * d.heightH s) := by
        gcongr
    _ = X / (b ^ n * d.heightH b) * ((b ^ n * d.heightH b) / (s ^ n * d.heightH s)) := by
        rw [div_mul_div_comm, mul_comm X, mul_div_mul_left _ _ hbH0]
    _ ≤ X / (b ^ n * d.heightH b) * (2 ^ n * RadialData.doublingConst Np) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hX0 (by positivity))
        rw [div_le_iff₀ (by positivity)]
        exact hden
    _ = 2 ^ n * RadialData.doublingConst Np * (X / (b ^ n * d.heightH b)) := by ring

end Doubling

/-- **Lemma 4.3 (H-doubling) with an error term**, for `t ≤ s ≤ r ≤ 2t` inside the data
interval: if `H > 0` on `[t, r]`, `Z(t) ≥ 0`, `κ r ≤ 1/2` and `Ñ(r) ≤ N₊` with `N₊ > 1`, then
`H(s) ≤ e^{κ² r² / 8} H(r)` and `H(r) ≤ C H(s)` with `C = exp(2(N₊ - 1) + 4√(N₊ - 1))`. -/
theorem heightH_doubling {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b) (hr2 : r ≤ 2 * t)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hZ : 0 ≤ d.modM t) (hκ : κ * r ≤ 1 / 2) {Np : ℝ}
    (hNp : 1 < Np) (hN : d.modN r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    d.heightH s ≤ Real.exp (κ ^ 2 * r ^ 2 / 8) * d.heightH r ∧
      d.heightH r ≤ RadialData.doublingConst Np * d.heightH s := by
  let d' := d.restrict ht htr hr
  refine ⟨?_, d'.heightH_le_doublingConst_mul hH hZ hκ hr2 hNp hN hs⟩
  have h1 := d'.heightH_le_exp_mul hH hZ hκ hs (right_mem_Icc.2 htr) hs.2
  have hHr := hH r (right_mem_Icc.2 htr)
  refine h1.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hHr.le)
  have : 0 ≤ κ ^ 2 * s ^ 2 := by positivity
  linarith [mul_sub (κ ^ 2) (r ^ 2) (s ^ 2)]

/-- **Lemma 4.4 (V-doubling) with an error term**, for `t ≤ s ≤ r ≤ 2t` inside the data interval:
`V(s) ≤ 2^n C V(r)`, under the hypotheses of `heightH_doubling`. -/
theorem volumeV_doubling {t r : ℝ} (ht : a ≤ t) (htr : t ≤ r) (hr : r ≤ b) (hr2 : r ≤ 2 * t)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hZ : 0 ≤ d.modM t) (hκ : κ * r ≤ 1 / 2) {Np : ℝ}
    (hNp : 1 < Np) (hN : d.modN r ≤ Np) {s : ℝ} (hs : s ∈ Icc t r) :
    d.volumeV s ≤ 2 ^ n * RadialData.doublingConst Np * d.volumeV r :=
  (d.restrict ht htr hr).volumeV_le_doublingConst_mul hH hZ hκ hr2 hNp hN hs

/-- A radius with small `V`: if `H > 0` on `[t₁, t₂]`, `Z(t₁) ≥ 0`, `κ t₂ ≤ 1/2`, `0 ≤ v` and
`Ñ(t₂) − Ñ(t₁) < (v² / 2) log(t₂ / t₁)`, then `V(σ) < v` for some `σ ∈ (t₁, t₂)`. This is the
pigeonhole step of the proof of Lemma 4.5, from `∫ V² / (2s) ≤ Ñ(t₂) − Ñ(t₁)`. -/
theorem exists_volumeV_lt {t₁ t₂ : ℝ} (ht₁ : a ≤ t₁) (ht : t₁ < t₂) (ht₂ : t₂ ≤ b)
    (hH : ∀ s ∈ Icc t₁ t₂, 0 < d.heightH s) (hZ : 0 ≤ d.modM t₁) (hκ : κ * t₂ ≤ 1 / 2)
    {v : ℝ} (hv0 : 0 ≤ v)
    (hv : d.modN t₂ - d.modN t₁ < v ^ 2 / 2 * (Real.log t₂ - Real.log t₁)) :
    ∃ σ ∈ Ioo t₁ t₂, d.volumeV σ < v := by
  by_contra hcon
  push Not at hcon
  have ht₁0 : 0 < t₁ := d.pos.trans_le ht₁
  let d' := d.restrict ht₁ ht.le ht₂
  have hfAC : AbsolutelyContinuousOnInterval (fun s => v ^ 2 / 2 * Real.log s) t₁ t₂ := by
    obtain ⟨K, hK⟩ := (LipschitzWith.id.lipschitzOnWith (s := Icc t₁ t₂)).exists_log
      (g := fun s => s) ht₁0 fun x hx => hx.1
    exact (hK.absolutelyContinuousOnInterval_of_Icc ht.le).const_mul (v ^ 2 / 2)
  have hf' : ∀ᵐ x, x ∈ Ioo t₁ t₂ →
      HasDerivAt (fun s => v ^ 2 / 2 * Real.log s) (v ^ 2 / 2 * x⁻¹) x :=
    Eventually.of_forall fun x hx =>
      (Real.hasDerivAt_log (ht₁0.trans hx.1).ne').const_mul (v ^ 2 / 2)
  have hle : ∀ᵐ x, x ∈ Ioo t₁ t₂ → v ^ 2 / 2 * x⁻¹ ≤ deriv d.modN x := by
    filter_upwards [d'.ae_volumeV_sq_le_deriv_modN hH hZ hκ] with x hx hmem
    have hx0 : 0 < x := ht₁0.trans hmem.1
    refine le_trans ?_ (hx hmem)
    have hV2 : v ^ 2 ≤ d.volumeV x ^ 2 := pow_le_pow_left₀ hv0 (hcon x hmem) 2
    calc v ^ 2 / 2 * x⁻¹ = v ^ 2 / (2 * x) := by field_simp
      _ ≤ d.volumeV x ^ 2 / (2 * x) := by gcongr
  have hcomp : v ^ 2 / 2 * Real.log t₂ - v ^ 2 / 2 * Real.log t₁ ≤ d.modN t₂ - d.modN t₁ :=
    hfAC.sub_le_sub_of_ae_hasDerivAt_le (d'.absolutelyContinuousOnInterval_modN hH) hf'
      (d'.ae_hasDerivAt_deriv_modN hH) hle (left_mem_Icc.2 ht.le) (right_mem_Icc.2 ht.le) ht.le
  linarith [mul_sub (v ^ 2 / 2) (Real.log t₂) (Real.log t₁)]

/-- **Lemma 4.5 (V-vanishing) with an error term**: if `2t ≤ r` inside the data interval,
`H > 0` on `[t, r]`, `Z(t) ≥ 0`, `κ r ≤ 1/2`, `Ñ(r) - Ñ(t) < δ` and `Ñ(r) < N₊`, then
`V(t) ≤ 2^n C √(3δ)`. -/
theorem volumeV_le_sqrt {t r : ℝ} (ht : a ≤ t) (htr : 2 * t ≤ r) (hr : r ≤ b)
    (hH : ∀ s ∈ Icc t r, 0 < d.heightH s) (hZ : 0 ≤ d.modM t) (hκ : κ * r ≤ 1 / 2) {Np δ : ℝ}
    (hN : d.modN r < Np) (hδ : d.modN r - d.modN t < δ) :
    d.volumeV t ≤ 2 ^ n * RadialData.doublingConst Np * √(3 * δ) := by
  have ht0 : 0 < t := d.pos.trans_le ht
  have htr' : t ≤ r := by linarith
  let d' := d.restrict ht htr' hr
  have htmem : t ∈ Icc t r := left_mem_Icc.2 htr'
  have hrmem : r ∈ Icc t r := right_mem_Icc.2 htr'
  have h2tmem : 2 * t ∈ Icc t r := ⟨by linarith, htr⟩
  have hmono : MonotoneOn d.modN (Icc t r) := d'.monotoneOn_modN hH hZ hκ
  have hNp : 1 < Np := (d'.one_le_modN hH hZ hκ hrmem).trans_lt hN
  have hδ0 : 0 < δ := by
    have := hmono htmem hrmem htr'
    linarith
  have hk := d.kappa_nonneg
  have hκ2 : κ * (2 * t) ≤ 1 / 2 := (mul_le_mul_of_nonneg_left htr hk).trans hκ
  -- there is `σ ∈ (t, 2t)` with `V σ < √(3δ)`
  obtain ⟨σ, hσ, hVσ⟩ : ∃ σ ∈ Ioo t (2 * t), d.volumeV σ < √(3 * δ) := by
    refine d.exists_volumeV_lt ht (by linarith) (htr.trans hr)
      (fun s hs => hH s ⟨hs.1, hs.2.trans htr⟩) hZ hκ2 (Real.sqrt_nonneg _) ?_
    have hmid : d.modN (2 * t) ≤ d.modN r := hmono h2tmem hrmem htr
    have hsq : √(3 * δ) ^ 2 = 3 * δ := Real.sq_sqrt (by linarith)
    have hlog2 : Real.log (2 * t) - Real.log t = Real.log 2 := by
      rw [Real.log_mul two_ne_zero ht0.ne']
      ring
    rw [hsq, hlog2]
    nlinarith [Real.log_two_gt_d9]
  -- apply V-doubling on `[t, σ]`
  have hσmem : σ ∈ Icc t r := ⟨hσ.1.le, hσ.2.le.trans htr⟩
  have hNσ : d.modN σ ≤ Np := (hmono hσmem hrmem hσmem.2).trans hN.le
  have hκσ : κ * σ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hσmem.2 hk).trans hκ
  have hdoub := d.volumeV_doubling ht hσ.1.le (hσmem.2.trans hr) (by linarith [hσ.2])
    (fun s hs => hH s ⟨hs.1, hs.2.trans hσmem.2⟩) hZ hκσ hNp hNσ (left_mem_Icc.2 hσ.1.le)
  have hC : 0 ≤ 2 ^ n * RadialData.doublingConst Np := by
    have := RadialData.doublingConst_pos Np
    positivity
  calc d.volumeV t ≤ 2 ^ n * RadialData.doublingConst Np * d.volumeV σ := hdoub
    _ ≤ 2 ^ n * RadialData.doublingConst Np * √(3 * δ) :=
        mul_le_mul_of_nonneg_left hVσ.le hC

end RadialDataErr

end InnerVariational.Abstract
