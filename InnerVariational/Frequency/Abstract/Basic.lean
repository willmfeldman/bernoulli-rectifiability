/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.LipschitzFTC
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Radial data: the structure and its elementary properties

The structure `RadialData` of the abstract monotonicity and frequency calculus
(`Frequency/Abstract.lean`), the quantities `M`, `N`, `V` built from it, its restriction to a
subinterval, the constant `C(N₊)` of Lemma 4.3, and two facts of one-variable calculus used by
both the constant-coefficient calculus and the calculus with an error term
(`Frequency/AbstractError.lean`).
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

include d in
theorem pos_of_mem {s : ℝ} (hs : s ∈ Icc a b) : 0 < s := d.pos.trans_le hs.1

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

/-- The constant `C(N₊) = exp(2(N₊ - 1) + 4 √(N₊ - 1))` of Lemma 4.3. -/
def doublingConst (Np : ℝ) : ℝ := Real.exp (2 * (Np - 1) + 4 * √(Np - 1))

theorem doublingConst_pos (Np : ℝ) : 0 < doublingConst Np := Real.exp_pos _

end RadialData

end InnerVariational.Abstract
