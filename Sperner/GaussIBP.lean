/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Basic
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Integration by parts for Lipschitz functions

For a Lipschitz function `w : ℝⁿ → ℝ` (differentiable only almost everywhere, by Rademacher's
theorem) and a differentiable weight `ψ` with integrable control,
`∫ Dw(x) a · ψ(x) dx = -∫ w(x) · Dψ(x) a dx`.

The proof avoids any fundamental theorem of calculus along lines: for `τ > 0`, translation
invariance of Lebesgue measure gives the exact discrete identity
`∫ (w(x + τa) - w(x))/τ · ψ(x) dx = ∫ w(x) · (ψ(x - τa) - ψ(x))/τ dx`,
and both sides converge by dominated convergence as `τ → 0`.

The Gaussian case `ψ = e^{-|x|²/2}` reads `∫ ∂ₐw dγ = ∫ w ⟪x, a⟫ dγ`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- A Lipschitz function grows at most linearly, uniformly under bounded translations. -/
lemma abs_le_of_lipschitzWith {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) {r : ℝ} (hr : 0 ≤ r) (x s : EuclideanSpace ℝ (Fin n))
    (hs : ‖s‖ ≤ r) : |w (x + s)| ≤ (|w 0| + L + L * r) * (1 + ‖x‖) := by
  have h := hw.dist_le_mul (x + s) 0
  rw [Real.dist_eq, dist_zero_right] at h
  have h1 : |w (x + s)| ≤ |w 0| + L * ‖x + s‖ := by
    have := abs_sub_abs_le_abs_sub (w (x + s)) (w 0); linarith
  have h2 : ‖x + s‖ ≤ ‖x‖ + r := (norm_add_le _ _).trans (by linarith)
  have hL : (0 : ℝ) ≤ L := L.2
  have hx := norm_nonneg x
  have hw0 := abs_nonneg (w 0)
  nlinarith [mul_le_mul_of_nonneg_left h2 hL, mul_nonneg hL hr, mul_nonneg hw0 hx,
    mul_nonneg (mul_nonneg hL hr) hx]

/-- **Integration by parts** for a Lipschitz `w` against a differentiable weight `ψ` whose values
and translated derivatives are controlled by `B`, with `(1 + |x|) B` integrable. -/
theorem integral_fderiv_mul_eq_neg_integral_mul_fderiv {w ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ≥0} (hw : LipschitzWith L w) (a : EuclideanSpace ℝ (Fin n))
    (hψ : Differentiable ℝ ψ) {B : EuclideanSpace ℝ (Fin n) → ℝ}
    (hB : Integrable fun x => (1 + ‖x‖) * B x) (hψB : ∀ x, |ψ x| ≤ B x)
    (hDψB : ∀ x (t : ℝ), |t| ≤ 1 → ‖fderiv ℝ ψ (x + t • a)‖ ≤ B x) :
    ∫ x, fderiv ℝ w x a * ψ x = -∫ x, w x * fderiv ℝ ψ x a := by
  have hB0 : ∀ x, 0 ≤ B x := fun x => (abs_nonneg _).trans (hψB x)
  have hBint : Integrable B := by
    have hmeas : AEStronglyMeasurable B volume := by
      have : B = fun x => (1 + ‖x‖)⁻¹ * ((1 + ‖x‖) * B x) := by
        funext x
        have : (1 + ‖x‖) ≠ 0 := by positivity
        field_simp
      rw [this]
      exact ((continuous_const.add continuous_norm).inv₀ fun x =>
        (by positivity : (0 : ℝ) < 1 + ‖x‖).ne' :
        Continuous fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖)⁻¹).aestronglyMeasurable.mul hB.1
    refine hB.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hB0 x)]
    nlinarith [hB0 x, norm_nonneg x]
  set K : ℝ := |w 0| + L + L * ‖a‖ with hK
  have hK0 : 0 ≤ K := by positivity
  have hwc : Continuous w := hw.continuous
  have hψc : Continuous ψ := hψ.continuous
  -- mean value bound for `ψ` along `-a`
  have hmv : ∀ x (τ : ℝ), 0 ≤ τ → τ ≤ 1 → |ψ (x - τ • a) - ψ x| ≤ ‖a‖ * B x * τ := by
    intro x τ hτ0 hτ1
    have hder : ∀ t ∈ Icc (0 : ℝ) τ, HasDerivWithinAt (fun t : ℝ => ψ (x + t • (-a)))
        (fderiv ℝ ψ (x + t • (-a)) (-a)) (Icc 0 τ) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => x + t • (-a)) (-a) t := by
        simpa using ((hasDerivAt_id t).smul_const (-a)).const_add x
      exact ((hψ _).hasFDerivAt.comp_hasDerivAt t h1).hasDerivWithinAt
    have := norm_image_sub_le_of_norm_deriv_le_segment' hder (C := ‖a‖ * B x) ?_ τ
      ⟨hτ0, le_rfl⟩
    · simpa [sub_eq_add_neg, Real.norm_eq_abs] using this
    · intro t ht
      have h := hDψB x (-t) (by rw [abs_neg, abs_of_nonneg ht.1]; linarith [ht.2])
      calc ‖fderiv ℝ ψ (x + t • -a) (-a)‖ ≤ ‖fderiv ℝ ψ (x + t • -a)‖ * ‖-a‖ :=
            (fderiv ℝ ψ _).le_opNorm _
        _ = ‖fderiv ℝ ψ (x + (-t) • a)‖ * ‖a‖ := by rw [norm_neg, smul_neg, neg_smul]
        _ ≤ B x * ‖a‖ := by gcongr
        _ = ‖a‖ * B x := mul_comm _ _
  -- the sequence of step sizes
  set τ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hτ
  have hτpos : ∀ k, 0 < τ k := fun k => by positivity
  have hτle : ∀ k, τ k ≤ 1 := fun k => by
    rw [hτ, div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hτlim : Tendsto τ atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun k => (hτpos k).ne'⟩
  -- the discrete identity
  have hdisc : ∀ k, ∫ x, (w (x + τ k • a) - w x) / τ k * ψ x =
      ∫ x, w x * ((ψ (x - τ k • a) - ψ x) / τ k) := by
    intro k
    have hint1 : Integrable fun x => w (x + τ k • a) * ψ x := by
      refine (hB.const_mul K).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_le_of_lipschitzWith hw (norm_nonneg a) x (τ k • a)
        (by rw [norm_smul, Real.norm_of_nonneg (hτpos k).le]
            nlinarith [hτle k, norm_nonneg a])
      calc |w (x + τ k • a)| * |ψ x| ≤ (K * (1 + ‖x‖)) * B x :=
            mul_le_mul h1 (hψB x) (abs_nonneg _) (by positivity)
        _ = K * ((1 + ‖x‖) * B x) := by ring
    have hwK : ∀ x, |w x| ≤ K * (1 + ‖x‖) := fun x => by
      simpa using abs_le_of_lipschitzWith hw (norm_nonneg a) x 0 (by simp)
    have hint2 : Integrable fun x => w x * ψ x := by
      refine (hB.const_mul K).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |w x| * |ψ x| ≤ (K * (1 + ‖x‖)) * B x :=
            mul_le_mul (hwK x) (hψB x) (abs_nonneg _) (by positivity)
        _ = K * ((1 + ‖x‖) * B x) := by ring
    have hint3 : Integrable fun x => w x * ψ (x - τ k • a) := by
      refine (hB.const_mul (K * (1 + ‖a‖))).mono' (by fun_prop)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |ψ (x - τ k • a)| ≤ (1 + ‖a‖) * B x := by
        have := hmv x (τ k) (hτpos k).le (hτle k)
        have := abs_sub_abs_le_abs_sub (ψ (x - τ k • a)) (ψ x)
        nlinarith [hψB x, hB0 x, hτle k, norm_nonneg a, mul_nonneg (norm_nonneg a) (hB0 x)]
      calc |w x| * |ψ (x - τ k • a)| ≤ (K * (1 + ‖x‖)) * ((1 + ‖a‖) * B x) :=
            mul_le_mul (hwK x) h1 (abs_nonneg _) (by positivity)
        _ = K * (1 + ‖a‖) * ((1 + ‖x‖) * B x) := by ring
    have htrans : ∫ x, w (x + τ k • a) * ψ x = ∫ x, w x * ψ (x - τ k • a) := by
      have := integral_add_right_eq_self (μ := volume)
        (fun x => w x * ψ (x - τ k • a)) (τ k • a)
      simpa using this
    simp_rw [div_mul_eq_mul_div, sub_mul, mul_div_assoc', mul_sub]
    rw [integral_div, integral_div, integral_sub hint1 hint2, integral_sub hint3 hint2, htrans]
  -- limits
  have hlim1 : Tendsto (fun k => ∫ x, (w (x + τ k • a) - w x) / τ k * ψ x) atTop
      (𝓝 (∫ x, fderiv ℝ w x a * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => L * ‖a‖ * B x)
      (fun k => by fun_prop) (hBint.const_mul _) (fun k => ?_) ?_
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (hτpos k)]
      have h := hw.dist_le_mul (x + τ k • a) x
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (hτpos k).le] at h
      have h' : |w (x + τ k • a) - w x| / τ k ≤ L * ‖a‖ := by
        rw [div_le_iff₀ (hτpos k)]; nlinarith
      calc |w (x + τ k • a) - w x| / τ k * |ψ x| ≤ (L * ‖a‖) * B x :=
            mul_le_mul h' (hψB x) (abs_nonneg _) (by positivity)
        _ = _ := rfl
    · filter_upwards [hw.ae_differentiableAt] with x hx
      have hd : HasDerivAt (fun t : ℝ => w (x + t • a)) (fderiv ℝ w x a) 0 :=
        hx.hasFDerivAt.hasLineDerivAt a
      have := (hasDerivAt_iff_tendsto_slope_zero.1 hd).comp hτlim
      refine (this.mul_const (ψ x)).congr fun k => ?_
      simp [Function.comp, smul_eq_mul, div_eq_inv_mul]
  have hlim2 : Tendsto (fun k => ∫ x, w x * ((ψ (x - τ k • a) - ψ x) / τ k)) atTop
      (𝓝 (∫ x, w x * -fderiv ℝ ψ x a)) := by
    have hwK : ∀ x, |w x| ≤ K * (1 + ‖x‖) := fun x => by
      simpa using abs_le_of_lipschitzWith hw (norm_nonneg a) x 0 (by simp)
    refine tendsto_integral_of_dominated_convergence
      (fun x => K * ‖a‖ * ((1 + ‖x‖) * B x)) (fun k => by fun_prop) (hB.const_mul _)
      (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (hτpos k)]
      have h' : |ψ (x - τ k • a) - ψ x| / τ k ≤ ‖a‖ * B x := by
        rw [div_le_iff₀ (hτpos k)]; exact hmv x _ (hτpos k).le (hτle k)
      calc |w x| * (|ψ (x - τ k • a) - ψ x| / τ k) ≤ (K * (1 + ‖x‖)) * (‖a‖ * B x) :=
            mul_le_mul (hwK x) h' (by positivity) (by positivity)
        _ = K * ‖a‖ * ((1 + ‖x‖) * B x) := by ring
    · have hd : HasDerivAt (fun t : ℝ => ψ (x + t • (-a))) (-fderiv ℝ ψ x a) 0 := by
        have := (hψ x).hasFDerivAt.hasLineDerivAt (-a)
        rw [map_neg] at this
        exact this
      have := (hasDerivAt_iff_tendsto_slope_zero.1 hd).comp hτlim
      refine (this.const_mul (w x)).congr fun k => ?_
      simp [Function.comp, smul_eq_mul, div_eq_inv_mul, sub_eq_add_neg]
  have := tendsto_nhds_unique (hlim1.congr hdisc) hlim2
  rw [this]
  simp_rw [mul_neg]
  exact integral_neg _

lemma hasFDerivAt_gaussWeight (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt gaussWeight (-gaussWeight x • innerSL ℝ x) x := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.neg).mul_const (1 / 2 : ℝ)).exp
  have hf : (gaussWeight : EuclideanSpace ℝ (Fin n) → ℝ) =
      fun x => Real.exp ((-fun x => ‖x‖ ^ 2) x * (1 / 2)) := by
    funext x; simp only [gaussWeight, Pi.neg_apply]; ring_nf
  rw [hf]
  convert h using 1
  ext v
  simp

lemma differentiable_gaussWeight : Differentiable ℝ (gaussWeight (n := n)) :=
  fun x => (hasFDerivAt_gaussWeight x).differentiableAt

lemma fderiv_gaussWeight_apply (x a : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ gaussWeight x a = -(⟪x, a⟫ * gaussWeight x) := by
  rw [(hasFDerivAt_gaussWeight x).fderiv]
  simp [mul_comm]

lemma norm_fderiv_gaussWeight (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ gaussWeight x‖ = ‖x‖ * gaussWeight x := by
  rw [(hasFDerivAt_gaussWeight x).fderiv, norm_smul, innerSL_apply_norm, norm_neg,
    Real.norm_of_nonneg (gaussWeight_pos x).le, mul_comm]

/-- Translating the Gaussian weight by a bounded amount costs a factor `e^{r²/2}` and half of the
exponent. -/
lemma gaussWeight_add_le (x s : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hs : ‖s‖ ≤ r) :
    gaussWeight (x + s) ≤ Real.exp (r ^ 2 / 2) * Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by
  rw [gaussWeight, ← Real.exp_add, Real.exp_le_exp]
  have h1 : ‖x‖ ≤ ‖x + s‖ + r := by
    have := norm_sub_le (x + s) s
    rw [add_sub_cancel_right] at this; linarith
  have h0 : 0 ≤ r := (norm_nonneg s).trans hs
  nlinarith [norm_nonneg (x + s), norm_nonneg x, sq_nonneg (‖x + s‖ - r)]

/-- The dominating function used for Gaussian integration by parts in direction `a`. -/
def gaussBound (a x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (‖x‖ + ‖a‖ + 1) * Real.exp (‖a‖ ^ 2 / 2) * Real.exp (-(1 / 4) * ‖x‖ ^ 2)

lemma integrable_one_add_norm_mul_gaussBound (a : EuclideanSpace ℝ (Fin n)) :
    Integrable fun x => (1 + ‖x‖) * gaussBound a x := by
  have hb : (0 : ℝ) < 1 / 4 := by norm_num
  have h0 := integrable_norm_pow_mul_exp_neg_mul_sq_norm (n := n) hb 0
  have h1 := integrable_norm_pow_mul_exp_neg_mul_sq_norm (n := n) hb 1
  have h2 := integrable_norm_pow_mul_exp_neg_mul_sq_norm (n := n) hb 2
  have := ((h2.add (h1.const_mul (2 + ‖a‖))).add (h0.const_mul (1 + ‖a‖))).const_mul
    (Real.exp (‖a‖ ^ 2 / 2))
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussBound, Pi.add_apply, pow_zero, pow_one]
  ring

lemma abs_gaussWeight_le_gaussBound (a x : EuclideanSpace ℝ (Fin n)) :
    |gaussWeight x| ≤ gaussBound a x := by
  rw [abs_of_pos (gaussWeight_pos x)]
  have := gaussWeight_add_le x 0 (r := 0) (by simp)
  simp only [add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Real.exp_zero, one_mul] at this
  have h1 : 1 ≤ ‖x‖ + ‖a‖ + 1 := by linarith [norm_nonneg x, norm_nonneg a]
  have h2 : 1 ≤ Real.exp (‖a‖ ^ 2 / 2) := Real.one_le_exp (by positivity)
  have h3 := Real.exp_pos (-(1 / 4) * ‖x‖ ^ 2)
  calc gaussWeight x ≤ Real.exp (-(1 / 4) * ‖x‖ ^ 2) := this
    _ = 1 * 1 * Real.exp (-(1 / 4) * ‖x‖ ^ 2) := by ring
    _ ≤ _ := by unfold gaussBound; gcongr

lemma norm_fderiv_gaussWeight_le_gaussBound (a x : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (ht : |t| ≤ 1) : ‖fderiv ℝ gaussWeight (x + t • a)‖ ≤ gaussBound a x := by
  have hs : ‖t • a‖ ≤ ‖a‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg a, abs_nonneg t]
  rw [norm_fderiv_gaussWeight]
  have h1 : ‖x + t • a‖ ≤ ‖x‖ + ‖a‖ + 1 := by
    linarith [norm_add_le x (t • a)]
  have h2 := gaussWeight_add_le x (t • a) hs
  calc ‖x + t • a‖ * gaussWeight (x + t • a)
      ≤ (‖x‖ + ‖a‖ + 1) * (Real.exp (‖a‖ ^ 2 / 2) * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) :=
        mul_le_mul h1 h2 (gaussWeight_pos _).le (by positivity)
    _ = gaussBound a x := by unfold gaussBound; ring

/-- **Gaussian integration by parts** for Lipschitz functions:
`∫ ∂ₐw · e^{-|x|²/2} dx = ∫ w ⟪x, a⟫ e^{-|x|²/2} dx`. -/
theorem integral_fderiv_mul_gaussWeight {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (a : EuclideanSpace ℝ (Fin n)) :
    ∫ x, fderiv ℝ w x a * gaussWeight x = ∫ x, w x * (⟪x, a⟫ * gaussWeight x) := by
  rw [integral_fderiv_mul_eq_neg_integral_mul_fderiv hw a differentiable_gaussWeight
    (integrable_one_add_norm_mul_gaussBound a) (abs_gaussWeight_le_gaussBound a)
    (norm_fderiv_gaussWeight_le_gaussBound a), ← integral_neg]
  congr 1; funext x
  rw [fderiv_gaussWeight_apply]; ring

/-- **Gaussian integration by parts** for Lipschitz functions, `γ` form:
`∫ ∂ₐw dγ = ∫ w ⟪x, a⟫ dγ`. -/
theorem integral_fderiv_gaussMeasure {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (a : EuclideanSpace ℝ (Fin n)) :
    ∫ x, fderiv ℝ w x a ∂gaussMeasure n = ∫ x, w x * ⟪x, a⟫ ∂gaussMeasure n := by
  rw [integral_gaussMeasure, integral_gaussMeasure]
  simp_rw [mul_comm (gaussWeight _)]
  rw [integral_fderiv_mul_gaussWeight hw a]
  congr 1; funext x; ring

end Sperner
