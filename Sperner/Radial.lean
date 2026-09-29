/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# A radial identity for Gaussian integrals of zero-homogeneous functions

For a bounded measurable `F` with `F (t • x) = F x` (`t > 0`),
`∫ F |x|² dγ = n ∫ F dγ`. In polar coordinates this is `∫₀^∞ r^{n+1} e^{-r²/2} dr =
n ∫₀^∞ r^{n-1} e^{-r²/2} dr`; we prove it without polar coordinates, by differentiating the
scaling identity `∫ F(x) e^{-λ²|x|²/2} dx = λ^{-n} ∫ F(x) e^{-|x|²/2} dx` at `λ = 1`.
-/

open MeasureTheory Set Filter Topology

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- Scaling: for zero-homogeneous `F` and `λ > 0`,
`∫ F(x) e^{-λ²|x|²/2} dx = λ^{-n} ∫ F(x) e^{-|x|²/2} dx`. -/
lemma integral_mul_exp_scale {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (h0 : ∀ x (t : ℝ), 0 < t → F (t • x) = F x) {l : ℝ} (hl : 0 < l) :
    ∫ x, F x * Real.exp (-(l ^ 2 * ‖x‖ ^ 2) / 2) =
      (l ^ n)⁻¹ * ∫ x, F x * Real.exp (-(1 ^ 2 * ‖x‖ ^ 2) / 2) := by
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume :
    Measure (EuclideanSpace ℝ (Fin n)))) (fun y => F y * Real.exp (-(1 ^ 2 * ‖y‖ ^ 2) / 2)) l
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at h
  rw [abs_of_pos (inv_pos.2 (pow_pos hl n))] at h
  rw [← h]
  congr 1
  ext x
  rw [h0 x l hl, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  ring_nf

/-- **Radial identity.** For a bounded measurable zero-homogeneous `F`,
`∫ F |x|² dγ = n ∫ F dγ`. -/
theorem integral_mul_norm_sq_gaussMeasure {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : Measurable F) (hbdd : ∃ C, ∀ x, |F x| ≤ C)
    (h0 : ∀ x (t : ℝ), 0 < t → F (t • x) = F x) :
    ∫ x, F x * ‖x‖ ^ 2 ∂gaussMeasure n = n * ∫ x, F x ∂gaussMeasure n := by
  obtain ⟨C, hC⟩ := hbdd
  set G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun l x => F x * Real.exp (-(l ^ 2 * ‖x‖ ^ 2) / 2) with hG
  set G' : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun l x => F x * (Real.exp (-(l ^ 2 * ‖x‖ ^ 2) / 2) * (-(l * ‖x‖ ^ 2))) with hG'
  have hmeas : ∀ l, AEStronglyMeasurable (G l) volume := fun l =>
    (hF.mul (by fun_prop)).aestronglyMeasurable
  have hInt1 : Integrable (G 1) volume := by
    refine ((integrable_exp_neg_mul_sq_norm (n := n) (b := 1 / 2) (by norm_num)).const_mul
      C).mono' (hmeas 1) (ae_of_all _ fun x => ?_)
    simp only [hG, norm_mul, Real.norm_eq_abs, Real.abs_exp]
    have : Real.exp (-(1 ^ 2 * ‖x‖ ^ 2) / 2) = Real.exp (-(1 / 2) * ‖x‖ ^ 2) := by ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le
  -- the dominating function on `λ ∈ (1/2, 3/2)`
  have hbound_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      C * (3 / 2) * (‖x‖ ^ 2 * Real.exp (-(1 / 8) * ‖x‖ ^ 2))) volume :=
    (integrable_norm_pow_mul_exp_neg_mul_sq_norm (k := 2) (n := n) (by norm_num)).const_mul _
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := G) (F' := G') (x₀ := (1 : ℝ)) (s := Metric.ball 1 (1 / 2))
    (Metric.ball_mem_nhds _ (by norm_num)) (Eventually.of_forall hmeas) hInt1
    ((hF.mul (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun x l hl => ?bound) hbound_int
    (ae_of_all _ fun x l _ => ?diff)
  case bound =>
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hl
    have hl1 : 1 / 2 < l := by linarith
    have hl2 : l < 3 / 2 := by linarith
    have hl0 : (0 : ℝ) < l := by linarith
    have hnorm : ‖G' l x‖ = |F x| * (Real.exp (-(l ^ 2 * ‖x‖ ^ 2) / 2) * (l * ‖x‖ ^ 2)) := by
      simp only [hG', Real.norm_eq_abs, abs_mul, Real.abs_exp, abs_neg, abs_of_pos hl0,
        abs_of_nonneg (sq_nonneg ‖x‖)]
    rw [hnorm]
    have hexp : Real.exp (-(l ^ 2 * ‖x‖ ^ 2) / 2) ≤ Real.exp (-(1 / 8) * ‖x‖ ^ 2) := by
      apply Real.exp_le_exp.2
      have : 1 / 4 ≤ l ^ 2 := by nlinarith
      nlinarith [sq_nonneg ‖x‖]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
    calc |F x| * (Real.exp (-(l ^ 2 * ‖x‖ ^ 2) / 2) * (l * ‖x‖ ^ 2))
        ≤ C * (Real.exp (-(1 / 8) * ‖x‖ ^ 2) * (3 / 2 * ‖x‖ ^ 2)) := by
          gcongr
          exact hC x
      _ = C * (3 / 2) * (‖x‖ ^ 2 * Real.exp (-(1 / 8) * ‖x‖ ^ 2)) := by ring
  case diff =>
    have := ((((hasDerivAt_pow 2 l).mul_const (‖x‖ ^ 2)).neg.div_const 2).exp).const_mul (F x)
    refine this.congr_deriv ?_
    simp only [hG', Pi.neg_apply]
    push_cast
    ring
  -- the scaling identity pins down the derivative
  have hscale : (fun l => ∫ x, G l x) =ᶠ[𝓝 1] fun l => (l ^ n)⁻¹ * ∫ x, G 1 x := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with l hl
    exact integral_mul_exp_scale h0 hl
  have hderiv2 : HasDerivAt (fun l : ℝ => (l ^ n)⁻¹ * ∫ x, G 1 x)
      (-(n : ℝ) * ∫ x, G 1 x) 1 := by
    have := ((hasDerivAt_pow n (1 : ℝ)).inv (by norm_num)).mul_const (∫ x, G 1 x)
    refine this.congr_deriv ?_
    simp
  have heq := (hderiv.2.congr_of_eventuallyEq hscale.symm).unique hderiv2
  -- translate to `γ`
  rw [integral_gaussMeasure, integral_gaussMeasure]
  have hL : ∫ x, gaussWeight x * (F x * ‖x‖ ^ 2) = -∫ x, G' 1 x := by
    rw [← integral_neg]
    congr 1; ext x
    simp only [hG', gaussWeight]; ring_nf
  have hR : ∫ x, gaussWeight x * F x = ∫ x, G 1 x := by
    congr 1; ext x
    simp only [hG, gaussWeight]; ring_nf
  rw [hL, hR, heq]
  ring

end Sperner
