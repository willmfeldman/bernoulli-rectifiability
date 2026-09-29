/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Sperner's inequality: basic definitions

We work on `ℝⁿ = EuclideanSpace ℝ (Fin n)` with the *unnormalized* Gaussian measure
`γ = exp(-|x|²/2) dx`. For one-homogeneous functions, Gaussian integrals are constant multiples
of integrals over the unit sphere, so the spherical Dirichlet eigenvalue problem
`-Δ_S φ = λ φ` becomes a problem about the Gaussian Rayleigh quotient
`∫ |∇f|² dγ / ∫ f² dγ` of the one-homogeneous extension `f(x) = |x| φ(x/|x|)`. The spherical
eigenvalue `n - 1` corresponds exactly to the Gaussian Rayleigh quotient `1`, and the
half-space function `x ↦ ⟪x, e⟫⁺` realizes it. This dictionary lets us avoid all calculus on
the sphere.

## Main definitions

* `Sperner.gaussWeight`, `Sperner.gaussMeasure`: the weight `exp(-|x|²/2)` and `γ`.
* `Sperner.IsOneHomogeneous`: `f (t • x) = t * f x` for `t > 0`.
* `Sperner.IsCone`: a set stable under positive dilations.
* `Sperner.dirichletEnergy f = ∫ ‖Df‖² dγ`, `Sperner.gaussL2 f = ∫ f² dγ`.
-/

open MeasureTheory Metric Set
open scoped RealInnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- The unnormalized standard Gaussian weight `exp(-|x|²/2)`. -/
def gaussWeight (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(‖x‖ ^ 2) / 2)

/-- The unnormalized Gaussian measure `γ = exp(-|x|²/2) dx` on `ℝⁿ`. -/
def gaussMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity fun x => ENNReal.ofReal (gaussWeight x)

/-- `f` is positively one-homogeneous: `f (t • x) = t * f x` for all `t > 0`. -/
def IsOneHomogeneous (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t → f (t • x) = t * f x

/-- `s` is a cone: it is stable under dilations by positive factors. -/
def IsCone (s : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ s, ∀ t : ℝ, 0 < t → t • x ∈ s

/-- The Gaussian Dirichlet energy `∫ ‖Df‖² dγ`. For Lipschitz `f` the Fréchet derivative exists
almost everywhere (Rademacher), and `fderiv` is `0` elsewhere. -/
def dirichletEnergy (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂gaussMeasure n

/-- The Gaussian `L²` mass `∫ f² dγ`. -/
def gaussL2 (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, f x ^ 2 ∂gaussMeasure n

/-- The Gaussian first moment `J_e(f) = ∫ f ⟪x, e⟫ dγ`, the functional maximized in the
symmetrization argument. -/
def gaussMoment (e : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, f x * ⟪x, e⟫ ∂gaussMeasure n

/-- The class of competitors in the symmetrization argument: `L`-Lipschitz, nonnegative,
one-homogeneous functions with `∫ w² dγ = M`, `∫ |Dw|² dγ ≤ D` and `γ{w > 0} ≤ m`. -/
def AdmissibleClass (L : ℝ≥0) (D M : ℝ) (m : ℝ≥0∞) (w : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LipschitzWith L w ∧ (∀ x, 0 ≤ w x) ∧ IsOneHomogeneous w ∧ gaussL2 w = M ∧
    dirichletEnergy w ≤ D ∧ gaussMeasure n {x | 0 < w x} ≤ m

lemma gaussWeight_pos (x : EuclideanSpace ℝ (Fin n)) : 0 < gaussWeight x :=
  Real.exp_pos _

lemma continuous_gaussWeight : Continuous (gaussWeight (n := n)) := by
  unfold gaussWeight; fun_prop

lemma integrable_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin n)) (show 0 < (b : ℂ).re by simpa using hb) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

/-- Gaussian moments are finite: `‖x‖ᵏ e^{-b‖x‖²}` is integrable on `ℝⁿ`. -/
lemma integrable_norm_pow_mul_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ k * Real.exp (-b * ‖x‖ ^ 2)) := by
  have h1 := integrable_exp_neg_mul_sq_norm (n := n) hb
  have h2 := integrable_exp_neg_mul_sq_norm (n := n) (half_pos hb)
  set C : ℝ := (2 / b) ^ k * k.factorial
  refine Integrable.mono' (h1.add (h2.const_mul C)) (by fun_prop) ?_
  filter_upwards with x
  have hC : 0 ≤ C := by positivity
  have hA : ‖x‖ ^ k ≤ 1 + (‖x‖ ^ 2) ^ k := by
    rcases le_total ‖x‖ 1 with h | h
    · have := pow_le_one₀ (norm_nonneg x) h (n := k)
      nlinarith [pow_nonneg (sq_nonneg ‖x‖) k]
    · have : ‖x‖ ^ k ≤ (‖x‖ ^ 2) ^ k := by
        rw [← pow_mul]; exact pow_le_pow_right₀ h (by omega)
      linarith
  have hB : (‖x‖ ^ 2) ^ k ≤ C * Real.exp (b / 2 * ‖x‖ ^ 2) := by
    have := Real.pow_div_factorial_le_exp (x := b / 2 * ‖x‖ ^ 2) (by positivity) k
    rw [div_le_iff₀ (by positivity), mul_pow] at this
    have hb' : (2 / b) ^ k * (b / 2) ^ k = 1 := by
      rw [← mul_pow]; field_simp; simp
    calc (‖x‖ ^ 2) ^ k = (2 / b) ^ k * ((b / 2) ^ k * (‖x‖ ^ 2) ^ k) := by
          rw [← mul_assoc, hb', one_mul]
      _ ≤ (2 / b) ^ k * (Real.exp (b / 2 * ‖x‖ ^ 2) * k.factorial) := by gcongr
      _ = C * Real.exp (b / 2 * ‖x‖ ^ 2) := by ring
  have hexp : Real.exp (b / 2 * ‖x‖ ^ 2) * Real.exp (-b * ‖x‖ ^ 2) =
      Real.exp (-(b / 2) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  calc ‖x‖ ^ k * Real.exp (-b * ‖x‖ ^ 2)
      ≤ (1 + C * Real.exp (b / 2 * ‖x‖ ^ 2)) * Real.exp (-b * ‖x‖ ^ 2) := by
        gcongr; linarith
    _ = Real.exp (-b * ‖x‖ ^ 2) + C * Real.exp (-(b / 2) * ‖x‖ ^ 2) := by
        rw [← hexp]; ring

lemma integrable_gaussWeight : Integrable (gaussWeight (n := n)) := by
  refine (integrable_exp_neg_mul_sq_norm (n := n) (b := 1 / 2) (by norm_num)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussWeight]
  ring_nf

instance : IsFiniteMeasure (gaussMeasure n) := by
  unfold gaussMeasure
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact (integrable_gaussWeight (n := n)).hasFiniteIntegral

lemma gaussMeasure_univ_pos : 0 < gaussMeasure n univ := by
  unfold gaussMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_pos_iff_support]
  · have : Function.support (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (gaussWeight x))
        = univ := by
      ext x; simp [gaussWeight_pos x]
    rw [this]; simpa using NeZero.ne (volume : Measure (EuclideanSpace ℝ (Fin n)))
  · exact (continuous_gaussWeight.measurable).ennreal_ofReal

lemma measurable_gaussWeight_toNNReal :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => (gaussWeight x).toNNReal :=
  continuous_gaussWeight.measurable.real_toNNReal

lemma gaussMeasure_eq_withDensity_toNNReal :
    gaussMeasure n = volume.withDensity fun x => ((gaussWeight x).toNNReal : ℝ≥0∞) := rfl

/-- Gaussian integrals as weighted Lebesgue integrals. -/
lemma integral_gaussMeasure (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, f x ∂gaussMeasure n = ∫ x, gaussWeight x * f x := by
  rw [gaussMeasure_eq_withDensity_toNNReal,
    integral_withDensity_eq_integral_smul measurable_gaussWeight_toNNReal]
  congr 1; funext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (gaussWeight_pos x).le, smul_eq_mul]

lemma integrable_gaussMeasure_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    Integrable f (gaussMeasure n) ↔ Integrable fun x => gaussWeight x * f x := by
  rw [gaussMeasure_eq_withDensity_toNNReal,
    integrable_withDensity_iff_integrable_smul measurable_gaussWeight_toNNReal]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (gaussWeight_pos x).le, smul_eq_mul]

lemma integrable_norm_pow_gaussMeasure (k : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ k) (gaussMeasure n) := by
  rw [integrable_gaussMeasure_iff]
  refine (integrable_norm_pow_mul_exp_neg_mul_sq_norm (n := n) (b := 1 / 2) (by norm_num) k).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussWeight]; ring_nf

lemma gaussMeasure_pos_of_isOpen {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    (hne : s.Nonempty) : 0 < gaussMeasure n s := by
  rw [pos_iff_ne_zero, gaussMeasure, ne_eq,
    withDensity_apply_eq_zero (continuous_gaussWeight.measurable.ennreal_ofReal)]
  have : {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal (gaussWeight x) ≠ 0} = univ := by
    ext x; simp [gaussWeight_pos x]
  rw [this, univ_inter]
  exact (hs.measure_pos volume hne).ne'

namespace IsOneHomogeneous

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

lemma map_zero (hf : IsOneHomogeneous f) : f 0 = 0 := by
  have := hf 0 2 two_pos
  rw [smul_zero] at this
  linarith

/-- **Euler's identity** `Df(x) x = f(x)` at points of differentiability. -/
lemma fderiv_apply_self (hf : IsOneHomogeneous f) {x : EuclideanSpace ℝ (Fin n)}
    (hd : DifferentiableAt ℝ f x) : fderiv ℝ f x x = f x := by
  have h1 : HasDerivAt (fun t : ℝ => f (x + t • x)) (fderiv ℝ f x x) 0 :=
    hd.hasFDerivAt.hasLineDerivAt x
  have h2 : HasDerivAt (fun t : ℝ => (1 + t) * f x) (f x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const (f x)
  have heq : (fun t : ℝ => f (x + t • x)) =ᶠ[nhds 0] fun t => (1 + t) * f x := by
    filter_upwards [lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
    rw [show x + t • x = (1 + t) • x by rw [add_smul, one_smul], hf x (1 + t) (by linarith)]
  exact h1.unique (h2.congr_of_eventuallyEq heq)

end IsOneHomogeneous

end Sperner
