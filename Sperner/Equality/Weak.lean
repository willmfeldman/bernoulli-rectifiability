/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Equality.Minimizer
public import Sperner.Harmonic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Minimizers are harmonic on their positivity sets

Let `w` be a minimizer (`Sperner/Equality/Minimizer.lean`): a nonnegative, one-homogeneous,
Lipschitz function with `∫ |Dw|² dγ ≤ ∫ w² dγ` and `2 γ{w > 0} ≤ γ(ℝⁿ)`. The first variation
gives `B(w, ψ) = 0` only for one-homogeneous test functions `ψ`. We convert these into arbitrary
test functions without polar coordinates: for `ζ ∈ C_c^∞({w > 0})` put `g(y) = |y|ⁿ ζ(y)` and
`ψ(x) = ∫₀^∞ g(x / s) ds` (one-homogeneous, Lipschitz, supported in the cone over `supp ζ`).
Fubini and the substitution `x = s y` give

`B(w, ψ) = c ∫ ⟨∇w, ∇ζ⟩ dx = -c ∫ w Δζ dx`, `c = ∫₀^∞ s^{n-1} e^{-s²/2} ds > 0`,

using the one-dimensional identity `∫₀^∞ s^{n+1} e^{-s²/2} ds = n c` and Euler's identity
`⟨y, ∇w(y)⟩ = w(y)`. Hence `w` is weakly harmonic on `{w > 0}`, and harmonic by Weyl's lemma.

## Main results

* `Sperner.integral_mul_laplacian_eq_zero_of_minimizer`: `∫ w Δζ = 0`.
* `Sperner.harmonicAt_of_minimizer`: a minimizer is harmonic on `{w > 0}`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace Metric
open scoped NNReal ENNReal RealInnerProductSpace Gradient ContDiff Laplacian

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-! ### One-dimensional Gaussian moments -/

/-- The radial Gaussian moment `c_k = ∫₀^∞ s^k e^{-s²/2} ds`. -/
def radialMoment (k : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(s ^ 2) / 2)

lemma radialMoment_eq_gamma (k : ℕ) :
    radialMoment k =
      (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 1) / 2) := by
  rw [← integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := k) (b := 1 / 2) two_pos
    (by have := k.cast_nonneg (α := ℝ); linarith) (by norm_num), radialMoment]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [Real.rpow_natCast]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring_nf

lemma radialMoment_pos (k : ℕ) : 0 < radialMoment k := by
  rw [radialMoment_eq_gamma]
  have : 0 < ((k : ℝ) + 1) / 2 := by positivity
  have := Real.Gamma_pos_of_pos this
  positivity

lemma radialMoment_add_two (k : ℕ) : radialMoment (k + 2) = (k + 1) * radialMoment k := by
  rw [radialMoment_eq_gamma, radialMoment_eq_gamma]
  have hk : ((k : ℝ) + 1) / 2 ≠ 0 := by positivity
  have hG : Real.Gamma ((((k + 2 : ℕ) : ℝ) + 1) / 2) =
      ((k : ℝ) + 1) / 2 * Real.Gamma (((k : ℝ) + 1) / 2) := by
    rw [← Real.Gamma_add_one hk]; congr 1; push_cast; ring
  have hp : (1 / 2 : ℝ) ^ (-(((k + 2 : ℕ) : ℝ) + 1) / 2) =
      (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * 2 := by
    rw [show -(((k + 2 : ℕ) : ℝ) + 1) / 2 = -((k : ℝ) + 1) / 2 + (-1) by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_neg_one]
    norm_num
  rw [hG, hp]
  ring

/-- Scaling of the radial moments: `∫₀^∞ s^k γ(s y) ds = c_k / |y|^{k+1}`. -/
lemma integral_pow_mul_gaussWeight_smul (k : ℕ) {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0) :
    ∫ s in Ioi (0 : ℝ), s ^ k * gaussWeight (s • y) = radialMoment k / ‖y‖ ^ (k + 1) := by
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
  set g : ℝ → ℝ := fun u => u ^ k * Real.exp (-(u ^ 2) / 2) with hg
  have h := integral_comp_mul_left_Ioi g 0 hny
  rw [mul_zero, smul_eq_mul] at h
  have h2 : ∫ s in Ioi (0 : ℝ), g (‖y‖ * s) =
      ‖y‖ ^ k * ∫ s in Ioi (0 : ℝ), s ^ k * gaussWeight (s • y) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
    simp only [hg, gaussWeight, norm_smul, Real.norm_of_nonneg hs.le]
    ring_nf
  rw [h2] at h
  rw [eq_div_iff (by positivity), radialMoment, ← hg]
  have : ‖y‖ ^ (k + 1) = ‖y‖ * ‖y‖ ^ k := by ring
  rw [this, mul_comm, mul_assoc, h, ← mul_assoc, mul_inv_cancel₀ hny.ne', one_mul]

/-! ### Homogeneity of the derivative -/

/-- The derivative of a one-homogeneous function is zero-homogeneous (everywhere, including
points of non-differentiability, where both sides vanish). -/
lemma IsOneHomogeneous.fderiv_smul {w : EuclideanSpace ℝ (Fin n) → ℝ} (hhom : IsOneHomogeneous w)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ w (t • x) = fderiv ℝ w x := by
  have hfun : (fun y => w (t • y)) = t • w := by
    funext y; simp [hhom y t ht]
  have h1 := fderiv_comp_smul (𝕜 := ℝ) (f := w) (x := x) t
  rw [hfun, fderiv_const_smul_field] at h1
  simp only [Pi.smul_apply] at h1
  have h2 := congrArg (fun L => t⁻¹ • L) h1
  simp only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h2
  exact h2.symm

lemma IsOneHomogeneous.gradient_smul {w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hhom : IsOneHomogeneous w) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ∇ w (t • x) = ∇ w x := by
  simp only [gradient, hhom.fderiv_smul ht x]

/-! ### Fubini in scaling coordinates -/

/-- Change of variables `x = s y` in `ℝⁿ`. -/
lemma integral_eq_pow_mul_integral_smul (f : EuclideanSpace ℝ (Fin n) → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, f x = s ^ n * ∫ y, f (s • y) := by
  rw [Measure.integral_comp_smul volume f s, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (inv_pos.2 (pow_pos hs n)), ← mul_assoc, mul_inv_cancel₀ (pow_pos hs n).ne',
    one_mul]

/-- A bounded measurable function vanishing outside a ball is integrable. -/
lemma integrable_of_abs_le_of_norm_le {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {K R : ℝ} (hK : ∀ y, |f y| ≤ K) (hsupp : ∀ y, f y ≠ 0 → ‖y‖ ≤ R) : Integrable f := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hi : Integrable ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R).indicator fun _ => K) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
  refine hi.mono' hf.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  by_cases hy : f y = 0
  · rw [hy, abs_zero]; exact indicator_nonneg (fun _ _ => hK0) y
  · rw [indicator_of_mem (by simpa using hsupp y hy)]; exact hK y

lemma gaussWeight_smul_le {y : EuclideanSpace ℝ (Fin n)} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hy : r ≤ ‖y‖) : gaussWeight (s • y) ≤ Real.exp (-(r ^ 2 / 2) * s ^ 2) := by
  unfold gaussWeight
  rw [Real.exp_le_exp, norm_smul, Real.norm_of_nonneg hs]
  have : (s * r) ^ 2 ≤ (s * ‖y‖) ^ 2 := pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left hy hs) 2
  nlinarith

lemma integrableOn_pow_mul_exp_neg_mul_sq (p : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s ^ p * Real.exp (-b * s ^ 2)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb (s := p) (by
    have := p.cast_nonneg (α := ℝ); linarith)
  refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]

/-- **Fubini in scaling coordinates.** Let `Φ` be bounded, measurable, supported in the annulus
`r ≤ |y| ≤ R` (`r > 0`), and `h` be measurable, `j`-homogeneous with `|h y| ≤ M |y|^j`. Then
`∫ γ(x) h(x) ∫₀^∞ s^{-m} Φ(x/s) ds dx = ∫ h Φ K_{n+j-m}` with
`K_p(y) = ∫₀^∞ s^p γ(s y) ds = c_p / |y|^{p+1}`. -/
theorem integral_gaussWeight_mul_integral_scale {Φ h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΦ : Measurable Φ) {C r R : ℝ} (hr : 0 < r) (hΦC : ∀ y, |Φ y| ≤ C)
    (hΦ0 : ∀ y, Φ y ≠ 0 → r ≤ ‖y‖ ∧ ‖y‖ ≤ R)
    (hR : 0 ≤ R) (hh : Measurable h) {j : ℕ} {M : ℝ} (hM : 0 ≤ M) (hhM : ∀ y, |h y| ≤ M * ‖y‖ ^ j)
    (hhom : ∀ y (t : ℝ), 0 < t → h (t • y) = t ^ j * h y)
    {m : ℕ} (hm : m ≤ n + j) :
    ∫ x, gaussWeight x * h x * ∫ s in Ioi (0 : ℝ), (s ^ m)⁻¹ * Φ (s⁻¹ • x) =
      ∫ y, h y * Φ y * (radialMoment (n + j - m) / ‖y‖ ^ (n + j - m + 1)) := by
  set p := n + j - m with hp
  set F : EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=
    fun x s => gaussWeight x * h x * ((s ^ m)⁻¹ * Φ (s⁻¹ • x)) with hF
  set G : EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=
    fun y s => s ^ p * gaussWeight (s • y) * (h y * Φ y) with hG
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hΦC 0)
  -- pointwise change of variables
  have hpt : ∀ y {s : ℝ}, 0 < s → s ^ n * F (s • y) s = G y s := by
    intro y s hs
    simp only [hF, hG, inv_smul_smul₀ hs.ne', hhom y s hs]
    have : s ^ n * s ^ j = s ^ p * s ^ m := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    field_simp
    linear_combination (gaussWeight (s • y) * h y * Φ y) * this
  have hcv : ∀ {s : ℝ}, 0 < s → ∫ x, F x s = ∫ y, G y s := fun hs => by
    rw [integral_eq_pow_mul_integral_smul _ hs, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => hpt y hs)
  have hcvn : ∀ {s : ℝ}, 0 < s → ∫ x, ‖F x s‖ = ∫ y, ‖G y s‖ := by
    intro s hs
    rw [integral_eq_pow_mul_integral_smul _ hs, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    change s ^ n * ‖F (s • y) s‖ = ‖G y s‖
    rw [← hpt y hs, norm_mul (s ^ n) (F (s • y) s), Real.norm_of_nonneg (pow_nonneg hs.le n)]
  -- measurability
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable fun z : EuclideanSpace ℝ (Fin n) × ℝ => z.2⁻¹ • z.1 := by fun_prop
    simp only [hF, Function.uncurry_def]
    exact ((continuous_gaussWeight.measurable.comp measurable_fst).mul (hh.comp measurable_fst)).mul
      (((measurable_snd.pow_const m).inv).mul (hΦ.comp h1))
  have hGm : Measurable (Function.uncurry G) := by
    have h1 : Measurable fun z : EuclideanSpace ℝ (Fin n) × ℝ => z.2 • z.1 := by fun_prop
    simp only [hG, Function.uncurry_def]
    exact ((measurable_snd.pow_const p).mul (continuous_gaussWeight.measurable.comp h1)).mul
      ((hh.comp measurable_fst).mul (hΦ.comp measurable_fst))
  -- integrability of `h Φ`
  have hhΦ : Integrable fun y => h y * Φ y := by
    refine integrable_of_abs_le_of_norm_le (hh.mul hΦ) (K := M * R ^ j * C) (R := R)
      (fun y => ?_) (fun y hy => (hΦ0 y (right_ne_zero_of_mul hy)).2)
    by_cases hy : Φ y = 0
    · rw [hy, mul_zero, abs_zero]; positivity
    · obtain ⟨h1, h2⟩ := hΦ0 y hy
      rw [abs_mul]
      refine mul_le_mul ((hhM y).trans ?_) (hΦC y) (abs_nonneg _) (by positivity)
      gcongr
  -- integrability on the product, before the change of variables
  have hFint : Integrable (Function.uncurry F) ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun s (hs : 0 < s) => ?_
      have hi : Integrable fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ j * gaussWeight x := by
        have := integrable_gaussMeasure_iff.1 (integrable_norm_pow_gaussMeasure (n := n) j)
        simpa only [mul_comm] using this
      refine (hi.const_mul ((s ^ m)⁻¹ * C * M)).mono'
        (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      simp only [hF, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
        abs_of_pos (gaussWeight_pos x), abs_inv, abs_of_pos (pow_pos hs m)]
      have h1 := hhM x
      have h2 := hΦC (s⁻¹ • x)
      have h3 := gaussWeight_pos x
      have h4 : 0 ≤ (s ^ m)⁻¹ := by positivity
      calc gaussWeight x * |h x| * ((s ^ m)⁻¹ * |Φ (s⁻¹ • x)|)
          ≤ gaussWeight x * (M * ‖x‖ ^ j) * ((s ^ m)⁻¹ * C) := by gcongr
        _ = (s ^ m)⁻¹ * C * M * (‖x‖ ^ j * gaussWeight x) := by ring
    · have hmeas : AEStronglyMeasurable
          (fun s : ℝ => ∫ x, ‖Function.uncurry F (x, s)‖) (volume.restrict (Ioi (0 : ℝ))) := by
        have := StronglyMeasurable.integral_prod_left
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
          (f := fun x s => ‖Function.uncurry F (x, s)‖) (by
            exact (hFm.norm).stronglyMeasurable)
        exact this.aestronglyMeasurable
      refine ((integrableOn_pow_mul_exp_neg_mul_sq p (b := r ^ 2 / 2) (by positivity)).mul_const
        (∫ y, |h y * Φ y|)).mono' hmeas ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun s (hs : 0 < s) => ?_
      simp only [Function.uncurry_apply_pair]
      rw [hcvn hs, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
        ← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (hhΦ.abs.const_mul _) (ae_of_all _ fun y => ?_)
      simp only [hG, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hs.le p),
        abs_of_pos (gaussWeight_pos _)]
      by_cases hy : Φ y = 0
      · simp [hy]
      · have := gaussWeight_smul_le hr.le hs.le (hΦ0 y hy).1
        have h0 : 0 ≤ s ^ p := pow_nonneg hs.le p
        have h1 : 0 ≤ |h y| * |Φ y| := by positivity
        calc s ^ p * gaussWeight (s • y) * (|h y| * |Φ y|)
            ≤ s ^ p * Real.exp (-(r ^ 2 / 2) * s ^ 2) * (|h y| * |Φ y|) := by gcongr
          _ = _ := by ring
  -- integrability on the product, after the change of variables
  have hGint : Integrable (Function.uncurry G) ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
      (volume.restrict (Ioi (0 : ℝ)))) := by
    have hprod := hhΦ.abs.mul_prod (integrableOn_pow_mul_exp_neg_mul_sq p (b := r ^ 2 / 2)
      (by positivity))
    refine hprod.mono' hGm.aestronglyMeasurable ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · refine ae_of_all _ fun y => ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun s (hs : 0 < s) => ?_
      simp only [hG, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg hs.le p), abs_of_pos (gaussWeight_pos _)]
      by_cases hy : Φ y = 0
      · simp [hy]
      · have := gaussWeight_smul_le hr.le hs.le (hΦ0 y hy).1
        have h0 : 0 ≤ s ^ p := pow_nonneg hs.le p
        have h1 : 0 ≤ |h y| * |Φ y| := by positivity
        calc s ^ p * gaussWeight (s • y) * (|h y| * |Φ y|)
            ≤ s ^ p * Real.exp (-(r ^ 2 / 2) * s ^ 2) * (|h y| * |Φ y|) := by gcongr
          _ = _ := by ring
    · exact measurableSet_le (hGm.norm) (by fun_prop)
  -- assemble
  calc ∫ x, gaussWeight x * h x * ∫ s in Ioi (0 : ℝ), (s ^ m)⁻¹ * Φ (s⁻¹ • x)
      = ∫ x, ∫ s in Ioi (0 : ℝ), F x s := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hF]; rw [integral_const_mul]
    _ = ∫ s in Ioi (0 : ℝ), ∫ x, F x s := integral_integral_swap hFint
    _ = ∫ s in Ioi (0 : ℝ), ∫ y, G y s :=
        setIntegral_congr_fun measurableSet_Ioi fun s hs => hcv hs
    _ = ∫ y, ∫ s in Ioi (0 : ℝ), G y s := (integral_integral_swap hGint).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [hG]
        rw [integral_mul_const]
        by_cases hy : Φ y = 0
        · simp [hy]
        · have hy0 : y ≠ 0 := by
            intro h0
            have := (hΦ0 y hy).1
            rw [h0, norm_zero] at this
            linarith
          rw [integral_pow_mul_gaussWeight_smul p hy0]
          ring

/-! ### The one-homogeneous function generated by a test function -/

/-- A `C¹` function supported in the closed annulus `r ≤ |y| ≤ R`, `0 < r ≤ R`. -/
structure IsAnnularTest (g : EuclideanSpace ℝ (Fin n) → ℝ) (r R : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 g
  hasCompactSupport : HasCompactSupport g
  pos : 0 < r
  le : r ≤ R
  mem_tsupport : ∀ y ∈ tsupport g, r ≤ ‖y‖ ∧ ‖y‖ ≤ R

/-- `ψ(x) = ∫₀^∞ g(x / s) ds`, the one-homogeneous function generated by `g`. -/
def homogenize (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ s in Ioi (0 : ℝ), g (s⁻¹ • x)

lemma isOneHomogeneous_homogenize (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    IsOneHomogeneous (homogenize g) := by
  intro x t ht
  have h := integral_comp_mul_left_Ioi (fun s => g (s⁻¹ • (t • x))) 0 ht
  rw [mul_zero, smul_eq_mul] at h
  have h2 : ∫ u in Ioi (0 : ℝ), g ((t * u)⁻¹ • (t • x)) = homogenize g x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    rw [smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
  rw [h2] at h
  change ∫ s in Ioi (0 : ℝ), g (s⁻¹ • (t • x)) = t * homogenize g x
  rw [h, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

lemma exists_ne_zero_of_homogenize_ne_zero {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : homogenize g x ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ g (s⁻¹ • x) ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  unfold homogenize
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ)) fun s hs => h s hs]
  simp

namespace IsAnnularTest

variable {g : EuclideanSpace ℝ (Fin n) → ℝ} {r R : ℝ} (hg : IsAnnularTest g r R)
include hg

lemma mem_of_ne_zero {y : EuclideanSpace ℝ (Fin n)} (hy : g y ≠ 0) : r ≤ ‖y‖ ∧ ‖y‖ ≤ R :=
  hg.mem_tsupport y (subset_tsupport g hy)

lemma mem_of_fderiv_ne_zero {y : EuclideanSpace ℝ (Fin n)} (hy : fderiv ℝ g y ≠ 0) :
    r ≤ ‖y‖ ∧ ‖y‖ ≤ R :=
  hg.mem_tsupport y (support_fderiv_subset ℝ hy)

omit hg in
lemma mem_Icc_of_mem {x : EuclideanSpace ℝ (Fin n)} {s r R : ℝ} (hs : 0 < s)
    (h : r ≤ ‖s⁻¹ • x‖ ∧ ‖s⁻¹ • x‖ ≤ R) (hr : 0 < r) :
    ‖x‖ / R ≤ s ∧ s ≤ ‖x‖ / r := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)] at h
  have hR : 0 < R := hr.trans_le (h.1.trans h.2)
  constructor
  · rw [div_le_iff₀ hR]
    have := h.2
    rw [inv_mul_le_iff₀ hs] at this
    linarith
  · rw [le_div_iff₀ hr]
    have := h.1
    rw [le_inv_mul_iff₀ hs] at this
    linarith

lemma exists_lipschitzWith : ∃ K, LipschitzWith K g :=
  hg.contDiff.lipschitzWith_of_hasCompactSupport hg.hasCompactSupport one_ne_zero

lemma exists_bound : ∃ C, ∀ y, |g y| ≤ C := by
  obtain ⟨C, hC⟩ := hg.contDiff.continuous.bounded_above_of_compact_support hg.hasCompactSupport
  exact ⟨C, fun y => by simpa using hC y⟩

/-- The integrand `s ↦ g(x/s)` is integrable on `(0, ∞)`. -/
lemma integrableOn (x : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun s : ℝ => g (s⁻¹ • x)) (Ioi 0) := by
  obtain ⟨C, hC⟩ := hg.exists_bound
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hi : IntegrableOn ((Icc (‖x‖ / R) (‖x‖ / r)).indicator fun _ => C) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const measure_Icc_lt_top.ne)).integrableOn
  refine hi.mono' ((hg.contDiff.continuous.measurable.comp
    (by fun_prop : Measurable fun s : ℝ => s⁻¹ • x)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine ae_of_all _ fun s (hs : 0 < s) => ?_
  rw [Real.norm_eq_abs]
  by_cases h : g (s⁻¹ • x) = 0
  · rw [h, abs_zero]; exact indicator_nonneg (fun _ _ => hC0) s
  · rw [indicator_of_mem (show s ∈ Icc (‖x‖ / R) (‖x‖ / r) from
      mem_Icc_of_mem hs (hg.mem_of_ne_zero h) hg.pos)]
    exact hC _

/-- **Differentiation under the integral sign**: away from the origin,
`Dψ(x) = ∫₀^∞ s⁻¹ Dg(x/s) ds`. -/
lemma hasFDerivAt_homogenize {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ≠ 0) :
    HasFDerivAt (homogenize g) (∫ s in Ioi (0 : ℝ), s⁻¹ • fderiv ℝ g (s⁻¹ • x₀)) x₀ ∧
      IntegrableOn (fun s : ℝ => s⁻¹ • fderiv ℝ g (s⁻¹ • x₀)) (Ioi 0) := by
  obtain ⟨K, hK⟩ := hg.exists_lipschitzWith
  have hr := hg.pos
  have hR : 0 < R := hr.trans_le hg.le
  have hn0 : 0 < ‖x₀‖ := norm_pos_iff.2 hx₀
  set a := ‖x₀‖ / (2 * R)
  set b := 3 * ‖x₀‖ / (2 * r)
  set bound : ℝ → ℝ := (Icc a b).indicator fun _ => (K : ℝ) * (2 * R / ‖x₀‖) with hbound
  have hbi : IntegrableOn bound (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const measure_Icc_lt_top.ne)).integrableOn
  have hgd : Differentiable ℝ g := hg.contDiff.differentiable one_ne_zero
  have hdiff : ∀ (s : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      HasFDerivAt (fun x => g (s⁻¹ • x)) (s⁻¹ • fderiv ℝ g (s⁻¹ • x)) x := by
    intro s x
    have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => s⁻¹ • x)
        (s⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x :=
      (hasFDerivAt_id x).const_smul s⁻¹
    have := (hgd (s⁻¹ • x)).hasFDerivAt.comp x h1
    convert this using 1
    ext v
    simp
  have hmeas' : ∀ x : EuclideanSpace ℝ (Fin n), AEStronglyMeasurable
      (fun s : ℝ => s⁻¹ • fderiv ℝ g (s⁻¹ • x)) (volume.restrict (Ioi 0)) := fun x =>
    (measurable_inv.smul ((hg.contDiff.continuous_fderiv one_ne_zero).measurable.comp
      (by fun_prop : Measurable fun s : ℝ => s⁻¹ • x))).aestronglyMeasurable
  have hbd : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ ball x₀ (‖x₀‖ / 2),
      ‖s⁻¹ • fderiv ℝ g (s⁻¹ • x)‖ ≤ bound s := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun s (hs : 0 < s) x hx => ?_
    have hK0 : 0 ≤ (K : ℝ) * (2 * R / ‖x₀‖) := by positivity
    by_cases h : fderiv ℝ g (s⁻¹ • x) = 0
    · rw [h, smul_zero, norm_zero]; exact indicator_nonneg (fun _ _ => hK0) s
    · have hm := hg.mem_of_fderiv_ne_zero h
      have hI := mem_Icc_of_mem hs hm hr
      rw [mem_ball, dist_eq_norm] at hx
      have hx1 : ‖x₀‖ / 2 ≤ ‖x‖ := by
        have := norm_sub_norm_le x₀ x
        rw [norm_sub_rev] at this; linarith
      have hx2 : ‖x‖ ≤ 3 * ‖x₀‖ / 2 := by
        have := norm_le_norm_add_norm_sub' x x₀
        linarith
      have hmem : s ∈ Icc a b := by
        constructor
        · calc a = (‖x₀‖ / 2) / R := by simp only [a]; field_simp
            _ ≤ ‖x‖ / R := by gcongr
            _ ≤ s := hI.1
        · calc s ≤ ‖x‖ / r := hI.2
            _ ≤ (3 * ‖x₀‖ / 2) / r := by gcongr
            _ = b := by simp only [b]; field_simp
      rw [hbound, indicator_of_mem hmem, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      have hs' : s⁻¹ ≤ 2 * R / ‖x₀‖ := by
        rw [inv_le_comm₀ hs (by positivity)]
        calc (2 * R / ‖x₀‖)⁻¹ = a := by simp only [a]; field_simp
          _ ≤ s := hmem.1
      calc s⁻¹ * ‖fderiv ℝ g (s⁻¹ • x)‖ ≤ (2 * R / ‖x₀‖) * K := by
            gcongr; exact norm_fderiv_le_of_lipschitz ℝ hK
        _ = _ := by ring
  have hint' : IntegrableOn (fun s : ℝ => s⁻¹ • fderiv ℝ g (s⁻¹ • x₀)) (Ioi 0) := by
    refine hbi.mono' (hmeas' x₀) ?_
    filter_upwards [hbd] with s hs
    exact hs x₀ (mem_ball_self (by positivity))
  refine ⟨?_, hint'⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x₀ (by positivity))
    (Eventually.of_forall fun x => (hg.integrableOn x).aestronglyMeasurable)
    (hg.integrableOn x₀) (hmeas' x₀) hbd hbi
    (ae_of_all _ fun s x _ => hdiff s x)

lemma fderiv_homogenize_apply {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (homogenize g) x v = ∫ s in Ioi (0 : ℝ), s⁻¹ * fderiv ℝ g (s⁻¹ • x) v := by
  obtain ⟨hd, hi⟩ := hg.hasFDerivAt_homogenize hx
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  simp

lemma norm_fderiv_homogenize_le {K : ℝ≥0} (hK : LipschitzWith K g)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖fderiv ℝ (homogenize g) x‖ ≤ K * (R / r) := by
  have hr := hg.pos
  have hR : 0 < R := hr.trans_le hg.le
  have hn0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨hd, hi⟩ := hg.hasFDerivAt_homogenize hx
  rw [hd.fderiv]
  set a := ‖x‖ / R
  set b := ‖x‖ / r
  have hab : a ≤ b := div_le_div_of_nonneg_left hn0.le hr hg.le
  have hsub : Icc a b ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le (by positivity) hs.1
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi hsub ?_]
  · refine (norm_setIntegral_le_of_norm_le_const (C := K * (R / ‖x‖)) measure_Icc_lt_top
      fun s hs => ?_).trans ?_
    · have hs0 : 0 < s := hsub hs
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le)]
      have h1 : s⁻¹ ≤ R / ‖x‖ := by
        rw [inv_le_comm₀ hs0 (by positivity), inv_div]; exact hs.1
      calc s⁻¹ * ‖fderiv ℝ g (s⁻¹ • x)‖ ≤ (R / ‖x‖) * K := by
            gcongr; exact norm_fderiv_le_of_lipschitz ℝ hK
        _ = _ := by ring
    · rw [Real.volume_real_Icc_of_le hab]
      have h0 : 0 ≤ ‖x‖ / R := by positivity
      have : b - a ≤ ‖x‖ / r := by simp only [a, b]; linarith
      calc K * (R / ‖x‖) * (b - a) ≤ K * (R / ‖x‖) * (‖x‖ / r) := by gcongr
        _ = K * (R / r) := by field_simp
  · intro s ⟨hs0, hs⟩
    by_contra h
    have h' : fderiv ℝ g (s⁻¹ • x) ≠ 0 := fun h0 => h (by rw [h0, smul_zero])
    exact hs (mem_Icc_of_mem hs0 (hg.mem_of_fderiv_ne_zero h') hr)

/-- The generated one-homogeneous function is Lipschitz. -/
lemma lipschitzWith_homogenize {K : ℝ≥0} (hK : LipschitzWith K g) :
    LipschitzWith (K * (R / r).toNNReal) (homogenize g) := by
  have hr := hg.pos
  have hR : 0 < R := hr.trans_le hg.le
  set C : ℝ := K * (R / r)
  have hCK : ((K * (R / r).toNNReal : ℝ≥0) : ℝ) = C := by
    simp [C, Real.coe_toNNReal _ (div_pos hR hr).le]
  have hhom := isOneHomogeneous_homogenize g
  have habs : ∀ x, |homogenize g x| ≤ C * ‖x‖ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [hhom.map_zero]
    · have hd := (hg.hasFDerivAt_homogenize hx).1.differentiableAt
      rw [← hhom.fderiv_apply_self hd]
      exact ((fderiv ℝ (homogenize g) x).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hg.norm_fderiv_homogenize_le hK hx) (norm_nonneg x))
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [hCK, Real.dist_eq]
  by_cases h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ segment ℝ x y
  · have := dist_add_dist_of_mem_segment h0
    rw [dist_zero_right, dist_zero_left] at this
    rw [← this]
    calc |homogenize g x - homogenize g y| ≤ |homogenize g x| + |homogenize g y| :=
          abs_sub _ _
      _ ≤ C * ‖x‖ + C * ‖y‖ := add_le_add (habs x) (habs y)
      _ = C * (‖x‖ + ‖y‖) := by ring
  · have hne : ∀ z ∈ segment ℝ x y, z ≠ 0 := fun z hz h => h0 (h ▸ hz)
    have := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hg.hasFDerivAt_homogenize (hne z hz)).1.differentiableAt)
      (fun z hz => hg.norm_fderiv_homogenize_le hK (hne z hz))
      (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)
    rw [← Real.norm_eq_abs, dist_eq_norm]
    exact this

omit hg in
lemma ae_ne_zero (hn : 1 ≤ n) : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ≠ 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [ae_iff]
  simp only [ne_eq, not_not, setOf_eq_eq_singleton]
  exact measure_singleton 0

/-- **The first variation in the direction of `homogenize g`**, computed by Fubini in scaling
coordinates: `B(w, ψ) = ∫ ⟨∇g, ∇w⟩ c_{n-1}/|y|ⁿ - ∫ w g c_{n+1}/|y|^{n+2}`. -/
theorem gaussBilin_homogenize (hn : 1 ≤ n) {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (hhom : IsOneHomogeneous w) :
    gaussBilin w (homogenize g) =
      (∫ y, fderiv ℝ g y (∇ w y) * (radialMoment (n - 1) / ‖y‖ ^ n)) -
        ∫ y, w y * g y * (radialMoment (n + 1) / ‖y‖ ^ (n + 2)) := by
  obtain ⟨K, hK⟩ := hg.exists_lipschitzWith
  obtain ⟨Cg, hCg⟩ := hg.exists_bound
  have hr := hg.pos
  have hR : 0 ≤ R := hr.le.trans hg.le
  unfold gaussBilin
  rw [integral_gaussMeasure, integral_gaussMeasure]
  congr 1
  · set Φ₁ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fderiv ℝ g y (∇ w y) with hΦ₁
    have hA := integral_gaussWeight_mul_integral_scale (Φ := Φ₁) (h := fun _ => (1 : ℝ))
      (measurable_fderiv_apply_gradient g w) (C := K * L) hr
      (fun y => by
        simp only [hΦ₁]
        refine (le_of_eq (Real.norm_eq_abs _).symm).trans
          (((fderiv ℝ g y).le_opNorm _).trans ?_)
        rw [norm_gradient]
        exact mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hK) (norm_fderiv_le_of_lipschitz ℝ hw)
          (norm_nonneg _) K.2)
      (fun y hy => hg.mem_of_fderiv_ne_zero fun h => hy (by simp only [hΦ₁, h,
        ContinuousLinearMap.zero_apply]))
      hR measurable_const (j := 0) (M := 1) zero_le_one (fun y => by simp)
      (fun y t ht => by simp) (m := 1) (by omega)
    simp only [add_zero, one_mul, mul_one, pow_one, Nat.sub_add_cancel hn] at hA
    rw [← hA]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero hn] with x hx
    congr 1
    rw [← inner_gradient_right w x, real_inner_comm, inner_gradient_right,
      hg.fderiv_homogenize_apply hx]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
    simp only [hΦ₁, hhom.gradient_smul (inv_pos.2 hs)]
  · have hB := integral_gaussWeight_mul_integral_scale (Φ := g) (h := w)
      hg.contDiff.continuous.measurable hr (fun y => hCg y) (fun y hy => hg.mem_of_ne_zero hy)
      hR hw.continuous.measurable (j := 1) (M := L) L.2
      (fun y => by rw [pow_one]; exact abs_le_mul_norm_of_lipschitzWith hw hhom.map_zero y)
      (fun y t ht => by rw [pow_one]; exact hhom y t ht) (m := 0) (by omega)
    simp only [pow_zero, inv_one, one_mul, Nat.sub_zero] at hB
    rw [← hB]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [homogenize]
    ring

end IsAnnularTest

/-! ### Weak harmonicity of minimizers -/

lemma integrable_mul_div_pow {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {A r R : ℝ} (hr : 0 < r) (hA : ∀ y, |f y| ≤ A) (hs : ∀ y, f y ≠ 0 → r ≤ ‖y‖ ∧ ‖y‖ ≤ R)
    {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : Integrable fun y => f y * (c / ‖y‖ ^ k) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  refine integrable_of_abs_le_of_norm_le
    (hf.mul (measurable_const.div (continuous_norm.measurable.pow_const k)))
    (K := A * (c / r ^ k)) (R := R) (fun y => ?_) (fun y hy => (hs y (left_ne_zero_of_mul hy)).2)
  by_cases hy : f y = 0
  · rw [hy, zero_mul, abs_zero]; positivity
  · have h1 := (hs y hy).1
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c / ‖y‖ ^ k)]
    refine mul_le_mul (hA y) ?_ (by positivity) hA0
    exact div_le_div_of_nonneg_left hc (by positivity) (pow_le_pow_left₀ hr.le h1 k)

/-- A compact set avoiding the origin lies in a closed annulus. -/
lemma exists_annulus {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsCompact s) (h0 : (0 : _) ∉ s) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ R ∧ ∀ y ∈ s, r ≤ ‖y‖ ∧ ‖y‖ ≤ R := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs.isClosed.isOpen_compl 0 h0
  obtain ⟨R₀, hR₀⟩ := hs.isBounded.subset_closedBall 0
  refine ⟨ε, max R₀ ε, hε, le_max_right _ _, fun y hy => ⟨?_, ?_⟩⟩
  · by_contra h
    push Not at h
    exact hball (by rwa [mem_ball, dist_zero_right]) hy
  · have := hR₀ hy
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)

lemma isAnnularTest_normPow_mul {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hmem : ∀ y ∈ tsupport ζ, r ≤ ‖y‖ ∧ ‖y‖ ≤ R) :
    IsAnnularTest (fun y => ‖y‖ ^ n * ζ y) r R := by
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport ζ := fun h => by
    have := (hmem 0 h).1; rw [norm_zero] at this; linarith
  refine ⟨?_, hζc.mul_left, hr, hrR, fun y hy => hmem y (tsupport_mul_subset_right hy)⟩
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y ∈ tsupport ζ
  · have hy0 : y ≠ 0 := fun h => h0 (h ▸ hy)
    exact ((contDiffAt_norm ℝ hy0).pow n).mul (hζ.contDiffAt.of_le (by norm_cast))
  · have := (notMem_tsupport_iff_eventuallyEq.1 hy)
    refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [this] with z hz
    simp only [Pi.zero_apply] at hz
    simp [hz]

/-- The pointwise identity behind `B(w, ψ) = c ∫ ⟨∇w, ∇ζ⟩`: the two correction terms cancel by
Euler's identity and `c_{n+1} = n c_{n-1}`. -/
lemma fderiv_normPow_mul_sub (hn : 1 ≤ n) {ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport ζ)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hhom : IsOneHomogeneous w) {y : EuclideanSpace ℝ (Fin n)}
    (hwd : DifferentiableAt ℝ w y) :
    fderiv ℝ (fun y => ‖y‖ ^ n * ζ y) y (∇ w y) * (radialMoment (n - 1) / ‖y‖ ^ n) -
        w y * (‖y‖ ^ n * ζ y) * (radialMoment (n + 1) / ‖y‖ ^ (n + 2)) =
      radialMoment (n - 1) * fderiv ℝ ζ y (∇ w y) := by
  by_cases hy : y ∈ tsupport ζ
  · have hy0 : y ≠ 0 := fun h => h0 (h ▸ hy)
    have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hd := ((hasFDerivAt_norm_of_ne_zero hy0).pow n).mul
      ((hζ.differentiable (by simp)) y).hasFDerivAt
    have hfd : fderiv ℝ (fun y => ‖y‖ ^ n * ζ y) y (∇ w y) =
        ‖y‖ ^ n * fderiv ℝ ζ y (∇ w y) + ζ y * ((n * ‖y‖ ^ (n - 1)) * (‖y‖⁻¹ * w y)) := by
      rw [show (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ n * ζ y) =
        (fun y => ‖y‖ ^ n) * ζ from rfl, hd.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
      rw [inner_gradient_right, hhom.fderiv_apply_self hwd]
    have hc : radialMoment (n + 1) = n * radialMoment (n - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [show k + 1 + 1 = k + 2 by ring, radialMoment_add_two]
      simp
    rw [hfd, hc]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    push_cast
    ring
  · have hev := notMem_tsupport_iff_eventuallyEq.1 hy
    have hζy : ζ y = 0 := hev.eq_of_nhds
    have hDζ : fderiv ℝ ζ y = 0 := by rw [hev.fderiv_eq]; exact fderiv_const_apply 0
    have hg : (fun y => ‖y‖ ^ n * ζ y) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hev] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
    rw [hg.fderiv_eq, hζy, hDζ]
    simp

/-- Integration by parts `∫ ⟨∇ζ, ∇w⟩ = -∫ w Δζ` for Lipschitz `w` and a test function `ζ`. -/
lemma integral_fderiv_apply_gradient_eq_neg {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) :
    ∫ y, fderiv ℝ ζ y (∇ w y) = -∫ y, w y * Δ ζ y := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hΨs : ∀ i, ContDiff ℝ ∞ (fun y => fderiv ℝ ζ y (b i)) := fun i =>
    (hζ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hΨ : ∀ i, ContDiff ℝ 1 (fun y => fderiv ℝ ζ y (b i)) ∧
      HasCompactSupport (fun y => fderiv ℝ ζ y (b i)) := fun i =>
    ⟨(hΨs i).of_le (by simp),
      hζc.mono' ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ (b i)))⟩
  have hpt : ∀ y, fderiv ℝ ζ y (∇ w y) = ∑ i, fderiv ℝ w y (b i) * fderiv ℝ ζ y (b i) := by
    intro y
    rw [clm_apply_eq_sum_inner b (fderiv ℝ ζ y) (∇ w y)]
    simp only [inner_gradient_right]
  have hint : ∀ i, Integrable fun y => fderiv ℝ w y (b i) * fderiv ℝ ζ y (b i) := by
    intro i
    obtain ⟨C, hC⟩ := (hΨ i).1.continuous.bounded_above_of_compact_support (hΨ i).2
    refine ((((hΨ i).1.continuous.integrable_of_hasCompactSupport (hΨ i).2).norm).const_mul
      (L * ‖b i‖)).mono' ((measurable_fderiv_apply_const ℝ w (b i)).mul
        ((hΨ i).1.continuous.measurable)).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [norm_mul]
    gcongr
    exact ((fderiv ℝ w y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hw) (norm_nonneg _))
  have hΔ := Vendor.Analysis.laplacian_eq_sum_fderiv_fderiv b (hζ.of_le (by norm_cast))
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => hint i]
  have hibp : ∀ i, ∫ y, fderiv ℝ w y (b i) * fderiv ℝ ζ y (b i) =
      -∫ y, w y * fderiv ℝ (fun y => fderiv ℝ ζ y (b i)) y (b i) := fun i =>
    integral_fderiv_mul_eq_neg_of_hasCompactSupport hw (b i) (hΨ i).1 (hΨ i).2
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum]
  · congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hΔ, Finset.mul_sum]
  · intro i _
    have hc : Continuous fun y => fderiv ℝ (fun y => fderiv ℝ ζ y (b i)) y (b i) :=
      ((hΨs i).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hw.continuous.mul hc).integrable_of_hasCompactSupport
      ((hΨ i).2.mono' ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ (b i)))).mul_left

/-- **Minimizers are weakly harmonic** on their positivity sets: `∫ w Δζ = 0` for every test
function `ζ` supported in `{w > 0}`. -/
theorem integral_mul_laplacian_eq_zero_of_minimizer (hn : 2 ≤ n)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (hnn : ∀ x, 0 ≤ w x) (hhom : IsOneHomogeneous w)
    (hmin : dirichletEnergy w ≤ gaussL2 w)
    (hhalf : 2 * gaussMeasure n {x | 0 < w x} ≤ gaussMeasure n univ)
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hζU : tsupport ζ ⊆ {x | 0 < w x}) :
    ∫ x, w x * Δ ζ x = 0 := by
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport ζ := fun h => by
    have := hζU h; simp [hhom.map_zero] at this
  obtain ⟨r, R, hr, hrR, hmem⟩ := exists_annulus hζc.isCompact h0
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ‖y‖ ^ n * ζ y with hgdef
  have hg : IsAnnularTest g r R := isAnnularTest_normPow_mul hζ hζc hr hrR hmem
  obtain ⟨K, hK⟩ := hg.exists_lipschitzWith
  obtain ⟨Cg, hCg⟩ := hg.exists_bound
  -- the first variation vanishes
  have hsupp : ∀ x, homogenize g x ≠ 0 → 0 < w x := by
    intro x hx
    obtain ⟨s, hs, hgs⟩ := exists_ne_zero_of_homogenize_ne_zero hx
    have hζs : ζ (s⁻¹ • x) ≠ 0 := fun h => hgs (by simp [hgdef, h])
    have hpos : 0 < w (s⁻¹ • x) := hζU (subset_tsupport ζ hζs)
    have : w x = s * w (s⁻¹ • x) := by
      rw [← hhom _ s hs, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    rw [this]; exact mul_pos hs hpos
  have hB := gaussBilin_eq_zero hn hw hnn hhom hmin hhalf (hg.lipschitzWith_homogenize hK)
    (isOneHomogeneous_homogenize g) hsupp
  rw [hg.gaussBilin_homogenize (by omega) hw hhom] at hB
  -- integrability of the two terms
  have hc1 := (radialMoment_pos (n - 1)).le
  have hc2 := (radialMoment_pos (n + 1)).le
  have hi1 : Integrable fun y => fderiv ℝ g y (∇ w y) * (radialMoment (n - 1) / ‖y‖ ^ n) :=
    integrable_mul_div_pow (measurable_fderiv_apply_gradient g w) hr (A := K * L)
      (fun y => by
        refine (le_of_eq (Real.norm_eq_abs _).symm).trans
          (((fderiv ℝ g y).le_opNorm _).trans ?_)
        rw [norm_gradient]
        exact mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hK) (norm_fderiv_le_of_lipschitz ℝ hw)
          (norm_nonneg _) K.2)
      (fun y hy => hg.mem_of_fderiv_ne_zero fun h => hy (by simp [h])) hc1 n
  have hi2 : Integrable fun y => w y * g y * (radialMoment (n + 1) / ‖y‖ ^ (n + 2)) :=
    integrable_mul_div_pow (f := fun y => w y * g y)
      (hw.continuous.mul hg.contDiff.continuous).measurable hr
      (A := L * R * Cg)
      (fun y => by
        have hCg0 := (abs_nonneg _).trans (hCg 0)
        have hR0 : 0 ≤ R := hr.le.trans hrR
        beta_reduce
        by_cases hy : g y = 0
        · rw [hy, mul_zero, abs_zero]
          positivity
        · rw [abs_mul]
          have hyR := (hg.mem_of_ne_zero hy).2
          have h1 : |w y| ≤ L * R := (abs_le_mul_norm_of_lipschitzWith hw hhom.map_zero y).trans
            (mul_le_mul_of_nonneg_left hyR L.2)
          exact mul_le_mul h1 (hCg y) (abs_nonneg _) (mul_nonneg L.2 hR0))
      (fun y hy => hg.mem_of_ne_zero (right_ne_zero_of_mul hy)) hc2 (n + 2)
  rw [← integral_sub hi1 hi2] at hB
  have hae : (fun y => fderiv ℝ g y (∇ w y) * (radialMoment (n - 1) / ‖y‖ ^ n) -
      w y * g y * (radialMoment (n + 1) / ‖y‖ ^ (n + 2))) =ᵐ[volume]
      fun y => radialMoment (n - 1) * fderiv ℝ ζ y (∇ w y) := by
    filter_upwards [hw.ae_differentiableAt] with y hy
    exact fderiv_normPow_mul_sub (by omega) hζ h0 hhom hy
  rw [integral_congr_ae hae, integral_const_mul,
    integral_fderiv_apply_gradient_eq_neg hw hζ hζc] at hB
  have hpos := radialMoment_pos (n - 1)
  have := (mul_eq_zero.1 hB).resolve_left hpos.ne'
  linarith

/-- **Minimizers are harmonic** on their positivity sets (Weyl's lemma). -/
theorem harmonicAt_of_minimizer (hn : 2 ≤ n)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (hnn : ∀ x, 0 ≤ w x) (hhom : IsOneHomogeneous w)
    (hmin : dirichletEnergy w ≤ gaussL2 w)
    (hhalf : 2 * gaussMeasure n {x | 0 < w x} ≤ gaussMeasure n univ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : 0 < w x) : HarmonicAt w x :=
  harmonicAt_of_integral_mul_laplacian_eq_zero (isOpen_lt continuous_const hw.continuous)
    hw.continuous.continuousOn
    (fun _ hζ hζc hζU => integral_mul_laplacian_eq_zero_of_minimizer hn hw hnn hhom hmin hhalf
      hζ hζc hζU) x hx

end Sperner
