/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Polar
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Monotonicity.Lemmas
import GMTFoundations.GMT.Polar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
public import GMTFoundations.Defs.Setup

/-!
# Calculus for sphere integrals

API for `sphereIntegral f x s = s^{n-1} ∫_{S^{n-1}} f(x + s ω) dσ(ω)`: linearity,
positivity, Cauchy–Schwarz, scaling, continuity, and differentiation in the radius.

## Main results

* `sphereIntegral_add`, `sphereIntegral_const_mul`, `sphereIntegral_nonneg`,
  `sphereIntegral_mono`, `sq_sphereIntegral_mul_le`: linearity, positivity, Cauchy–Schwarz.
* `sphereIntegral_comp_add_smul`, `setIntegral_ball_comp_add_smul`,
  `gradient_comp_add_smul_div`: scaling and translation.
* `ae_hasDerivAt_integral_ball`, `lipschitzOnWith_integral_ball`,
  `ae_tendsto_average_annulus`: `d/ds ∫_{B_s(x)} f = ∫_{∂B_s(x)} f` for a.e. `s`.
* `LipschitzOnWith.sub_integral_sphere_sq_eq`,
  `LipschitzOnWith.ae_hasDerivAt_sphereIntegral_sq`: for `u` Lipschitz on `B_R(x)` and
  `P(s) = ∫_{∂B_s(x)} u²`, `P' = ((n-1)/s) P + (2/s) ∫_{∂B_s(x)} u ⟪∇u, y - x⟫` for a.e. `s`.
  `LipschitzOnWith.lipschitzOnWith_sphereIntegral_sq` shows that `P` is Lipschitz on `[0, b]`
  for every `b < R`.
* `continuous_sphereIntegral`, `continuousAt_sphereIntegral`, `continuous_integral_ball`:
  continuity in the centre and radius.

## Dimension

Results that use polar coordinates assume `[NeZero n]`, i.e. `n ≥ 1`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Integrability on a sphere -/

/-- `f` is integrable on the sphere `∂B_s(x)`, i.e. `ω ↦ f (x + s ω)` is `σ`-integrable. -/
def SphereIntegrable (f : Rn n → ℝ) (x : Rn n) (s : ℝ) : Prop :=
  Integrable (fun ω : sphere (0 : Rn n) 1 => f (x + s • (ω : Rn n))) (sphereMeasure n)

theorem add_smul_mem_sphere {x : Rn n} {s : ℝ} (hs : 0 ≤ s) (ω : sphere (0 : Rn n) 1) :
    x + s • (ω : Rn n) ∈ sphere x s := by
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul_sphere hs]

theorem continuous_add_smul_sphere (x : Rn n) (s : ℝ) :
    Continuous fun ω : sphere (0 : Rn n) 1 => x + s • (ω : Rn n) :=
  by fun_prop

theorem _root_.ContinuousOn.sphereIntegrable {f : Rn n → ℝ} {x : Rn n} {s : ℝ} (hs : 0 ≤ s)
    (hf : ContinuousOn f (sphere x s)) : SphereIntegrable f x s := by
  have hc : Continuous fun ω : sphere (0 : Rn n) 1 => f (x + s • (ω : Rn n)) :=
    hf.comp_continuous (continuous_add_smul_sphere x s) (add_smul_mem_sphere hs)
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem _root_.Continuous.sphereIntegrable {f : Rn n → ℝ} (hf : Continuous f) (x : Rn n) (s : ℝ) :
    SphereIntegrable f x s :=
  integrableOn_univ.1 ((hf.comp (continuous_add_smul_sphere x s)).continuousOn.integrableOn_compact
    isCompact_univ)

/-- If `f`, `g` are measurable on the sphere with `f²`, `g²` integrable there, then `f g` is
integrable there. -/
theorem SphereIntegrable.mul_of_sq {f g : Rn n → ℝ} {x : Rn n} {s : ℝ}
    (hfm : AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => f (x + s • (ω : Rn n)))
      (sphereMeasure n))
    (hgm : AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => g (x + s • (ω : Rn n)))
      (sphereMeasure n))
    (hf : SphereIntegrable (fun y => f y ^ 2) x s) (hg : SphereIntegrable (fun y => g y ^ 2) x s) :
    SphereIntegrable (fun y => f y * g y) x s := by
  refine Integrable.mono' ((hf.add hg).div_const 2) (hfm.mul hgm) (.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
  nlinarith [sq_nonneg (|f (x + s • (ω : Rn n))| - |g (x + s • (ω : Rn n))|),
    sq_abs (f (x + s • (ω : Rn n))), sq_abs (g (x + s • (ω : Rn n)))]

/-! ### Linearity and positivity -/

theorem sphereIntegral_congr {f g : Rn n → ℝ} {x : Rn n} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ y ∈ sphere x s, f y = g y) : sphereIntegral f x s = sphereIntegral g x s := by
  rw [sphereIntegral, sphereIntegral]
  congr 1
  exact integral_congr_ae (.of_forall fun ω => h _ (add_smul_mem_sphere hs ω))

theorem sphereIntegral_add {f g : Rn n → ℝ} {x : Rn n} {s : ℝ} (hf : SphereIntegrable f x s)
    (hg : SphereIntegrable g x s) :
    sphereIntegral (fun y => f y + g y) x s = sphereIntegral f x s + sphereIntegral g x s := by
  simp only [sphereIntegral]
  rw [integral_add hf hg, mul_add]

theorem sphereIntegral_sub {f g : Rn n → ℝ} {x : Rn n} {s : ℝ} (hf : SphereIntegrable f x s)
    (hg : SphereIntegrable g x s) :
    sphereIntegral (fun y => f y - g y) x s = sphereIntegral f x s - sphereIntegral g x s := by
  simp only [sphereIntegral]
  rw [integral_sub hf hg, mul_sub]

theorem sphereIntegral_const_mul (c : ℝ) (f : Rn n → ℝ) (x : Rn n) (s : ℝ) :
    sphereIntegral (fun y => c * f y) x s = c * sphereIntegral f x s := by
  simp only [sphereIntegral]
  rw [integral_const_mul]
  ring

theorem sphereIntegral_neg (f : Rn n → ℝ) (x : Rn n) (s : ℝ) :
    sphereIntegral (fun y => -f y) x s = -sphereIntegral f x s := by
  simp only [sphereIntegral]
  rw [integral_neg, mul_neg]

theorem sphereIntegral_nonneg {f : Rn n → ℝ} {x : Rn n} {s : ℝ} (hs : 0 ≤ s)
    (hf : ∀ y ∈ sphere x s, 0 ≤ f y) : 0 ≤ sphereIntegral f x s :=
  mul_nonneg (pow_nonneg hs _)
    (integral_nonneg fun ω => hf _ (add_smul_mem_sphere hs ω))

theorem sphereIntegral_mono {f g : Rn n → ℝ} {x : Rn n} {s : ℝ} (hs : 0 ≤ s)
    (hf : SphereIntegrable f x s) (hg : SphereIntegrable g x s)
    (hfg : ∀ y ∈ sphere x s, f y ≤ g y) : sphereIntegral f x s ≤ sphereIntegral g x s :=
  mul_le_mul_of_nonneg_left
    (integral_mono hf hg fun ω => hfg _ (add_smul_mem_sphere hs ω)) (pow_nonneg hs _)

/-- Cauchy–Schwarz for real integrals, stated with only integrability of `F²`, `G²`, `F G`. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G : α → ℝ}
    (hF : Integrable (fun a => F a ^ 2) μ) (hG : Integrable (fun a => G a ^ 2) μ)
    (hFG : Integrable (fun a => F a * G a) μ) :
    (∫ a, F a * G a ∂μ) ^ 2 ≤ (∫ a, F a ^ 2 ∂μ) * ∫ a, G a ^ 2 ∂μ := by
  have hquad : ∀ t : ℝ, 0 ≤ (∫ a, F a ^ 2 ∂μ) * (t * t) + (2 * ∫ a, F a * G a ∂μ) * t +
      ∫ a, G a ^ 2 ∂μ := by
    intro t
    have h12 : Integrable (fun a => t * t * F a ^ 2 + 2 * t * (F a * G a)) μ :=
      (hF.const_mul (t * t)).add (hFG.const_mul (2 * t))
    have e : ∫ a, (t * F a + G a) ^ 2 ∂μ = (∫ a, F a ^ 2 ∂μ) * (t * t) +
        (2 * ∫ a, F a * G a ∂μ) * t + ∫ a, G a ^ 2 ∂μ := by
      have h1 : ∀ a, (t * F a + G a) ^ 2 = t * t * F a ^ 2 + 2 * t * (F a * G a) + G a ^ 2 :=
        fun a => by ring
      simp_rw [h1]
      rw [integral_add h12 hG, integral_add (hF.const_mul _) (hFG.const_mul _),
        integral_const_mul, integral_const_mul]
      ring
    rw [← e]
    exact integral_nonneg fun a => sq_nonneg _
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith

/-- **Cauchy–Schwarz** for sphere integrals. -/
theorem sq_sphereIntegral_mul_le {f g : Rn n → ℝ} {x : Rn n} {s : ℝ}
    (hf : SphereIntegrable (fun y => f y ^ 2) x s) (hg : SphereIntegrable (fun y => g y ^ 2) x s)
    (hfg : SphereIntegrable (fun y => f y * g y) x s) :
    sphereIntegral (fun y => f y * g y) x s ^ 2 ≤
      sphereIntegral (fun y => f y ^ 2) x s * sphereIntegral (fun y => g y ^ 2) x s := by
  have h := sq_integral_mul_le (F := fun ω : sphere (0 : Rn n) 1 => f (x + s • (ω : Rn n)))
    (G := fun ω : sphere (0 : Rn n) 1 => g (x + s • (ω : Rn n))) hf hg hfg
  simp only [sphereIntegral]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg (s ^ (n - 1)))]

/-! ### Scaling and translation -/

theorem sphereIntegral_comp_add (f : Rn n → ℝ) (x z : Rn n) (s : ℝ) :
    sphereIntegral (fun y => f (x + y)) z s = sphereIntegral f (x + z) s := by
  simp only [sphereIntegral, add_assoc]

/-- Scaling: `r^{n-1} ∫_{∂B_s} f(x + r ·) = ∫_{∂B_{rs}(x)} f`. -/
theorem sphereIntegral_comp_add_smul (f : Rn n → ℝ) (x : Rn n) (r s : ℝ) :
    r ^ (n - 1) * sphereIntegral (fun y => f (x + r • y)) 0 s = sphereIntegral f x (r * s) := by
  simp only [sphereIntegral, zero_add, smul_smul, mul_pow]
  ring

/-- Scaling: `∫_{∂B_s} f(x + r ·) = r^{1-n} ∫_{∂B_{rs}(x)} f`. -/
theorem sphereIntegral_comp_add_smul' (f : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    sphereIntegral (fun y => f (x + r • y)) 0 s = (r ^ (n - 1))⁻¹ * sphereIntegral f x (r * s) := by
  rw [← sphereIntegral_comp_add_smul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr), one_mul]

/-- Scaling of ball integrals: `∫_{B_s(z)} f(x + r ·) = r^{-n} ∫_{B_{rs}(x + r z)} f`. -/
theorem setIntegral_ball_comp_add_smul (f : Rn n → ℝ) (x z : Rn n) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    ∫ y in ball z s, f (x + r • y) = (r ^ n)⁻¹ * ∫ y in ball (x + r • z) (r * s), f y := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  have hiff : ∀ y : Rn n, y ∈ ball z s ↔ x + r • y ∈ ball (x + r • z) (r * s) := by
    intro y
    rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact ⟨fun h => mul_lt_mul_of_pos_left h hr, fun h => lt_of_mul_lt_mul_left h hr.le⟩
  have hH : ∀ y, (ball z s).indicator (fun y => f (x + r • y)) y =
      (ball (x + r • z) (r * s)).indicator f (x + r • y) := by
    intro y
    by_cases hy : y ∈ ball z s
    · rw [indicator_of_mem hy, indicator_of_mem ((hiff y).1 hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy ((hiff y).2 h))]
  simp_rw [hH]
  have h1 := Measure.integral_comp_smul (volume : Measure (Rn n))
    (fun w => (ball (x + r • z) (r * s)).indicator f (x + w)) r
  rw [h1, integral_add_left_eq_self, finrank_Rn, smul_eq_mul,
    abs_of_pos (inv_pos.2 (pow_pos hr n))]

/-- Scaling of gradients: `∇(u(x + r ·) / r)(y) = ∇u(x + r y)`. -/
theorem gradient_comp_add_smul_div (u : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : r ≠ 0) (y : Rn n) :
    gradient (fun z => u (x + r • z) / r) y = gradient u (x + r • y) := by
  simp only [gradient]
  congr 1
  set L : Rn n ≃L[ℝ] Rn n := (LinearEquiv.smulOfNeZero ℝ (Rn n) r hr).toContinuousLinearEquiv
  have hL : ∀ z, L z = r • z := fun z => by simp [L]
  have hφ : (fun z => u (x + r • z) / r) = r⁻¹ • ((fun w => u (x + w)) ∘ L) := by
    ext z
    simp [hL, div_eq_inv_mul]
  rw [hφ, fderiv_const_smul_field, Pi.smul_apply, L.comp_right_fderiv, fderiv_comp_add_left, hL]
  ext v
  simp [hL, hr]

/-! ### Derivative of ball integrals in the radius -/

/-- For `f` integrable on `B_R(x)`, `d/ds ∫_{B_s(x)} f = ∫_{∂B_s(x)} f` for a.e. `s ∈ (0, R)`. -/
theorem ae_hasDerivAt_integral_ball [NeZero n] {f : Rn n → ℝ} {x : Rn n} {R : ℝ}
    (hf : IntegrableOn f (ball x R)) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      HasDerivAt (fun s => ∫ y in ball x s, f y) (sphereIntegral f x s) s := by
  rcases le_or_gt R 0 with hR | hR
  · exact .of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.2 hR)
  have hint := intervalIntegrable_sphereIntegral hR.le hf
  filter_upwards [hint.ae_hasDerivAt_integral] with s hs hsR
  have hsI : s ∈ uIcc 0 R := by rw [uIcc_of_le hR.le]; exact Ioo_subset_Icc_self hsR
  refine (hs hsI 0 left_mem_uIcc).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hsR.1 hsR.2] with t ht
  exact integral_ball_eq ht.1.le (hf.mono_set (ball_subset_ball ht.2.le))

/-- For `|f| ≤ M` on `B_R(x)`, `s ↦ ∫_{B_s(x)} f` is `n |B_1| R^{n-1} M`-Lipschitz on `[0, R]`. -/
theorem lipschitzOnWith_integral_ball [NeZero n] {f : Rn n → ℝ} {x : Rn n} {R M : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (ball x R)))
    (hM : ∀ y ∈ ball x R, |f y| ≤ M) :
    LipschitzOnWith (Real.toNNReal (n * unitBallVolume n * R ^ (n - 1) * M))
      (fun s => ∫ y in ball x s, f y) (Icc 0 R) := by
  have hf : IntegrableOn f (ball x R) :=
    IntegrableOn.of_bound measure_ball_lt_top hfm M
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact hM y hy))
  set K := n * unitBallVolume n * R ^ (n - 1) * M
  have key : ∀ a ∈ Icc 0 R, ∀ b ∈ Icc 0 R, a ≤ b →
      |(∫ y in ball x b, f y) - ∫ y in ball x a, f y| ≤ K * (b - a) := by
    intro a ha b hb hab
    have hfb := hf.mono_set (ball_subset_ball hb.2)
    rw [← setIntegral_sdiff measurableSet_ball hfb (ball_subset_ball hab),
      integral_ball_diff_ball ha.1 hab hfb, ← Real.norm_eq_abs,
      ← abs_of_nonneg (sub_nonneg.2 hab)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := R))] with t htR ht
    rw [uIoc_of_le hab] at ht
    have ht0 : 0 ≤ t := ha.1.trans ht.1.le
    have htR' : t < R := lt_of_le_of_ne (ht.2.trans hb.2) htR
    rw [sphereIntegral, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
    have h1 : |∫ ω, f (x + t • (ω : Rn n)) ∂sphereMeasure n| ≤ M * (sphereMeasure n).real univ := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le_const (.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      exact hM _ ((add_smul_mem_ball_iff ht0 ω).2 htR')
    have h2 : t ^ (n - 1) ≤ R ^ (n - 1) := pow_le_pow_left₀ ht0 htR'.le _
    rw [sphereMeasure_real_univ] at h1
    have hM0 : 0 ≤ M * (n * unitBallVolume n) := (abs_nonneg _).trans h1
    calc t ^ (n - 1) * |∫ ω, f (x + t • (ω : Rn n)) ∂sphereMeasure n|
        ≤ R ^ (n - 1) * (M * (n * unitBallVolume n)) :=
          mul_le_mul h2 h1 (abs_nonneg _) ((pow_nonneg ht0 _).trans h2)
      _ = K := by ring
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Real.dist_eq, Real.dist_eq]
  have hK : K ≤ (Real.toNNReal K : ℝ) := Real.le_coe_toNNReal K
  rcases le_total a b with hab | hab
  · rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.2 hab)]
    calc _ ≤ K * (b - a) := key a ha b hb hab
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (by linarith)
      _ = _ := by ring
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]
    calc _ ≤ K * (a - b) := key b hb a ha hab
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (by linarith)

/-- For `f` integrable on `B_R(x)` and a.e. `s ∈ (0, R)`,
`k ∫_{B_{s + 1/k}(x) ∖ B_s(x)} f → ∫_{∂B_s(x)} f`. -/
theorem ae_tendsto_average_annulus [NeZero n] {f : Rn n → ℝ} {x : Rn n} {R : ℝ}
    (hf : IntegrableOn f (ball x R)) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      Tendsto (fun k : ℕ => (k : ℝ) * ∫ y in ball x (s + 1 / k) \ ball x s, f y) atTop
        (𝓝 (sphereIntegral f x s)) := by
  filter_upwards [ae_hasDerivAt_integral_ball hf] with s hs hsR
  have hd := (hs hsR).tendsto_slope_zero_right
  have hk : Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_atTop_nhds_zero_nat,
      (eventually_ge_atTop 1).mono fun k hk => by
        simp only [mem_Ioi, one_div, inv_pos, Nat.cast_pos]; omega⟩
  refine (hd.comp hk).congr' ?_
  have hsmall : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / k < R - s :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds (sub_pos.2 hsR.2))
  filter_upwards [hsmall, eventually_ge_atTop 1] with k hk hk1
  have hk0 : (0 : ℝ) < 1 / k := by
    simp only [one_div, inv_pos, Nat.cast_pos]; omega
  simp only [Function.comp_apply, smul_eq_mul, one_div, inv_inv]
  rw [setIntegral_sdiff measurableSet_ball
    (hf.mono_set (ball_subset_ball (by rw [one_div] at hk; linarith)))
    (ball_subset_ball (by rw [one_div] at hk0; linarith))]

/-! ### Continuity in the centre and the radius -/

/-- For `f` continuous, `(x, s) ↦ ∫_{∂B_s(x)} f` is continuous. -/
theorem continuous_sphereIntegral {f : Rn n → ℝ} (hf : Continuous f) :
    Continuous fun p : Rn n × ℝ => sphereIntegral f p.1 p.2 := by
  simp only [sphereIntegral]
  refine (continuous_snd.pow _).mul ?_
  have h := continuous_parametric_integral_of_continuous (μ := sphereMeasure n)
    (f := fun (p : Rn n × ℝ) (ω : sphere (0 : Rn n) 1) => f (p.1 + p.2 • (ω : Rn n)))
    (hf.comp ((continuous_fst.comp continuous_fst).add
      ((continuous_snd.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd))))
    isCompact_univ
  simpa only [Measure.restrict_univ] using h

/-- For `f` continuous on an open set `U ⊇ closedBall x |s|`, `(y, t) ↦ ∫_{∂B_t(y)} f` is
continuous at `(x, s)`. -/
theorem continuousAt_sphereIntegral {f : Rn n → ℝ} {U : Set (Rn n)} (hU : IsOpen U)
    (hf : ContinuousOn f U) {x : Rn n} {s : ℝ} (hxs : closedBall x |s| ⊆ U) :
    ContinuousAt (fun p : Rn n × ℝ => sphereIntegral f p.1 p.2) (x, s) := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x |s|).exists_cthickening_subset_open hU hxs
  rw [cthickening_closedBall hδ.le (abs_nonneg s)] at hδU
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (δ + |s|)).exists_bound_of_continuousOn (hf.mono hδU)
  have hnear : ∀ᶠ p : Rn n × ℝ in 𝓝 (x, s), ∀ ω : sphere (0 : Rn n) 1,
      p.1 + p.2 • (ω : Rn n) ∈ closedBall x (δ + |s|) := by
    have h1 : ∀ᶠ p : Rn n × ℝ in 𝓝 (x, s), dist p.1 x < δ / 2 :=
      (continuous_fst.tendsto (x, s)).eventually (ball_mem_nhds x (half_pos hδ))
    have h2 : ∀ᶠ p : Rn n × ℝ in 𝓝 (x, s), dist p.2 s < δ / 2 :=
      (continuous_snd.tendsto (x, s)).eventually (ball_mem_nhds s (half_pos hδ))
    filter_upwards [h1, h2] with p hp1 hp2 ω
    rw [mem_closedBall]
    have h3 : dist (p.1 + p.2 • (ω : Rn n)) x ≤ dist p.1 x + |p.2| := by
      rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
      refine (norm_add_le _ _).trans_eq ?_
      rw [norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_eq_abs]
    have h4 : |p.2| ≤ |s| + dist p.2 s := by
      rw [Real.dist_eq]; linarith [abs_sub_abs_le_abs_sub p.2 s]
    linarith
  simp only [sphereIntegral]
  refine (continuous_snd.pow _).continuousAt.mul ?_
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · filter_upwards [hnear] with p hp
    exact ((hf.mono hδU).comp_continuous (continuous_add_smul_sphere p.1 p.2)
      hp).aestronglyMeasurable
  · filter_upwards [hnear] with p hp
    exact .of_forall fun ω => hM _ (hp ω)
  · refine .of_forall fun ω => ?_
    have hmem : x + s • (ω : Rn n) ∈ U := hxs (mem_closedBall.2 (le_of_eq (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere ω, mul_one,
        Real.norm_eq_abs])))
    have hc : Continuous fun p : Rn n × ℝ => p.1 + p.2 • (ω : Rn n) :=
      continuous_fst.add (continuous_snd.smul continuous_const)
    exact ContinuousAt.comp (g := f) (f := fun p : Rn n × ℝ => p.1 + p.2 • (ω : Rn n))
      (x := (x, s)) (hf.continuousAt (hU.mem_nhds hmem)) hc.continuousAt

/-- For `g` locally integrable, `x ↦ ∫_{B_s(x)} g` is continuous. -/
theorem continuous_integral_ball [NeZero n] {g : Rn n → ℝ} (hg : LocallyIntegrable g) (s : ℝ) :
    Continuous fun x : Rn n => ∫ y in ball x s, g y := by
  rw [continuous_iff_continuousAt]
  intro x₀
  simp_rw [← integral_indicator measurableSet_ball]
  have hnear : ∀ᶠ x in 𝓝 x₀, dist x x₀ < 1 := ball_mem_nhds x₀ one_pos
  refine continuousAt_of_dominated
    (bound := (closedBall x₀ (|s| + 1)).indicator fun y => ‖g y‖) ?_ ?_ ?_ ?_
  · exact .of_forall fun x => hg.aestronglyMeasurable.indicator measurableSet_ball
  · filter_upwards [hnear] with x hx
    refine .of_forall fun y => ?_
    by_cases hy : y ∈ ball x s
    · have hy' : y ∈ closedBall x₀ (|s| + 1) := by
        rw [mem_closedBall]
        rw [mem_ball] at hy
        linarith [dist_triangle y x x₀, le_abs_self s]
      simp only [indicator_of_mem hy, indicator_of_mem hy', le_refl]
    · rw [indicator_of_notMem hy, norm_zero]
      exact indicator_nonneg (fun y _ => norm_nonneg _) y
  · exact IntegrableOn.integrable_indicator (f := fun y => ‖g y‖)
      (hg.integrableOn_isCompact (isCompact_closedBall x₀ (|s| + 1))).norm measurableSet_closedBall
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume x₀ s)]
      with y hy
    rw [mem_sphere] at hy
    rcases lt_or_gt_of_ne hy with h | h
    · have hev : ∀ᶠ x in 𝓝 x₀, y ∈ ball x s :=
        (isOpen_lt (continuous_const.dist continuous_id) continuous_const).mem_nhds h
      exact continuousAt_const.congr (hev.mono fun x hx => (indicator_of_mem hx g).symm)
    · have hev : ∀ᶠ x in 𝓝 x₀, y ∉ ball x s := by
        filter_upwards [(isOpen_lt continuous_const
          (continuous_const.dist continuous_id)).mem_nhds h] with x hx
        rw [mem_ball]
        exact not_lt.2 (le_of_lt hx)
      exact continuousAt_const.congr (hev.mono fun x hx => (indicator_of_notMem hx g).symm)

/-! ### The radial derivative of `∫_{∂B_s(x)} u²` -/

/-- `2 u(x + t ω) ⟪∇u(x + t ω), ω⟫`, the radial derivative of `t ↦ u(x + t ω)²`. -/
def radialSqDeriv (u : Rn n → ℝ) (x : Rn n) (ω : sphere (0 : Rn n) 1) (t : ℝ) : ℝ :=
  2 * u (x + t • (ω : Rn n)) * ⟪gradient u (x + t • (ω : Rn n)), (ω : Rn n)⟫

theorem measurable_gradient (u : Rn n → ℝ) : Measurable (gradient u) :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ u)

theorem lipschitzWith_ray (x : Rn n) (ω : sphere (0 : Rn n) 1) :
    LipschitzWith 1 fun τ : ℝ => x + τ • (ω : Rn n) :=
  LipschitzWith.of_dist_le_mul fun τ₁ τ₂ => by
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, norm_eq_of_mem_sphere ω, mul_one,
      NNReal.coe_one, one_mul, Real.dist_eq, Real.norm_eq_abs]

theorem abs_inner_gradient_le {u : Rn n → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u) (p : Rn n)
    (ω : sphere (0 : Rn n) 1) : |⟪gradient u p, (ω : Rn n)⟫| ≤ C := by
  rw [gradient, InnerProductSpace.toDual_symm_apply, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ u p ω‖ ≤ ‖fderiv ℝ u p‖ * ‖(ω : Rn n)‖ := (fderiv ℝ u p).le_opNorm _
    _ ≤ C * 1 := by
        rw [norm_eq_of_mem_sphere ω]
        exact mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) zero_le_one
    _ = C := mul_one _

theorem abs_apply_add_smul_le {u : Rn n → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u) (x : Rn n)
    {t : ℝ} (ht : 0 ≤ t) (ω : sphere (0 : Rn n) 1) :
    |u (x + t • (ω : Rn n))| ≤ |u x| + C * t := by
  have := hu.dist_le_mul (x + t • (ω : Rn n)) x
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul_sphere ht] at this
  linarith [abs_sub_abs_le_abs_sub (u (x + t • (ω : Rn n))) (u x)]

theorem abs_radialSqDeriv_le {u : Rn n → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u) (x : Rn n)
    {t b : ℝ} (ht : t ∈ Icc 0 b) (ω : sphere (0 : Rn n) 1) :
    |radialSqDeriv u x ω t| ≤ 2 * (|u x| + C * b) * C := by
  have h1 : |u (x + t • (ω : Rn n))| ≤ |u x| + C * b :=
    (abs_apply_add_smul_le hu x ht.1 ω).trans (by gcongr; exact ht.2)
  have hB : 0 ≤ |u x| + C * b :=
    add_nonneg (abs_nonneg _) (mul_nonneg C.2 (ht.1.trans ht.2))
  rw [radialSqDeriv, abs_mul, abs_mul, abs_two]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 zero_le_two) (abs_inner_gradient_le hu _ ω)
    (abs_nonneg _) (mul_nonneg zero_le_two hB)

theorem measurable_uncurry_radialSqDeriv {u : Rn n → ℝ} (hu : Continuous u) (x : Rn n) :
    Measurable (Function.uncurry (radialSqDeriv u x)) := by
  have hp : Continuous fun q : sphere (0 : Rn n) 1 × ℝ => x + q.2 • (q.1 : Rn n) :=
    continuous_const.add (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))
  exact (measurable_const.mul (hu.measurable.comp hp.measurable)).mul
    (((measurable_gradient u).comp hp.measurable).inner
      (measurable_subtype_coe.comp measurable_fst))

/-- **Integrated radial derivative**, globally Lipschitz case: for `0 ≤ a ≤ b`,
`∫_{S} u(x + bω)² - ∫_{S} u(x + aω)² = ∫_a^b ∫_{S} 2 u ∂_r u`. -/
theorem _root_.LipschitzWith.integral_sphere_sq_sub {u : Rn n → ℝ} {C : ℝ≥0} [NeZero n]
    (hu : LipschitzWith C u) (x : Rn n) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => ∫ ω, radialSqDeriv u x ω t ∂sphereMeasure n) volume a b ∧
    ∫ ω, u (x + b • (ω : Rn n)) ^ 2 ∂sphereMeasure n -
        ∫ ω, u (x + a • (ω : Rn n)) ^ 2 ∂sphereMeasure n =
      ∫ t in a..b, ∫ ω, radialSqDeriv u x ω t ∂sphereMeasure n := by
  have hprod : Integrable (Function.uncurry (radialSqDeriv u x))
      ((sphereMeasure n).prod (volume.restrict (Ioc a b))) := by
    refine Integrable.of_bound
      (measurable_uncurry_radialSqDeriv hu.continuous x).aestronglyMeasurable
      (2 * (|u x| + C * b) * C) ?_
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := sphereMeasure n)
      (ν := volume.restrict (Ioc a b))).ae (ae_restrict_mem measurableSet_Ioc)] with q hq
    rw [Real.norm_eq_abs]
    exact abs_radialSqDeriv_le hu x ⟨ha.trans hq.1.le, hq.2⟩ q.1
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hprod.integral_prod_right
  have hray := (hu.lipschitzOnWith (s := ball x (b + 1))).ae_sphere_ae_hasDerivAt
  have hpt : ∀ᵐ (ω : sphere (0 : Rn n) 1) ∂sphereMeasure n,
      u (x + b • (ω : Rn n)) ^ 2 - u (x + a • (ω : Rn n)) ^ 2 =
      ∫ t in a..b, radialSqDeriv u x ω t := by
    filter_upwards [hray] with ω hω
    have hv : LipschitzWith C fun τ : ℝ => u (x + τ • (ω : Rn n)) := by
      have h := hu.comp (lipschitzWith_ray x ω)
      rw [mul_one] at h
      exact h
    have hac := (hv.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
    have key := hac.integral_deriv_mul_eq_sub hac
    rw [sq, sq, ← key]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hω] with t ht htab
    rw [uIoc_of_le hab] at htab
    have htR : t ∈ Ioo 0 (b + 1) := ⟨ha.trans_lt htab.1, by linarith [htab.2]⟩
    rw [(ht htR).2.deriv, radialSqDeriv]
    ring
  have hc2 : Continuous fun y => u y ^ 2 := hu.continuous.pow 2
  rw [← integral_sub (hc2.sphereIntegrable x b) (hc2.sphereIntegrable x a),
    integral_congr_ae hpt]
  simp_rw [intervalIntegral.integral_of_le hab]
  exact integral_integral_swap hprod

/-- Globally Lipschitz case: `d/ds ∫_{S} u(x + sω)² = ∫_{S} 2 u ∂_r u` for a.e. `s ∈ (0, R)`. -/
theorem _root_.LipschitzWith.ae_hasDerivAt_integral_sphere_sq {u : Rn n → ℝ} {C : ℝ≥0} [NeZero n]
    (hu : LipschitzWith C u) (x : Rn n) (R : ℝ) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      HasDerivAt (fun s => ∫ ω, u (x + s • (ω : Rn n)) ^ 2 ∂sphereMeasure n)
        (∫ ω, radialSqDeriv u x ω s ∂sphereMeasure n) s := by
  rcases le_or_gt R 0 with hR | hR
  · exact .of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.2 hR)
  obtain ⟨hint, -⟩ := hu.integral_sphere_sq_sub x le_rfl hR.le
  filter_upwards [hint.ae_hasDerivAt_integral] with s hs hsR
  have hsI : s ∈ uIcc 0 R := by rw [uIcc_of_le hR.le]; exact Ioo_subset_Icc_self hsR
  have hd := (hs hsI 0 left_mem_uIcc).const_add
    (∫ ω, u (x + (0 : ℝ) • (ω : Rn n)) ^ 2 ∂sphereMeasure n)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hsR.1] with t ht
  rw [← (hu.integral_sphere_sq_sub x le_rfl (le_of_lt ht)).2]
  ring

theorem radialSqDeriv_congr {u v : Rn n → ℝ} {x : Rn n} {R : ℝ} (huv : EqOn u v (ball x R))
    {t : ℝ} (ht : t ∈ Ico 0 R) (ω : sphere (0 : Rn n) 1) :
    radialSqDeriv u x ω t = radialSqDeriv v x ω t := by
  have hmem : x + t • (ω : Rn n) ∈ ball x R := (add_smul_mem_ball_iff ht.1 ω).2 ht.2
  rw [radialSqDeriv, radialSqDeriv, huv hmem,
    (huv.eventuallyEq_of_mem (isOpen_ball.mem_nhds hmem)).gradient_eq]

/-- **Integrated radial derivative of `∫_{∂B_s} u²`**: for `u` Lipschitz on `B_R(x)` and
`0 ≤ a ≤ b < R`, `∫_{S} u(x + bω)² - ∫_{S} u(x + aω)² = ∫_a^b ∫_{S} 2 u(x + tω) ⟪∇u(x + tω), ω⟫`,
and the inner integral is interval integrable. -/
theorem _root_.LipschitzOnWith.integral_sphere_sq_sub [NeZero n] {u : Rn n → ℝ} {C : ℝ≥0}
    {x : Rn n} {R : ℝ} (hu : LipschitzOnWith C u (ball x R)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbR : b < R) :
    IntervalIntegrable (fun t => ∫ ω, radialSqDeriv u x ω t ∂sphereMeasure n) volume a b ∧
    ∫ ω, u (x + b • (ω : Rn n)) ^ 2 ∂sphereMeasure n -
        ∫ ω, u (x + a • (ω : Rn n)) ^ 2 ∂sphereMeasure n =
      ∫ t in a..b, ∫ ω, radialSqDeriv u x ω t ∂sphereMeasure n := by
  obtain ⟨v, hv, huv⟩ := hu.extend_real
  obtain ⟨h1, h2⟩ := hv.integral_sphere_sq_sub x ha hab
  have hG : EqOn (fun t => ∫ ω, radialSqDeriv u x ω t ∂sphereMeasure n)
      (fun t => ∫ ω, radialSqDeriv v x ω t ∂sphereMeasure n) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact integral_congr_ae (.of_forall fun ω =>
      radialSqDeriv_congr huv ⟨ha.trans ht.1, ht.2.trans_lt hbR⟩ ω)
  have hS : ∀ t ∈ Icc a b, ∫ ω, u (x + t • (ω : Rn n)) ^ 2 ∂sphereMeasure n =
      ∫ ω, v (x + t • (ω : Rn n)) ^ 2 ∂sphereMeasure n := fun t ht =>
    integral_congr_ae (.of_forall fun ω => by
      simp only
      rw [huv ((add_smul_mem_ball_iff (ha.trans ht.1) ω).2 (ht.2.trans_lt hbR))])
  refine ⟨h1.congr (hG.symm.mono uIoc_subset_uIcc), ?_⟩
  rw [hS b ⟨hab, le_rfl⟩, hS a ⟨le_rfl, hab⟩, h2, intervalIntegral.integral_congr hG]

/-- **Derivative of `P(s) = ∫_{∂B_s(x)} u²`** for `u` Lipschitz on `B_R(x)`: for a.e.
`s ∈ (0, R)`, `P'(s) = ((n-1)/s) P(s) + (2/s) ∫_{∂B_s(x)} u ⟪∇u, y - x⟫`. -/
theorem _root_.LipschitzOnWith.ae_hasDerivAt_sphereIntegral_sq [NeZero n] {u : Rn n → ℝ}
    {C : ℝ≥0} {x : Rn n} {R : ℝ} (hu : LipschitzOnWith C u (ball x R)) :
    ∀ᵐ s, s ∈ Ioo 0 R → HasDerivAt (fun s => sphereIntegral (fun y => u y ^ 2) x s)
      (((n : ℝ) - 1) / s * sphereIntegral (fun y => u y ^ 2) x s +
        2 / s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s) s := by
  obtain ⟨v, hv, huv⟩ := hu.extend_real
  filter_upwards [hv.ae_hasDerivAt_integral_sphere_sq x R] with s hs hsR
  have hP := (hasDerivAt_pow (n - 1) s).mul (hs hsR)
  have heq : (fun s => sphereIntegral (fun y => u y ^ 2) x s) =ᶠ[𝓝 s]
      fun s => s ^ (n - 1) * ∫ ω, v (x + s • (ω : Rn n)) ^ 2 ∂sphereMeasure n := by
    filter_upwards [Ioo_mem_nhds hsR.1 hsR.2] with t ht
    rw [sphereIntegral]
    congr 1
    exact integral_congr_ae (.of_forall fun ω => by
      simp only
      rw [huv ((add_smul_mem_ball_iff ht.1.le ω).2 ht.2)])
  refine (hP.congr_of_eventuallyEq heq).congr_deriv ?_
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ ω, v (x + s • (ω : Rn n)) *
      ⟪gradient v (x + s • (ω : Rn n)), (ω : Rn n)⟫ ∂sphereMeasure n := ⟨_, rfl⟩
  have hG : ∫ ω, radialSqDeriv v x ω s ∂sphereMeasure n = 2 * I := by
    simp only [radialSqDeriv, mul_assoc]
    rw [integral_const_mul, hI]
  have hsu : sphereIntegral (fun y => u y ^ 2) x s =
      s ^ (n - 1) * ∫ ω, v (x + s • (ω : Rn n)) ^ 2 ∂sphereMeasure n := heq.eq_of_nhds
  have hsg : sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s =
      s ^ (n - 1) * (s * I) := by
    rw [sphereIntegral, hI, ← integral_const_mul s]
    congr 1
    refine integral_congr_ae (.of_forall fun ω => ?_)
    have hmem : x + s • (ω : Rn n) ∈ ball x R := (add_smul_mem_ball_iff hsR.1.le ω).2 hsR.2
    simp only
    rw [huv hmem, (huv.eventuallyEq_of_mem (isOpen_ball.mem_nhds hmem)).gradient_eq,
      add_sub_cancel_left, real_inner_smul_right]
    ring
  rw [hG, hsu, hsg]
  have hs0 : s ≠ 0 := hsR.1.ne'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  rcases m with _ | k
  · field_simp
    simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    field_simp
    ring

/-- `P(s) = ∫_{∂B_s(x)} u²` is Lipschitz on `[0, b]` for every `b < R`, when `u` is Lipschitz
on `B_R(x)`. -/
theorem _root_.LipschitzOnWith.lipschitzOnWith_sphereIntegral_sq [NeZero n] {u : Rn n → ℝ}
    {C : ℝ≥0} {x : Rn n} {R : ℝ} (hu : LipschitzOnWith C u (ball x R)) {b : ℝ} (hb : b < R) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun s => sphereIntegral (fun y => u y ^ 2) x s) (Icc 0 b) := by
  obtain ⟨v, hv, huv⟩ := hu.extend_real
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ, ∀ t, Q t = ∫ ω, v (x + t • (ω : Rn n)) ^ 2 ∂sphereMeasure n :=
    ⟨_, fun t => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |v x| + C * b := ⟨_, rfl⟩
  obtain ⟨σu, hσu⟩ : ∃ σu : ℝ, σu = (sphereMeasure n).real univ := ⟨_, rfl⟩
  have hQb : ∀ t ∈ Icc 0 b, |Q t| ≤ B ^ 2 * σu := by
    intro t ht
    rw [hQ, hσu, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    have h1 : |v (x + t • (ω : Rn n))| ≤ B := by
      rw [hB]
      exact (abs_apply_add_smul_le hv x ht.1 ω).trans (by gcongr; exact ht.2)
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hQL : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, s ≤ t →
      |Q t - Q s| ≤ 2 * B * C * σu * (t - s) := by
    intro s hs t ht hst
    rw [hQ, hQ, (hv.integral_sphere_sq_sub x hs.1 hst).2, ← Real.norm_eq_abs,
      ← abs_of_nonneg (sub_nonneg.2 hst), hσu, hB]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
    rw [uIoc_of_le hst] at hτ
    exact norm_integral_le_of_norm_le_const (.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_radialSqDeriv_le hv x ⟨hs.1.trans hτ.1.le, hτ.2.trans ht.2⟩ ω)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (n - 1 : ℕ) * b ^ (n - 1 - 1) * (B ^ 2 * σu) +
      b ^ (n - 1) * (2 * B * C * σu) := ⟨_, rfl⟩
  have key : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, s ≤ t →
      |t ^ (n - 1) * Q t - s ^ (n - 1) * Q s| ≤ K * (t - s) := by
    intro s hs t ht hst
    have e : t ^ (n - 1) * Q t - s ^ (n - 1) * Q s =
        (t ^ (n - 1) - s ^ (n - 1)) * Q t + s ^ (n - 1) * (Q t - Q s) := by ring
    have hpow : |t ^ (n - 1) - s ^ (n - 1)| ≤ (t - s) * (n - 1 : ℕ) * b ^ (n - 1 - 1) := by
      refine (abs_pow_sub_pow_le t s (n - 1)).trans ?_
      rw [abs_of_nonneg (sub_nonneg.2 hst)]
      gcongr
      rw [abs_of_nonneg ht.1, abs_of_nonneg hs.1]
      exact max_le ht.2 hs.2
    have hsk : |s ^ (n - 1)| ≤ b ^ (n - 1) := by
      rw [abs_of_nonneg (pow_nonneg hs.1 _)]; exact pow_le_pow_left₀ hs.1 hs.2 _
    rw [e, hK]
    calc |(t ^ (n - 1) - s ^ (n - 1)) * Q t + s ^ (n - 1) * (Q t - Q s)|
        ≤ |t ^ (n - 1) - s ^ (n - 1)| * |Q t| + |s ^ (n - 1)| * |Q t - Q s| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ((t - s) * (n - 1 : ℕ) * b ^ (n - 1 - 1)) * (B ^ 2 * σu) +
            b ^ (n - 1) * (2 * B * C * σu * (t - s)) := by
          have hb : 0 ≤ b := hs.1.trans hs.2
          exact add_le_add
            (mul_le_mul hpow (hQb t ht) (abs_nonneg _)
              (mul_nonneg (mul_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)) (pow_nonneg hb _)))
            (mul_le_mul hsk (hQL s hs t ht hst) (abs_nonneg _) (pow_nonneg hb _))
      _ = _ := by ring
  refine ⟨Real.toNNReal K, LipschitzOnWith.of_dist_le_mul fun a ha c hc => ?_⟩
  have hP : ∀ t ∈ Icc 0 b, sphereIntegral (fun y => u y ^ 2) x t = t ^ (n - 1) * Q t := by
    intro t ht
    rw [sphereIntegral, hQ]
    congr 1
    exact integral_congr_ae (.of_forall fun ω => by
      simp only
      rw [huv ((add_smul_mem_ball_iff ht.1 ω).2 (ht.2.trans_lt hb))])
  rw [hP a ha, hP c hc, Real.dist_eq, Real.dist_eq]
  have hK' : K ≤ (Real.toNNReal K : ℝ) := Real.le_coe_toNNReal K
  rcases le_total a c with hac | hac
  · rw [abs_sub_comm, abs_sub_comm a c, abs_of_nonneg (sub_nonneg.2 hac)]
    exact (key a ha c hc hac).trans (mul_le_mul_of_nonneg_right hK' (sub_nonneg.2 hac))
  · rw [abs_of_nonneg (sub_nonneg.2 hac)]
    exact (key c hc a ha hac).trans (mul_le_mul_of_nonneg_right hK' (sub_nonneg.2 hac))

end InnerVariational
