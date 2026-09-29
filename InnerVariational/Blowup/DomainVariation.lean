/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Tangential
public import InnerVariational.Kernel.BV
public import InnerVariational.Regular.ZeroGradient
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Real.Hom

/-!
# Theorem 5.3, steps (b)–(c): strong convergence off `{⟪ν, x⟫ = 0}` and the limit domain variation

Steps (b) and (c) of the proof of Theorem 5.3 of Kriventsov–Weiss (full reference below): the
second and third paragraphs of that proof, up to equation (5.15).

* Step (b) (strong convergence on `U ⋐ A \ {x_n = 0}`). If the tangential part of `F_k = ∇v_k`
  tends to `0` in `L²` and `⟪F_k, y⟫ → ⟪G, y⟫` in `L²` (this follows from the vanishing Euler
  defect and the weak Euler identity of the limit), where `G = ⟪G, ν⟫ ν`, then `F_k → G` strongly
  in `L²(K)` on every set `K` where `|⟪ν, y⟫|` is bounded below. This is a direct pointwise
  estimate (`norm_sub_sq_le_of_tangentialPart`), in place of the paper's "expanding the square".
* Step (c) (the limit domain variation). Strong `L²` convergence of gradients passes the quadratic
  part of the inner variation, `∫ (|∇v_k|² div ξ − 2 ∇v_k · Dξ ∇v_k)`, to the limit.
* For `G = g ν` and `ξ = φ ν`, the limit integrand is `−g² ∂_ν φ`.

## Main results

* `norm_sub_sq_le_of_tangentialPart`: the pointwise estimate behind step (b).
* `tendsto_setIntegral_norm_sub_sq_of_tangentialPart`: step (b).
* `tendsto_integral_quadratic`: continuity of `∫ (‖F‖² a − 2 ⟪F, A F⟫)` under strong `L²`
  convergence, for bounded `a`, `A`.
* `tendsto_integral_gradVariation`: step (c), passing `∫ gradVariation (v k) ξ` to the limit.
* `quadratic_smul_const_eq`: the limit integrand for `G = g ν`, `ξ = φ ν`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

/-! ### Step (b): strong convergence away from the hyperplane -/

section StepB

variable {n : ℕ}

/-- **Pointwise estimate for step (b).** If `‖ν‖ = 1`, `‖y‖ ≤ 1`, `c ≤ |⟪ν, y⟫|` with `c > 0`,
and `G = ⟪ν, G⟫ ν`, then
`‖F − G‖² ≤ (1 + 2/c²) ‖F − ⟪ν, F⟫ ν‖² + (2/c²) (⟪F, y⟫ − ⟪G, y⟫)²`. -/
theorem norm_sub_sq_le_of_tangentialPart {ν y F G : Rn n} (hν : ‖ν‖ = 1) (hy : ‖y‖ ≤ 1)
    {c : ℝ} (hc : 0 < c) (hcy : c ≤ |⟪ν, y⟫|) (hG : tangentialPart ν G = 0) :
    ‖F - G‖ ^ 2 ≤ (1 + 2 / c ^ 2) * ‖tangentialPart ν F‖ ^ 2 +
      2 / c ^ 2 * (⟪F, y⟫ - ⟪G, y⟫) ^ 2 := by
  set P := tangentialPart ν F with hP
  set f := ⟪ν, F⟫
  set g := ⟪ν, G⟫
  set t := ⟪ν, y⟫
  have hGe : G = g • ν := by
    rw [tangentialPart_apply, sub_eq_zero] at hG
    exact hG
  have hFe : F = P + f • ν := by
    rw [hP, tangentialPart_apply]
    abel
  have hPν : ⟪P, ν⟫ = 0 := by
    rw [hP, tangentialPart_apply, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hν,
      real_inner_comm]
    simp
  have hdiff : F - G = P + (f - g) • ν := by
    rw [hGe]
    nth_rw 1 [hFe]
    rw [sub_smul]
    abel
  have hnorm : ‖F - G‖ ^ 2 = ‖P‖ ^ 2 + (f - g) ^ 2 := by
    rw [hdiff, norm_add_sq_real, inner_smul_right, hPν, norm_smul, hν, Real.norm_eq_abs,
      mul_one, mul_zero, mul_zero, add_zero, sq_abs]
  have hinner : ⟪F, y⟫ - ⟪G, y⟫ = ⟪P, y⟫ + (f - g) * t := by
    rw [← inner_sub_left, hdiff, inner_add_left, inner_smul_left, conj_trivial]
  have hp : ⟪P, y⟫ ^ 2 ≤ ‖P‖ ^ 2 := by
    have h1 : |⟪P, y⟫| ≤ ‖P‖ :=
      (abs_real_inner_le_norm P y).trans (by
        calc ‖P‖ * ‖y‖ ≤ ‖P‖ * 1 := by gcongr
          _ = ‖P‖ := mul_one _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have ht : c ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ hc.le hcy 2
  have hc2 : 0 < c ^ 2 := by positivity
  have hkey : (f - g) ^ 2 * c ^ 2 ≤ 2 * (⟪F, y⟫ - ⟪G, y⟫) ^ 2 + 2 * ‖P‖ ^ 2 := by
    have h1 : (f - g) ^ 2 * c ^ 2 ≤ (f - g) ^ 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    have h2 : (f - g) ^ 2 * t ^ 2 = ((⟪F, y⟫ - ⟪G, y⟫) - ⟪P, y⟫) ^ 2 := by
      rw [hinner]
      ring
    nlinarith [sq_nonneg ((⟪F, y⟫ - ⟪G, y⟫) + ⟪P, y⟫)]
  have hfg : (f - g) ^ 2 ≤ (2 * (⟪F, y⟫ - ⟪G, y⟫) ^ 2 + 2 * ‖P‖ ^ 2) / c ^ 2 :=
    (le_div_iff₀ hc2).2 hkey
  rw [hnorm]
  calc ‖P‖ ^ 2 + (f - g) ^ 2
      ≤ ‖P‖ ^ 2 + (2 * (⟪F, y⟫ - ⟪G, y⟫) ^ 2 + 2 * ‖P‖ ^ 2) / c ^ 2 := by linarith
    _ = (1 + 2 / c ^ 2) * ‖P‖ ^ 2 + 2 / c ^ 2 * (⟪F, y⟫ - ⟪G, y⟫) ^ 2 := by
        field_simp
        ring

/-- **Theorem 5.3, step (b), strong convergence off `{⟪ν, y⟫ = 0}`.** Suppose
`F_k, G ∈ L²(μ)`, `‖y‖ ≤ 1` a.e., `G = ⟪ν, G⟫ ν` a.e. with `‖ν‖ = 1`, the tangential part
`F_k − ⟪ν, F_k⟫ ν` tends to `0` in `L²(μ)`, and `⟪F_k, y⟫ → ⟪G, y⟫` in `L²(μ)`. Then `F_k → G` in
`L²(K)` on every measurable `K` where `|⟪ν, y⟫| ≥ c > 0`. -/
theorem tendsto_setIntegral_norm_sub_sq_of_tangentialPart {μ : Measure (Rn n)}
    {F : ℕ → Rn n → Rn n} {G : Rn n → Rn n} (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ)
    (hball : ∀ᵐ y ∂μ, ‖y‖ ≤ 1) {ν : Rn n} (hν : ‖ν‖ = 1)
    (hGν : ∀ᵐ y ∂μ, tangentialPart ν (G y) = 0)
    (hP : Tendsto (fun k => ∫ y, ‖tangentialPart ν (F k y)‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hR : Tendsto (fun k => ∫ y, (⟪F k y, y⟫ - ⟪G y, y⟫) ^ 2 ∂μ) atTop (𝓝 0))
    {K : Set (Rn n)} (hK : MeasurableSet K) {c : ℝ} (hc : 0 < c)
    (hKc : ∀ y ∈ K, c ≤ |⟪ν, y⟫|) :
    Tendsto (fun k => ∫ y in K, ‖F k y - G y‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hPF : ∀ k, Integrable (fun y => ‖tangentialPart ν (F k y)‖ ^ 2) μ := fun k =>
    MemLp.integrable_norm_sq ((tangentialPart ν).comp_memLp' (hF k))
  have hIF : ∀ k, MemLp (fun y => ⟪F k y, y⟫ - ⟪G y, y⟫) 2 μ := fun k => by
    have e : (fun y => ⟪F k y, y⟫ - ⟪G y, y⟫) = fun y => ⟪F k y - G y, y⟫ := by
      funext y; rw [inner_sub_left]
    rw [e]
    refine ((hF k).sub hG).of_le (((hF k).sub hG).1.inner aestronglyMeasurable_id) ?_
    filter_upwards [hball] with y hy
    calc ‖⟪F k y - G y, y⟫‖ ≤ ‖F k y - G y‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ ‖F k y - G y‖ * 1 := by gcongr
      _ = ‖(F k - G) y‖ := by rw [mul_one]; rfl
  have hRF : ∀ k, Integrable (fun y => (⟪F k y, y⟫ - ⟪G y, y⟫) ^ 2) μ := fun k =>
    (hIF k).integrable_sq
  have hbound : ∀ k, ∫ y in K, ‖F k y - G y‖ ^ 2 ∂μ ≤
      (1 + 2 / c ^ 2) * (∫ y, ‖tangentialPart ν (F k y)‖ ^ 2 ∂μ) +
        2 / c ^ 2 * ∫ y, (⟪F k y, y⟫ - ⟪G y, y⟫) ^ 2 ∂μ := by
    intro k
    have hint : Integrable (fun y => (1 + 2 / c ^ 2) * ‖tangentialPart ν (F k y)‖ ^ 2 +
        2 / c ^ 2 * (⟪F k y, y⟫ - ⟪G y, y⟫) ^ 2) μ :=
      ((hPF k).const_mul _).add ((hRF k).const_mul _)
    calc ∫ y in K, ‖F k y - G y‖ ^ 2 ∂μ
        ≤ ∫ y in K, ((1 + 2 / c ^ 2) * ‖tangentialPart ν (F k y)‖ ^ 2 +
            2 / c ^ 2 * (⟪F k y, y⟫ - ⟪G y, y⟫) ^ 2) ∂μ := by
          refine setIntegral_mono_on_ae ?_ hint.integrableOn hK ?_
          · exact (MemLp.integrable_norm_sq ((hF k).sub hG)).integrableOn
          · filter_upwards [hball, hGν] with y hy hGy hyK
            exact norm_sub_sq_le_of_tangentialPart hν hy hc (hKc y hyK) hGy
      _ ≤ ∫ y, ((1 + 2 / c ^ 2) * ‖tangentialPart ν (F k y)‖ ^ 2 +
            2 / c ^ 2 * (⟪F k y, y⟫ - ⟪G y, y⟫) ^ 2) ∂μ :=
          setIntegral_le_integral hint (Eventually.of_forall fun y => by positivity)
      _ = _ := by
          rw [integral_add ((hPF k).const_mul _) ((hRF k).const_mul _), integral_const_mul,
            integral_const_mul]
  have hRHS := (hP.const_mul (1 + 2 / c ^ 2)).add (hR.const_mul (2 / c ^ 2))
  simp only [mul_zero, add_zero] at hRHS
  exact squeeze_zero (fun k => setIntegral_nonneg_ae hK (Eventually.of_forall fun y _ => by
    positivity)) hbound hRHS

end StepB

/-! ### Step (c): passing the quadratic part of the inner variation to the limit -/

section Quadratic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The difference of the quadratic forms `‖w‖² a − 2 ⟪w, A w⟫` at `G + d` and at `G`. -/
theorem abs_quadratic_sub_le {a M : ℝ} {A : E →L[ℝ] E} (ha : |a| ≤ M) (hA : ‖A‖ ≤ M)
    (G d : E) :
    |(‖G + d‖ ^ 2 * a - 2 * ⟪G + d, A (G + d)⟫) - (‖G‖ ^ 2 * a - 2 * ⟪G, A G⟫)| ≤
      3 * M * ‖d‖ ^ 2 + 6 * M * (‖G‖ * ‖d‖) := by
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  have e : (‖G + d‖ ^ 2 * a - 2 * ⟪G + d, A (G + d)⟫) - (‖G‖ ^ 2 * a - 2 * ⟪G, A G⟫) =
      (2 * ⟪G, d⟫ + ‖d‖ ^ 2) * a - 2 * (⟪G, A d⟫ + ⟪d, A G⟫ + ⟪d, A d⟫) := by
    rw [norm_add_sq_real, map_add, inner_add_left, inner_add_right, inner_add_right]
    ring
  rw [e]
  have h1 : |⟪G, d⟫| ≤ ‖G‖ * ‖d‖ := abs_real_inner_le_norm _ _
  have hAv : ∀ w : E, ‖A w‖ ≤ M * ‖w‖ := fun w =>
    (A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h2 : |⟪G, A d⟫| ≤ M * (‖G‖ * ‖d‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖G‖ * ‖A d‖ ≤ ‖G‖ * (M * ‖d‖) := mul_le_mul_of_nonneg_left (hAv d) (norm_nonneg _)
      _ = M * (‖G‖ * ‖d‖) := by ring
  have h3 : |⟪d, A G⟫| ≤ M * (‖G‖ * ‖d‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖d‖ * ‖A G‖ ≤ ‖d‖ * (M * ‖G‖) := mul_le_mul_of_nonneg_left (hAv G) (norm_nonneg _)
      _ = M * (‖G‖ * ‖d‖) := by ring
  have h4 : |⟪d, A d⟫| ≤ M * ‖d‖ ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖d‖ * ‖A d‖ ≤ ‖d‖ * (M * ‖d‖) := mul_le_mul_of_nonneg_left (hAv d) (norm_nonneg _)
      _ = M * ‖d‖ ^ 2 := by ring
  have hGd : 0 ≤ ‖G‖ * ‖d‖ := by positivity
  have h5 : |(2 * ⟪G, d⟫ + ‖d‖ ^ 2) * a| ≤ (2 * (‖G‖ * ‖d‖) + ‖d‖ ^ 2) * M := by
    rw [abs_mul]
    refine mul_le_mul ?_ ha (abs_nonneg _) (by positivity)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg ‖d‖)]
    linarith
  have h6 : |2 * (⟪G, A d⟫ + ⟪d, A G⟫ + ⟪d, A d⟫)| ≤
      2 * (2 * M * (‖G‖ * ‖d‖) + M * ‖d‖ ^ 2) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    linarith
  refine (abs_sub _ _).trans ?_
  nlinarith

/-- **Continuity of quadratic integrals under strong `L²` convergence.** Let `a` and `A` be
bounded by `M` and a.e. strongly measurable. If `F k → G` in `L²(μ)`, then
`∫ (‖F k‖² a − 2 ⟪F k, A (F k)⟫) → ∫ (‖G‖² a − 2 ⟪G, A G⟫)`. -/
theorem tendsto_integral_quadratic {F : ℕ → α → E} {G : α → E} (hF : ∀ k, MemLp (F k) 2 μ)
    (hG : MemLp G 2 μ) {a : α → ℝ} {A : α → E →L[ℝ] E} {M : ℝ} (hM : 0 ≤ M)
    (ham : AEStronglyMeasurable a μ) (hAm : AEStronglyMeasurable A μ) (ha : ∀ x, |a x| ≤ M)
    (hA : ∀ x, ‖A x‖ ≤ M) (h : Tendsto (fun k => ∫ x, ‖F k x - G x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, (‖F k x‖ ^ 2 * a x - 2 * ⟪F k x, A x (F k x)⟫) ∂μ) atTop
      (𝓝 (∫ x, (‖G x‖ ^ 2 * a x - 2 * ⟪G x, A x (G x)⟫) ∂μ)) := by
  set q : (α → E) → α → ℝ := fun H x => ‖H x‖ ^ 2 * a x - 2 * ⟪H x, A x (H x)⟫ with hq
  have hqint : ∀ {H : α → E}, MemLp H 2 μ → Integrable (q H) μ := by
    intro H hH
    have hm : AEStronglyMeasurable (q H) μ := by
      have h1 : AEStronglyMeasurable (fun x => A x (H x)) μ :=
        Continuous.comp_aestronglyMeasurable₂ (g := fun (L : E →L[ℝ] E) (w : E) => L w)
          isBoundedBilinearMap_apply.continuous hAm hH.1
      exact ((hH.1.norm.aemeasurable.pow_const 2).aestronglyMeasurable.mul ham).sub
        ((hH.1.inner h1).const_mul 2)
    refine ((MemLp.integrable_norm_sq hH).const_mul (3 * M)).mono' hm
      (Eventually.of_forall fun x => ?_)
    have := abs_quadratic_sub_le (ha x) (hA x) 0 (H x)
    simp only [zero_add, norm_zero, map_zero, inner_zero_right, zero_mul,
      mul_zero, sub_zero, zero_pow two_ne_zero, add_zero] at this
    rw [Real.norm_eq_abs]
    exact this
  have hd : ∀ k, MemLp (fun x => F k x - G x) 2 μ := fun k => (hF k).sub hG
  set s : ℕ → ℝ := fun k => ∫ x, ‖F k x - G x‖ ^ 2 ∂μ with hs
  set g : ℝ := ∫ x, ‖G x‖ ^ 2 ∂μ with hg
  have hbound : ∀ k, ‖(∫ x, q (F k) x ∂μ) - ∫ x, q G x ∂μ‖ ≤
      3 * M * s k + 6 * M * (√g * √(s k)) := by
    intro k
    have hGd : MemLp (fun x => ‖G x‖) 2 μ := hG.norm
    have hdd : MemLp (fun x => ‖F k x - G x‖) 2 μ := (hd k).norm
    have hprod : Integrable (fun x => ‖G x‖ * ‖F k x - G x‖) μ := by
      refine (MemLp.integrable_inner_two hGd hdd).congr (Eventually.of_forall fun x => ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    have hCS : ∫ x, ‖G x‖ * ‖F k x - G x‖ ∂μ ≤ √g * √(s k) := by
      have h1 := abs_integral_inner_le hGd hdd
      simp only [RCLike.inner_apply, conj_trivial, norm_norm] at h1
      refine (le_abs_self _).trans ?_
      convert h1 using 3
      · funext x; ring
    rw [← integral_sub (hqint (hF k)) (hqint hG), Real.norm_eq_abs]
    calc |∫ x, (q (F k) x - q G x) ∂μ|
        ≤ ∫ x, |q (F k) x - q G x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (3 * M * ‖F k x - G x‖ ^ 2 + 6 * M * (‖G x‖ * ‖F k x - G x‖)) ∂μ := by
          refine integral_mono ((hqint (hF k)).sub (hqint hG)).abs
            (((MemLp.integrable_norm_sq (hd k)).const_mul _).add (hprod.const_mul _))
            fun x => ?_
          have := abs_quadratic_sub_le (ha x) (hA x) (G x) (F k x - G x)
          rwa [add_sub_cancel] at this
      _ = 3 * M * s k + 6 * M * ∫ x, ‖G x‖ * ‖F k x - G x‖ ∂μ := by
          rw [integral_add ((MemLp.integrable_norm_sq (hd k)).const_mul _) (hprod.const_mul _),
            integral_const_mul, integral_const_mul]
      _ ≤ 3 * M * s k + 6 * M * (√g * √(s k)) := by gcongr
  have hsq : Tendsto (fun k => √(s k)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp h
  have hlim : Tendsto (fun k => 3 * M * s k + 6 * M * (√g * √(s k))) atTop (𝓝 0) := by
    simpa using (h.const_mul (3 * M)).add ((hsq.const_mul √g).const_mul (6 * M))
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) hbound hlim)

end Quadratic

section GradVariation

variable {n : ℕ}

/-- **Theorem 5.3, step (c): the quadratic part of the inner variation passes to the limit**, as in
the proof of Theorem 5.3 just before equation (5.15). Let `ξ` be `D`-Lipschitz with
`tsupport ξ ⊆ K`. If `∇v_k → G` in `L²(K)`, then
`∫ (|∇v_k|² div ξ − 2 ∇v_k · Dξ ∇v_k) → ∫_K (|G|² div ξ − 2 G · Dξ G)`. -/
theorem tendsto_integral_gradVariation {v : ℕ → Rn n → ℝ} {G : Rn n → Rn n}
    {ξ : Rn n → Rn n} {D : ℝ≥0} (hξ : LipschitzWith D ξ) {K : Set (Rn n)}
    (hξK : tsupport ξ ⊆ K) (hF : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict K))
    (hG : MemLp G 2 (volume.restrict K))
    (h : Tendsto (fun k => ∫ y in K, ‖gradient (v k) y - G y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y, Kernel.gradVariation (v k) ξ y) atTop
      (𝓝 (∫ y in K, (‖G y‖ ^ 2 * divergence ξ y - 2 * ⟪G y, fderiv ℝ ξ y (G y)⟫))) := by
  have e : ∀ k, ∫ y, Kernel.gradVariation (v k) ξ y =
      ∫ y in K, Kernel.gradVariation (v k) ξ y := fun k =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      Kernel.gradVariation_eq_zero_of_notMem_tsupport fun h' => hy (hξK h')).symm
  refine (tendsto_congr e).2 ?_
  simp only [Kernel.gradVariation]
  refine tendsto_integral_quadratic hF hG (M := n * D + D) (by positivity)
    (Kernel.measurable_divergence ξ).aestronglyMeasurable
    (measurable_fderiv ℝ ξ).aestronglyMeasurable (fun y => ?_) (fun y => ?_) h
  · exact (Kernel.abs_divergence_le hξ y).trans (le_add_of_nonneg_right D.2)
  · exact (norm_fderiv_le_of_lipschitz ℝ hξ).trans (le_add_of_nonneg_left (by positivity))

/-- **The limit integrand for one-dimensional gradients.** For `G = g ν` with `‖ν‖ = 1` and
`ξ = φ ν`: `|G|² div ξ − 2 G · Dξ G = −g² ∂_ν φ`. -/
theorem quadratic_smul_const_eq {φ : Rn n → ℝ} (hφ : Differentiable ℝ φ) {ν : Rn n}
    (hν : ‖ν‖ = 1) (g : ℝ) (y : Rn n) :
    ‖g • ν‖ ^ 2 * divergence (fun z => φ z • ν) y -
        2 * ⟪g • ν, fderiv ℝ (fun z => φ z • ν) y (g • ν)⟫ =
      -(g ^ 2 * fderiv ℝ φ y ν) := by
  rw [Regular.divergence_smul_const hφ, fderiv_smul_const (hφ y) ν,
    ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul, inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, hν]
  simp only [Real.norm_eq_abs, mul_one, one_pow, sq_abs, conj_trivial]
  ring

end GradVariation

end InnerVariational
