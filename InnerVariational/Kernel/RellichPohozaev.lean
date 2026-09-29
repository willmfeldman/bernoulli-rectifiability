/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.Energy
public import InnerVariational.Kernel.Subharmonic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral

/-!
# The Rellich–Pohozaev identity (3.7)

Identity (3.7) of Kriventsov–Weiss (in the proof of Proposition 3.4; full reference below): for a
variational solution `(u, χ)` on `Ω`, `B_R(x) ⊆ Ω`, and a.e. `s ∈ (0, R)`,
`(n − 2) ∫_{B_s(x)} |∇u|² + n ∫_{B_s(x)} χ = s ∫_{∂B_s(x)} (|∇u|² + χ − 2 (∇u · ν)²)`,
with `ν(y) = (y − x) / |y − x|`.

## Proof

We follow the paper. Test the inner variation with `ξ(y) = η_k(y) (y − x)`, where
`η_k = radialCutoff x s (1/k)`. Off the two spheres bounding the annulus
`A_k = B_{s+1/k} ∖ B_s`, `Dξ = η_k I + (y − x) ⊗ ∇η_k`. The inner variation then reads
`∫ ((n − 2)|∇u|² + nχ) η_k = k ∫_{A_k} |y − x| (|∇u|² + χ − 2 (∇u · ν)²)`.
The left side tends to `∫_{B_s} ((n − 2)|∇u|² + nχ)` by dominated convergence, and the right side
to the sphere integral at a.e. `s` (`ae_tendsto_average_annulus`).

The paper's intermediate display just before (3.7) has `∫_{B_s} (n − 2)(|∇u|² + χ)` on the
left; the correct left side is
`∫_{B_s} ((n − 2)|∇u|² + nχ)`: `div ξ` multiplies `|∇u|² + χ`, while `−2 ∇u·Dξ∇u` contributes
`−2η|∇u|²` only to the gradient part. The identity (3.7) itself is correct, and it is what we
formalize.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

open Kernel

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

theorem aestronglyMeasurable_chi (h : IsVariationalSolution Ω C u χ) {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) : AEStronglyMeasurable χ (volume.restrict S) :=
  h.measurable_chi.aestronglyMeasurable.congr
    ((ae_restrict_iff' hS).2 (.of_forall fun _ hy => indicator_of_mem (hSΩ hy) χ))

theorem abs_chi_le_one (h : IsVariationalSolution Ω C u χ) {y : Rn n} (hy : y ∈ Ω) :
    |χ y| ≤ 1 := by
  rcases h.chi_mem y hy with h0 | h1 <;> simp [*]

/-- **The Rellich–Pohozaev identity (3.7)** (proof of Proposition 3.4). If `B_R(x) ⊆ Ω`, then
for a.e. `s ∈ (0, R)`,
`(n − 2) ∫_{B_s(x)} |∇u|² + n ∫_{B_s(x)} χ = s ∫_{∂B_s(x)} (|∇u|² + χ − 2 (∇u · ν)²)`,
with `ν(y) = (y − x) / |y − x|`. -/
theorem rellich_pohozaev_ae [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n} {R : ℝ}
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      ((n : ℝ) - 2) * (∫ y in ball x s, ‖gradient u y‖ ^ 2) + n * ∫ y in ball x s, χ y =
        s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y -
          2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s := by
  rcases le_or_gt R 0 with hR0 | hR0
  · exact .of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.2 hR0)
  obtain ⟨Cg, hCg⟩ := h.isLipHarmonicPos.exists_norm_gradient_le
  set ν : Rn n → Rn n := fun y => ‖y - x‖⁻¹ • (y - x) with hνdef
  have hνb : ∀ y, ‖ν y‖ ≤ 1 := by
    intro y
    rw [hνdef]; simp only
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖y - x‖ 0 with h0 | h0
    · rw [h0]; simp
    · rw [inv_mul_cancel₀ h0]
  have hνm : Measurable ν := (measurable_id.sub_const x).norm.inv.smul (measurable_id.sub_const x)
  set g : Rn n → ℝ := fun y => ‖y - x‖ * (‖gradient u y‖ ^ 2 + χ y - 2 * ⟪gradient u y, ν y⟫ ^ 2)
    with hgdef
  set G : Rn n → ℝ := fun y => ((n : ℝ) - 2) * ‖gradient u y‖ ^ 2 + n * χ y with hGdef
  have hgrad2 : Measurable fun y => ‖gradient u y‖ ^ 2 := (measurable_gradient u).norm.pow_const 2
  have hinner : ∀ y ∈ Ω, |⟪gradient u y, ν y⟫| ≤ Cg := fun y hy => by
    rw [← Real.norm_eq_abs]
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖gradient u y‖ * ‖ν y‖ ≤ Cg * 1 := mul_le_mul (hCg y hy) (hνb y) (norm_nonneg _) Cg.2
      _ = Cg := mul_one _
  have hsq : ∀ y ∈ Ω, ‖gradient u y‖ ^ 2 ≤ (Cg : ℝ) ^ 2 := fun y hy =>
    pow_le_pow_left₀ (norm_nonneg _) (hCg y hy) 2
  -- `g` is integrable on `B_R(x)`
  have hg : IntegrableOn g (ball x R) := by
    have hm : AEStronglyMeasurable g (volume.restrict (ball x R)) :=
      (measurable_id.sub_const x).norm.aestronglyMeasurable.mul
        ((hgrad2.aestronglyMeasurable.add (h.aestronglyMeasurable_chi measurableSet_ball hR)).sub
          ((((measurable_gradient u).inner hνm).pow_const 2).const_mul 2).aestronglyMeasurable)
    refine IntegrableOn.of_bound measure_ball_lt_top hm (R * ((Cg : ℝ) ^ 2 + 1 + 2 * Cg ^ 2))
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
    have hyΩ := hR hy
    have h1 : ‖y - x‖ ≤ R := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
    have h2 : |‖gradient u y‖ ^ 2 + χ y - 2 * ⟪gradient u y, ν y⟫ ^ 2| ≤
        (Cg : ℝ) ^ 2 + 1 + 2 * Cg ^ 2 := by
      have a1 := hsq y hyΩ
      have a2 := h.abs_chi_le_one hyΩ
      have a3 : ⟪gradient u y, ν y⟫ ^ 2 ≤ (Cg : ℝ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hinner y hyΩ) 2
      have a4 : 0 ≤ ⟪gradient u y, ν y⟫ ^ 2 := sq_nonneg _
      have a5 : 0 ≤ ‖gradient u y‖ ^ 2 := sq_nonneg _
      rw [abs_le] at a2 ⊢
      constructor <;> nlinarith
    rw [hgdef, Real.norm_eq_abs, abs_mul, abs_norm]
    exact mul_le_mul h1 h2 (abs_nonneg _) hR0.le
  filter_upwards [ae_tendsto_average_annulus hg] with s hs hsR
  have hlim := hs hsR
  set ρ := (s + R) / 2 with hρ
  have hsρ : s < ρ := by rw [hρ]; linarith [hsR.2]
  have hρR : ρ < R := by rw [hρ]; linarith [hsR.2]
  have hρΩ : closedBall x ρ ⊆ Ω := (closedBall_subset_ball hρR).trans hR
  have hev := eventually_one_div_lt (sub_pos.2 hsρ)
  have hGmS : ∀ S, MeasurableSet S → S ⊆ Ω → AEStronglyMeasurable G (volume.restrict S) :=
    fun S hS hSΩ => (hgrad2.aestronglyMeasurable.const_mul _).add
      ((h.aestronglyMeasurable_chi hS hSΩ).const_mul _)
  have hGm := hGmS _ measurableSet_closedBall hρΩ
  have hGb : ∀ y ∈ closedBall x ρ, |G y| ≤ |(n : ℝ) - 2| * Cg ^ 2 + n := by
    intro y hy
    rw [hGdef]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (sq_nonneg ‖gradient u y‖)]
      exact mul_le_mul_of_nonneg_left (hsq y (hρΩ hy)) (abs_nonneg _)
    · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      calc (n : ℝ) * |χ y| ≤ n * 1 :=
            mul_le_mul_of_nonneg_left (h.abs_chi_le_one (hρΩ hy)) (Nat.cast_nonneg n)
        _ = n := mul_one _
  -- the inner variation along `ξ_k = η_k (y − x)`
  have hid : ∀ᶠ k : ℕ in atTop, ∫ y, G y * radialCutoff x s (1 / k) y =
      (k : ℝ) * ∫ y in ball x (s + 1 / k) \ ball x s, g y := by
    filter_upwards [hev] with k ⟨hk0, hkρ⟩
    set δ : ℝ := 1 / k with hδdef
    set η := radialCutoff x s δ with hηdef
    set A := ball x (s + δ) \ ball x s with hAdef
    set ξ : Rn n → Rn n := fun y => η y • (y - x) with hξdef
    have hK : closedBall x (s + δ) ⊆ Ω :=
      (closedBall_subset_closedBall (by linarith)).trans hρΩ
    have hξ : IsLipTestField Ω ξ := by
      refine ⟨⟨_, lipschitzWith_smul_of_support (lipschitzWith_radialCutoff hk0)
        abs_radialCutoff_le_one (K := closedBall x (s + δ)) (fun y hy => ?_) (Lg := 1)
        (LipschitzOnWith.of_dist_le_mul fun a _ b _ => by rw [dist_sub_right]; simp)
        (M := s + δ) (fun y hy => by rw [← dist_eq_norm]; exact hy)⟩,
        (hasCompactSupport_radialCutoff hk0).smul_right,
        (tsupport_smul_subset_left _ _).trans ((tsupport_radialCutoff_subset hk0).trans hK)⟩
      rw [mem_closedBall, dist_eq_norm, not_le] at hy
      exact radialCutoff_eq_zero hk0 hy.le
    have hIV := h.innerVariation_eq_zero ξ hξ
    -- the integrand, off the two spheres
    have hpt : ∀ᵐ y, ((‖gradient u y‖ ^ 2 + χ y) * divergence ξ y -
        2 * ⟪gradient u y, fderiv ℝ ξ y (gradient u y)⟫) =
        G y * η y - δ⁻¹ * A.indicator g y := by
      have h1 := Measure.addHaar_sphere (volume : Measure (Rn n)) x s
      have h2 := Measure.addHaar_sphere (volume : Measure (Rn n)) x (s + δ)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
        with y hy1 hy2
      rw [mem_sphere, dist_eq_norm] at hy1 hy2
      have hη := hasFDerivAt_radialCutoff_indicator hk0 hsR.1.le hy1 hy2
      set η' := A.indicator (fun z => -(δ⁻¹ * ‖z - x‖⁻¹) • innerSL ℝ (z - x)) y with hη'def
      have hid' : HasFDerivAt (fun z : Rn n => z - x) (ContinuousLinearMap.id ℝ (Rn n)) y :=
        (hasFDerivAt_id y).sub_const x
      have hD : fderiv ℝ ξ y = η y • ContinuousLinearMap.id ℝ (Rn n) + η'.smulRight (y - x) :=
        (hη.smul hid').fderiv
      have hdiv : divergence ξ y = η y * n + η' (y - x) := by
        rw [divergence, hD]
        simp [LinearMap.trace_smulRight, mul_comm]
      have hquad : ⟪gradient u y, fderiv ℝ ξ y (gradient u y)⟫ =
          η y * ‖gradient u y‖ ^ 2 + η' (gradient u y) * ⟪gradient u y, y - x⟫ := by
        rw [hD]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, inner_add_right,
          inner_smul_right, real_inner_self_eq_norm_sq]
      rw [hdiv, hquad]
      by_cases hyA : y ∈ A
      · have ha : ‖y - x‖ ≠ 0 := by
          have := hyA.2; rw [mem_ball, dist_eq_norm, not_lt] at this
          exact (lt_of_lt_of_le hsR.1 this).ne'
        rw [hη'def, indicator_of_mem hyA, indicator_of_mem hyA]
        simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, hgdef,
          hGdef, hνdef, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm (y - x)]
        field_simp
        ring
      · rw [hη'def, indicator_of_notMem hyA, indicator_of_notMem hyA]
        simp only [ContinuousLinearMap.zero_apply, hGdef]
        ring
    -- integrability
    have hI1 : Integrable fun y => G y * η y := by
      refine integrable_mul_of_isCompact (isCompact_closedBall x (s + δ))
        ((hGmS _ measurableSet_closedBall hK).mul continuous_radialCutoff.aestronglyMeasurable)
        (A := |(n : ℝ) - 2| * Cg ^ 2 + n) (B := 1) (fun y hy => ?_)
        (fun y _ => by rw [Real.norm_eq_abs]; exact abs_radialCutoff_le_one y) (fun y hy => ?_)
      · rw [Real.norm_eq_abs]
        exact hGb y (closedBall_subset_closedBall (by linarith) hy)
      · rw [mem_closedBall, dist_eq_norm, not_le] at hy
        exact radialCutoff_eq_zero hk0 hy.le
    have hI2 : Integrable (A.indicator g) :=
      (hg.mono_set (diff_subset.trans (ball_subset_ball (by linarith)))).integrable_indicator
        (measurableSet_ball.diff measurableSet_ball)
    rw [innerVariation, integral_congr_ae hpt, integral_sub hI1 (hI2.const_mul _),
      integral_const_mul, integral_indicator (measurableSet_ball.diff measurableSet_ball),
      hδdef, one_div, inv_inv] at hIV
    have hA : A = ball x (s + (k : ℝ)⁻¹) \ ball x s := by rw [hAdef, hδdef, one_div]
    rw [hA]
    linarith
  have hL := tendsto_integral_mul_radialCutoff hsρ hGm hGb
  have heq := tendsto_nhds_unique (hL.congr' hid) hlim
  -- rewrite both sides
  have hball : ball x s ⊆ Ω := (ball_subset_ball hsR.2.le).trans hR
  have hi1 : IntegrableOn (fun y => ‖gradient u y‖ ^ 2) (ball x s) :=
    IntegrableOn.of_bound measure_ball_lt_top hgrad2.aestronglyMeasurable ((Cg : ℝ) ^ 2)
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq y (hball hy)))
  have hi2 : IntegrableOn χ (ball x s) :=
    IntegrableOn.of_bound measure_ball_lt_top (h.aestronglyMeasurable_chi measurableSet_ball hball)
      1 ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hball hy)))
  have hLHS : ∫ y in ball x s, G y =
      ((n : ℝ) - 2) * (∫ y in ball x s, ‖gradient u y‖ ^ 2) + n * ∫ y in ball x s, χ y := by
    rw [hGdef, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
      integral_const_mul]
  have hRHS : sphereIntegral g x s = s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y -
      2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s := by
    rw [← sphereIntegral_const_mul]
    refine sphereIntegral_congr hsR.1.le fun y hy => ?_
    rw [mem_sphere, dist_eq_norm] at hy
    rw [hgdef]; simp only [hνdef, hy]
  rw [← hLHS, ← hRHS]
  exact heq

end IsVariationalSolution

end InnerVariational
