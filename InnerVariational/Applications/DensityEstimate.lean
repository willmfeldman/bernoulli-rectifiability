/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Density
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Basic.SphereIntegral

/-!
# Lemma 9.2: positive density of `{u > 0}` at free boundary points

Lemma 9.2 of Kriventsov–Weiss (full reference below). Let `(u, χ_{u>0})` be a variational solution
on `B_r(x)` with constant `C_V`, and `x ∈ ∂{u > 0}`. Then `|{u > 0} ∩ B_r(x)| ≥ c r^n` with
`c = c(n, C_V) > 0`.

We prove it with the explicit constant `c = |B_1| / (2 (1 + C_V²))` and `2 ≤ n` (Lemma 8.1 uses
Sperner's inequality, which needs `n ≥ 2`).

## Proof

By Lemma 8.1 (`half_le_Mzero_of_mem_frontier`), `M_x(0+) ≥ |B_1|/2`. For `0 < s < r`, monotonicity
gives `M_x(0+) ≤ M_x(s) ≤ D_x(s) = s^{-n} ∫_{B_s(x)} (|∇u|² + χ_{u>0})`. On `{u = 0}` the
integrand vanishes (`∇u = 0` at a minimum), and elsewhere it is at most `1 + C_V²`. So
`|B_1| s^n / 2 ≤ (1 + C_V²) |{u > 0} ∩ B_r(x)|`, and we let `s → r`. The paper works at `s = r`
directly; since the monotonicity formula is used here only at radii `s` with `B̄_s(x)` inside the
domain (at larger radii `M_x(s)` would involve values of `u` outside it), we pass to the limit
instead.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {C : ℝ≥0} {u : Rn n → ℝ} {x : Rn n} {r : ℝ}

/-- The energy of a one-phase solution on a ball `B_s(x) ⊆ Ω` is at most
`(1 + C_V²) |{u > 0} ∩ B_s(x)|`. -/
theorem setIntegral_energy_le {Ω : Set (Rn n)} (h : IsVariationalSolution Ω C u (posIndicator u))
    {s : ℝ} (hs : ball x s ⊆ Ω) :
    ∫ y in ball x s, (‖gradient u y‖ ^ 2 + posIndicator u y) ≤
      (1 + (C : ℝ) ^ 2) * volume.real (ball x s ∩ {y | 0 < u y}) := by
  have hH := h.isLipHarmonicPos
  set S : Set (Rn n) := ball x s ∩ {y | 0 < u y} with hSdef
  have hSo : IsOpen S := h.continuousOn.mono hs |>.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hpt : ∀ y ∈ ball x s, ‖gradient u y‖ ^ 2 + posIndicator u y ≤
      (1 + (C : ℝ) ^ 2) * S.indicator 1 y := by
    intro y hy
    rcases (h.nonneg y (hs hy)).lt_or_eq with hpos | h0
    · rw [posIndicator_of_pos hpos, indicator_of_mem (show y ∈ S from ⟨hy, hpos⟩), Pi.one_apply,
        mul_one, add_comm]
      gcongr
      exact h.norm_gradient_le (hs hy)
    · rw [posIndicator_of_nonpos h0.symm.le, hH.gradient_eq_zero_of_eq_zero (hs hy) h0.symm,
        indicator_of_notMem (fun h' => by have := h'.2; simp [← h0] at this)]
      simp
  calc ∫ y in ball x s, (‖gradient u y‖ ^ 2 + posIndicator u y)
      ≤ ∫ y in ball x s, (1 + (C : ℝ) ^ 2) * S.indicator 1 y := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_ball hpt
        · refine IntegrableOn.of_bound measure_ball_lt_top
            (((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable.add ?_)
            ((C : ℝ) ^ 2 + 1) ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
          · have hae : S.indicator (1 : Rn n → ℝ) =ᵐ[volume.restrict (ball x s)]
                posIndicator u := by
              refine (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_)
              by_cases hpos : 0 < u y
              · rw [posIndicator_of_pos hpos, indicator_of_mem (show y ∈ S from ⟨hy, hpos⟩)]
                rfl
              · rw [posIndicator_of_nonpos (not_lt.1 hpos),
                  indicator_of_notMem (fun h' => hpos h'.2)]
            exact (Measurable.aestronglyMeasurable
              (measurable_one.indicator hSo.measurableSet)).congr hae
          · have h1 := hpt y hy
            have h2 : S.indicator (1 : Rn n → ℝ) y ≤ 1 := by
              by_cases hyS : y ∈ S <;> simp [hyS]
            have h3 : 0 ≤ posIndicator u y := by
              rw [posIndicator]; exact indicator_nonneg (fun _ _ => zero_le_one) y
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            nlinarith [sq_nonneg (C : ℝ)]
        · exact ((integrableOn_const (s := S) (C := (1 : ℝ))
            (measure_ne_top_of_subset inter_subset_left
              measure_ball_lt_top.ne)).integrable_indicator
            hSo.measurableSet).const_mul _ |>.integrableOn
    _ = (1 + (C : ℝ) ^ 2) * volume.real S := by
        have hSB : S ∩ ball x s = S := inter_eq_left.2 inter_subset_left
        rw [integral_const_mul, integral_indicator_one hSo.measurableSet,
          measureReal_restrict_apply hSo.measurableSet, hSB]

/-- **Lemma 9.2** of Kriventsov–Weiss. Let `2 ≤ n`, and let `(u, χ_{u>0})`
be a variational solution on `B_r(x)`, `r > 0`, with constant `C_V`, and `x ∈ ∂{u > 0}`. Then
`|{u > 0} ∩ B_r(x)| ≥ c r^n` with `c = |B_1| / (2 (1 + C_V²))`. -/
theorem le_volume_pos_inter_ball [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution (ball x r) C u (posIndicator u)) (hr : 0 < r)
    (hx : x ∈ frontier {y | 0 < u y}) :
    unitBallVolume n / (2 * (1 + (C : ℝ) ^ 2)) * r ^ n ≤
      volume.real (ball x r ∩ {y | 0 < u y}) := by
  obtain ⟨m, hmM, hm, -⟩ := h.half_le_Mzero_of_mem_frontier hn (mem_ball_self hr) hx
  have hC : 0 < 1 + (C : ℝ) ^ 2 := by positivity
  -- the bound at every `s ∈ (0, r)`
  have hs : ∀ s ∈ Ioo 0 r, unitBallVolume n / (2 * (1 + (C : ℝ) ^ 2)) * s ^ n ≤
      volume.real (ball x r ∩ {y | 0 < u y}) := by
    rintro s ⟨hs0, hsr⟩
    have hM : m ≤ monotonicityM u (posIndicator u) x s := by
      have := h.Mzero_le subset_rfl hs0 hsr
      rwa [hmM, EReal.coe_le_coe_iff] at this
    have hsub : ball x s ⊆ ball x r := ball_subset_ball hsr.le
    have hE := h.setIntegral_energy_le hsub
    have hV : volume.real (ball x s ∩ {y | 0 < u y}) ≤ volume.real (ball x r ∩ {y | 0 < u y}) :=
      measureReal_mono (inter_subset_inter_left _ hsub)
        (measure_ne_top_of_subset inter_subset_left measure_ball_lt_top.ne)
    have hD : monotonicityM u (posIndicator u) x s ≤
        (s ^ n)⁻¹ * ∫ y in ball x s, (‖gradient u y‖ ^ 2 + posIndicator u y) := by
      rw [monotonicityM, energyD]
      have hH0 : 0 ≤ heightH u x s := mul_nonneg (inv_nonneg.2 (pow_nonneg hs0.le _))
        (sphereIntegral_nonneg hs0.le fun _ _ => sq_nonneg _)
      linarith
    have hsn : 0 < s ^ n := pow_pos hs0 n
    have key : unitBallVolume n / 2 * s ^ n ≤
        (1 + (C : ℝ) ^ 2) * volume.real (ball x r ∩ {y | 0 < u y}) := by
      have h1 : unitBallVolume n / 2 ≤
          (s ^ n)⁻¹ * ((1 + (C : ℝ) ^ 2) * volume.real (ball x r ∩ {y | 0 < u y})) :=
        hm.trans (hM.trans (hD.trans (mul_le_mul_of_nonneg_left (hE.trans
          (mul_le_mul_of_nonneg_left hV hC.le)) (inv_nonneg.2 hsn.le))))
      rwa [inv_mul_eq_div, le_div_iff₀ hsn] at h1
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- let `s → r`
  have hlim : Tendsto (fun s : ℝ => unitBallVolume n / (2 * (1 + (C : ℝ) ^ 2)) * s ^ n)
      (𝓝[<] r) (𝓝 (unitBallVolume n / (2 * (1 + (C : ℝ) ^ 2)) * r ^ n)) :=
    ((continuous_pow n).tendsto r |>.mono_left nhdsWithin_le_nhds).const_mul _
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsLT hr] with t ht using hs t ht)

end IsVariationalSolution

end InnerVariational
