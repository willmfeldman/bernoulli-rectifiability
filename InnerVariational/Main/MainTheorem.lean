/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Main.Laplacian
public import InnerVariational.Singular.Chi
import InnerVariational.Main.Distributional
import InnerVariational.Main.Covering
public import InnerVariational.Defs.LaplacianMeasure
import InnerVariational.Singular.Density
import InnerVariational.NaberValtorta.MainFrequency
import InnerVariational.Registry.GMT
import InnerVariational.Monotonicity.HighestDensity
import InnerVariational.Monotonicity.Radial
import InnerVariational.Kernel.BV
public import InnerVariational.Defs.VariationalSolution

/-!
# The main theorem, Theorem 1.2

Theorem 1.2 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), assembled as in the
paper's proof of Theorem 1.2 (end of §8). Each theorem here has exactly the statement of the
corresponding `Statements.main_theorem_*`, which is proved from it.

* (i) is Theorem 8.6 (`Singular/Chi.lean`).
* (ii) is the first part of Theorem 8.7, proved in `Main/Distributional.lean` without Laplacian
  measures.
* (iii) is the second part of Theorem 8.7 (`Main/Laplacian.lean`).
* (iv) (`main_theorem_iv`): off `Σ^H`, `∂{u > 0} \ ∂*{u > 0}` is `ℋ^{n-1}`-null, by the
  De Giorgi–Federer structure theorem for sets of locally finite perimeter. On `Σ^H`, the first
  display equals `N_x(u; r)` (`ratio_energy_eq_frequencyN`), which tends to `1` a.e. by
  Theorem 7.2 (3). The second display, with the factor `√(H_x(u; r))` (see `main_theorem_iv`),
  equals
  `(r^n H_x(u; r))⁻¹ ∫_{B_r(x)} |∇u − √(H_x(u;r)) α(n) ∇|(y−x)·ν||²` (`ratio_eq_div`), which
  tends to `0` a.e. by Lemma 8.5 (1).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Main

variable {n : ℕ} {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-! ### Algebra for Theorem 1.2 (iv) -/

/-- `∫_{∂B_r(x)} u² = r^{n+1} H_x(u; r)` for `r > 0`. -/
theorem sphereIntegral_sq_eq_mul_heightH (u : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    sphereIntegral (fun y => u y ^ 2) x r = r ^ (n + 1) * heightH u x r := by
  rw [heightH, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

/-- The first display of Theorem 1.2 (iv) is the frequency:
`r ∫_{B_r(x)} (|∇u|² + χ − 1) / ∫_{∂B_r(x)} u² = N_x(u; r)` when `B_r(x) ⊆ Ω`. Both sides use the
denominator `H_x(u; r)`, so no sign condition is needed (where `H_x(u; r) = 0` both sides are `0`
by Lean's convention `a / 0 = 0`; the paper sets `N = −∞` there). -/
theorem ratio_energy_eq_frequencyN (h : IsVariationalSolution Ω C u χ) {x : Rn n} {r : ℝ}
    (hr : 0 < r) (hB : ball x r ⊆ Ω) :
    r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
        sphereIntegral (fun y => u y ^ 2) x r = frequencyN u χ x r := by
  have h1 : IntegrableOn (fun _ : Rn n => (1 : ℝ)) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have hint : (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) =
      (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y)) - ∫ _ in ball x r, (1 : ℝ) :=
    integral_sub ((h.integrableOn_norm_gradient_sq hB).add (h.integrableOn_chi hB)) h1
  have hone : (∫ _ in ball x r, (1 : ℝ)) = r ^ n * unitBallVolume n := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, volume_ball_toReal x hr]
  have hE : (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y)) = r ^ n * energyD u χ x r := by
    rw [energyD, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
  rw [hint, hone, hE, sphereIntegral_sq_eq_mul_heightH u x hr, frequencyN, ← mul_sub,
    ← mul_assoc, ← pow_succ']
  exact mul_div_mul_left _ _ (pow_ne_zero _ hr.ne')

/-- `r I / ∫_{∂B_r(x)} u² = I / (r^n H_x(u; r))` for `r > 0`: the second display of
Theorem 1.2 (iv) is the gradient part of Lemma 8.5 (1) with `R = 1`. -/
theorem ratio_eq_div (u : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r) (I : ℝ) :
    r * I / sphereIntegral (fun y => u y ^ 2) x r = I / (r ^ n * heightH u x r) := by
  rw [sphereIntegral_sq_eq_mul_heightH u x hr, pow_succ', mul_assoc]
  exact mul_div_mul_left _ _ hr.ne'

/-! ### The regular part of Theorem 1.2 (iv) -/

/-- **Structure theorem for `BV_loc`, local form**, restated from
`Registry.hasLocallyFinitePerimeter_of_local` (proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0). If a measurable `E` satisfies, near each
point of the open set `U`, a bound `|∫_E div φ| ≤ C sup|φ|` for `φ ∈ C^∞_c(B_r(x); ℝⁿ)`, then `E`
has a Gauss–Green pair on all of `U`. This is the structure theorem for `χ_E ∈ BV_loc(U)`
(L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed., CRC
Press, 2015, Theorem 5.1), whose hypothesis is local; the global form
`Registry.exists_isGaussGreenPair_of_integral_divergence_le` needs a bound on all of `U`. It is
needed because `reducedBoundary Ω E` is empty unless a pair exists on all of `Ω`. -/
theorem hasLocallyFinitePerimeter_of_local (hn : 2 ≤ n) {U E : Set (Rn n)} (hU : IsOpen U)
    (hE : MeasurableSet E)
    (h : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ C : ℝ, ∀ φ : Rn n → Rn n,
      IsSmoothTestField (ball x r) φ → |∫ y in E, divergence φ y| ≤ C * ⨆ y, ‖φ y‖) :
    HasLocallyFinitePerimeter U E :=
  Registry.hasLocallyFinitePerimeter_of_local hn hU hE h

/-- `Ω ∩ {χ = 1}` has locally finite perimeter in `Ω` (Lemma 3.3, with the local form of the
structure theorem, `hasLocallyFinitePerimeter_of_local`). -/
theorem hasLocallyFinitePerimeter_chi (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    HasLocallyFinitePerimeter Ω (Ω ∩ {y | χ y = 1}) := by
  have : NeZero n := ⟨by omega⟩
  refine hasLocallyFinitePerimeter_of_local hn h.isOpen h.measurableSet_chi_eq_one
    fun x hx => ?_
  obtain ⟨r, hr, hB⟩ := exists_closedBall_two_mul_subset h.isOpen hx
  refine ⟨3 * r / 2, by positivity,
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hB,
    2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * r ^ (n - 1), fun φ hφ => ?_⟩
  refine (h.abs_setIntegral_divergence_le hr hB hφ).trans_eq ?_
  ring

/-- A point of `Ω ∩ ∂{u > 0}` has points of `{u > 0}` in every ball inside `Ω`; so if `u ≡ 0` on
`Ω`, then `Ω ∩ ∂{u > 0} = ∅`. -/
theorem inter_frontier_pos_eq_empty_of_eq_zero (h : IsVariationalSolution Ω C u χ)
    (h0 : ∀ x ∈ Ω, u x = 0) : Ω ∩ frontier {y | 0 < u y} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x ⟨hxΩ, hxf⟩ => ?_
  obtain ⟨hcl, -⟩ := (h.mem_frontier_pos_iff hxΩ).1 hxf
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hxΩ
  obtain ⟨z, hz, hzpos⟩ := mem_closure_iff_nhds.1 hcl (ball x δ) (ball_mem_nhds x hδ)
  have hz0 : u z = 0 := h0 z (hδΩ hz)
  have hzpos' : 0 < u z := hzpos
  linarith

/-- Off `Σ^H`, `ℋ^{n-1}`-a.e. point of `Ω ∩ ∂{u > 0}` is in the reduced boundary `∂*{u > 0}`.
By Theorem 8.6 either `u ≡ 0` (no free boundary) or `χ = χ_{u>0}` a.e.; in the second case
`∂{u > 0} \ Σ^H ⊆ ∂ᵉ{χ = 1}` (`frontier_pos_diff_sigmaH_subset_essentialBoundary`), and the
De Giorgi–Federer structure theorem on `Ω` (H. Federer, *Geometric Measure Theory*, Springer,
1969, 4.5.6; proved in gmt-foundations), with the global perimeter pair of
`hasLocallyFinitePerimeter_chi`, gives `ℋ^{n-1}(∂ᵉ{χ = 1} \ ∂*{χ = 1}) = 0`, while
`∂*{χ = 1} = ∂*{u > 0}`. The paper's proof of Theorem 1.2 (iv) cites only Lemma 8.5 and
Theorem 7.2 and leaves this step implicit; the dimension bound of Corollary 8.4 would also give
it. -/
theorem hausdorffN_frontier_diff_sigmaH_diff_reducedBoundary_eq_zero (hn : 2 ≤ n)
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C u χ) :
    hausdorffN n (n - 1) {x | x ∈ Ω ∩ frontier {y | 0 < u y} ∧ x ∉ sigmaH Ω u χ ∧
      x ∉ reducedBoundary Ω {y | 0 < u y}} = 0 := by
  rcases Singular.chi_eq_indicator hn hΩ h with h0 | hae
  · refine measure_mono_null (fun x hx => ?_) measure_empty
    rw [← inter_frontier_pos_eq_empty_of_eq_zero h h0]
    exact hx.1
  have hEE : (Ω ∩ (Ω ∩ {y | χ y = 1}) : Set (Rn n)) =ᵐ[volume]
      (Ω ∩ {y | 0 < u y} : Set (Rn n)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' h.isOpen.measurableSet] at hae
    filter_upwards [hae] with y hy
    refine propext ⟨fun hy' => ⟨hy'.1, ?_⟩, fun hy' => ?_⟩
    · have hχ := hy hy'.1
      rw [hy'.2.2] at hχ
      by_contra hp
      rw [posIndicator_of_nonpos (not_lt.1 hp)] at hχ
      exact one_ne_zero hχ
    · have hχ := hy hy'.1
      rw [posIndicator_of_pos hy'.2] at hχ
      exact ⟨hy'.1, hy'.1, hχ⟩
  obtain ⟨μ, ν, hpair⟩ := hasLocallyFinitePerimeter_chi hn h
  have hR9 := (Registry.HasLocallyFinitePerimeter.rectifiable_essentialBoundary hn h.isOpen
    h.measurableSet_chi_eq_one ⟨μ, ν, hpair⟩).2.1
  refine measure_mono_null ?_ hR9
  rintro x ⟨hxS, hxH, hxR⟩
  exact ⟨⟨hxS.1, frontier_pos_diff_sigmaH_subset_essentialBoundary hn h ⟨hxS, hxH⟩⟩,
    fun hxE => hxR (reducedBoundary_subset_of_ae_eq h.isOpen.measurableSet hEE hxE)⟩

/-! ### Theorem 1.2 -/

/-- **Theorem 1.2 (i)**, from Theorem 8.6. -/
theorem main_theorem_i (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    (∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u :=
  Singular.chi_eq_indicator hn hΩ h

/-- **Theorem 1.2 (ii)**. The topological free boundary `Ω ∩ ∂{u > 0}` is
countably `ℋ^{n-1}`-rectifiable and has locally finite `ℋ^{n-1}`-measure. Connectedness is not
needed (`rectifiable_and_locallyFinite_frontier_pos`). -/
theorem main_theorem_ii [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (_hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞ :=
  rectifiable_and_locallyFinite_frontier_pos hn h

/-- **Theorem 1.2 (iii)**, from Theorem 8.7, in its form: with `Σ^H` and the unaveraged
`H_x(u; 0+)` (the introduction states (iii) with `Σ_**` and a spherically averaged `H_x`; we use
the form of Theorem 8.7; see `Statements.main_theorem_iii`). -/
theorem main_theorem_iii [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (_hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ) :=
  (laplacian_measure_eq hn h).2.2

/-- **Theorem 1.2 (iv)**, with the factor `√(H_x(u; r))` in the second display (without it, as
printed, the statement fails for `u = 2α(n)|y_n|`, `χ ≡ 1`). The exceptional set is
covered by three `ℋ^{n-1}`-null sets: `(∂{u>0} \ Σ^H) \ ∂*{u>0}`
(`hausdorffN_frontier_diff_sigmaH_diff_reducedBoundary_eq_zero`), the points of `Σ^H` where
`N_x(u; 0+) ≠ 1` (Theorem 7.2 (3)), and the points of `Σ^H` where Lemma 8.5 (1) fails. -/
theorem main_theorem_iv [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    hausdorffN n (n - 1) {x | x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      x ∉ reducedBoundary Ω {y | 0 < u y} ∧
      ¬ (Tendsto (fun r => r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
            sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 1) ∧
          ∃ ν : Rn n, ‖ν‖ = 1 ∧
            Tendsto (fun r => r * (∫ y in ball x r,
                ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
              sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 0))} = 0 := by
  refine measure_mono_null ?_ (measure_union_null (measure_union_null
    (hausdorffN_frontier_diff_sigmaH_diff_reducedBoundary_eq_zero hn hΩ h)
    (NaberValtorta.hausdorffN_not_tendsto_frequencyN_eq_zero hn h))
    (Singular.renormalized_tendsto_alpha_ae hn h))
  rintro x ⟨hxΩ, hxf, hxR, hx⟩
  by_cases hxS : x ∈ sigmaH Ω u χ
  swap
  · exact Or.inl (Or.inl ⟨⟨hxΩ, hxf⟩, hxS, hxR⟩)
  by_cases hN : Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)
  swap
  · exact Or.inl (Or.inr ⟨hxS, hN⟩)
  refine Or.inr ⟨hxS, fun ⟨ν, hν, hR⟩ => hx ⟨?_, ν, hν, ?_⟩⟩
  · obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hxΩ
    refine hN.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    exact (ratio_energy_eq_frequencyN h hr.1 ((ball_subset_ball hr.2.le).trans hδΩ)).symm
  · refine (hR 1 one_pos).2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [one_mul, ratio_eq_div u x hr]

/-- **Theorem 1.2**, the conjunction of (i)–(iv), with exactly the statement of
`Statements.main_theorem`. -/
theorem main_theorem [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    ((∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u) ∧
    (IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞) ∧
    HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ) ∧
    hausdorffN n (n - 1) {x | x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      x ∉ reducedBoundary Ω {y | 0 < u y} ∧
      ¬ (Tendsto (fun r => r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
            sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 1) ∧
          ∃ ν : Rn n, ‖ν‖ = 1 ∧
            Tendsto (fun r => r * (∫ y in ball x r,
                ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
              sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 0))} = 0 :=
  ⟨main_theorem_i hn hΩ h, main_theorem_ii hn hΩ h, main_theorem_iii hn hΩ h,
    main_theorem_iv hn hΩ h⟩

end InnerVariational.Main
