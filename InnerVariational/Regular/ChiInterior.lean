/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Kernel.BV
public import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.Density
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Kernel.RellichPohozaev

/-!
# `χ` on the interior of the zero set

The start of §8.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure,
and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on `Ω`. On an open set `U ⊆ Ω` where `u ≡ 0`, the inner variation
(equation (3.5)) reduces to `∫ χ div ξ = 0` for `ξ ∈ C^{0,1}_c(U; ℝⁿ)`. Hence `χ` is a.e.
constant, equal to `0` or `1`, on each connected open subset of `{u = 0}°`. Correspondingly
`M_x(u; 0+) = 0` (the "natural" case) or `M_x(u; 0+) = |B_1|` (the "pathological" case, e.g.
`(u, χ) = (0, 1)`) there.

## Main statements

* `IsVariationalSolution.integral_chi_mul_divergence_eq_zero`: `∫ χ div ξ = 0` for test fields
  supported in an open set where `u = 0`.
* `IsVariationalSolution.exists_ae_eq_const_of_eq_zero`: if `u = 0` on a preconnected open
  `U ⊆ Ω`, then `χ = c` a.e. on `U` with `c ∈ {0, 1}`.
* `IsVariationalSolution.chi_ae_eq_const_connectedComponentIn`: the paper's form, on each
  connected component of `Ω ∩ {u = 0}°`.
* `IsVariationalSolution.Mzero_eq_of_ae_eq_const`,
  `IsVariationalSolution.Mzero_mem_of_mem_interior`: `M_x(u; 0+) = c |B_1|` when `χ = c` a.e.
  near `x`; so `M_x(u; 0+) ∈ {0, |B_1|}` on `{u = 0}°`.

The constancy step is the "zero distributional gradient" fact
(`exists_ae_eq_const_of_hasWeakGrad_zero`, in divergence form in `Regular/ZeroGradient.lean`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-- `∇u(y) = 0` when `u = 0` near `y`. -/
theorem gradient_eq_zero_of_eventuallyEq {u : Rn n → ℝ} {y : Rn n}
    (h : u =ᶠ[𝓝 y] fun _ => 0) : gradient u y = 0 := by
  simp [gradient, h.fderiv_eq]

/-- If `χ = c` a.e. on `B_δ(x)`, then `r^{-n} ∫_{B_r(x)} χ → c |B_1|` as `r → 0+` (the integral is
`c |B_r| = c r^n |B_1|` for `r < δ`). -/
theorem tendsto_density_of_ae_eq_const {χ : Rn n → ℝ} {x : Rn n} {δ : ℝ} (hδ : 0 < δ) {c : ℝ}
    (hc : ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = c) :
    Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0)
      (𝓝 (c * unitBallVolume n)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hsub : ball x r ⊆ ball x δ := ball_subset_ball hr.2.le
  have e : ∫ y in ball x r, χ y = ∫ y in ball x r, c :=
    setIntegral_congr_ae measurableSet_ball
      ((ae_restrict_iff' measurableSet_ball).1 (ae_restrict_of_ae_restrict_of_subset hsub hc))
  have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.1.ne'
  rw [e, setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hr.1]
  field_simp

end Regular

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-- On an open set `U ⊆ Ω` with `u = 0`, the inner variation reduces to `∫ χ div ξ = 0` for
`ξ ∈ C^{0,1}_c(U; ℝⁿ)` (start of §8.1), because `∇u = 0` on `U`. -/
theorem integral_chi_mul_divergence_eq_zero (h : IsVariationalSolution Ω C u χ) {U : Set (Rn n)}
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) (hu : ∀ y ∈ U, u y = 0) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField U ξ) : ∫ y, χ y * divergence ξ y = 0 := by
  rw [h.integral_chi_mul_divergence_eq (hξ.mono hUΩ), neg_eq_zero]
  have h0 : ∀ y, Kernel.gradVariation u ξ y = 0 := by
    intro y
    by_cases hy : y ∈ U
    · exact Kernel.gradVariation_eq_zero_of_gradient_eq_zero
        (Regular.gradient_eq_zero_of_eventuallyEq
          (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) fun z hz => hu z hz))
    · exact Kernel.gradVariation_eq_zero_of_notMem_tsupport fun h' => hy (hξ.2.2 h')
  simp [h0]

/-- `χ` is locally integrable on every open `U ⊆ Ω` (it is measurable with `|χ| ≤ 1`). -/
theorem locallyIntegrableOn_chi (h : IsVariationalSolution Ω C u χ) {U : Set (Rn n)}
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) : LocallyIntegrableOn χ U := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  exact IntegrableOn.of_bound hK.measure_lt_top
    (h.aestronglyMeasurable_chi hK.measurableSet (hKU.trans hUΩ)) 1
    ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hUΩ (hKU hy))))

/-- **`u ≡ 0 ⇒ χ` a.e. constant** (start of §8.1). If `u = 0` on a preconnected open `U ⊆ Ω`,
then `χ = c` a.e. on `U` for some `c ∈ {0, 1}`. -/
theorem exists_ae_eq_const_of_eq_zero (h : IsVariationalSolution Ω C u χ) {U : Set (Rn n)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUΩ : U ⊆ Ω) (hu : ∀ y ∈ U, u y = 0) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧ ∀ᵐ y ∂(volume.restrict U), χ y = c := by
  obtain ⟨c, hc⟩ := Regular.exists_ae_eq_const_of_integral_mul_divergence_eq_zero hU hUc
    (h.locallyIntegrableOn_chi hU hUΩ) fun ξ hξ =>
      h.integral_chi_mul_divergence_eq_zero hU hUΩ hu hξ.isLipTestField
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, Or.inl rfl, by simp⟩
  have hne' : (ae (volume.restrict U)).NeBot :=
    ae_neBot.2 fun h0 => (hU.measure_pos volume hne).ne' (Measure.restrict_eq_zero.1 h0)
  obtain ⟨y, hyU, hy⟩ := ((ae_restrict_mem hU.measurableSet).and hc).exists
  refine ⟨c, ?_, hc⟩
  rw [← hy]
  exact h.chi_mem y (hUΩ hyU)

/-- **`χ` on `{u = 0}°`** (start of §8.1): `χ` is a.e. constant, equal to `0` or `1`, on each
connected component of `Ω ∩ {u = 0}°`. (For `x ∉ Ω ∩ {u = 0}°` the component is empty.) -/
theorem chi_ae_eq_const_connectedComponentIn (h : IsVariationalSolution Ω C u χ) (x : Rn n) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧ ∀ᵐ y ∂(volume.restrict
      (connectedComponentIn (Ω ∩ interior {y | u y = 0}) x)), χ y = c := by
  have hWo : IsOpen (Ω ∩ interior {y | u y = 0}) := h.isOpen.inter isOpen_interior
  exact h.exists_ae_eq_const_of_eq_zero hWo.connectedComponentIn
    isPreconnected_connectedComponentIn
    ((connectedComponentIn_subset _ _).trans inter_subset_left)
    fun y hy => (interior_subset (s := {y | u y = 0}) (connectedComponentIn_subset _ _ hy).2 :)

/-- `M_x(u; 0+) = c |B_1|` when `u(x) = 0` and `χ = c` a.e. near `x` (Proposition 3.5, (3.10)). -/
theorem Mzero_eq_of_ae_eq_const [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    (hx : x ∈ Ω) (hux : u x = 0) {δ : ℝ} (hδ : 0 < δ) {c : ℝ}
    (hc : ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = c) :
    Mzero u χ x = ((c * unitBallVolume n : ℝ) : EReal) := by
  obtain ⟨m, hm, -, hd⟩ := h.tendsto_monotonicityM_zero hx hux
  rw [hm, tendsto_nhds_unique hd (Regular.tendsto_density_of_ae_eq_const hδ hc)]

/-- `M_x(u; 0+) ∈ {0, |B_1|}` on `Ω ∩ {u = 0}°` (start of §8.1). -/
theorem Mzero_mem_of_mem_interior [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    (hx : x ∈ Ω) (hint : x ∈ interior {y | u y = 0}) :
    Mzero u χ x = 0 ∨ Mzero u χ x = unitBallVolume n := by
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 (h.isOpen.inter isOpen_interior) x ⟨hx, hint⟩
  obtain ⟨c, hc01, hc⟩ := h.exists_ae_eq_const_of_eq_zero isOpen_ball
    (convex_ball x δ).isPreconnected (hδsub.trans inter_subset_left)
    fun y hy => (interior_subset (s := {y | u y = 0}) (hδsub hy).2 :)
  rw [h.Mzero_eq_of_ae_eq_const hx (interior_subset (s := {y | u y = 0}) hint :) hδ hc]
  rcases hc01 with rfl | rfl
  · left; simp
  · right; simp

end IsVariationalSolution

end InnerVariational
