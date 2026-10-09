/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import InnerVariational.Kernel.VariationalQ
public import InnerVariational.Regular.ZeroGradient
import InnerVariational.Kernel.BV
import InnerVariational.Monotonicity.DensityQ

/-!
# `χ` on the interior of the zero set, with a Lipschitz coefficient

The start of §8.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure,
and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for a variational
solution `(u, χ)` on `Ω` with a coefficient `Q`, `QBounds Ω Q L c C'`. The paper treats `Q ≡ 1`.
On an open set `U ⊆ Ω` where `u ≡ 0`, the inner variation reduces to `∫ χ div (Q² ξ) = 0`; since
every test field is of the form `Q² ξ` (take `Q⁻² ξ`), `∫ χ div ξ = 0` for
`ξ ∈ C^{0,1}_c(U; ℝⁿ)`. Hence `χ` is a.e. constant, equal to `0` or `1`, on each connected open
subset of `{u = 0}°`, and `M^{Q(x)}_x(u; 0+) ∈ {0, Q(x)² |B_1|}` there.

## Main statements

* `IsVariationalSolutionQ.integral_chi_mul_divergence_eq_zero`: `∫ χ div ξ = 0` for test fields
  supported in an open set where `u = 0`.
* `IsVariationalSolutionQ.exists_ae_eq_const_of_eq_zero`: if `u = 0` on a preconnected open
  `U ⊆ Ω`, then `χ = c` a.e. on `U` with `c ∈ {0, 1}`.
* `IsVariationalSolutionQ.MzeroQ_eq_of_ae_eq_const`: `M^{Q(x)}_x(u; 0+) = Q(x)² c |B_1|` when
  `χ = c` a.e. near `x`.

The paper treats the case `Q ≡ 1`.
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

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- On an open set `U ⊆ Ω` with `u = 0`, `∫ χ div ξ = 0` for `ξ ∈ C^{0,1}_c(U; ℝⁿ)` (start of
§8.1): the key identity for the test field `Q⁻² ξ`, whose quadratic part vanishes because `∇u = 0`
on `U`. -/
theorem integral_chi_mul_divergence_eq_zero (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {U : Set (Rn n)} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (hu : ∀ y ∈ U, u y = 0) {ξ : Rn n → Rn n} (hξ : IsLipTestField U ξ) :
    ∫ y, χ y * divergence ξ y = 0 := by
  have hξ' := (hQ.mono hUΩ).isLipTestField_inv_sq_smul hξ
  have e := h.integral_chi_mul_divergence_sq_smul_eq hQ (hξ'.mono hUΩ)
  rw [(hQ.mono hUΩ).sq_smul_inv_sq_smul hξ.2.2] at e
  rw [e, neg_eq_zero]
  have h0 : ∀ y, Kernel.gradVariation u (fun z => (Q z ^ 2)⁻¹ • ξ z) y = 0 := by
    intro y
    by_cases hy : y ∈ U
    · exact Kernel.gradVariation_eq_zero_of_gradient_eq_zero
        (Regular.gradient_eq_zero_of_eventuallyEq
          (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) fun z hz => hu z hz))
    · exact Kernel.gradVariation_eq_zero_of_notMem_tsupport fun h' => hy (hξ'.2.2 h')
  simp [h0]

/-- `χ` is locally integrable on every open `U ⊆ Ω` (it is measurable with `|χ| ≤ 1`). -/
theorem locallyIntegrableOn_chi (h : IsVariationalSolutionQ Ω C Q u χ) {U : Set (Rn n)}
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) : LocallyIntegrableOn χ U := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  exact IntegrableOn.of_bound hK.measure_lt_top
    (h.aestronglyMeasurable_chi hK.measurableSet (hKU.trans hUΩ)) 1
    ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hUΩ (hKU hy))))

/-- **`u ≡ 0 ⇒ χ` a.e. constant** (start of §8.1). If `u = 0` on a preconnected open `U ⊆ Ω`,
then `χ = c` a.e. on `U` for some `c ∈ {0, 1}`. -/
theorem exists_ae_eq_const_of_eq_zero (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {U : Set (Rn n)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUΩ : U ⊆ Ω) (hu : ∀ y ∈ U, u y = 0) :
    ∃ c₀ : ℝ, (c₀ = 0 ∨ c₀ = 1) ∧ ∀ᵐ y ∂(volume.restrict U), χ y = c₀ := by
  obtain ⟨c₀, hc⟩ := Regular.exists_ae_eq_const_of_integral_mul_divergence_eq_zero hU hUc
    (h.locallyIntegrableOn_chi hU hUΩ) fun ξ hξ =>
      h.integral_chi_mul_divergence_eq_zero hQ hU hUΩ hu hξ.isLipTestField
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, Or.inl rfl, by simp⟩
  have hne' : (ae (volume.restrict U)).NeBot :=
    ae_neBot.2 fun h0 => (hU.measure_pos volume hne).ne' (Measure.restrict_eq_zero.1 h0)
  obtain ⟨y, hyU, hy⟩ := ((ae_restrict_mem hU.measurableSet).and hc).exists
  refine ⟨c₀, ?_, hc⟩
  rw [← hy]
  exact h.chi_mem y (hUΩ hyU)

/-- `M^{Q(x)}_x(u; 0+) = Q(x)² c |B_1|` when `u(x) = 0` and `χ = c` a.e. near `x` (the analogue of
Proposition 3.5, (3.10)). -/
theorem MzeroQ_eq_of_ae_eq_const [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {x : Rn n} (hx : x ∈ Ω) (hux : u x = 0) {δ : ℝ} (hδ : 0 < δ)
    {c₀ : ℝ} (hc : ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = c₀) :
    MzeroQ (Q x) u χ x = ((Q x ^ 2 * (c₀ * unitBallVolume n) : ℝ) : EReal) := by
  obtain ⟨m, hm, -, hd⟩ := h.tendsto_monotonicityMq_zero hQ hx hux
  rw [hm, tendsto_nhds_unique hd
    ((Regular.tendsto_density_of_ae_eq_const hδ hc).const_mul (Q x ^ 2))]

end IsVariationalSolutionQ

end InnerVariational
