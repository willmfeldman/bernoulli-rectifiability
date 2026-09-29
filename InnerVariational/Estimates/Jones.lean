/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Discrete
public import InnerVariational.Basic.SphereIntegral
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.GMT

/-!
# Two bounds on the Jones number used by Theorem 6.1

The squared Jones number `jonesBetaSq μ x r = β²_μ(x, r)` (§6.1 of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131,
numbering of arXiv v2) is the infimum of
`jonesTerm μ x r p ν = r^{-(n-1)} ∫_{B_r(x)} ⟪y − p, ν⟫² / r² dμ(y)` over `p` and unit `ν`
(`NaberValtorta/Discrete.lean`). The proof of Theorem 6.1 of the paper uses:

* `jonesBetaSq_le_measure_ball`: `β²_μ(x, r) ≤ μ(B_r(x)) / r^{n-1}` (the hyperplane through `x`;
  the paper's "trivial case", where it normalizes `μ(B_1) = 1` and writes `β² ≤ 1`).
* `jonesBetaSq_mul_sq_norm_le`: for every `p` and every (not necessarily unit) `w`,
  `β²_μ(x, r) ‖w‖² ≤ r^{-(n-1)} ∫_{B_r(x)} ⟪y − p, w⟫² / r² dμ(y)`. With `w = ∇u(z)` this is the
  key display of the proof. The paper divides by `|∇u(z)|` and restricts to `z ∈ {u > 0}`; the
  homogeneous form needs neither.
* `jonesBetaSq_mul_lintegral_le`: the same inequality integrated over `z ∈ A` against Lebesgue
  measure, with the order of integration exchanged (Tonelli).

No rescaling lemma is needed: Theorem 6.1 is proved directly at scale `r` (see
`Estimates/L2Subspace.lean`), and the scaling lemmas needed in Section 7 are in `Discrete.lean`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

open NaberValtorta in
/-- `β²_μ(x, r) ≤ μ(B_r(x)) / r^{n-1}` for `n > 0`: test the hyperplane through `x`, on which
`⟪y − x, ν⟫² / r² ≤ ‖y − x‖² / r² < 1` for `y ∈ B_r(x)`. -/
theorem jonesBetaSq_le_measure_ball (hn : 0 < n) (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    jonesBetaSq μ x r ≤ μ (ball x r) / ENNReal.ofReal (r ^ (n - 1)) := by
  obtain ⟨ν, hν⟩ := exists_norm_eq_one hn
  refine (jonesBetaSq_le_jonesTerm μ x r x hν).trans ?_
  rw [jonesTerm]
  gcongr
  calc ∫⁻ y in ball x r, ENNReal.ofReal (⟪y - x, ν⟫ ^ 2 / r ^ 2) ∂μ
      ≤ ∫⁻ _ in ball x r, 1 ∂μ := by
        refine setLIntegral_mono measurable_const fun y hy => ?_
        rw [ENNReal.ofReal_le_one]
        have hy' : ‖y - x‖ < r := by rw [← dist_eq_norm]; exact hy
        have hr : 0 < r := (norm_nonneg _).trans_lt hy'
        rw [div_le_one (by positivity)]
        have h1 : |⟪y - x, ν⟫| ≤ ‖y - x‖ := by
          simpa [hν] using abs_real_inner_le_norm (y - x) ν
        have h2 : |⟪y - x, ν⟫| ≤ r := h1.trans hy'.le
        calc ⟪y - x, ν⟫ ^ 2 = |⟪y - x, ν⟫| ^ 2 := (sq_abs _).symm
          _ ≤ r ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = μ (ball x r) := by rw [setLIntegral_const, one_mul]

open NaberValtorta in
/-- `β²_μ(x, r) ‖w‖² ≤ r^{-(n-1)} ∫_{B_r(x)} ⟪y − p, w⟫² / r² dμ(y)` for all `p` and `w`
(proof of Theorem 6.1, homogeneous form): for `w ≠ 0` test the unit normal `ν = w / ‖w‖`. -/
theorem jonesBetaSq_mul_sq_norm_le (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) (p w : Rn n) :
    jonesBetaSq μ x r * ENNReal.ofReal (‖w‖ ^ 2) ≤
      (∫⁻ y in ball x r, ENNReal.ofReal (⟪y - p, w⟫ ^ 2 / r ^ 2) ∂μ) /
        ENNReal.ofReal (r ^ (n - 1)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ν : Rn n := ‖w‖⁻¹ • w with hνdef
  have hν : ‖ν‖ = 1 := by
    rw [hνdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0.ne']
  have hterm := jonesBetaSq_le_jonesTerm μ x r p hν
  have hpt : ∀ y, ENNReal.ofReal (⟪y - p, ν⟫ ^ 2 / r ^ 2) =
      ENNReal.ofReal ((‖w‖ ^ 2)⁻¹) * ENNReal.ofReal (⟪y - p, w⟫ ^ 2 / r ^ 2) := fun y => by
    rw [← ENNReal.ofReal_mul (by positivity), hνdef, real_inner_smul_right]
    congr 1
    field_simp
  have hI : ∫⁻ y in ball x r, ENNReal.ofReal (⟪y - p, ν⟫ ^ 2 / r ^ 2) ∂μ =
      ENNReal.ofReal ((‖w‖ ^ 2)⁻¹) *
        ∫⁻ y in ball x r, ENNReal.ofReal (⟪y - p, w⟫ ^ 2 / r ^ 2) ∂μ := by
    simp_rw [hpt]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [jonesTerm, hI] at hterm
  have hone : ENNReal.ofReal ((‖w‖ ^ 2)⁻¹) * ENNReal.ofReal (‖w‖ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
  calc jonesBetaSq μ x r * ENNReal.ofReal (‖w‖ ^ 2)
      ≤ ENNReal.ofReal ((‖w‖ ^ 2)⁻¹) *
          (∫⁻ y in ball x r, ENNReal.ofReal (⟪y - p, w⟫ ^ 2 / r ^ 2) ∂μ) /
            ENNReal.ofReal (r ^ (n - 1)) * ENNReal.ofReal (‖w‖ ^ 2) := by gcongr
    _ = ENNReal.ofReal ((‖w‖ ^ 2)⁻¹) * ENNReal.ofReal (‖w‖ ^ 2) *
          (∫⁻ y in ball x r, ENNReal.ofReal (⟪y - p, w⟫ ^ 2 / r ^ 2) ∂μ) /
            ENNReal.ofReal (r ^ (n - 1)) := by
        simp only [div_eq_mul_inv]; ring
    _ = _ := by rw [hone, one_mul]

/-- **The Fubini step in the proof of Theorem 6.1**. For a measurable `A` and a finite
measure `μ`,
`β²_μ(x, r) ∫_A ‖∇u‖² ≤ r^{-(n-1)} ∫_{B_r(x)} ∫_A ⟪∇u(z), y − p⟫² / r² dz dμ(y)`,
with all integrals in `ℝ≥0∞`. -/
theorem jonesBetaSq_mul_lintegral_le (μ : Measure (Rn n)) [IsFiniteMeasure μ] (x : Rn n) (r : ℝ)
    (p : Rn n) {A : Set (Rn n)} (u : Rn n → ℝ) :
    jonesBetaSq μ x r * ∫⁻ z in A, ENNReal.ofReal (‖gradient u z‖ ^ 2) ≤
      (∫⁻ y in ball x r, (∫⁻ z in A, ENNReal.ofReal (⟪gradient u z, y - p⟫ ^ 2 / r ^ 2)) ∂μ) /
        ENNReal.ofReal (r ^ (n - 1)) := by
  have hmeas : Measurable fun q : Rn n × Rn n =>
      ENNReal.ofReal (⟪q.2 - p, gradient u q.1⟫ ^ 2 / r ^ 2) :=
    ENNReal.measurable_ofReal.comp
      ((((measurable_snd.sub_const p).inner ((measurable_gradient u).comp measurable_fst)).pow_const
        2).div_const _)
  have hG : Measurable fun z => ∫⁻ y in ball x r,
      ENNReal.ofReal (⟪y - p, gradient u z⟫ ^ 2 / r ^ 2) ∂μ :=
    hmeas.lintegral_prod_right'
  calc jonesBetaSq μ x r * ∫⁻ z in A, ENNReal.ofReal (‖gradient u z‖ ^ 2)
      ≤ ∫⁻ z in A, jonesBetaSq μ x r * ENNReal.ofReal (‖gradient u z‖ ^ 2) :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ z in A, (∫⁻ y in ball x r,
          ENNReal.ofReal (⟪y - p, gradient u z⟫ ^ 2 / r ^ 2) ∂μ) / ENNReal.ofReal (r ^ (n - 1)) :=
        lintegral_mono fun z => jonesBetaSq_mul_sq_norm_le μ x r p (gradient u z)
    _ = (∫⁻ z in A, ∫⁻ y in ball x r,
          ENNReal.ofReal (⟪y - p, gradient u z⟫ ^ 2 / r ^ 2) ∂μ) /
          ENNReal.ofReal (r ^ (n - 1)) := by
        simp_rw [div_eq_mul_inv]
        exact lintegral_mul_const _ hG
    _ = _ := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
        simp_rw [real_inner_comm (gradient u _)]

end InnerVariational
