/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Reduction
public import Sperner.Cone
public import Sperner.Equality

/-!
# Sperner's inequality for one-homogeneous harmonic functions

**Theorem** (E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134
(1973), 317–327; here in homogeneous form). Let `n ≥ 2`, let `u ≥ 0` be Lipschitz and
one-homogeneous on `ℝⁿ`, and let `U` be the connected component of `{u > 0}` through `y₀`.
If `u` is harmonic on `U`, then `|U ∩ B₁| ≥ |B₁| / 2`. If equality holds, `U` is an open
half-space `{⟪y, e⟫ > 0}` and `u = a ⟪y, e⟫` on `U` for some `a > 0`.

Equivalently: a spherical domain carrying a positive Dirichlet eigenfunction with eigenvalue
`n - 1` has at least half the area of the sphere, with equality only for hemispheres.

The proof assembles
* `Sperner.Reduction`: truncate `u` to `U`;
* `Sperner.EnergyInequality`: the truncation has Gaussian Rayleigh quotient `≤ 1`;
* `Sperner.FaberKrahn`: positivity sets of Gaussian measure `< 1/2` force Rayleigh quotient `> 1`;
* `Sperner.Cone`: Gaussian measure of a cone vs. volume of its trace on `B₁`;
* `Sperner.Equality`: the equality case.
-/

open MeasureTheory Metric Set InnerProductSpace
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- **Sperner's inequality** (homogeneous form), with the equality case. -/
theorem sperner_half_volume (hn : 2 ≤ n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hLip : ∃ L, LipschitzWith L u) (hnn : ∀ y, 0 ≤ u y)
    (hhom : ∀ y (t : ℝ), 0 < t → u (t • y) = t * u y) {y₀ : EuclideanSpace ℝ (Fin n)}
    (hy₀ : 0 < u y₀)
    (hharm : ∀ y ∈ connectedComponentIn {y | 0 < u y} y₀, HarmonicAt u y) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / 2 ≤
        (volume (connectedComponentIn {y | 0 < u y} y₀ ∩ ball 0 1)).toReal ∧
      ((volume (connectedComponentIn {y | 0 < u y} y₀ ∩ ball 0 1)).toReal =
          (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / 2 →
        ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 ∧
          connectedComponentIn {y | 0 < u y} y₀ = {y | 0 < ⟪y, e⟫} ∧
          ∃ a : ℝ, 0 < a ∧ ∀ y ∈ connectedComponentIn {y | 0 < u y} y₀, u y = a * ⟪y, e⟫) := by
  obtain ⟨L, hL⟩ := hLip
  have hcont := hL.continuous
  have hhom' : IsOneHomogeneous u := hhom
  set U := connectedComponentIn {y | 0 < u y} y₀ with hUdef
  set v := U.indicator u with hvdef
  have hUo : IsOpen U := isOpen_connectedComponentIn_pos hcont
  have hUc : IsCone U := isCone_connectedComponentIn_pos hhom'
  have hvL : LipschitzWith L v := lipschitzWith_indicator_connectedComponentIn hL hnn
  have hvnn : ∀ x, 0 ≤ v x := fun x => Set.indicator_nonneg (fun y _ => hnn y) x
  have hvhom : IsOneHomogeneous v := isOneHomogeneous_indicator hhom'
  have hvpos : {x | 0 < v x} = U := setOf_indicator_pos
  have hvharm : ∀ x, 0 < v x → HarmonicAt v x := by
    intro x hx
    have hxU : x ∈ U := by rw [← hvpos]; exact hx
    exact harmonicAt_indicator hcont hxU (hharm x hxU)
  have hy₀U : y₀ ∈ U := mem_connectedComponentIn hy₀
  have hvne : ∃ x, 0 < v x := ⟨y₀, by rw [← hvpos] at hy₀U; exact hy₀U⟩
  -- Pass from Lebesgue measure on `B₁` to the Gaussian measure.
  have hcone := gaussMeasure_mul_volume_ball hUo.measurableSet hUc
  have hUfin : gaussMeasure n U ≠ ⊤ := measure_ne_top _ _
  have hGfin : gaussMeasure n univ ≠ ⊤ := measure_ne_top _ _
  have hreal : (gaussMeasure n U).toReal * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
      = (gaussMeasure n univ).toReal * (volume (U ∩ ball 0 1)).toReal := by
    have := congrArg ENNReal.toReal hcone
    simpa only [ENNReal.toReal_mul] using this
  have hG : 0 < (gaussMeasure n univ).toReal :=
    ENNReal.toReal_pos gaussMeasure_univ_pos.ne' hGfin
  have hb : 0 < (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have h2fin : 2 * gaussMeasure n U ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hUfin
  refine ⟨?_, fun heq => ?_⟩
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have hsmall : 2 * gaussMeasure n {x | 0 < v x} < gaussMeasure n univ := by
      rw [hvpos, ← ENNReal.toReal_lt_toReal h2fin hGfin, ENNReal.toReal_mul]
      simp only [ENNReal.toReal_ofNat]
      nlinarith
    have h1 := gaussL2_lt_dirichletEnergy hn hvL hvnn hvhom hvne hsmall
    have h2 := dirichletEnergy_le_gaussL2 hvL hvnn hvhom hvharm
    exact absurd (h1.trans_le h2) (lt_irrefl _)
  · have hhalf : 2 * gaussMeasure n {x | 0 < v x} = gaussMeasure n univ := by
      rw [hvpos, ← ENNReal.toReal_eq_toReal_iff' h2fin hGfin, ENNReal.toReal_mul]
      simp only [ENNReal.toReal_ofNat]
      rw [heq] at hreal
      nlinarith
    have hconn : IsConnected {x | 0 < v x} := by
      rw [hvpos]; exact isConnected_connectedComponentIn_iff.2 hy₀
    obtain ⟨e, he, hUe, a, ha, hva⟩ :=
      eq_halfSpace_of_two_mul_gaussMeasure_eq hn hvL hvnn hvhom hvharm hconn hhalf
    refine ⟨e, he, by rw [← hvpos, hUe], a, ha, fun y hy => ?_⟩
    have hvy : 0 < v y := by rw [← hvpos] at hy; exact hy
    rw [← hva y hvy, hvdef, indicator_of_mem hy]

end Sperner
