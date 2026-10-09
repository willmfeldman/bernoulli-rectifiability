/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Density
public import InnerVariational.Monotonicity.HighestDensityQ
public import InnerVariational.Defs.HighestDensity
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.EMetricSpace.Paracompact
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Basic.Polar

/-!
# `Σ^H` through `M_x(0+)` and through the density of `{χ = 1}`

Consequences of Propositions 3.4 and 3.5 of Kriventsov–Weiss (see the references) for the set of
highest density `Σ^H`, defined at the start of Section 6 of the paper. Let `(u, χ)` be a
variational solution on `Ω`.

* `mem_sigmaH_iff_le_Mzero`: `x ∈ Σ^H` if and only if `x ∈ Ω ∩ closure{u > 0}` and
  `M_x(u; 0+) ≥ |B_1|`, the definition of `Σ^H` in Section 6. This library defines `Σ^H` (`sigmaH`)
  instead by `M_x(u; r) ≥ |B_1|` for every `r > 0` with `B̄_r(x) ⊆ Ω`; by the monotonicity of
  `M_x` (Proposition 3.4) the two agree.
* `mem_sigmaH_iff_tendsto_volume` (density characterization): `x ∈ Σ^H` if and only if
  `x ∈ Ω`, `x ∈ closure{u > 0}`, `u(x) = 0`, and `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1`.
* `closure_sigmaH_inter_subset` (relative closedness, from the upper semicontinuity in
  Proposition 3.5): `closure Σ^H ∩ Ω ⊆ Σ^H`.

The density characterization uses (3.10) and `M_x(0+) ≤ |B_1|`: `M_x(0+) ≥ |B_1|` forces
`u(x) = 0` (otherwise `M_x(0+) = −∞`) and then `M_x(0+) = lim r^{-n} |{χ = 1} ∩ B_r(x)| = |B_1|`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Characterizations of `Σ^H` -/

/-- **The definition of `Σ^H` in Section 6**: `x ∈ Σ^H` if and only if `x ∈ Ω`,
`x ∈ closure {u > 0}`, and `M_x(u; 0+) ≥ |B_1|`. The library's `sigmaH` asks instead for
`M_x(u; r) ≥ |B_1|` at every radius `r > 0` with `B̄_r(x) ⊆ Ω`; this theorem shows the two agree
for variational solutions. -/
theorem mem_sigmaH_iff_le_Mzero [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    x ∈ sigmaH Ω u χ ↔
      x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧ (unitBallVolume n : EReal) ≤ Mzero u χ x := by
  constructor
  · rintro ⟨hx, hcl, hM⟩
    exact ⟨hx, hcl, (h.le_Mzero_iff_closedBall hx).2 fun r hr hball =>
      EReal.coe_le_coe_iff.2 (hM r hr hball)⟩
  · rintro ⟨hx, hcl, hM⟩
    exact ⟨hx, hcl, fun r hr hball =>
      EReal.coe_le_coe_iff.1 ((h.le_Mzero_iff_closedBall hx).1 hM r hr hball)⟩

/-- For a variational solution, the set `sigmaHQ` with the coefficient `Q ≡ 1` is `sigmaH`. -/
theorem sigmaHQ_one (h : IsVariationalSolution Ω C u χ) [NeZero n] :
    sigmaHQ Ω (fun _ => 1) u χ = sigmaH Ω u χ := by
  ext x
  rw [h.mem_sigmaH_iff_le_Mzero]
  simp only [sigmaHQ, MzeroQ_one, mem_ofPred_eq, one_pow, one_mul]

/-- `u(x) = 0` on `Σ^H`. -/
theorem eq_zero_of_mem_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hxS : x ∈ sigmaH Ω u χ) : u x = 0 := by
  rw [← h.sigmaHQ_one] at hxS
  exact IsVariationalSolutionQ.eq_zero_of_mem_sigmaHQ (QBounds.one Ω) h.toQ hxS

/-- **Density characterization of `Σ^H`** (Props 3.4, 3.5): `x ∈ Σ^H` if and only if `x ∈ Ω`,
`x ∈ closure {u > 0}`, `u(x) = 0`, and `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` as `r → 0+`. -/
theorem mem_sigmaH_iff_tendsto_volume [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    x ∈ sigmaH Ω u χ ↔ x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧ u x = 0 ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1) := by
  rw [← h.sigmaHQ_one]
  exact IsVariationalSolutionQ.mem_sigmaHQ_iff_tendsto_volume (QBounds.one Ω) h.toQ

/-- For `x ∈ Ω`: `x ∈ frontier {u > 0}` if and only if `x ∈ closure {u > 0}` and `u(x) = 0`. -/
theorem mem_frontier_pos_iff (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    x ∈ frontier {y | 0 < u y} ↔ x ∈ closure {y | 0 < u y} ∧ u x = 0 :=
  h.toQ.mem_frontier_pos_iff hx

/-- For `x ∈ Ω`: `x ∈ frontier {y ∈ Ω | u(y) > 0}` if and only if `x ∈ frontier {u > 0}`. -/
theorem mem_frontier_pos_inter_iff (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    x ∈ frontier {y | y ∈ Ω ∧ 0 < u y} ↔ x ∈ frontier {y | 0 < u y} :=
  h.toQ.mem_frontier_pos_inter_iff hx

/-! ### Relative closedness -/

/-- **`Σ^H` is relatively closed in `Ω`** (from the upper semicontinuity in Proposition 3.5). -/
theorem closure_sigmaH_inter_subset [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    closure (sigmaH Ω u χ) ∩ Ω ⊆ sigmaH Ω u χ := by
  rw [← h.sigmaHQ_one]
  exact IsVariationalSolutionQ.closure_sigmaHQ_inter_subset' (QBounds.one Ω) h.toQ

end IsVariationalSolution

end InnerVariational
