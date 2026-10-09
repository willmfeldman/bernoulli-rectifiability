/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Concrete
public import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Basic.Polar

/-!
# Existence of `H_x(u; 0+)` on `Σ^H`

D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), paragraph after Theorem 8.6: for
`x ∈ Σ^H`, `r ↦ H_x(u; r)` is nondecreasing (the lower bound of Lemma 4.3), so the limit
`H_x(u; 0+) ∈ [0, ∞)` exists, and `H_x(u; 0+) ≤ C_V² |∂B_1|` by the Lipschitz bound on `u`.

## Main statements

* `Singular.monotoneOn_heightH_of_mem_sigmaH`: `H_x` is nondecreasing on `(0, R]` when
  `B̄_R(x) ⊆ Ω` and `x ∈ Σ^H`.
* `Singular.tendsto_heightH_zero`: `H_x(u; r) → heightHZero u x` as `r → 0+`, i.e. the junk-valued
  `limUnder` of `Defs/Quantities.lean` is the actual limit on `Σ^H`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Singular

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- On `Σ^H`, `r ↦ H_x(u; r)` is nondecreasing on `(0, R]` whenever `B̄_R(x) ⊆ Ω`
(paragraph after Theorem 8.6, via the lower bound of Lemma 4.3: `M_x(u; t) ≥ |B_1|` at every
admissible `t`). -/
theorem monotoneOn_heightH_of_mem_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ sigmaH Ω u χ) {R : ℝ} (hR : closedBall x R ⊆ Ω) :
    MonotoneOn (heightH u x) (Ioc 0 R) := by
  intro s hs t ht hst
  exact h.monotoneOn_heightH hx.2.1 hs.1
    (hx.2.2 s hs.1 ((closedBall_subset_closedBall hs.2).trans hR)) hR ⟨le_rfl, hs.2⟩
    ⟨hst, ht.2⟩ hst

/-- A point of `Σ^H` has a closed ball of positive radius inside `Ω`. -/
theorem exists_closedBall_subset_of_mem_sigmaH (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ sigmaH Ω u χ) : ∃ R > 0, closedBall x R ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hx.1
  exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hδΩ⟩

/-- **Existence of `H_x(u; 0+)`** (paragraph after Theorem 8.6). For `x ∈ Σ^H`,
`H_x(u; r) → H_x(u; 0+)` as `r → 0+`, where `H_x(u; 0+)` is `heightHZero u x`. -/
theorem tendsto_heightH_zero [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ sigmaH Ω u χ) :
    Tendsto (heightH u x) (𝓝[>] 0) (𝓝 (heightHZero u x)) := by
  obtain ⟨R, hR, hRΩ⟩ := exists_closedBall_subset_of_mem_sigmaH h hx
  have hmono : MonotoneOn (heightH u x) (Ioo 0 R) :=
    (monotoneOn_heightH_of_mem_sigmaH h hx hRΩ).mono Ioo_subset_Ioc_self
  have hlim := hmono.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hR)
    ⟨0, by rintro _ ⟨s, hs, rfl⟩; exact heightH_nonneg u x hs.1.le⟩
  rwa [heightHZero, hlim.limUnder_eq]

end Singular

end InnerVariational
