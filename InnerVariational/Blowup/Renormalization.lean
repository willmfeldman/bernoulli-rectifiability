/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Concrete
public import InnerVariational.Blowup.RenormalizationQ
public import InnerVariational.Kernel.BV
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.Quantities
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Basic.Polar
public import InnerVariational.Frequency.Abstract
import InnerVariational.Defs.Calculus

/-!
# Frequency input for the renormalized blow-up sequence (Section 5)

The estimates of Section 4 of Kriventsov–Weiss (full reference below), as proved in
`Frequency/Concrete.lean`, applied at the scales `[1/2, 2]` of the standing assumptions of
Section 5: `(u, χ)` is a variational solution on `Ω ⊇ B̄_2`, `0 ∈ closure {u > 0}`,
`M_0(u; 1/2) ≥ |B_1|`, `N_0(u; 2) ≤ N₊`. (We write `M_0(u_k; 1/2)` with the index `k` for each
member of the sequence, where the paper writes `M_0(u; 1/2)`; we also use
`0 ∈ closure {u_k > 0}` and `B̄_2 ⊆ Ω` where the paper writes `0 ∈ {u_k > 0}` and `B_2 ⊆ Ω`.)
These are the inputs to the proofs of Lemma 5.1 and Theorem 5.3 for `v = u / √H_0(u; 1)`.

## Main results

* `IsVariationalSolution.frequencyN_half_le_one_le_two`: `1 ≤ N(1/2) ≤ N(1) ≤ N(2)`.
* `gradient_const_mul`: `∇(c u) = c ∇u`.

The remaining estimates of this section (identity (4.11) at `r = 1`, equation (4.13) integrated
over `B_1 \ B̄_{1/2}`, and the mass bounds on that annulus) are used in their
Lipschitz-coefficient form, in `Blowup/RenormalizationQ.lean`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

section Setting

variable (h : IsVariationalSolution Ω C u χ) (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
  (hcl : (0 : Rn n) ∈ closure {y | 0 < u y})
  (hM : unitBallVolume n ≤ monotonicityM u χ 0 (1 / 2))
include h hΩ hcl hM

/-- `1 ≤ N(1/2) ≤ N(1) ≤ N(2)` (Lemma 4.1). -/
theorem frequencyN_half_le_one_le_two :
    1 ≤ frequencyN u χ 0 (1 / 2) ∧ frequencyN u χ 0 (1 / 2) ≤ frequencyN u χ 0 1 ∧
      frequencyN u χ 0 1 ≤ frequencyN u χ 0 2 := by
  have hmono := h.monotoneOn_frequencyN hcl (t := 1 / 2) (R := 2) (by norm_num) hM hΩ
  refine ⟨h.one_le_frequencyN hcl (t := 1 / 2) (R := 2) (by norm_num) hM hΩ
    (by norm_num : (1 / 2 : ℝ) ∈ Icc (1 / 2) 2), ?_, ?_⟩
  · exact hmono (by norm_num) (by norm_num) (by norm_num)
  · exact hmono (by norm_num) (by norm_num) (by norm_num)

end Setting

end IsVariationalSolution

end InnerVariational
