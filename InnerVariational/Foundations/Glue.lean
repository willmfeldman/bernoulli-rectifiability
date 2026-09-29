/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Foundations.Bridge
public import InnerVariational.Foundations.InnerVariation
public import EllipticBernoulli.Classical.GradientBound
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Defs.Solutions

/-!
# Background results imported from elliptic-bernoulli-foundations

Two classical facts about classical solutions used in Section 9 of Kriventsov–Weiss, proved in
the dependency elliptic-bernoulli-foundations v0.1.0
(https://github.com/willmfeldman/elliptic-bernoulli-foundations):

* the Alt–Caffarelli gradient bound for classical solutions, from
  `EllipticBernoulli.classical_lipschitz_bound` (the uniform blow-up argument of Alt–Caffarelli,
  Remark 6.4; Alt–Caffarelli, Theorem 6.3, itself concerns their weak solutions only);
* classical solutions are variational solutions. The domain-variation identity comes from
  `EllipticBernoulli.IsClassicalSolution.integral_innerVarIntegrand_eq_zero` (see
  `Foundations/InnerVariation.lean`); the other fields come from the definition.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
* H. W. Alt and L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
-/

@[expose] public section

open Metric Set Filter Topology
open scoped NNReal

namespace InnerVariational.Foundations

variable {n : ℕ}

/-- **Alt–Caffarelli gradient bound** (Kriventsov–Weiss, Proposition 9.1). If `u` is a classical
solution on `B_1` with `u(0) = 0`, then `|∇u| ≤ 1 + w(r)` on `B_r` for a continuous
nondecreasing modulus `w` with `w(0+) = 0`. The paper states that `w` depends only on `n`,
citing Alt–Caffarelli, Theorem 6.3; as we read the argument, which is a compactness (blow-up)
argument, it uses a uniform Lipschitz bound `L` for `u`, so here `w` depends on `n` and `L`.
Alt–Caffarelli's Theorem 6.3 concerns their weak solutions rather than classical ones. -/
theorem classical_lipschitz_bound (L : ℝ≥0) :
    ∃ w : ℝ → ℝ, ContinuousOn w (Ico 0 1) ∧ MonotoneOn w (Ico 0 1) ∧
      Tendsto w (𝓝[>] 0) (𝓝 0) ∧
      ∀ u : Rn n → ℝ, IsClassicalSolution (ball 0 1) u → LipschitzOnWith L u (ball 0 1) →
        u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r) := by
  obtain ⟨w, hwc, hwm, hw0, hw⟩ := EllipticBernoulli.classical_lipschitz_bound (n := n) L
  exact ⟨w, hwc, hwm, hw0, fun u hu ↦ hw u hu.toEB⟩

/-- **Classical solutions are variational solutions** (Kriventsov–Weiss, §9, the remark after
Definition 9.1). -/
theorem isVariationalSolution_of_isClassicalSolution {Ω : Set (Rn n)} {u : Rn n → ℝ}
    (hu : IsClassicalSolution Ω u) {L : ℝ≥0} (hL : LipschitzOnWith L u Ω) :
    IsVariationalSolution Ω L u (posIndicator u) where
  isOpen := hu.isOpen
  nonneg := hu.nonneg
  continuousOn := hu.continuousOn
  contDiffOn := fun x hx => (hu.harmonicAt x hx.1 hx.2).1.contDiffWithinAt
  lipschitzOnWith := fun _ _ hsub => hL.mono hsub
  measurable_chi := by
    have hopen : IsOpen (Ω ∩ {x | 0 < u x}) :=
      hu.continuousOn.isOpen_inter_preimage hu.isOpen isOpen_Ioi
    have : Ω.indicator (posIndicator u) = (Ω ∩ {x | 0 < u x}).indicator 1 := by
      rw [posIndicator, indicator_indicator]
    rw [this]
    exact measurable_const.indicator hopen.measurableSet
  chi_mem := fun x _ => by
    by_cases h : 0 < u x
    · exact Or.inr (posIndicator_of_pos h)
    · exact Or.inl (posIndicator_of_nonpos (not_lt.1 h))
  posIndicator_le_chi := Filter.Eventually.of_forall fun _ => le_rfl
  innerVariation_eq_zero := fun _ hξ => innerVariation_posIndicator_eq_zero_of_eb hu.toEB hξ

end InnerVariational.Foundations
