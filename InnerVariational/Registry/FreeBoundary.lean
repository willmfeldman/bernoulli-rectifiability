/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Defs.Solutions
public import InnerVariational.Foundations.Glue

/-!
# Registry: free boundary literature

Classical results on free boundaries used by the proof, imported from the dependency
elliptic-bernoulli-foundations v0.1.0
(https://github.com/willmfeldman/elliptic-bernoulli-foundations) through `Foundations/Glue.lean` and
`Foundations/InnerVariation.lean`:

* `classical_lipschitz_bound`: the Alt–Caffarelli gradient bound near the free boundary for
  classical solutions (Proposition 9.1 of Kriventsov–Weiss, which cites Alt–Caffarelli,
  Thm 6.3);
* `IsClassicalSolution.isVariationalSolution`: classical solutions are variational solutions (the
  sentence after Definition 9.1 of Kriventsov–Weiss).

Where a statement here is weaker than the cited one, for example through a constant that may
depend on more data, the docstring says so.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
* H. W. Alt and L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
-/

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Registry

variable {n : ℕ}

/-- **Alt–Caffarelli gradient bound** (Proposition 9.1 of Kriventsov–Weiss, citing Alt–Caffarelli,
Thm 6.3). For a classical solution on `B_1` with `u(0) = 0`, `sup_{B_r} |∇u| ≤ 1 + ω(r)` for a
continuous nondecreasing modulus `ω` (named `w` in Lean) with `ω(0+) = 0`.

**Weakened relative to the paper:** the paper lets `ω` depend on `n` only. Here `ω` may also
depend on a Lipschitz bound `L` for `u` on `B_1`. That suffices for its only use (Theorem 9.3,
where a uniform Lipschitz bound is assumed), and it avoids relying on the `n`-only claim: the
cited Alt–Caffarelli theorem concerns their weak solutions, and the proof in
elliptic-bernoulli-foundations follows the blow-up argument of Alt–Caffarelli, Remark 6.4. The
bound `sup_{B_r}|∇u| ≤ 1 + ω(r)` is encoded as a Lipschitz bound on the convex set `B_r`. -/
theorem classical_lipschitz_bound (L : ℝ≥0) :
    ∃ w : ℝ → ℝ, ContinuousOn w (Ico 0 1) ∧ MonotoneOn w (Ico 0 1) ∧
      Tendsto w (𝓝[>] 0) (𝓝 0) ∧
      ∀ u : Rn n → ℝ, IsClassicalSolution (ball 0 1) u → LipschitzOnWith L u (ball 0 1) →
        u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r) := by
  exact Foundations.classical_lipschitz_bound L

/-- **Classical solutions are variational solutions** (the sentence after Definition 9.1 of
Kriventsov–Weiss). If `u` is a classical solution on `Ω` that is `L`-Lipschitz on `Ω`, then
`(u, χ_{u>0})` is a variational solution on `Ω` with constant `L`. The paper says this "can be
verified through integration by parts"; as we read it, an additional argument is needed to obtain
`|∇u| → 1` uniformly up to the free boundary from the directional limit in the definition; it is
given in elliptic-bernoulli-foundations. -/
theorem IsClassicalSolution.isVariationalSolution {Ω : Set (Rn n)} {u : Rn n → ℝ}
    (hu : IsClassicalSolution Ω u) {L : ℝ≥0} (hL : LipschitzOnWith L u Ω) :
    IsVariationalSolution Ω L u (posIndicator u) := by
  exact Foundations.isVariationalSolution_of_isClassicalSolution hu hL

end InnerVariational.Registry
