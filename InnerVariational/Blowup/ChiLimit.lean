/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Quantities
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Applications.Compactness
import InnerVariational.Monotonicity.Density
import Mathlib.MeasureTheory.Function.Floor
import InnerVariational.Blowup.ChiLimitQ

/-!
# Blow-up limits of variational solutions

Let `(u, χ)` be a variational solution on `Ω`, let `x ∈ Ω`, and let `r_k → 0+` be such that the
rescalings `u_{x,r_k}(y) = u(x + r_k y) / r_k` converge locally uniformly on `ℝⁿ` to `u₀`. Then,
along a subsequence, the rescalings `χ_{x,r_k}(y) = χ(x + r_k y)` converge in `L¹_loc(ℝⁿ)` to a
function `χ₀` such that `(u₀, χ₀)` is a variational solution on `ℝⁿ` with the same constant.

The paper D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
DOI 10.1002/cpa.22226, arXiv:2306.10131, does not state this separately. It combines the rescaling
(3.6) with the compactness of variational solutions from the first paragraph of the proof of
Theorem 9.3.

## Main results

* `IsVariationalSolution.exists_blowup_limit`

## Proof

This is the case `Q ≡ 1` of `IsVariationalSolutionQ.exists_blowup_limit_ae`
(`Blowup/ChiLimitQ.lean`). The argument: for every radius `ρ > 0` the rescalings are eventually
variational solutions on `B_ρ` with the same constant. Compactness on `B_{m+1}`
(`IsVariationalSolutionQ.exists_subseq_limit`) gives a subsequence along which `χ_{x,r_k}`
converges a.e. on `B_{m+1}` to some `χ_m`, with `(u₀, χ_m)` a variational solution on `B_{m+1}`.
A diagonal argument over `m ∈ ℕ` gives a single subsequence that converges a.e. on `ℝⁿ`. The
limits `χ_m` agree a.e. where their balls overlap, so they glue to a measurable `{0, 1}`-valued
`χ₀`, and `(u₀, χ₀)` is a variational solution on `ℝⁿ` because every test field is supported in
some ball. Convergence in `L¹(K)` for compact `K` then follows by dominated convergence.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

@[expose] public section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- **Blow-up limits of variational solutions.** Let `(u, χ)` be a variational solution on `Ω`,
`x ∈ Ω`, and `r_k → 0+` with `u_{x,r_k} → u₀` locally uniformly on `ℝⁿ`. Then along a
subsequence the rescalings `χ_{x,r_k} = χ(x + r_k ·)` converge in `L¹_loc(ℝⁿ)` to a function `χ₀`
such that `(u₀, χ₀)` is a variational solution on `ℝⁿ` with the same constant `C`.

This combines the rescaling (3.6) with the compactness in the first paragraph of the proof of
Theorem 9.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
DOI 10.1002/cpa.22226, arXiv:2306.10131. -/
theorem exists_blowup_limit (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀, IsVariationalSolution univ C u₀ χ₀ ∧
      ∀ K, IsCompact K →
        Tendsto (fun k => ∫ y in K, |chiRescale χ x (r (φ k)) y - χ₀ y|) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, χ₀, hsol, -, hL⟩ :=
    IsVariationalSolutionQ.exists_blowup_limit_ae (QBounds.one Ω) h.toQ hx hr hr0 hconv
  exact ⟨φ, hφ, χ₀, isVariationalSolutionQ_one_iff.1 hsol, hL⟩

end IsVariationalSolution

end InnerVariational
