/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
import InnerVariational.Blowup.ChiLimitQ
import InnerVariational.Monotonicity.HighestDensityQ
import InnerVariational.Regular.Viscosity.MainQ
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Singular.Chi

/-!
# Headline statements for a Lipschitz coefficient

The Lipschitz-coefficient versions of the results of Kriventsov–Weiss (full reference below) on
the set `Σ^H` of highest density, the viscosity property off `Σ^H`, blow-up limits and the
identification of `χ`. Here `(u, χ)` is a `Q`-variational solution (`IsVariationalSolutionQ`)
for a coefficient `Q` with `QBounds Ω Q L c C'`. Each statement mirrors the corresponding
statement for `Q ≡ 1`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-- **Density characterization of `Σ^H`** (Theorem 7.2), Lipschitz-coefficient version of
`IsVariationalSolution.mem_sigmaH_iff_frontier_inter`: `x ∈ Σ^H` if and only if `x ∈ Ω` lies on
the relative free boundary `frontier {y ∈ Ω | u(y) > 0}` and
`|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` as `r → 0+`. -/
theorem mem_sigmaHQ_iff_frontier_inter [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    x ∈ sigmaHQ Ω Q u χ ↔ x ∈ Ω ∧ x ∈ frontier {y | y ∈ Ω ∧ 0 < u y} ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1) :=
  h.mem_sigmaHQ_iff_frontier_inter' hQ

/-- **`Σ^H` is relatively closed in `Ω`** (Section 6), Lipschitz-coefficient version of
`IsVariationalSolution.closure_sigmaH_inter_subset`. -/
theorem closure_sigmaHQ_inter_subset [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    closure (sigmaHQ Ω Q u χ) ∩ Ω ⊆ sigmaHQ Ω Q u χ :=
  h.closure_sigmaHQ_inter_subset' hQ

/-- **Lemma 8.3 on `Ω \ Σ^H`**, Lipschitz-coefficient version of
`IsVariationalSolution.isViscositySolution_diff_sigmaH`: for `2 ≤ n`, `u` is a viscosity solution
of `|∇u| = Q` on the open set `Ω \ Σ^H`. -/
theorem isViscositySolutionQ_diff_sigmaHQ (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    IsViscositySolutionQ (Ω \ sigmaHQ Ω Q u χ) Q u where
  continuousOn := h.continuousOn.mono diff_subset
  nonneg x hx := h.nonneg x hx.1
  harmonicAt _ hx hpos := h.harmonicOn_pos hQ hx.1 hpos
  norm_gradient_le _ hx _ hr _ _ hφ hφx hle :=
    h.norm_gradient_le_of_le hn hQ hx.1.1 hx.2 hx.1.2 hr hφ hφx hle
  one_le_norm_gradient _ hx _ hr _ _ hφ hφx hle :=
    h.le_norm_gradient_of_le_max hn hQ hx.1.1 hx.2 hx.1.2 hr hφ hφx hle

/-- **Blow-up limits** (first paragraph of the proof of Theorem 9.3), Lipschitz-coefficient
version of `IsVariationalSolution.exists_blowup_limit`. If `x ∈ Ω`, `r_k → 0+` and
`u_{x,r_k} → u₀` locally uniformly, then along a subsequence `χ_{x,r_k} → χ₀` in `L¹_loc(ℝⁿ)`,
where `(u₀, χ₀)` is a variational solution on `ℝⁿ` with the constant coefficient `Q(x)` and the
same gradient constant `C`. -/
theorem exists_blowup_limit (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hx : x ∈ Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀, IsVariationalSolutionQ univ C (fun _ => Q x) u₀ χ₀ ∧
      ∀ K, IsCompact K →
        Tendsto (fun k => ∫ y in K, |chiRescale χ x (r (φ k)) y - χ₀ y|) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, χ₀, hsol, -, hL⟩ := exists_blowup_limit_ae hQ h hx hr hr0 hconv
  exact ⟨φ, hφ, χ₀, hsol, hL⟩

/-- **Blow-up limits are homogeneous** (Proposition 3.4, last claim), Lipschitz-coefficient
version of `IsVariationalSolution.blowup_homogeneous`: a blow-up limit `u₀` of `u` at `x ∈ Ω`
satisfies `u₀(t y) = t u₀(y)` for `t > 0`. -/
theorem blowup_homogeneous [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y :=
  blowup_homogeneous' hQ h hx hr hr0 hconv

end IsVariationalSolutionQ

namespace Singular

/-- **Theorem 8.6, glued form**, Lipschitz-coefficient version of `chi_eq_indicator_of_local`.
Let `U` be connected and let `(u, χ)` be a `Q`-variational solution near every point of `U`,
with bounded and Lipschitz coefficient on the neighbourhood. Then either `u ≡ 0` on `U` and
`χ = 1` a.e. on `U`, or `χ = χ_{u>0}` a.e. on `U`. The proof is
`Singular.chi_eq_indicator_of_localQ'`. -/
theorem chi_eq_indicator_of_localQ (hn : 2 ≤ n) {U : Set (Rn n)} {Q u χ : Rn n → ℝ}
    (hU : IsConnected U)
    (h : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ (C L : ℝ≥0) (c C' : ℝ),
      QBounds V Q L c C' ∧ IsVariationalSolutionQ V C Q u χ) :
    ((∀ x ∈ U, u x = 0) ∧ ∀ᵐ y ∂(volume.restrict U), χ y = 1) ∨
      χ =ᵐ[volume.restrict U] posIndicator u :=
  chi_eq_indicator_of_localQ' hn hU h

end Singular

end InnerVariational
