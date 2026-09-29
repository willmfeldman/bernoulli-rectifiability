/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Defs.GMT
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import GMTFoundations.Defs.GMT

/-!
# The Laplacian measure of a variational solution

The measure of Theorem 8.7 and Theorem 1.2 (iii) of Kriventsov–Weiss:
`ℋ^{n-1}⌊∂*{u>0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H`,
and the predicate `HasDistribLaplacianOn Ω u μ`, "`Δu = μ` in `Ω` in the sense of distributions".

## Encoding

* `Δu = μ` is stated distributionally: `∫ u Δφ = ∫ φ dμ` for every `φ ∈ C^∞_c(Ω)`,
  together with local finiteness of `μ` on `Ω`. The paper's `Δu` is a Radon measure. Local
  finiteness is part of the paper's meaning, and it makes `∫ φ dμ` a genuine integral.
* The measure is the one of Theorem 8.7, with the set of highest density `Σ^H` (Section 6) and
  the unaveraged `H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u²` of Section 3.3. Theorem 1.2 (iii) is
  printed with a set `Σ_**` from the introduction and with `H_x(u; 0+)` defined through the
  spherical average `⨍_{∂B_r(x)}`; with the average the density would be off by the factor
  `√|∂B_1|`, since `α(n)` is normalized by `H_0(α(n)|x_n|; r) = 1` for the unaveraged `H`
  (Section 8.2). We follow Theorem 8.7.
* The density `x ↦ 2 α(n) √(H_x(u; 0+))` is only needed on `Σ^H`, where the limit exists.
  It agrees `ℋ^{n-1}⌊Σ^H`-a.e. with the measurable function `x ↦ lim_k 2α√(H_x(u; 1/k))`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Laplacian
open scoped ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The Laplacian measure of Theorem 8.7 of Kriventsov–Weiss:
`ℋ^{n-1}⌊(∂*{u>0} ∩ Ω) + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H`. -/
def laplacianMeasure [NeZero n] (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : Measure (Rn n) :=
  (hausdorffN n (n - 1)).restrict (reducedBoundary Ω {x | 0 < u x}) +
    ((hausdorffN n (n - 1)).restrict (sigmaH Ω u χ)).withDensity
      (fun x => ENNReal.ofReal (2 * alphaN n * √(heightHZero u x)))

/-- `Δu = μ` in `Ω` in the sense of distributions. `μ` is finite on compact subsets
of `Ω`, and `∫ u Δφ = ∫ φ dμ` for every `φ ∈ C^∞_c(Ω)`. -/
def HasDistribLaplacianOn (Ω : Set (Rn n)) (u : Rn n → ℝ) (μ : Measure (Rn n)) : Prop :=
  (∀ K, IsCompact K → K ⊆ Ω → μ K < ∞) ∧
    ∀ φ, IsTestFunction Ω φ → ∫ x, u x * Δ φ x = ∫ x, φ x ∂μ

end InnerVariational
