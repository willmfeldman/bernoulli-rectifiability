/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Laplacian.GaussGreen
public import InnerVariational.Regular.Laplacian.Measure
public import InnerVariational.Regular.Laplacian.BlowUp

/-!
# The Laplacian of a variational solution without highest-density points (Corollary 8.4)

Corollary 8.4 of Kriventsov–Weiss: if `(u, χ)` is a variational solution on `Ω`, `2 ≤ n`, and
`Σ^H = ∅`, then `Δu = ℋ^{n-1}⌊∂*{u > 0}` in `Ω` in the sense of distributions
(`IsVariationalSolution.laplacian_eq_of_sigmaH_empty`). The proof is split into three parts.

* `Regular/Laplacian/GaussGreen.lean`: Laplacian measures of subharmonic functions and
  Gauss–Green pairs.
* `Regular/Laplacian/Measure.lean`: the Laplacian measure of a variational solution and the
  positivity set as a set of locally finite perimeter.
* `Regular/Laplacian/BlowUp.lean`: blow-ups at reduced-boundary points and Corollary 8.4.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/
