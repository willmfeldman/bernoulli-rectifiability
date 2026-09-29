/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Viscosity.Classification
public import InnerVariational.Regular.Viscosity.Main

/-!
# Variational solutions are viscosity solutions off `Σ^H` (Lemma 8.3)

Lemma 8.3 of Kriventsov–Weiss: if `(u, χ)` is a variational solution on `Ω`, `2 ≤ n`, and
`Σ^H = ∅`, then `u` is a viscosity solution on `Ω` (`IsVariationalSolution.isViscositySolution`).
The proof is split into two parts.

* `Regular/Viscosity/Classification.lean`: half-spaces, the half-space computation, and the
  classification of the blow-up.
* `Regular/Viscosity/Main.lean`: blow-up pairs and Lemma 8.3.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/
