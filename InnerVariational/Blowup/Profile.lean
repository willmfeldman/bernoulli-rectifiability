/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Profile.L2Limits
public import InnerVariational.Blowup.Profile.Limit
public import InnerVariational.Blowup.Profile.Normalization

/-!
# Theorem 5.3, steps (d)–(e): strong convergence to the profile `α(n) |⟪y, ν⟫|`

Steps (d) and (e) of the proof of Theorem 5.3 of Kriventsov–Weiss, together with the
normalization `β = α(n)`, for an abstract renormalized sequence `v_k`. The proof is split into
three parts.

* `Blowup/Profile/L2Limits.lean`: test functions and `L²` limit lemmas.
* `Blowup/Profile/Limit.lean`: the energy identity and step (e) for the explicit limit.
* `Blowup/Profile/Normalization.lean`: Theorem 5.3, steps (d)–(e), with the normalization.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/
