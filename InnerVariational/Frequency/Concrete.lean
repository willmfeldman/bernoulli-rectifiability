/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Concrete.Basic
public import InnerVariational.Frequency.Concrete.ChangeOfPoint

/-!
# The frequency formula for a variational solution (Section 4)

Section 4 of Kriventsov–Weiss: the results for `frequencyN`, `heightH` and `volumeV` of a
variational solution. The proofs are split into two parts.

* `Frequency/Concrete/Basic.lean`: Lemmas 4.1 and 4.3–4.5, the integrated form of (4.13) and the
  annulus estimate.
* `Frequency/Concrete/ChangeOfPoint.lean`: Lemma 4.6 (change of point) and continuity in the
  centre.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/
