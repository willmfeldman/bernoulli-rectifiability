/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.ConcreteQ.Basic
public import InnerVariational.Frequency.ConcreteQ.ChangeOfPoint
public import InnerVariational.Frequency.ConcreteQ.Rescale

/-!
# The frequency formula with a Lipschitz coefficient (Section 4)

Section 4 of Kriventsov–Weiss for variational solutions with a Lipschitz coefficient `Q`: the
results for the frequency `weightedFrequencyN`, the modified frequency `modFrequencyN`, the
shifted Weiss energy `modMonotonicityM`, `heightH` and `weightedVolumeV`.

* `Frequency/ConcreteQ/Basic.lean`: Lemmas 4.1 and 4.3–4.5, the growth of the modified
  frequency, the integrated form of (4.13) and the annulus estimate.
* `Frequency/ConcreteQ/ChangeOfPoint.lean`: Lemma 4.6 (change of point) and continuity in the
  centre.
* `Frequency/ConcreteQ/Rescale.lean`: scaling of the quantities.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/
