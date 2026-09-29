/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup

/-!
# Foundational setup

Ambient space, surface measure on spheres, and the dimensional constants used throughout the
formalization of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).

## Conventions

* Sphere integrals `∫_{∂B_r(x)} f dℋ^{n-1}` are *defined* through Mathlib's polar
  decomposition measure `Measure.toSphere` on the unit sphere, rescaled by `r ^ (n - 1)`.
  Its agreement with the (normalized) Hausdorff measure on the sphere is
  `Registry.map_sphereMeasure_eq_hausdorffN`.
  Every proof in the project uses the definition below; the Hausdorff description is only needed
  to match the paper's notation.
* The paper's `ℋ^d` is the *normalized* Hausdorff measure. Mathlib's `μH[d]` omits the
  factor `ω_d / 2^d`; we define `hausdorffN d` with that factor.
-/

open MeasureTheory Metric Set

@[expose] public noncomputable section

namespace InnerVariational

/-! The definitions `Rn`, `sphereMeasure`, `sphereIntegral`, `unitBallVolume` and `hausdorffN`
are those of the dependency gmt-foundations v0.1.0
(https://github.com/willmfeldman/gmt-foundations), file `GMTFoundations/Defs/Setup.lean`. They are
re-exported here so that the whole project uses the same constants as the gmt-foundations
theorems. -/
export GMTFoundations (Rn sphereMeasure sphereIntegral unitBallVolume hausdorffN)

end InnerVariational
