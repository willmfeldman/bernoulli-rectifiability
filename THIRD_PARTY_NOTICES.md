# Third-party code

This project is released under the Apache License 2.0 (`LICENSE`). A few files contain code adapted
from TauCeti, an Apache-2.0 Lean project. Each of those files keeps the upstream copyright holder on
its header's copyright line, and its module docstring has a `## Provenance` section that names the
upstream file and commit, lists the declarations taken, and says what was changed (Apache-2.0
§4(b)). The upstream project ships no `NOTICE` file.

| Upstream | Commit | License | Upstream copyright | Files here |
|---|---|---|---|---|
| TauCeti, https://github.com/TauCetiProject/TauCeti | `91f66a0514e6523efdccddb9e35fb82c96dd6405` | Apache-2.0 | © 2026 The Tau Ceti contributors | `InnerVariational/Vendor/Analysis/BallAverage.lean` (from `TauCeti/MeasureTheory/Function/Lp/BallAverage.lean`), `InnerVariational/Vendor/Analysis/DuBoisReymond.lean` and `Sperner/Vendor/Weyl/DuBoisReymond.lean` (from `TauCeti/Analysis/Distribution/DuBoisReymond.lean`), `InnerVariational/Vendor/Analysis/FrechetKolmogorovCompact.lean` (from `TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean`), `InnerVariational/Vendor/Analysis/LaplacianInvariance.lean` and `Sperner/Vendor/Weyl/LaplacianInvariance.lean` (from `TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`), `InnerVariational/Vendor/Analysis/MeanValue.lean`, `InnerVariational/Vendor/SubMeanValue.lean` and `Sperner/Vendor/Weyl/MeanValue.lean` (from `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean`), `InnerVariational/Vendor/Analysis/PolarCoord.lean` and `Sperner/Vendor/Weyl/PolarCoord.lean` (from `TauCeti/MeasureTheory/Constructions/HaarToSphere.lean`) |
| TauCeti, https://github.com/TauCetiProject/TauCeti | `90cca67c0c8e91cd30b0d46cb58101f8c5c59236` | Apache-2.0 | © 2026 The Tau Ceti contributors | `InnerVariational/Vendor/Harnack.lean` (from `TauCeti/Analysis/PDE/Harnack/Basic.lean` and related files listed in its `## Provenance`), `Sperner/Vendor/HarmonicBasic.lean` (from `TauCeti/Analysis/Sobolev/WeakDeriv/Laplacian.lean`, by way of elliptic-bernoulli-foundations v0.1.0) |

The `Sperner/Vendor/Weyl/*` files reached this repository by way of the author's
viscosity-solution-theory v0.2.0 (https://github.com/willmfeldman/viscosity-solution-theory), and
`Sperner/Vendor/HarmonicBasic.lean` by way of elliptic-bernoulli-foundations v0.1.0
(https://github.com/willmfeldman/elliptic-bernoulli-foundations); both are Apache-2.0.

Everything else is original to this project. Mathlib, gmt-foundations
(https://github.com/willmfeldman/gmt-foundations, v0.1.0) and elliptic-bernoulli-foundations
(v0.1.0) are used as Lake dependencies (normal libraries; no code copied from them apart from the
file noted above).
