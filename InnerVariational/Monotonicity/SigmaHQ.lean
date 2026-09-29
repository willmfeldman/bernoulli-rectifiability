/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import InnerVariational.Monotonicity.Limits
public import InnerVariational.Monotonicity.HighestDensity

/-!
# The coefficient `Q ≡ 1` in the Lipschitz-coefficient definitions

For the coefficient `Q ≡ 1`, the limit `MzeroQ 1` is `Mzero` (`MzeroQ_one`, in
`Monotonicity/Limits.lean`), and the set `sigmaHQ` of highest density is the set `sigmaH` of
`Defs/HighestDensity.lean` for every variational solution
(`IsVariationalSolution.sigmaHQ_one`, in `Monotonicity/HighestDensity.lean`). This file collects
both.
-/
