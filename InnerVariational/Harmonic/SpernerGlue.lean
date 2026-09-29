/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Main
public import InnerVariational.Basic.Setup
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import GMTFoundations.Defs.Setup

/-!
# Sperner's inequality from the `Sperner` library

The self-contained library `Sperner` (directory `Sperner/`, Mathlib-only) proves Sperner's
inequality (E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134
(1973), 317–327) in homogeneous form, `Sperner.sperner_half_volume`. This file restates it
verbatim in the vocabulary of `InnerVariational.Registry.sperner_half_volume` (`Rn n`,
`unitBallVolume n`), which is proved from it. The inequality enters the proofs of Lemmas 8.1
and 8.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2): if `u₀ ≥ 0` is
one-homogeneous and harmonic where positive, each connected component of `{u₀ > 0}` meets `B_1`
in volume at least `|B_1|/2`, with equality only for a half-space on which `u₀` is linear.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Harmonic

variable {n : ℕ}

/-- Sperner's inequality, homogeneous form, proved in the `Sperner` library. Same
statement as `InnerVariational.Registry.sperner_half_volume`. -/
theorem sperner_half_volume (hn : 2 ≤ n) {u₀ : Rn n → ℝ} (hLip : ∃ L, LipschitzWith L u₀)
    (hnn : ∀ y, 0 ≤ u₀ y) (hhom : ∀ y (t : ℝ), 0 < t → u₀ (t • y) = t * u₀ y) {y₀ : Rn n}
    (hy₀ : 0 < u₀ y₀) (hharm : ∀ y ∈ connectedComponentIn {y | 0 < u₀ y} y₀, HarmonicAt u₀ y) :
    unitBallVolume n / 2 ≤
        (volume (connectedComponentIn {y | 0 < u₀ y} y₀ ∩ ball 0 1)).toReal ∧
      ((volume (connectedComponentIn {y | 0 < u₀ y} y₀ ∩ ball 0 1)).toReal =
          unitBallVolume n / 2 →
        ∃ e : Rn n, ‖e‖ = 1 ∧ connectedComponentIn {y | 0 < u₀ y} y₀ = {y | 0 < ⟪y, e⟫} ∧
          ∃ a : ℝ, 0 < a ∧ ∀ y ∈ connectedComponentIn {y | 0 < u₀ y} y₀, u₀ y = a * ⟪y, e⟫) :=
  Sperner.sperner_half_volume hn hLip hnn hhom hy₀ hharm

end InnerVariational.Harmonic
