/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
public import InnerVariational.Vendor.HarmonicLimit
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Algebra.Order.Ring.Star
public import GMTFoundations.Defs.Setup

/-!
# Locally uniform limits of harmonic functions

`harmonicAt_of_tendstoLocallyUniformlyOn`: a locally uniform limit of harmonic functions on an
open set is harmonic, and the gradients converge locally uniformly (Gilbarg–Trudinger,
Theorems 2.8 and 2.10).

This file has exactly the statement of
`InnerVariational.Registry.harmonicAt_of_tendstoLocallyUniformlyOn` (`Registry/Harmonic.lean`)
and does not import the registry, so that the registry entry can delegate to it.

## Proof

`Vendor.harmonicOnNhd_of_tendstoLocallyUniformlyOn`: the limit is continuous and weakly
harmonic, hence harmonic by Weyl's lemma. The derivatives converge by
the interior gradient estimate `‖D(F_k - f)‖ ≤ C sup_{B_{2r}} |F_k - f|` on `B_r`, which comes
from reproducing `F_k - f` by convolution with a radial kernel (mean-value property). The
gradient is the Riesz representative of the derivative, an isometric image.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001 (reprint of the 1998 edition).
-/

open InnerProductSpace Metric Set Filter

@[expose] public noncomputable section

namespace InnerVariational.Analysis

variable {n : ℕ}

/-- **Convergence of harmonic functions** (Gilbarg–Trudinger, Theorems 2.8 and 2.10).
A locally uniform limit of harmonic functions on an open set is harmonic,
and the gradients converge locally uniformly. -/
theorem harmonicAt_of_tendstoLocallyUniformlyOn {U : Set (Rn n)} (hU : IsOpen U)
    {F : ℕ → Rn n → ℝ} {f : Rn n → ℝ} (hF : ∀ k, ∀ x ∈ U, HarmonicAt (F k) x)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    (∀ x ∈ U, HarmonicAt f x) ∧
      TendstoLocallyUniformlyOn (fun k => gradient (F k)) (gradient f) atTop U := by
  obtain ⟨hf, hD⟩ := Vendor.harmonicOnNhd_of_tendstoLocallyUniformlyOn hU hF hconv
  exact ⟨hf, (toDual ℝ (Rn n)).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hD⟩

end InnerVariational.Analysis
