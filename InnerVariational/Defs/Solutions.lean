/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.Setup

/-!
# Viscosity and classical solutions

* `IsViscositySolution Ω u`: Definition 8.1 of Kriventsov–Weiss (full reference below). The
  paper's conclusions `|∇u| ≤ 1` (resp. `≥ 1`) are read as `|∇φ(x)| ≤ 1` (resp. `≥ 1`): `u` is
  not differentiable at free boundary points, and the test function `φ` is what is meant.
* `IsClassicalSolution Ω u`: Definition 9.1 of Kriventsov–Weiss.

## Encoding notes

* "Harmonic in `{u > 0}`" is `InnerProductSpace.HarmonicAt u x` at every `x ∈ Ω` with `u x > 0`.
  `Ω ∩ {u > 0}` is open whenever `u` is continuous on the open set `Ω`.
* Viscosity test functions are globally smooth (`ContDiff ℝ ∞`) with `φ(x) = 0`, compared with
  `u` on a ball `B_r(x) ⊆ Ω`. Restricting to global test functions only weakens the defining
  condition. It is equivalent, since near `x` a `C²` test function can be replaced by its
  second-order Taylor polynomial with the Hessian shifted by `∓δ I`.
* `φ₊ ≥ u` is `u ≤ max φ 0`.
* Classical solutions: "Lipschitz continuous `u : Ω → [0, ∞)`" (Definition 9.1 prints
  `[0, \R)`, read as `[0, ∞)`) is `∃ L, LipschitzOnWith L u Ω`. "`∂{u>0}` is locally a
  smooth graph" is encoded as "locally the zero set of a smooth `F` with `∇F(x) ≠ 0`". The two
  are equivalent by the implicit function theorem. The unit normals at `x` are
  `±∇F(x)/|∇F(x)|`, which do not depend on `F`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped NNReal ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- Viscosity solutions of the one-phase Bernoulli problem (Kriventsov–Weiss,
Definition 8.1). `u : Ω → [0, ∞)` is continuous and harmonic in `{u > 0}`. For every free
boundary point `x ∈ Ω ∩ ∂{u > 0}`, every ball `B_r(x) ⊆ Ω`, and every smooth `φ` with `φ(x) = 0`:
`φ ≤ u` on `B_r(x)` implies `|∇φ(x)| ≤ 1`, and `φ₊ ≥ u` on `B_r(x)` implies `|∇φ(x)| ≥ 1`.
The paper writes `|∇u|` in the conclusions where `|∇φ(x)|` is meant, since `u` need not be
differentiable at `x`. -/
structure IsViscositySolution (Ω : Set (Rn n)) (u : Rn n → ℝ) : Prop where
  /-- `u ∈ C⁰(Ω)`. -/
  continuousOn : ContinuousOn u Ω
  /-- `u ≥ 0` on `Ω`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u` is harmonic in `Ω ∩ {u > 0}`. -/
  harmonicAt : ∀ x ∈ Ω, 0 < u x → HarmonicAt u x
  /-- Touching from below: `φ ≤ u` near a free boundary point forces `|∇φ(x)| ≤ 1`. -/
  norm_gradient_le : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∀ r, 0 < r → ball x r ⊆ Ω →
    ∀ φ : Rn n → ℝ, ContDiff ℝ ∞ φ → φ x = 0 → (∀ y ∈ ball x r, φ y ≤ u y) →
      ‖gradient φ x‖ ≤ 1
  /-- Touching from above: `φ₊ ≥ u` near a free boundary point forces `|∇φ(x)| ≥ 1`. -/
  one_le_norm_gradient : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∀ r, 0 < r → ball x r ⊆ Ω →
    ∀ φ : Rn n → ℝ, ContDiff ℝ ∞ φ → φ x = 0 → (∀ y ∈ ball x r, u y ≤ max (φ y) 0) →
      1 ≤ ‖gradient φ x‖

/-- Classical solutions of the one-phase Bernoulli problem (Kriventsov–Weiss,
Definition 9.1). `u : Ω → [0, ∞)` is Lipschitz and harmonic on `{u > 0}`. Near each free
boundary point `x`, `∂{u > 0}` is the zero set of a smooth `F` with `∇F(x) ≠ 0`. For each unit
normal `ν = ±∇F(x)/|∇F(x)|` with `u(x + tν) > 0` for small `t > 0`,
`(u(x + tν) − u(x)) / t → 1` as `t → 0+`. -/
structure IsClassicalSolution (Ω : Set (Rn n)) (u : Rn n → ℝ) : Prop where
  /-- `Ω` is open. -/
  isOpen : IsOpen Ω
  /-- `u` is Lipschitz on `Ω`. -/
  lipschitzOnWith : ∃ L, LipschitzOnWith L u Ω
  /-- `u ≥ 0` on `Ω`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u` is harmonic on `Ω ∩ {u > 0}`. -/
  harmonicAt : ∀ x ∈ Ω, 0 < u x → HarmonicAt u x
  /-- Smooth free boundary with the free boundary condition along both unit normals. -/
  free_boundary : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∃ r, 0 < r ∧ ∃ F : Rn n → ℝ,
    ContDiff ℝ ∞ F ∧ gradient F x ≠ 0 ∧
    ball x r ∩ frontier {y | 0 < u y} = ball x r ∩ {y | F y = 0} ∧
    ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x + t • (s * ‖gradient F x‖⁻¹) • gradient F x)) →
      Tendsto (fun t => (u (x + t • (s * ‖gradient F x‖⁻¹) • gradient F x) - u x) / t)
        (𝓝[>] 0) (𝓝 1)

theorem IsClassicalSolution.continuousOn {Ω : Set (Rn n)} {u : Rn n → ℝ}
    (h : IsClassicalSolution Ω u) : ContinuousOn u Ω := by
  obtain ⟨L, hL⟩ := h.lipschitzOnWith
  exact hL.continuousOn

end InnerVariational
