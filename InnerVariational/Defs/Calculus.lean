/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
public import GMTFoundations.Defs.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Calculus vocabulary: divergence, test functions, test fields

Elementary differential-calculus notions used by the definitions of variational and viscosity
solutions in Sections 3.2 and 8 of Kriventsov–Weiss (full reference below).

* `divergence ξ x` is `tr (Dξ(x))`. At points where `ξ` is not differentiable Mathlib's `fderiv` is
  `0`, so the divergence is `0` there. For Lipschitz `ξ` this happens only on a Lebesgue-null set
  (Rademacher).
* `IsLipTestField Ω ξ` is the class `C^{0,1}_c(Ω; ℝⁿ)` of the domain-variation identity (3.5).
* `IsSmoothTestField Ω ξ` is `C^∞_c(Ω; ℝⁿ)`.
* `IsTestFunction Ω φ` is `C^∞_c(Ω)`.
* `IsWeaklySubharmonicOn Ω u` is distributional subharmonicity, `∫ u Δφ ≥ 0` for `0 ≤ φ ∈ C^∞_c(Ω)`.

Smoothness is `ContDiff ℝ ∞` (with `open scoped ContDiff`). In this Mathlib `⊤` would mean
analytic, which is *not* intended.

`divergence`, `IsLipTestField`, `IsSmoothTestField` and `IsTestFunction` are defined in the
dependency gmt-foundations v0.1.0 (https://github.com/willmfeldman/gmt-foundations) and
re-exported here.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Laplacian
open scoped ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! `divergence`, `IsLipTestField`, `IsSmoothTestField` and `IsTestFunction` are GMT-foundations'
(`GMTFoundations/Defs/Calculus.lean`), re-exported. -/
export GMTFoundations (divergence IsLipTestField IsSmoothTestField IsTestFunction)

/-- Distributional subharmonicity on `Ω`: `∫ u Δφ ≥ 0` for every nonnegative `φ ∈ C^∞_c(Ω)`.
Here `Δ` is Mathlib's `InnerProductSpace` Laplacian. -/
def IsWeaklySubharmonicOn (Ω : Set (Rn n)) (u : Rn n → ℝ) : Prop :=
  ∀ φ, IsTestFunction Ω φ → (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, u x * Δ φ x

/-- A smooth compactly supported vector field is a Lipschitz test field. -/
theorem IsSmoothTestField.isLipTestField {Ω : Set (Rn n)} {ξ : Rn n → Rn n}
    (h : IsSmoothTestField Ω ξ) : IsLipTestField Ω ξ :=
  ⟨ContDiff.lipschitzWith_of_hasCompactSupport h.2.1 h.1 (by simp), h.2.1, h.2.2⟩

theorem IsLipTestField.mono {Ω Ω' : Set (Rn n)} {ξ : Rn n → Rn n} (h : IsLipTestField Ω ξ)
    (hΩ : Ω ⊆ Ω') : IsLipTestField Ω' ξ :=
  ⟨h.1, h.2.1, h.2.2.trans hΩ⟩

theorem IsTestFunction.mono {Ω Ω' : Set (Rn n)} {φ : Rn n → ℝ} (h : IsTestFunction Ω φ)
    (hΩ : Ω ⊆ Ω') : IsTestFunction Ω' φ :=
  ⟨h.1, h.2.1, h.2.2.trans hΩ⟩

/-! The types above are `GMTFoundations`', so dot notation (`h.mono`) looks in the `GMTFoundations`
namespace: these aliases make it find the lemmas above. (Explicit names such as
`IsLipTestField.mono` must resolve to the `InnerVariational` declarations: resolving them through
the `export` fails.) -/

alias _root_.GMTFoundations.IsSmoothTestField.isLipTestField := IsSmoothTestField.isLipTestField
alias _root_.GMTFoundations.IsLipTestField.mono := IsLipTestField.mono
alias _root_.GMTFoundations.IsTestFunction.mono := IsTestFunction.mono

/-- Outside the topological support of `ξ` the divergence vanishes. -/
theorem divergence_eq_zero_of_notMem_tsupport {ξ : Rn n → Rn n} {x : Rn n}
    (hx : x ∉ tsupport ξ) : divergence ξ x = 0 := by
  simp [divergence, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

end InnerVariational
