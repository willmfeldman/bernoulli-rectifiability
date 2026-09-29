/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.Calculus

/-!
# Variational solutions

The central definition of Kriventsov–Weiss (Section 3.2; full reference below): a pair `(u, χ)`
is a *variational solution* on an open set `Ω` with constant `C_V` if

1. `u ∈ C⁰(Ω) ∩ C²({u > 0})`, `u ≥ 0`, and `|∇u| ≤ C_V` on `Ω`;
2. `χ : Ω → {0, 1}` is Borel measurable;
3. `χ_{u>0} ≤ χ` Lebesgue-a.e. on `Ω`;
4. for each `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`,
   `∫ ((|∇u|² + χ) div ξ − 2 ∇u · Dξ ∇u) = 0` (equation (3.5)).

## Encoding

* `u` and `χ` are total functions `ℝⁿ → ℝ`. Only their values on `Ω` matter: every field below
  looks at `Ω` only, and in the inner variation the integrand vanishes outside `tsupport ξ ⊆ Ω`.
* `|∇u| ≤ C_V on Ω` is encoded as `LipschitzOnWith C_V u (ball x r)` for every ball
  `ball x r ⊆ Ω`. For a locally Lipschitz `u` this is equivalent to `|∇u| ≤ C_V` a.e. on `Ω`,
  since balls are convex. `∇u` is Mathlib's `gradient u`, which exists a.e. by Rademacher.
* Borel measurability of `χ : Ω → {0,1}` is encoded as `Measurable (Ω.indicator χ)`. Since `Ω` is
  open, this is equivalent to measurability of the restriction of `χ` to `Ω`, and it does not
  constrain the (irrelevant) values of `χ` outside `Ω`.
* `C²({u > 0})` is read as `C²` on the open set `Ω ∩ {u > 0}`.
* The product `∇u · Dξ ∇u` is `⟪∇u, Dξ(∇u)⟫`. The quadratic form only sees the symmetric part of
  `Dξ`, so the matrix-transpose convention does not matter.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
* H. W. Alt and L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
-/

open MeasureTheory Metric Set
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The characteristic function `χ_{u>0}` of the positivity set of `u`, as a real function. -/
def posIndicator (u : Rn n → ℝ) : Rn n → ℝ :=
  {x | 0 < u x}.indicator 1

theorem posIndicator_apply (u : Rn n → ℝ) (x : Rn n) :
    posIndicator u x = {y | 0 < u y}.indicator 1 x := rfl

theorem posIndicator_of_pos {u : Rn n → ℝ} {x : Rn n} (hx : 0 < u x) : posIndicator u x = 1 := by
  simp [posIndicator, Set.indicator_of_mem (show x ∈ {y | 0 < u y} from hx)]

theorem posIndicator_of_nonpos {u : Rn n → ℝ} {x : Rn n} (hx : u x ≤ 0) :
    posIndicator u x = 0 := by
  simp [posIndicator, Set.indicator_of_notMem (show x ∉ {y | 0 < u y} from not_lt.2 hx)]

/-- The inner variation of the Alt–Caffarelli functional `∫ (|∇u|² + χ)` in the direction `ξ`
(the left side of equation (3.5)):
`∫ ((|∇u|² + χ) div ξ − 2 ∇u · Dξ ∇u)`. -/
def innerVariation (u χ : Rn n → ℝ) (ξ : Rn n → Rn n) : ℝ :=
  ∫ x, ((‖gradient u x‖ ^ 2 + χ x) * divergence ξ x -
    2 * ⟪gradient u x, fderiv ℝ ξ x (gradient u x)⟫)

/-- `(u, χ)` is a variational solution on `Ω` with constant `C_V` (Kriventsov–Weiss,
Section 3.2).

`u` and `χ` are total functions and only their values on `Ω` matter. See the module docstring
for the encoding choices, in particular of the gradient bound. -/
structure IsVariationalSolution (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ) : Prop where
  /-- `Ω` is open. -/
  isOpen : IsOpen Ω
  /-- `u : Ω → [0, ∞)`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u ∈ C⁰(Ω)`. -/
  continuousOn : ContinuousOn u Ω
  /-- `u ∈ C²(Ω ∩ {u > 0})`. -/
  contDiffOn : ContDiffOn ℝ 2 u (Ω ∩ {x | 0 < u x})
  /-- `|∇u| ≤ C_V` on `Ω`, encoded as a Lipschitz bound on every ball in `Ω`. -/
  lipschitzOnWith : ∀ x r, ball x r ⊆ Ω → LipschitzOnWith C_V u (ball x r)
  /-- `χ` is Borel measurable on `Ω`. -/
  measurable_chi : Measurable (Ω.indicator χ)
  /-- `χ` takes values in `{0, 1}` on `Ω`. -/
  chi_mem : ∀ x ∈ Ω, χ x = 0 ∨ χ x = 1
  /-- `χ_{u>0} ≤ χ` Lebesgue-a.e. on `Ω`. -/
  posIndicator_le_chi : ∀ᵐ x ∂(volume.restrict Ω), posIndicator u x ≤ χ x
  /-- The domain-variation identity (3.5) for every `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. -/
  innerVariation_eq_zero : ∀ ξ, IsLipTestField Ω ξ → innerVariation u χ ξ = 0

namespace IsVariationalSolution

variable {Ω Ω' : Set (Rn n)} {C C' : ℝ≥0} {u χ : Rn n → ℝ}

/-- A variational solution on `Ω` is one on every open subset of `Ω`. -/
theorem mono (h : IsVariationalSolution Ω C u χ) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) :
    IsVariationalSolution Ω' C u χ where
  isOpen := hΩ'
  nonneg x hx := h.nonneg x (hsub hx)
  continuousOn := h.continuousOn.mono hsub
  contDiffOn := h.contDiffOn.mono (inter_subset_inter_left _ hsub)
  lipschitzOnWith x r hr := h.lipschitzOnWith x r (hr.trans hsub)
  measurable_chi := by
    have : Ω'.indicator χ = Ω'.indicator (Ω.indicator χ) := by
      rw [indicator_indicator, inter_eq_left.2 hsub]
    rw [this]
    exact h.measurable_chi.indicator hΩ'.measurableSet
  chi_mem x hx := h.chi_mem x (hsub hx)
  posIndicator_le_chi := ae_restrict_of_ae_restrict_of_subset hsub h.posIndicator_le_chi
  innerVariation_eq_zero ξ hξ := h.innerVariation_eq_zero ξ (hξ.mono hsub)

/-- The constant of a variational solution can be increased. -/
theorem of_le (h : IsVariationalSolution Ω C u χ) (hC : C ≤ C') :
    IsVariationalSolution Ω C' u χ where
  isOpen := h.isOpen
  nonneg := h.nonneg
  continuousOn := h.continuousOn
  contDiffOn := h.contDiffOn
  lipschitzOnWith x r hr := (h.lipschitzOnWith x r hr).weaken hC
  measurable_chi := h.measurable_chi
  chi_mem := h.chi_mem
  posIndicator_le_chi := h.posIndicator_le_chi
  innerVariation_eq_zero := h.innerVariation_eq_zero

end IsVariationalSolution

end InnerVariational
