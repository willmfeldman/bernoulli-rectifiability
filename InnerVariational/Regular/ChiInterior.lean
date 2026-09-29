/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Kernel.BV
public import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.Density
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Regular.ChiInteriorQ
import InnerVariational.Monotonicity.SigmaHQ

/-!
# `χ` on the interior of the zero set

The start of §8.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure,
and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on `Ω`. On an open set `U ⊆ Ω` where `u ≡ 0`, the inner variation
(equation (3.5)) reduces to `∫ χ div ξ = 0` for `ξ ∈ C^{0,1}_c(U; ℝⁿ)`. Hence `χ` is a.e.
constant, equal to `0` or `1`, on each connected open subset of `{u = 0}°`. Correspondingly
`M_x(u; 0+) = 0` (the "natural" case) or `M_x(u; 0+) = |B_1|` (the "pathological" case, e.g.
`(u, χ) = (0, 1)`) there.

## Main statements

* `IsVariationalSolution.integral_chi_mul_divergence_eq_zero`: `∫ χ div ξ = 0` for test fields
  supported in an open set where `u = 0`.
* `IsVariationalSolution.exists_ae_eq_const_of_eq_zero`: if `u = 0` on a preconnected open
  `U ⊆ Ω`, then `χ = c` a.e. on `U` with `c ∈ {0, 1}`.
* `IsVariationalSolution.chi_ae_eq_const_connectedComponentIn`: the paper's form, on each
  connected component of `Ω ∩ {u = 0}°`.
* `IsVariationalSolution.Mzero_eq_of_ae_eq_const`,
  `IsVariationalSolution.Mzero_mem_of_mem_interior`: `M_x(u; 0+) = c |B_1|` when `χ = c` a.e.
  near `x`; so `M_x(u; 0+) ∈ {0, |B_1|}` on `{u = 0}°`.

The constancy step is the "zero distributional gradient" fact
(`exists_ae_eq_const_of_hasWeakGrad_zero`, in divergence form in `Regular/ZeroGradient.lean`).
Every statement is the case `Q ≡ 1` of its version for a Lipschitz coefficient
(`Regular/ChiInteriorQ.lean`), via `IsVariationalSolution.toQ` and `QBounds.one`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-- On an open set `U ⊆ Ω` with `u = 0`, the inner variation reduces to `∫ χ div ξ = 0` for
`ξ ∈ C^{0,1}_c(U; ℝⁿ)` (start of §8.1), because `∇u = 0` on `U`. -/
theorem integral_chi_mul_divergence_eq_zero (h : IsVariationalSolution Ω C u χ) {U : Set (Rn n)}
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) (hu : ∀ y ∈ U, u y = 0) {ξ : Rn n → Rn n}
    (hξ : IsLipTestField U ξ) : ∫ y, χ y * divergence ξ y = 0 :=
  h.toQ.integral_chi_mul_divergence_eq_zero (QBounds.one Ω) hU hUΩ hu hξ

/-- `χ` is locally integrable on every open `U ⊆ Ω` (it is measurable with `|χ| ≤ 1`). -/
theorem locallyIntegrableOn_chi (h : IsVariationalSolution Ω C u χ) {U : Set (Rn n)}
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) : LocallyIntegrableOn χ U :=
  h.toQ.locallyIntegrableOn_chi hU hUΩ

/-- **`u ≡ 0 ⇒ χ` a.e. constant** (start of §8.1). If `u = 0` on a preconnected open `U ⊆ Ω`,
then `χ = c` a.e. on `U` for some `c ∈ {0, 1}`. -/
theorem exists_ae_eq_const_of_eq_zero (h : IsVariationalSolution Ω C u χ) {U : Set (Rn n)}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUΩ : U ⊆ Ω) (hu : ∀ y ∈ U, u y = 0) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧ ∀ᵐ y ∂(volume.restrict U), χ y = c :=
  h.toQ.exists_ae_eq_const_of_eq_zero (QBounds.one Ω) hU hUc hUΩ hu

/-- **`χ` on `{u = 0}°`** (start of §8.1): `χ` is a.e. constant, equal to `0` or `1`, on each
connected component of `Ω ∩ {u = 0}°`. (For `x ∉ Ω ∩ {u = 0}°` the component is empty.) -/
theorem chi_ae_eq_const_connectedComponentIn (h : IsVariationalSolution Ω C u χ) (x : Rn n) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧ ∀ᵐ y ∂(volume.restrict
      (connectedComponentIn (Ω ∩ interior {y | u y = 0}) x)), χ y = c :=
  h.toQ.chi_ae_eq_const_connectedComponentIn (QBounds.one Ω) x

/-- `M_x(u; 0+) = c |B_1|` when `u(x) = 0` and `χ = c` a.e. near `x` (Proposition 3.5, (3.10)). -/
theorem Mzero_eq_of_ae_eq_const [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    (hx : x ∈ Ω) (hux : u x = 0) {δ : ℝ} (hδ : 0 < δ) {c : ℝ}
    (hc : ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = c) :
    Mzero u χ x = ((c * unitBallVolume n : ℝ) : EReal) := by
  have := h.toQ.MzeroQ_eq_of_ae_eq_const (QBounds.one Ω) hx hux hδ hc
  rwa [MzeroQ_one, one_pow, one_mul] at this

/-- `M_x(u; 0+) ∈ {0, |B_1|}` on `Ω ∩ {u = 0}°` (start of §8.1). -/
theorem Mzero_mem_of_mem_interior [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    (hx : x ∈ Ω) (hint : x ∈ interior {y | u y = 0}) :
    Mzero u χ x = 0 ∨ Mzero u χ x = unitBallVolume n := by
  have := h.toQ.MzeroQ_mem_of_mem_interior (QBounds.one Ω) hx hint
  rwa [MzeroQ_one, one_pow, one_mul] at this

end IsVariationalSolution

end InnerVariational
