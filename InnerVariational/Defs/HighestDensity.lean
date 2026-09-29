/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Quantities
public import GMTFoundations.Defs.GMT

/-!
# The set of highest density and the Jones number

* `sigmaH Ω u χ = Σ^H`, the free boundary points of highest density (defined at the start of
  Section 6 of Kriventsov–Weiss).
* `sigmaHr Ω u χ r = Σ^H_r` (same place).
* `jonesBetaSq μ x r = β²_μ(x, r)` (Section 6.1), the squared `L²` Jones number with respect to
  affine hyperplanes.

## Encoding

* The definition of `Σ^H` in Section 6 is
  `Σ^H = {x ∈ Ω : x ∈ closure{u>0}, M_x(u;0+) ≥ |B_1|}`. We define it as `M_x(u; r) ≥ |B_1|`
  *for every admissible radius* (`0 < r`, `closedBall x r ⊆ Ω`). For a variational solution
  `r ↦ M_x(u; r)` is nondecreasing (Proposition 3.4), so this is equivalent to
  `M_x(u; 0+) ≥ |B_1|`; the equivalence is `mem_sigmaH_iff`. This form avoids a limit with
  values in `[−∞, ∞)`.
* `Σ^H_r` requires `B_r(x) ⊂⊂ Ω`. For `r > 0` in `ℝⁿ` this means `closedBall x r ⊆ Ω`, because the
  closure of `B_r(x)` is `closedBall x r` and it is compact. We also record `x ∈ Ω` explicitly, as
  the paper does.
* `jonesBetaSq` takes the infimum over affine hyperplanes `L = {y : ⟪y − p, ν⟫ = 0}`,
  `‖ν‖ = 1`, for which `dist(y, L) = |⟪y − p, ν⟫|`. It is valued in `ℝ≥0∞`. It is normalized by
  `r^{n-1}`, i.e. codimension one, as in the paper. It is defined in the dependency
  gmt-foundations v0.1.0 (https://github.com/willmfeldman/gmt-foundations) and re-exported here.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The set of highest density `Σ^H` (Kriventsov–Weiss, start of Section 6), in the form
`x ∈ Ω`, `x ∈ closure {u > 0}`, and `M_x(u; r) ≥ |B_1|` for every `r > 0` with `B_r(x) ⊂⊂ Ω`.
The paper asks for `M_x(u; 0+) ≥ |B_1|`; the two agree for variational solutions by the
monotonicity of `M` (Proposition 3.4, see `mem_sigmaH_iff`). `B_r(x) ⊂⊂ Ω` is encoded as
`closedBall x r ⊆ Ω`, because `M_x(u; r)` reads `u` on `∂B_r(x)`: with `ball x r ⊆ Ω` it would see
values of `u` outside `Ω`, and the equivalence with `M_x(0+)` would fail. -/
def sigmaH (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    ∀ r, 0 < r → closedBall x r ⊆ Ω → unitBallVolume n ≤ monotonicityM u χ x r}

/-- `Σ^H_r = {x ∈ Ω : B_r(x) ⊂⊂ Ω, x ∈ closure {u > 0}, M_x(u; r) ≥ |B_1|}` (Kriventsov–Weiss,
start of Section 6). `B_r(x) ⊂⊂ Ω` is encoded as `closedBall x r ⊆ Ω`. -/
def sigmaHr (Ω : Set (Rn n)) (u χ : Rn n → ℝ) (r : ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ closedBall x r ⊆ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    unitBallVolume n ≤ monotonicityM u χ x r}

/-! The squared Jones number `jonesBetaSq μ x r = β²_μ(x, r)` (Section 6.1 of the paper) is
defined in gmt-foundations (`GMTFoundations/Defs/GMT.lean`) and re-exported here. -/
export GMTFoundations (jonesBetaSq)

theorem sigmaH_subset (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : sigmaH Ω u χ ⊆ Ω :=
  fun _ hx => hx.1

theorem sigmaH_subset_closure (Ω : Set (Rn n)) (u χ : Rn n → ℝ) :
    sigmaH Ω u χ ⊆ closure {y | 0 < u y} :=
  fun _ hx => hx.2.1

theorem sigmaHr_subset (Ω : Set (Rn n)) (u χ : Rn n → ℝ) (r : ℝ) : sigmaHr Ω u χ r ⊆ Ω :=
  fun _ hx => hx.1

/-- `Σ^H ∩ Ω_r ⊆ Σ^H_r` (stated after the definition of `Σ^H_r` in
Kriventsov–Weiss, Section 6), where `Ω_r = {x : B_r(x) ⊂⊂ Ω}`. -/
theorem mem_sigmaHr_of_mem_sigmaH {Ω : Set (Rn n)} {u χ : Rn n → ℝ} {x : Rn n} {r : ℝ}
    (hx : x ∈ sigmaH Ω u χ) (hr : 0 < r) (hball : closedBall x r ⊆ Ω) :
    x ∈ sigmaHr Ω u χ r :=
  ⟨hx.1, hball, hx.2.1, hx.2.2 r hr hball⟩

end InnerVariational
