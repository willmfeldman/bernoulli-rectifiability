/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Perimeter
public import InnerVariational.Regular.HarmonicCone
public import InnerVariational.Blowup.ExplicitForm
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Regular.Density
import InnerVariational.Regular.DensityQ
public import InnerVariational.Regular.Viscosity.MainQ
import InnerVariational.Monotonicity.SigmaHQ
import InnerVariational.Registry.BV
import InnerVariational.Regular.ChiInterior
import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Monotonicity.Density
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Registry.Harmonic
public import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.Solutions
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
public import InnerVariational.Regular.Viscosity.Classification

/-!
# Lemma 8.3: variational solutions are viscosity solutions off `Σ^H`

Lemma 8.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on `Ω`, `2 ≤ n`, with `Σ^H = ∅`. Then `u` is a viscosity solution on `Ω`
(`IsViscositySolution`). The paper's Definition 8.1 of viscosity solution concludes `|∇u| ≤ 1`
(resp. `|∇u| ≥ 1`) at the touching point; since `u` is not differentiable at free boundary
points, the conclusion used here is `|∇φ(x)| ≤ 1` (resp. `|∇φ(x)| ≥ 1`) for the touching
function `φ`.

## Main results

* `IsVariationalSolution.isViscositySolution`: the lemma as stated in the paper.
* `IsVariationalSolution.isViscositySolution_diff_sigmaH`: `u` is a viscosity solution on the open
  set `Ω \ Σ^H`, for any variational solution.
* `IsVariationalSolution.norm_gradient_le_one_of_le`,
  `IsVariationalSolution.one_le_norm_gradient_of_le_max`: the pointwise statements at a free
  boundary point `x ∉ Σ^H`.

## Proof

Let `φ` touch `u` from below (resp. `φ₊` from above) at `x ∈ Ω ∩ ∂{u > 0}`, `x ∉ Σ^H`, and let
`p = ∇φ(x)`, `β = |p|`, `e = p / β`.

1. `M_x(u; 0+) = m ∈ [|B_1|/2, |B_1|)` (Lemma 8.1 and `x ∉ Σ^H`). Along `r_k → 0+` the blow-ups
   `u_{x,r_k} → u₀` locally uniformly (Proposition 3.5); `u₀` is Lipschitz, one-homogeneous,
   harmonic on
   `{u₀ > 0}`, and `|{u₀ > 0} ∩ B_1| ≤ m`. By Lemma 8.1's last claim, `u₀ ≢ 0`.
2. `χ_{x,r_k} → χ₀` in `L¹_loc` along a subsequence (Lemma 3.3 and BV compactness, L. C. Evans
   and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed., CRC Press,
   2015, Theorem 5.5), and the
   inner variation passes to the limit (`exists_chi_blowup`): `∫ Q_ξ(∇u₀) + ∫ χ₀ div ξ = 0`,
   `χ₀ ∈ {0, 1}`, `χ₀ ≥ χ_{u₀ > 0}`, `∫_{B_1} χ₀ = m`.
3. `φ(x + r y)/r → ⟪p, y⟫`, so `⟪p, y⟫ ≤ u₀(y)` (resp. `u₀(y) ≤ ⟪p, y⟫₊`).
4. Classification (the proof of Lemma 8.3, classification of `u₀`): `u₀ = a ⟪y, e⟫₊`, `a > 0`
   (`eq_mul_max_of_le_max`, `eq_mul_max_of_le`). From above, `{u₀ > 0}` lies in the half-space
   `{⟪y, e⟫ > 0}`, so each component has volume `≤ |B_1|/2` and the equality case of Sperner's
   inequality (E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134
   (1973), 317–327) applies. From below, the component through `e` contains the half-space; it
   *is* the half-space (`connectedComponentIn_eq_halfSpace`, `Regular/HarmonicCone.lean`; the
   paper uses domain monotonicity of the first Dirichlet eigenvalue), and any further
   component would add `|B_1|/2` by Sperner's inequality, contradicting
   `|{u₀ > 0} ∩ B_1| ≤ m < |B_1|`.
5. The half-space computation (end of the proof of Lemma 8.3, `eq_one_of_halfSpace`): `a = 1`.
6. Hence `β = ⟪p, e⟫ ≤ u₀(e) = 1` (resp. `1 = u₀(e) ≤ β`).

Steps 4 and 5 and the deviations from the paper's argument there are in
`Regular/Viscosity/Classification.lean`. The pointwise statements and the blow-up data are the
case `Q ≡ 1` of their versions for a Lipschitz coefficient (`Regular/Viscosity/MainQ.lean`), via
`IsVariationalSolution.toQ`, `QBounds.one` and `IsVariationalSolution.sigmaHQ_one`; steps 3–6
are carried out there.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

set_option linter.unusedVariables false in
/-- **Blow-up pairs** (proof of Lemma 8.3). Along a blow-up sequence `u_{x,r_k} → u₀` with
`M_x(r) → m`, a subsequence of `χ_{x,r_k}` converges a.e. and in `L¹_loc` to some `χ₀` with

* `χ₀ ∈ {0, 1}` a.e. on `B_1`, and `χ₀ = 1` a.e. on `B_1 ∩ {u₀ > 0}`;
* `∫_{B_1} χ₀ = m`;
* the limit domain variation identity `∫ (|∇u₀|² div ξ − 2 ∇u₀·Dξ ∇u₀) + ∫ χ₀ div ξ = 0` for all
  `ξ ∈ C^∞_c(B_1; ℝⁿ)`.

Uses Lemma 3.3, BV compactness and the strong `L²_loc` convergence of gradients (proof of
Proposition 3.5), through the blow-up limit `IsVariationalSolutionQ.exists_blowup_limit_density`.
-/
theorem exists_chi_blowup [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) {m : ℝ}
    (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    ∃ f₀ : Rn n → ℝ, Measurable f₀ ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1) ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → f₀ y = 1) ∧
      ∫ y in ball (0 : Rn n) 1, f₀ y = m ∧
      ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
        (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, f₀ y * divergence ξ y = 0 := by
  obtain ⟨χ₀, hsol, hint⟩ := IsVariationalSolutionQ.exists_blowup_limit_density (QBounds.one Ω)
    h.toQ hx hd hr hr0 hconv
  obtain ⟨hχ₀m, h01, hpos, hid⟩ := (isVariationalSolutionQ_one_iff.1 hsol).blowup_chi_data
  exact ⟨χ₀, hχ₀m, h01, hpos, hint, hid⟩

/-! ### Lemma 8.3 -/

/-- The blow-up data at a free boundary point `x ∉ Σ^H` (proof of Lemma 8.3): a blow-up
`u_{x,r_k} → u₀` that is Lipschitz, nonnegative, one-homogeneous, harmonic on `{u₀ > 0}`, not
identically zero (Lemma 8.1, last claim), with `|{u₀ > 0} ∩ B_1| ≤ M_x(0+) < |B_1|`, and a limit
`χ₀` of `χ_{x,r_k}` satisfying the limit domain variation identity (`exists_chi_blowup`). -/
theorem exists_blowup_of_notMem_sigmaH (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) (hS : x ∉ sigmaH Ω u χ) :
    ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝 0) ∧ ∃ u₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop ∧
      LipschitzWith C u₀ ∧ (∀ y, 0 ≤ u₀ y) ∧ (∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y) ∧
      (∀ y, 0 < u₀ y → HarmonicAt u₀ y) ∧ (∃ y, 0 < u₀ y) ∧
      volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) < unitBallVolume n ∧
      ∃ f₀ : Rn n → ℝ, Measurable f₀ ∧
        (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1) ∧
        (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → f₀ y = 1) ∧
        ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
          (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, f₀ y * divergence ξ y = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨r, hr, hr0, u₀, hconv, hhom, hy₀, hvol, χ₀, hsol⟩ :=
    IsVariationalSolutionQ.exists_blowup_of_notMem_sigmaHQ hn (QBounds.one Ω) h.toQ hx hfr
      (by rwa [h.sigmaHQ_one])
  have h₀ := isVariationalSolutionQ_one_iff.1 hsol
  obtain ⟨hχ₀m, h01, hpos, hid⟩ := h₀.blowup_chi_data
  exact ⟨r, hr, hr0, u₀, hconv, hsol.lipschitzWith_of_univ, fun y => h₀.nonneg y trivial, hhom,
    fun y hy => h₀.harmonicOn_pos trivial hy, hy₀, hvol, χ₀, hχ₀m, h01, hpos, hid⟩

/-- **Lemma 8.3**, touching from below. If `x ∈ Ω ∩ ∂{u > 0}`, `x ∉ Σ^H`,
`φ` is smooth, `φ(x) = 0` and `φ ≤ u` on `B_ρ(x)`, then `|∇φ(x)| ≤ 1`. -/
theorem norm_gradient_le_one_of_le (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) (hS : x ∉ sigmaH Ω u χ) {ρ : ℝ} (hρ : 0 < ρ)
    {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφx : φ x = 0) (hle : ∀ y ∈ ball x ρ, φ y ≤ u y) :
    ‖gradient φ x‖ ≤ 1 :=
  haveI : NeZero n := ⟨by omega⟩
  IsVariationalSolutionQ.norm_gradient_le_of_le hn (QBounds.one Ω) h.toQ hx hfr
    (by rwa [h.sigmaHQ_one]) hρ hφ hφx hle

/-- **Lemma 8.3**, touching from above. If `x ∈ Ω ∩ ∂{u > 0}`, `x ∉ Σ^H`,
`φ` is smooth, `φ(x) = 0` and `u ≤ φ₊` on `B_ρ(x)`, then `|∇φ(x)| ≥ 1`. -/
theorem one_le_norm_gradient_of_le_max (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) (hS : x ∉ sigmaH Ω u χ) {ρ : ℝ} (hρ : 0 < ρ)
    {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφx : φ x = 0)
    (hle : ∀ y ∈ ball x ρ, u y ≤ max (φ y) 0) : 1 ≤ ‖gradient φ x‖ :=
  haveI : NeZero n := ⟨by omega⟩
  IsVariationalSolutionQ.le_norm_gradient_of_le_max hn (QBounds.one Ω) h.toQ hx hfr
    (by rwa [h.sigmaHQ_one]) hρ hφ hφx hle

/-- **Lemma 8.3**. Let `(u, χ)` be a variational solution on
`Ω`, `2 ≤ n`, with `Σ^H = ∅`. Then `u` is a viscosity solution on `Ω`, with the conclusions
`|∇φ(x)| ≤ 1` (resp. `≥ 1`) for the touching function `φ`; the paper's Definition 8.1 writes
`|∇u|`, which is not defined at free boundary points. -/
theorem isViscositySolution (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hS : sigmaH Ω u χ = ∅) : IsViscositySolution Ω u where
  continuousOn := h.continuousOn
  nonneg := h.nonneg
  harmonicAt _ hx hpos := h.harmonicOn_pos hx hpos
  norm_gradient_le x hx _ hr _ _ hφ hφx hle :=
    h.norm_gradient_le_one_of_le hn hx.1 hx.2 (by rw [hS]; exact notMem_empty x) hr hφ hφx hle
  one_le_norm_gradient x hx _ hr _ _ hφ hφx hle :=
    h.one_le_norm_gradient_of_le_max hn hx.1 hx.2 (by rw [hS]; exact notMem_empty x) hr hφ hφx
      hle

/-- **Lemma 8.3 on `Ω \ Σ^H`**. For every variational solution
`(u, χ)` on `Ω`, `2 ≤ n`, `u` is a viscosity solution on the open set `Ω \ Σ^H`. -/
theorem isViscositySolution_diff_sigmaH (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    IsViscositySolution (Ω \ sigmaH Ω u χ) u := by
  haveI : NeZero n := ⟨by omega⟩
  exact h.diff_sigmaH.isViscositySolution hn h.sigmaH_diff_sigmaH_eq_empty

end IsVariationalSolution

end InnerVariational
