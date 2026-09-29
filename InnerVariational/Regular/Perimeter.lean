/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Density
import InnerVariational.Registry.GMT
import InnerVariational.Regular.ChiInterior
import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Monotonicity.Density
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Basic.Polar
public import InnerVariational.Regular.PerimeterQ
import InnerVariational.Monotonicity.SigmaHQ
import InnerVariational.Monotonicity.HighestDensityQ
public import GMTFoundations.Defs.GMT

/-!
# The regular free boundary has locally finite perimeter (Lemma 8.2)

Lemma 8.2 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on a connected open set `Ω` with `Σ^H = ∅` and `2 ≤ n`. Then

* either `u ≡ 0` (and then `χ = 1` a.e.), or `χ = χ_{u>0}` a.e. on `Ω`
  (`eq_zero_or_ae_chi_eq_posIndicator`);
* `{u > 0}` has locally finite perimeter in `Ω` (`hasLocallyFinitePerimeter_pos`);
* `ℋ^{n-1}(∂{u > 0} ∩ B_r(x)) ≤ C(C_V) r^{n-1}` whenever `B̄_{2r}(x) ⊆ Ω`
  (`hausdorffN_frontier_pos_inter_ball_le`, with `C = 2^{n+1} |B_1| C_V²`).

Only the dichotomy uses connectedness. The perimeter bound and `|∂{u > 0} ∩ Ω| = 0` are local.

## Localization to `Ω \ Σ^H`

For applying Lemma 8.3 (variational solutions are viscosity solutions off `Σ^H`) on
`Ω' = Ω \ Σ^H`:

* `IsVariationalSolution.sigmaH_eq_inter_of_subset`: `Σ^H(Ω') = Σ^H(Ω) ∩ Ω'` for open `Ω' ⊆ Ω`;
* `IsVariationalSolution.isOpen_diff_sigmaH`: `Ω \ Σ^H` is open (`Σ^H` is relatively closed);
* `IsVariationalSolution.diff_sigmaH`, `IsVariationalSolution.sigmaH_diff_sigmaH_eq_empty`:
  `(u, χ)` is a variational solution on `Ω \ Σ^H`, and its `Σ^H` there is empty.

## Proof

Every statement except the localization of `Σ^H` is the case `Q ≡ 1` of its version for a
Lipschitz coefficient (`Regular/PerimeterQ.lean`), via `IsVariationalSolution.toQ`, `QBounds.one`
and `IsVariationalSolution.sigmaHQ_one`.

The paper's proof argues: `χ = χ_{u>0}` off `∂{u > 0}` ("as discussed at the start of
this section"); on `∂{u > 0} ∩ Ω` the density `M_x(0+)/|B_1|` of `{χ = 1}` lies in `[1/2, 1)` by
Lemma 8.1 and `Σ^H = ∅`, so `∂{u > 0} ∩ Ω ⊆ ∂ᵉ{χ = 1}`, and Lemma 3.3 with Federer's
`|Dχ_E| = ℋ^{n-1}⌊∂ᵉE` (H. Federer, *Geometric Measure Theory*, Springer, 1969, 4.5.6 and
4.5.11; the BV structure theorem, L. C. Evans and R. F. Gariepy, *Measure Theory and Fine
Properties of Functions*, rev. ed., CRC Press, 2015, §5.7–5.8; both proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0) bounds its measure.

* The "start of the section" step (§8.1): the set `A` of points near which `u = 0` and
  `χ = 1` a.e. is open, and relatively closed in `Ω`: at `x ∈ closure A ∩ Ω` upper
  semicontinuity gives `M_x(0+) ≥ |B_1|`, so `x ∉ closure {u > 0}` (as `Σ^H = ∅`), so `u = 0` near
  `x`, where `χ` is constant (`Regular/ChiInterior.lean`) and hence `1`. If `A = Ω` then
  `u ≡ 0`; if `A = ∅` then `χ = 0` a.e. on `Ω \ closure {u > 0}`.
* `|∂{u > 0} ∩ Ω| = 0`: we use the Lebesgue density theorem (densities are `0` or `1` a.e.)
  instead of the paper's `ℋ^{n-1}`-finiteness, which would need the comparison of `ℋ^n` with
  Lebesgue measure.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Localization to `Ω \ Σ^H` -/

/-- `Σ^H` is local: for open `Ω' ⊆ Ω`, `Σ^H(Ω') = Σ^H(Ω) ∩ Ω'`. -/
theorem sigmaH_eq_inter_of_subset [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {Ω' : Set (Rn n)} (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) :
    sigmaH Ω' u χ = sigmaH Ω u χ ∩ Ω' := by
  rw [← (h.mono hΩ' hsub).sigmaHQ_one, ← h.sigmaHQ_one, sigmaHQ_inter_of_subset hsub]

/-- `Ω \ Σ^H` is open (start of §8.1: `Σ^H` is relatively closed, by upper semicontinuity of
`x ↦ M_x(u; 0+)`). -/
theorem isOpen_diff_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    IsOpen (Ω \ sigmaH Ω u χ) := by
  rw [← h.sigmaHQ_one]
  exact h.toQ.isOpen_diff_sigmaHQ (QBounds.one Ω)

/-- `(u, χ)` is a variational solution on `Ω \ Σ^H`. -/
theorem diff_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    IsVariationalSolution (Ω \ sigmaH Ω u χ) C u χ :=
  h.mono h.isOpen_diff_sigmaH diff_subset

/-- On `Ω' = Ω \ Σ^H`, the set of highest density is empty. So the results below (and
Lemma 8.3) apply on `Ω'`. -/
theorem sigmaH_diff_sigmaH_eq_empty [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    sigmaH (Ω \ sigmaH Ω u χ) u χ = ∅ := by
  rw [h.sigmaH_eq_inter_of_subset h.isOpen_diff_sigmaH diff_subset]
  exact inter_diff_self _ _

/-! ### Densities on the free boundary -/

/-- A point of `Ω` outside `closure {u > 0}` has a ball in `Ω` on which `u = 0`. -/
theorem exists_ball_eq_zero (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hncl : x ∉ closure {y | 0 < u y}) :
    ∃ δ > 0, ball x δ ⊆ Ω ∧ ∀ y ∈ ball x δ, u y = 0 :=
  h.toQ.exists_ball_eq_zero hx hncl

/-- On `∂{u > 0} ∩ Ω`, if `Σ^H = ∅`, then `{χ = 1}` has a density `d ∈ [1/2, 1)` (proof of
Lemma 8.2):
`d = M_x(0+)/|B_1|` with `M_x(0+) ∈ [|B_1|/2, |B_1|)` by Lemma 8.1 and `x ∉ Σ^H`. -/
theorem exists_hasDensity_of_mem_frontier [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅)
    (hx : x ∈ Ω ∩ frontier {y | 0 < u y}) :
    ∃ d : ℝ, HasDensity (Ω ∩ {y | χ y = 1}) x d ∧ 1 / 2 ≤ d ∧ d < 1 :=
  h.toQ.exists_hasDensity_of_mem_frontier hn (QBounds.one Ω) (by rwa [h.sigmaHQ_one]) hx

/-- `∂{u > 0} ∩ Ω ⊆ ∂ᵉ{χ = 1}` when `Σ^H = ∅` (proof of Lemma 8.2). -/
theorem frontier_pos_inter_subset_essentialBoundary [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) :
    Ω ∩ frontier {y | 0 < u y} ⊆ essentialBoundary (Ω ∩ {y | χ y = 1}) :=
  h.toQ.frontier_pos_inter_subset_essentialBoundary hn (QBounds.one Ω) (by rwa [h.sigmaHQ_one])

/-- `|∂{u > 0} ∩ Ω| = 0` when `Σ^H = ∅` (proof of Lemma 8.2), by the Lebesgue density theorem. -/
theorem volume_inter_frontier_pos_eq_zero [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) :
    volume (Ω ∩ frontier {y | 0 < u y}) = 0 :=
  h.toQ.volume_inter_frontier_pos_eq_zero hn (QBounds.one Ω) (by rwa [h.sigmaHQ_one])

/-! ### Lemma 8.2 -/

/-- **Lemma 8.2**, dichotomy. On a connected open `Ω` with
`Σ^H = ∅`: either `u ≡ 0` and `χ = 1` a.e., or `χ = χ_{u>0}` a.e. on `Ω`. (If `u ≡ 0` and `χ = 0`
a.e., the second alternative holds.) -/
theorem eq_zero_or_ae_chi_eq_posIndicator [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hΩc : IsPreconnected Ω) (hS : sigmaH Ω u χ = ∅) :
    ((∀ y ∈ Ω, u y = 0) ∧ ∀ᵐ y ∂(volume.restrict Ω), χ y = 1) ∨
      ∀ᵐ y ∂(volume.restrict Ω), χ y = posIndicator u y :=
  h.toQ.eq_zero_or_ae_chi_eq_posIndicator hn (QBounds.one Ω) hΩc (by rwa [h.sigmaHQ_one])

/-- **Lemma 3.3 as a perimeter measure** (with the BV structure theorem): `{χ = 1}` has a
Gauss–Green pair on
`B_{3r/2}(x)` with total mass `≤ 2^{n+1} |B_1| C_V² r^{n-1}` when `B̄_{2r}(x) ⊆ Ω`. -/
theorem exists_isGaussGreenPair_chi [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    {r : ℝ} (hr : 0 < r) (hball : closedBall x (2 * r) ⊆ Ω) :
    ∃ μ ν, IsGaussGreenPair (ball x (3 * r / 2)) (Ω ∩ {y | χ y = 1}) μ ν ∧
      μ (ball x (3 * r / 2)) ≤
        ENNReal.ofReal (2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * r ^ (n - 1)) := by
  obtain ⟨μ, ν, hpair, hμ⟩ := h.toQ.exists_isGaussGreenPair_chi hn (QBounds.one Ω) hr hball
  rw [one_pow, div_one] at hμ
  exact ⟨μ, ν, hpair, hμ⟩

/-- **Lemma 8.2**, perimeter bound. If `Σ^H = ∅` and
`B̄_{2r}(x) ⊆ Ω`, then `ℋ^{n-1}(∂{u > 0} ∩ B_r(x)) ≤ 2^{n+1} |B_1| C_V² r^{n-1}`. Connectedness
of `Ω` is not needed. -/
theorem hausdorffN_frontier_pos_inter_ball_le [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    hausdorffN n (n - 1) (frontier {y | 0 < u y} ∩ ball x r) ≤
      ENNReal.ofReal (2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * r ^ (n - 1)) := by
  have := h.toQ.hausdorffN_frontier_pos_inter_ball_le hn (QBounds.one Ω)
    (by rwa [h.sigmaHQ_one]) hr hball
  rwa [one_pow, div_one] at this

/-- **Lemma 8.2**, locally finite perimeter. If
`χ = χ_{u>0}` a.e. on `Ω` (the second alternative of the dichotomy), then `Ω ∩ {u > 0}` has a
Gauss–Green pair on every `B_{3r/2}(x)` with `B̄_{2r}(x) ⊆ Ω`. -/
theorem hasLocallyFinitePerimeter_pos [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hae : ∀ᵐ y ∂(volume.restrict Ω), χ y = posIndicator u y) {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    HasLocallyFinitePerimeter (ball x (3 * r / 2)) (Ω ∩ {y | 0 < u y}) :=
  h.toQ.hasLocallyFinitePerimeter_pos hn (QBounds.one Ω) hae hr hball

end IsVariationalSolution

end InnerVariational
