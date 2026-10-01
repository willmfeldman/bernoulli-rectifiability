/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.ChiInterior
public import InnerVariational.Registry.BV
public import InnerVariational.Registry.Harmonic
public import InnerVariational.Registry.GMT
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.HighestDensity
import InnerVariational.Monotonicity.Density
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
import InnerVariational.Regular.DensityQ
import InnerVariational.Monotonicity.SigmaHQ
public import GMTFoundations.Defs.GMT

/-!
# The density dichotomy at zeros of `u` (Lemma 8.1)

Lemma 8.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on `Ω`, `2 ≤ n`, and `x ∈ Ω` with `u(x) = 0`. Then

* `M_x(u; 0+) ∈ {0} ∪ [|B_1|/2, |B_1|]` (`Mzero_eq_zero_or_half_le`);
* `M_x(u; 0+) = 0` only if `x ∈ {u = 0}°` (`mem_interior_of_Mzero_eq_zero`);
* if `x ∈ ∂{u > 0}` and the blow-ups `u(x + r ·)/r` tend to `0`, then `M_x(u; 0+) = |B_1|`
  (`Mzero_eq_of_tendsto_rescale_zero`; the last line of the paper's proof reads `1`, the intended
  value being `|B_1|`).

Consequently `|B_1|/2 ≤ M_x(u; 0+) ≤ |B_1|` on `Ω ∩ ∂{u > 0}` (`half_le_Mzero_of_mem_frontier`).

## Proof

Every result here is the case `Q ≡ 1` of its version for a Lipschitz coefficient in
`Regular/DensityQ.lean`, via `IsVariationalSolution.toQ`, `QBounds.one` and `MzeroQ_one`. The
argument there: take a blow-up `u_{x,r_k} → u₀` (`exists_tendsto_rescale`, from
`exists_blowup_subseq`). It is one-homogeneous, `C_V`-Lipschitz, and harmonic on `{u₀ > 0}` (proof
of Proposition 3.5), and a subsequence of `χ_{x,r_k}` converges to `χ₀` with `(u₀, χ₀)` a
variational solution on `ℝⁿ` and `∫_{B_1} χ₀ = M_x(0+)`.

* If `u₀ ≢ 0`, Sperner's inequality (E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf
  Sphären*, Math. Z. 134 (1973), 317–327; `Registry.sperner_half_volume`, proved in the
  `Sperner` library) gives `|{u₀ > 0} ∩ B_1| ≥ |B_1|/2`, and `χ₀ ≥ χ_{u₀>0}` gives
  `|{u₀ > 0} ∩ B_1| ≤ ∫_{B_1} χ₀ = M_x(0+)` (`measureReal_pos_inter_ball_le`; the second
  paragraph of the proof of Lemma 8.1).
* If `u₀ ≡ 0`, the inner variation of `(0, χ₀)` gives `∫ χ₀ div ξ = 0`, so `χ₀` is a constant
  `c ∈ {0, 1}` on `B_1`, and `M_x(0+) = c |B_1| ∈ {0, |B_1|}`
  (`eq_zero_or_eq_of_tendsto_rescale_zero`; the last paragraph of the proof of Lemma 8.1).

The openness argument (third paragraph of the proof): `M` is upper semicontinuous
(Proposition 3.5), so `{M_y(0+) < |B_1|/4}` is a neighbourhood `B_δ(x)` of a point with
`M_x(0+) = 0`. By the dichotomy, every `y ∈ B_δ(x)` has `u(y) > 0` (density of `{χ = 1}` is `1`)
or `M_y(0+) = 0` (density `0`). So the essential boundary of `{χ = 1}` misses `B_δ(x)`, and
Federer's theorem (H. Federer, *Geometric Measure Theory*, Springer, 1969, 4.5.11 and 4.5.6;
`Registry.ae_trivial_of_essentialBoundary_inter_ball`, proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0) makes `{χ = 1}` null or full there.
Full contradicts density `0` at `x`; null forces `{u > 0} ∩ B_δ(x) = ∅`.

## Ordering of the paper's argument

The paper's second paragraph gives `M_x(0+) ≥ |B_1|/2` whenever some blow-up is nonzero. The case
where *every* blow-up vanishes, which the openness argument needs at every point of `B_δ(x)`, is
proved at the end of the paper's argument (the limit of `χ(x + r ·)` is constant, using the
`L¹_loc` compactness of `χ(x + r_k ·)` from Lemma 3.3 and BV compactness). Here it is proved first
(`eq_zero_or_eq_of_tendsto_rescale_zero`), and then the dichotomy.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Densities of `{χ = 1}` -/

/-- The Lebesgue density of `Ω ∩ {χ = 1}` at `x` is `d / |B_1|` when `r^{-n} ∫_{B_r(x)} χ → d`. -/
theorem hasDensity_of_tendsto (h : IsVariationalSolution Ω C u χ) {δ : ℝ} (hδ : 0 < δ)
    (hδΩ : ball x δ ⊆ Ω) {d : ℝ}
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 d)) :
    HasDensity (Ω ∩ {y | χ y = 1}) x (d / unitBallVolume n) :=
  h.toQ.hasDensity_of_tendsto hδ hδΩ hd

/-- Near a point with `u > 0`, `{χ = 1}` has density `1`. -/
theorem hasDensity_one_of_pos (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hpos : 0 < u x) : HasDensity (Ω ∩ {y | χ y = 1}) x 1 :=
  h.toQ.hasDensity_one_of_pos hx hpos

/-! ### Blow-ups at a zero of `u` -/

/-- Every sequence `r_k → 0+` has a subsequence along which `u_{x,r_k}` converges locally
uniformly (Arzelà–Ascoli, as in the proof of Proposition 3.5), provided `u(x) = 0`. -/
theorem exists_tendsto_rescale (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) (hux : u x = 0)
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => oneHomRescale u x (r (φ k))) u₀ atTop :=
  h.toQ.exists_tendsto_rescale hx hux hr hr0

section Blowup

variable [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) {m : ℝ}
  (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
  (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m))
  {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
include h hx hm hd hr hr0

/- The statements below keep the hypotheses `NeZero n` and `M_x(r) → m` of the `Q ≡ 1` chain; the
proofs only use the density limit. -/
set_option linter.unusedSectionVars false

/-- **Lower semicontinuity of the positivity set** (proof of Lemma 8.1): for a blow-up `u₀`,
`|{u₀ > 0} ∩ B_1| ≤ lim ∫_{B_1} χ_{x,r_k} = M_x(u; 0+)`, since `χ ≥ χ_{u>0}` and
`χ_{u₀>0} ≤ liminf χ_{u_{x,r_k}>0}`. -/
theorem measureReal_pos_inter_ball_le {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) ≤ m :=
  IsVariationalSolutionQ.measureReal_pos_inter_ball_le (QBounds.one Ω) h.toQ hx hd hr hr0 hconv

/-- **Sperner step** (proof of Lemma 8.1): if a blow-up `u₀` is not identically zero, then
`M_x(u; 0+) ≥ |B_1|/2`. Uses Sperner's inequality (`Registry.sperner_half_volume`). -/
theorem half_le_of_tendsto_rescale (hn : 2 ≤ n) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {y₀ : Rn n}
    (hy₀ : 0 < u₀ y₀) : unitBallVolume n / 2 ≤ m :=
  IsVariationalSolutionQ.half_le_of_tendsto_rescale (QBounds.one Ω) h.toQ hx hd hr hr0 hn hconv
    hy₀

/-- **Zero blow-ups** (last paragraph of the proof of Lemma 8.1, completed; see the module
docstring). If `u_{x,r_k} → 0` locally uniformly along some `r_k → 0+`, then
`M_x(u; 0+) ∈ {0, |B_1|}`. Uses Lemma 3.3, BV compactness and the strong `L²_loc` convergence of
gradients (proof of Proposition 3.5). -/
theorem eq_zero_or_eq_of_tendsto_rescale_zero
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) (fun _ => 0) atTop) :
    m = 0 ∨ m = unitBallVolume n :=
  IsVariationalSolutionQ.eq_zero_or_eq_of_tendsto_rescale_zero (QBounds.one Ω) h.toQ hx hd hr hr0
    hconv

end Blowup

/-! ### Lemma 8.1 -/

private theorem MzeroQ_one_apply (u χ : Rn n → ℝ) (x : Rn n) :
    MzeroQ ((fun _ : Rn n => (1 : ℝ)) x) u χ x = Mzero u χ x := by
  rw [MzeroQ_one]

/-- **Lemma 8.1**, first claim. If `2 ≤ n`, `x ∈ Ω` and
`u(x) = 0`, then `M_x(u; 0+)` is a real number `m ∈ {0} ∪ [|B_1|/2, |B_1|]`. -/
theorem Mzero_eq_zero_or_half_le [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hux : u x = 0) : ∃ m : ℝ, Mzero u χ x = m ∧
      (m = 0 ∨ unitBallVolume n / 2 ≤ m) ∧ m ≤ unitBallVolume n := by
  obtain ⟨m, hm, h1, h2⟩ :=
    IsVariationalSolutionQ.MzeroQ_eq_zero_or_half_le hn (QBounds.one Ω) h.toQ hx hux
  rw [MzeroQ_one_apply] at hm
  simp only [one_pow, one_mul] at h1 h2
  exact ⟨m, hm, h1, h2⟩

/-- **Lemma 8.1**, second claim.
`M_x(u; 0+) = 0` only if `x` is in the interior of `{u = 0}`. -/
theorem mem_interior_of_Mzero_eq_zero [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hM : Mzero u χ x = 0) : x ∈ interior {y | u y = 0} :=
  IsVariationalSolutionQ.mem_interior_of_MzeroQ_eq_zero hn (QBounds.one Ω) h.toQ hx
    (by rw [MzeroQ_one_apply]; exact hM)

/-- **Lemma 8.1**, last claim, with `M_x(u; 0+) = |B_1|` (the last line of the paper's proof
reads `1`; the intended value is `|B_1|`). If `x ∈ Ω ∩ ∂{u > 0}` and `u_{x,r_k} → 0` locally
uniformly along some `r_k → 0+`, then `M_x(u; 0+) = |B_1|`. The paper assumes `u(x + r ·)/r → 0` as
`r → 0`; convergence along one sequence suffices. -/
theorem Mzero_eq_of_tendsto_rescale_zero [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y})
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) (fun _ => 0) atTop) :
    Mzero u χ x = unitBallVolume n := by
  have := IsVariationalSolutionQ.MzeroQ_eq_of_tendsto_rescale_zero hn (QBounds.one Ω) h.toQ hx
    hfr hr hr0 hconv
  rwa [MzeroQ_one_apply, one_pow, one_mul] at this

/-- On the free boundary, `|B_1|/2 ≤ M_x(u; 0+) ≤ |B_1|` (used in the proofs of Lemmas 8.2
and 8.3). -/
theorem half_le_Mzero_of_mem_frontier [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) : ∃ m : ℝ, Mzero u χ x = m ∧
      unitBallVolume n / 2 ≤ m ∧ m ≤ unitBallVolume n := by
  obtain ⟨m, hm, h1, h2⟩ :=
    IsVariationalSolutionQ.half_le_MzeroQ_of_mem_frontier hn (QBounds.one Ω) h.toQ hx hfr
  rw [MzeroQ_one_apply] at hm
  simp only [one_pow, one_mul] at h1 h2
  exact ⟨m, hm, h1, h2⟩

end IsVariationalSolution

end InnerVariational
