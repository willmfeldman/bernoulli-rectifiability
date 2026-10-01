/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Homogeneity
public import InnerVariational.Monotonicity.DensityQ
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Monotonicity.Radial
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Kernel.Harmonic
import InnerVariational.Basic.Polar

/-!
# Blow-ups and the density formula (3.10)

The last claim of Proposition 3.4 of Kriventsov–Weiss (see the references), and
Proposition 3.5, including the density formula (3.10). Let `(u, χ)` be a variational solution on
`Ω` and `x ∈ Ω`.

## Blow-ups (Proposition 3.4)

Let `r_k → 0+` and `u_{x, r_k} → u₀` locally uniformly on `ℝⁿ`. Then `u(x) = 0`
(`IsVariationalSolution.eq_zero_of_tendstoLocallyUniformly_rescale`), `u₀` is `C_V`-Lipschitz and
harmonic on `{u₀ > 0}` (`blowup_lipschitzWith`, `blowup_isLipHarmonicPos`), it satisfies Euler's
identity `∇u₀(y)·y = u₀(y)` (`blowup_inner_gradient_eq`), and it is homogeneous of degree one
(`blowup_homogeneous`). Such limits exist along a subsequence of any `r_k → 0+`
(`exists_blowup_subseq`, `Blowup.lean`). The paper's `W^{1,2}` bound is immediate from the
Lipschitz bound.

Proposition 3.4 states, for every `x`, that the rescalings `u_{x,r}` are bounded in `W^{1,2}(D)`
and that their subsequential limits are homogeneous of degree one. This holds only when
`u(x) = 0`: if `u(x) > 0`, then `u_{x,r}(0) = u(x)/r → ∞`. Here the hypothesis is the existence
of a locally uniform limit, which forces `u(x) = 0`.

## Proposition 3.5

* `tendsto_monotonicityM_zero_of_pos`: if `u(x) > 0`, then `M_x(r) → −∞`.
* `tendsto_monotonicityM_zero`, formula (3.10): if `u(x) = 0`, then `M_x(0+)` is a real number
  `m`, `M_x(r) → m`, and `r^{-n} ∫_{B_r(x)} χ → m`. The existence of the second limit is part of
  the statement, as in the paper.
* `Mzero_le_unitBallVolume`: `M_x(0+) ≤ |B_1|`, and `0 ≤ M_x(0+)` when `u(x) = 0`.
* `upperSemicontinuousOn_Mzero` (`Limits.lean`): `x ↦ M_x(0+)` is upper semicontinuous on `Ω`.

`χ` takes values in `{0, 1}` on `Ω`, so `∫_{B_r(x)} χ = |{χ = 1} ∩ B_r(x)|`
(`setIntegral_chi_eq_measureReal`); (3.10) is stated with `∫ χ`.

## Proof of (3.10)

We follow the proof of Proposition 3.5. By the subsequence principle it suffices to show that
each `r_k → 0+` has a subsequence along which `r_k^{-n} ∫_{B_{r_k}(x)} χ → m`. Extract a blow-up
`u₀`. On `B_2`, the rescalings are variational solutions for large `k`, so `∇u_{x,r_k} → ∇u₀` in
`L²(B_1)` (`Blowup.lean`) and `u_{x,r_k} → u₀` uniformly on `∂B_1`. Euler's identity gives
`∫_{B_1} |∇u₀|² = ∫_{∂B_1} u₀²` (`integral_norm_gradient_sq_eq_of_inner_gradient_eq`). Hence
`∫_{B_1} χ_{x,r_k} = M_0(u_{x,r_k}; 1) − ∫_{B_1} |∇u_{x,r_k}|² + ∫_{∂B_1} u_{x,r_k}²
→ m − ∫_{B_1} |∇u₀|² + ∫_{∂B_1} u₀² = m`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- `M_0(u_{x,r_k}, χ_{x,r_k}; t) → m` when `M_x(r) → m` as `r → 0+` and `r_k → 0+`. -/
theorem tendsto_monotonicityM_rescale [NeZero n] {u χ : Rn n → ℝ} {x : Rn n} {m : ℝ}
    (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => monotonicityM (oneHomRescale u x (r k)) (chiRescale χ x (r k)) 0 t) atTop
      (𝓝 m) := by
  have e : ∀ k, monotonicityM u χ x (r k * t) =
      monotonicityM (oneHomRescale u x (r k)) (chiRescale χ x (r k)) 0 t := fun k =>
    (monotonicityM_rescale u χ x (hr k) t).symm
  refine (hm.comp (tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall fun k => mul_pos (hr k) ht⟩)).congr e
  simpa using hr0.mul_const t

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n} {R : ℝ}

/-! ### Blow-up sequences -/

/-- For `r_k → 0+`, the rescalings `(u_{x,r_k}, χ_{x,r_k})` are eventually variational solutions
on `B_ρ`. -/
theorem eventually_rescale_ball (h : IsVariationalSolution Ω C u χ) (hR0 : 0 < R)
    (hR : ball x R ⊆ Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {ρ : ℝ}
    (hρ : 0 < ρ) : ∀ᶠ k in atTop,
      IsVariationalSolution (ball 0 ρ) C (oneHomRescale u x (r k)) (chiRescale χ x (r k)) := by
  filter_upwards [hr0.eventually (gt_mem_nhds (div_pos hR0 hρ))] with k hk
  refine (h.rescale x (hr k)).mono isOpen_ball
    ((ball_subset_ball ?_).trans (ball_div_subset_preimage (hr k) hR))
  rw [le_div_iff₀ (hr k)]
  rw [lt_div_iff₀ hρ] at hk
  linarith

/-- The blow-up data on the window `B_ρ`: after dropping finitely many terms, the rescalings are
variational solutions on `B_ρ`, converge locally uniformly there, and `M_0(u_{x,r_k}; t) → m`. -/
theorem blowup_window [NeZero n] (h : IsVariationalSolution Ω C u χ) (hR0 : 0 < R)
    (hR : ball x R ⊆ Ω) {m : ℝ} (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ k₀ : ℕ,
      (∀ j, IsVariationalSolution (ball 0 ρ) C (oneHomRescale u x (r (j + k₀)))
        (chiRescale χ x (r (j + k₀)))) ∧
      TendstoLocallyUniformlyOn (fun j => oneHomRescale u x (r (j + k₀))) u₀ atTop (ball 0 ρ) ∧
      ∀ t, 0 < t → Tendsto (fun j => monotonicityM (oneHomRescale u x (r (j + k₀)))
        (chiRescale χ x (r (j + k₀))) 0 t) atTop (𝓝 m) := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (h.eventually_rescale_ball hR0 hR hr hr0 hρ)
  refine ⟨k₀, fun j => hk₀ _ (Nat.le_add_left _ _), ?_, fun t ht => ?_⟩
  · exact tendstoLocallyUniformlyOn_comp_add_nat
      ((tendstoLocallyUniformlyOn_univ.2 hconv).mono (subset_univ _)) k₀
  · exact (tendsto_add_atTop_iff_nat k₀).2 (tendsto_monotonicityM_rescale hm hr hr0 ht)

/-- On the window `B_ρ`, a blow-up is Lipschitz, harmonic on its positivity set, and satisfies
Euler's identity away from `0`. -/
theorem blowup_ball [NeZero n] (h : IsVariationalSolution Ω C u χ) (hR0 : 0 < R)
    (hR : ball x R ⊆ Ω) {m : ℝ} (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsLipHarmonicPos (ball 0 ρ) u₀ ∧ LipschitzOnWith C u₀ (ball 0 ρ) ∧
      ∀ y ∈ ball (0 : Rn n) ρ, y ≠ 0 → 0 < u₀ y → ⟪gradient u₀ y, y⟫ = u₀ y :=
  IsVariationalSolutionQ.blowup_ball (QBounds.one Ω) h.toQ hR0 hR
    (by simpa [monotonicityMq_one] using hm) hr hr0 hconv hρ

section Blowup

variable [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) {r : ℕ → ℝ}
  (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
  (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop)
include h hx hr hr0 hconv

/-- `blowup_ball` for any window, with the hypotheses of the section. -/
theorem blowup_ball' {ρ : ℝ} (hρ : 0 < ρ) :
    IsLipHarmonicPos (ball 0 ρ) u₀ ∧ LipschitzOnWith C u₀ (ball 0 ρ) ∧
      ∀ y ∈ ball (0 : Rn n) ρ, y ≠ 0 → 0 < u₀ y → ⟪gradient u₀ y, y⟫ = u₀ y :=
  IsVariationalSolutionQ.blowup_ball' (QBounds.one Ω) h.toQ hx hr hr0 hconv hρ

/-- **Blow-ups are Lipschitz** (proof of Proposition 3.5): `u₀` is `C_V`-Lipschitz on `ℝⁿ`. -/
theorem blowup_lipschitzWith : LipschitzWith C u₀ :=
  IsVariationalSolutionQ.blowup_lipschitzWith (QBounds.one Ω) h.toQ hx hr hr0 hconv

/-- **Blow-ups are harmonic on their positivity set** (proof of Proposition 3.5). -/
theorem blowup_isLipHarmonicPos : IsLipHarmonicPos univ u₀ :=
  IsVariationalSolutionQ.blowup_isLipHarmonicPos (QBounds.one Ω) h.toQ hx hr hr0 hconv

/-- **Euler's identity for blow-ups** (proof of Proposition 3.5): `∇u₀(y)·y = u₀(y)` for every
`y`. -/
theorem blowup_inner_gradient_eq (y : Rn n) : ⟪gradient u₀ y, y⟫ = u₀ y :=
  IsVariationalSolutionQ.blowup_inner_gradient_eq (QBounds.one Ω) h.toQ hx hr hr0 hconv y

/-- **Proposition 3.4, last claim**: blow-up limits are homogeneous of degree one,
`u₀(t y) = t u₀(y)` for `t > 0`. As in the proof of Proposition 3.5, this comes after the strong
convergence of the gradients of the rescalings, which it uses. -/
theorem blowup_homogeneous : ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y :=
  IsVariationalSolutionQ.blowup_homogeneous' (QBounds.one Ω) h.toQ hx hr hr0 hconv

end Blowup

/-! ### The density formula (3.10) -/

/-- **Formula (3.10) along a blow-up sequence** (proof of Proposition 3.5): if `u(x) = 0`,
`M_x(r) → m`, and `u_{x,r_k} → u₀` locally uniformly, then `r_k^{-n} ∫_{B_{r_k}(x)} χ → m`. -/
theorem tendsto_density_of_tendstoLocallyUniformly [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR0 : 0 < R) (hR : ball x R ⊆ Ω) (hux : u x = 0) {m : ℝ}
    (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    Tendsto (fun k => (r k ^ n)⁻¹ * ∫ y in ball x (r k), χ y) atTop (𝓝 m) := by
  simpa using IsVariationalSolutionQ.tendsto_density_of_tendstoLocallyUniformly (QBounds.one Ω)
    h.toQ hR0 hR hux (by simpa [monotonicityMq_one] using hm) hr hr0 hconv

/-- **Proposition 3.5, formula (3.10)**: if `u(x) = 0`, then
`M_x(u; 0+)` is a real number `m`, `M_x(r) → m`, and `r^{-n} ∫_{B_r(x)} χ → m` as `r → 0+`. -/
theorem tendsto_monotonicityM_zero [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hux : u x = 0) : ∃ m : ℝ, Mzero u χ x = m ∧
      Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m) ∧
      Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m) := by
  simpa [monotonicityMq_one, MzeroQ_one] using
    IsVariationalSolutionQ.tendsto_monotonicityMq_zero (QBounds.one Ω) h.toQ hx hux

/-- **Proposition 3.5**: if `u(x) > 0`, then `M_x(r) → −∞` as `r → 0+`. -/
theorem tendsto_monotonicityM_zero_of_pos [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hpos : 0 < u x) : Tendsto (monotonicityM u χ x) (𝓝[>] 0) atBot :=
  h.tendsto_monotonicityM_atBot_of_pos hx hpos

/-! ### Bounds on `M_x(0+)` -/

/-- `0 ≤ r^{-n} ∫_{B_r(x)} χ ≤ |B_1|` when `B_r(x) ⊆ Ω`. -/
theorem density_mem_Icc (h : IsVariationalSolution Ω C u χ) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ Ω) :
    (r ^ n)⁻¹ * ∫ y in ball x r, χ y ∈ Icc 0 (unitBallVolume n) :=
  h.toQ.density_mem_Icc hr hball

/-- **Proposition 3.5**: `M_x(0+) ≤ |B_1|`. -/
theorem Mzero_le_unitBallVolume [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    Mzero u χ x ≤ unitBallVolume n := by
  simpa [MzeroQ_one] using
    IsVariationalSolutionQ.MzeroQ_le_sq_mul_unitBallVolume (QBounds.one Ω) h.toQ hx

/-- **Proposition 3.5**: `0 ≤ M_x(0+)` when `u(x) = 0`. -/
theorem Mzero_nonneg [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hux : u x = 0) : 0 ≤ Mzero u χ x := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨m, hm, -, hlim⟩ := h.tendsto_monotonicityM_zero hx hux
  rw [hm, ← EReal.coe_zero, EReal.coe_le_coe_iff]
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hR0] with r hr
  exact (h.density_mem_Icc hr.1 ((ball_subset_ball hr.2.le).trans hR)).1

end IsVariationalSolution

end InnerVariational
