/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Blowup
public import InnerVariational.Monotonicity.LimitsQ
public import InnerVariational.Kernel.Rescale
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.Quantities
import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Basic.Polar

/-!
# The limit `M_x(u; 0+)` (Proposition 3.5)

Proposition 3.5 of Kriventsov–Weiss (see the references). Let `(u, χ)` be a variational solution
on `Ω` and `x ∈ Ω`. Then

* the limit `M_x(u; 0+) = lim_{r → 0+} M_x(u; r)` exists in `[−∞, ∞)`
  (`IsVariationalSolution.tendsto_Mzero`, from Proposition 3.4);
* `M_x(u; 0+) = −∞` if and only if `u(x) > 0` (`IsVariationalSolution.Mzero_eq_bot_iff`);
* if `u(x) = 0`, then `M_x(u; 0+)` is finite
  (`IsVariationalSolution.exists_tendsto_monotonicityM_of_eq_zero`);
  formula (3.10), `M_x(u; 0+) = lim_{r → 0} r^{-n} |{χ = 1} ∩ B_r(x)| ∈ [0, |B_1|]`, is
  `IsVariationalSolution.tendsto_monotonicityM_zero` in `Monotonicity/Density.lean`;
* `x ↦ M_x(u; 0+)` is upper semicontinuous on `Ω`
  (`IsVariationalSolution.upperSemicontinuousOn_Mzero`).

## Main definitions

* `Mzero u χ x : EReal`, the limit `M_x(u; 0+)`, as `limUnder` along `𝓝[>] 0`. It is junk for
  `x ∉ Ω`.

## Scaling

`monotonicityM_rescale`: `M_0(u_{x,r}, χ_{x,r}; t) = M_x(u, χ; r t)`, the invariance of `D`, `H`
and `M` under the one-homogeneous rescaling (3.6) (§3.3 of the paper).

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- `M_x(u; 0+) = lim_{r → 0+} M_x(u; r)` (Proposition 3.4), valued in `EReal`. For a variational
solution and `x ∈ Ω` the limit exists (`IsVariationalSolution.tendsto_Mzero`); it is `⊥ = −∞`
exactly when `u(x) > 0` (`IsVariationalSolution.Mzero_eq_bot_iff`). -/
def Mzero (u χ : Rn n → ℝ) (x : Rn n) : EReal :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => (monotonicityM u χ x r : EReal)

/-- For the coefficient `Q ≡ 1`, `M^1_x(0+)` is `M_x(0+)`. -/
theorem MzeroQ_one : (MzeroQ 1 : (Rn n → ℝ) → _) = Mzero := by
  funext u χ x
  simp [MzeroQ, Mzero, monotonicityMq_one]

/-! ### Scaling -/

section Scaling

variable (u χ : Rn n → ℝ) (x : Rn n) {r : ℝ}

/-- `D_0(u_{x,r}, χ_{x,r}; t) = D_x(u, χ; r t)` (§3.3). -/
theorem energyD_rescale (hr : 0 < r) (t : ℝ) :
    energyD (oneHomRescale u x r) (chiRescale χ x r) 0 t = energyD u χ x (r * t) := by
  have hg : ∀ y, ‖gradient (oneHomRescale u x r) y‖ ^ 2 + chiRescale χ x r y =
      (fun z => ‖gradient u z‖ ^ 2 + χ z) (x + r • y) := by
    intro y
    have : oneHomRescale u x r = fun z => u (x + r • z) / r := rfl
    rw [this, gradient_comp_add_smul_div u x hr.ne' y]
    rfl
  rw [energyD, energyD, integral_congr_ae (.of_forall hg),
    setIntegral_ball_comp_add_smul (fun z => ‖gradient u z‖ ^ 2 + χ z) x 0 hr, smul_zero,
    add_zero, mul_pow, mul_inv]
  ring

/-- `H_0(u_{x,r}; t) = H_x(u; r t)` (§3.3). -/
theorem heightH_rescale [NeZero n] (hr : 0 < r) (t : ℝ) :
    heightH (oneHomRescale u x r) 0 t = heightH u x (r * t) := by
  have e : (fun y => oneHomRescale u x r y ^ 2) = fun y => (r ^ 2)⁻¹ * u (x + r • y) ^ 2 := by
    ext y; rw [oneHomRescale_apply, div_pow, div_eq_inv_mul]
  rw [heightH, heightH, e, sphereIntegral_const_mul,
    sphereIntegral_comp_add_smul' (fun z => u z ^ 2) x hr.ne']
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  simp only [Nat.add_sub_cancel]
  rw [mul_pow]
  have hr0 : r ≠ 0 := hr.ne'
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · field_simp
    ring

/-- `M_0(u_{x,r}, χ_{x,r}; t) = M_x(u, χ; r t)` (§3.3). -/
theorem monotonicityM_rescale [NeZero n] (hr : 0 < r) (t : ℝ) :
    monotonicityM (oneHomRescale u x r) (chiRescale χ x r) 0 t = monotonicityM u χ x (r * t) := by
  rw [monotonicityM, monotonicityM, energyD_rescale u χ x hr, heightH_rescale u x hr]

/-- `∫_{B_t} χ_{x,r} = r^{-n} ∫_{B_{r t}(x)} χ`. -/
theorem setIntegral_chiRescale (hr : 0 < r) (t : ℝ) :
    ∫ y in ball (0 : Rn n) t, chiRescale χ x r y = (r ^ n)⁻¹ * ∫ y in ball x (r * t), χ y := by
  rw [show (fun y => chiRescale χ x r y) = fun y => χ (x + r • y) from rfl,
    setIntegral_ball_comp_add_smul _ x 0 hr, smul_zero, add_zero]

end Scaling

/-- `ball 0 (R / r)` lies in the domain `(x + r ·)⁻¹' Ω` of the rescaled solution when
`B_R(x) ⊆ Ω`. -/
theorem ball_div_subset_preimage {Ω : Set (Rn n)} {x : Rn n} {R r : ℝ} (hr : 0 < r)
    (hR : ball x R ⊆ Ω) : ball (0 : Rn n) (R / r) ⊆ (fun y => x + r • y) ⁻¹' Ω := by
  intro y hy
  apply hR
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
  rw [mem_ball_zero_iff, lt_div_iff₀ hr] at hy
  linarith

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Existence of `M_x(0+)` -/

theorem exists_ball_subset (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    ∃ R > 0, ball x R ⊆ Ω :=
  Metric.isOpen_iff.1 h.isOpen x hx

/-- The limit `M_x(u; 0+)` exists in `EReal`, and equals the infimum of `M_x` on `(0, R)` for any
`B_R(x) ⊆ Ω` (Proposition 3.4). -/
theorem tendsto_Mzero [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    Tendsto (fun r => (monotonicityM u χ x r : EReal)) (𝓝[>] 0) (𝓝 (Mzero u χ x)) := by
  simpa [monotonicityMq_one, MzeroQ_one] using
    IsVariationalSolutionQ.tendsto_MzeroQ (QBounds.one Ω) h.toQ hx

/-- `M_x(0+) ≤ M_x(r)` for `0 < r < R`, `B_R(x) ⊆ Ω`. -/
theorem Mzero_le [NeZero n] (h : IsVariationalSolution Ω C u χ) {R r : ℝ} (hR : ball x R ⊆ Ω)
    (hr : 0 < r) (hrR : r < R) : Mzero u χ x ≤ monotonicityM u χ x r := by
  have hx : x ∈ Ω := hR (mem_ball_self (hr.trans hrR))
  refine le_of_tendsto (h.tendsto_Mzero hx) ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with s hs
  exact EReal.coe_le_coe_iff.2
    (h.monotoneOn_monotonicityM hR ⟨hs.1, hs.2.trans hrR⟩ ⟨hr, hrR⟩ hs.2.le)

/-- `M_x(0+) ≤ M_x(r)` for `0 < r` and `B̄_r(x) ⊆ Ω`. -/
theorem Mzero_le_of_closedBall [NeZero n] (h : IsVariationalSolution Ω C u χ) {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ Ω) : Mzero u χ x ≤ monotonicityM u χ x r := by
  obtain ⟨R', hR', hR'Ω⟩ := exists_gt_ball_subset h.isOpen hr.le hball
  exact h.Mzero_le hR'Ω hr hR'

/-- The form used for `Σ^H`: `c ≤ M_x(0+)` if and only if `c ≤ M_x(r)` for every `r > 0` with
`B̄_r(x) ⊆ Ω` (the admissible radii in the definition of `Σ^H` in this library). -/
theorem le_Mzero_iff_closedBall [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    {c : EReal} :
    c ≤ Mzero u χ x ↔ ∀ r, 0 < r → closedBall x r ⊆ Ω → c ≤ monotonicityM u χ x r := by
  refine ⟨fun hc r hr hball => hc.trans (h.Mzero_le_of_closedBall hr hball), fun hc => ?_⟩
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  refine ge_of_tendsto (h.tendsto_Mzero hx) ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos hR0)] with s hs
  exact hc s hs.1 ((closedBall_subset_ball (hs.2.trans (half_lt_self hR0))).trans hR)

/-! ### Bounds on `D` and `H` -/

/-- `0 ≤ χ` on `Ω`. -/
theorem chi_nonneg (h : IsVariationalSolution Ω C u χ) {y : Rn n} (hy : y ∈ Ω) : 0 ≤ χ y := by
  rcases h.chi_mem y hy with h0 | h1 <;> simp [*]

/-! ### Proposition 3.5: `M_x(0+) = −∞` if and only if `u(x) > 0` -/

/-- If `u(x) = 0`, `M_x(0+)` is finite and is the limit of `M_x(r)` in `ℝ` (proof of
Proposition 3.5). -/
theorem exists_tendsto_monotonicityM_of_eq_zero [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hux : u x = 0) :
    ∃ m : ℝ, Mzero u χ x = m ∧ Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m) := by
  simpa [monotonicityMq_one, MzeroQ_one] using
    IsVariationalSolutionQ.exists_tendsto_monotonicityMq_of_eq_zero (QBounds.one Ω) h.toQ hx hux

/-- **Proposition 3.5**: `M_x(u; 0+) = −∞` if and only if `u(x) > 0`. -/
theorem Mzero_eq_bot_iff [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    Mzero u χ x = ⊥ ↔ 0 < u x := by
  simpa [MzeroQ_one] using IsVariationalSolutionQ.MzeroQ_eq_bot_iff (QBounds.one Ω) h.toQ hx

/-! ### Upper semicontinuity -/

/-- **Proposition 3.5**: `x ↦ M_x(u; 0+)` is upper semicontinuous on `Ω`. -/
theorem upperSemicontinuousOn_Mzero [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    UpperSemicontinuousOn (Mzero u χ) Ω := by
  simpa [MzeroQ_one] using IsVariationalSolutionQ.upperSemicontinuousOn_MzeroQ (QBounds.one Ω) h.toQ

end IsVariationalSolution

end InnerVariational
