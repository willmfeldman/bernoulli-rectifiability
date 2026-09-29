/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Blowup
public import InnerVariational.Kernel.Rescale
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
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
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  have hmono : MonotoneOn (fun r => (monotonicityM u χ x r : EReal)) (Ioo 0 R) :=
    fun s hs t ht hst => EReal.coe_le_coe_iff.2 (h.monotoneOn_monotonicityM hR hs ht hst)
  have ht := hmono.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hR0) (OrderBot.bddBelow _)
  rw [Mzero, ht.limUnder_eq]
  exact ht

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

/-- `c ≤ M_x(0+)` if and only if `c ≤ M_x(r)` for all `r ∈ (0, R)`, `B_R(x) ⊆ Ω`. This is the
form of the equivalence used for `Σ^H`: the definition of `Σ^H` in Section 6 is
`M_x(0+) ≥ |B_1|`, and this
library by `M_x(r) ≥ |B_1|` for every admissible radius `r`. -/
theorem le_Mzero_iff [NeZero n] (h : IsVariationalSolution Ω C u χ) {R : ℝ} (hR0 : 0 < R)
    (hR : ball x R ⊆ Ω) {c : EReal} :
    c ≤ Mzero u χ x ↔ ∀ r ∈ Ioo 0 R, c ≤ monotonicityM u χ x r := by
  refine ⟨fun hc r hr => hc.trans (h.Mzero_le hR hr.1 hr.2), fun hc => ?_⟩
  refine ge_of_tendsto (h.tendsto_Mzero (hR (mem_ball_self hR0))) ?_
  filter_upwards [Ioo_mem_nhdsGT hR0] with s hs using hc s hs

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

/-- `0 ≤ D_x(r)` when `B_r(x) ⊆ Ω`. -/
theorem energyD_nonneg (h : IsVariationalSolution Ω C u χ) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ Ω) : 0 ≤ energyD u χ x r :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) (setIntegral_nonneg_of_ae_restrict
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun _ hy =>
      add_nonneg (sq_nonneg _) (h.chi_nonneg (hball hy)))))

/-- `D_x(r) ≤ (C_V² + 1) |B_1|` when `B_r(x) ⊆ Ω`. -/
theorem energyD_le (h : IsVariationalSolution Ω C u χ) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ Ω) : energyD u χ x r ≤ ((C : ℝ) ^ 2 + 1) * unitBallVolume n := by
  have h1 : IntegrableOn (fun _ : Rn n => (C : ℝ) ^ 2 + 1) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have hle : ∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y) ≤
      ∫ y in ball x r, ((C : ℝ) ^ 2 + 1) :=
    setIntegral_mono_on (h.integrableOn_energy hball) h1 measurableSet_ball fun y hy =>
      add_le_add (h.sq_norm_gradient_le (hball hy)) (abs_le.1 (h.abs_chi_le_one (hball hy))).2
  rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hr] at hle
  rw [energyD]
  calc (r ^ n)⁻¹ * ∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y)
      ≤ (r ^ n)⁻¹ * (r ^ n * unitBallVolume n * ((C : ℝ) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (pow_nonneg hr.le n))
    _ = _ := by field_simp

/-- If `u(x) = 0`, then `H_x(r) ≤ C_V² n |B_1|` for `0 < r < R`, `B_R(x) ⊆ Ω`. -/
theorem heightH_le_of_eq_zero [NeZero n] (h : IsVariationalSolution Ω C u χ) {R r : ℝ}
    (hR : ball x R ⊆ Ω)
    (hr : 0 < r) (hrR : r < R) (hux : u x = 0) :
    heightH u x r ≤ (C : ℝ) ^ 2 * (n * unitBallVolume n) := by
  have hle : sphereIntegral (fun y => u y ^ 2) x r ≤
      sphereIntegral (fun _ => ((C : ℝ) * r) ^ 2) x r :=
    sphereIntegral_mono hr.le (h.sphereIntegrable_u_sq hR hr.le hrR)
      (continuous_const.sphereIntegrable x r) fun y hy => by
        have := h.abs_le_of_mem_sphere hR hr.le hrR hy
        rw [hux, abs_zero, zero_add] at this
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [sphereIntegral_const] at hle
  rw [heightH]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  simp only [Nat.add_sub_cancel] at hle
  calc (r ^ (m + 1 + 1))⁻¹ * sphereIntegral (fun y => u y ^ 2) x r
      ≤ (r ^ (m + 1 + 1))⁻¹ * (↑(m + 1) * unitBallVolume (m + 1) * r ^ m * ((C : ℝ) * r) ^ 2) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by field_simp; ring

/-- If `u(x) = 0`, then `M_x(r) ≥ −C_V² n |B_1|` for `0 < r < R`, `B_R(x) ⊆ Ω`. -/
theorem neg_le_monotonicityM_of_eq_zero [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {R r : ℝ} (hR : ball x R ⊆ Ω) (hr : 0 < r) (hrR : r < R) (hux : u x = 0) :
    -((C : ℝ) ^ 2 * (n * unitBallVolume n)) ≤ monotonicityM u χ x r := by
  have h1 := h.energyD_nonneg hr ((ball_subset_ball hrR.le).trans hR)
  have h2 := h.heightH_le_of_eq_zero hR hr hrR hux
  rw [monotonicityM]
  linarith

/-! ### Proposition 3.5: `M_x(0+) = −∞` if and only if `u(x) > 0` -/

/-- If `u(x) > 0`, then `M_x(r) → −∞` as `r → 0+` (proof of Proposition 3.5): `D` stays bounded
while `H_x(r) ≥ n |B_1| (u(x)/2)² / r²`. -/
theorem tendsto_monotonicityM_atBot_of_pos [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hpos : 0 < u x) :
    Tendsto (monotonicityM u χ x) (𝓝[>] 0) atBot := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  have hc : {y | u x / 2 < u y} ∈ 𝓝 x :=
    (h.continuousOn.continuousAt (h.isOpen.mem_nhds hx)).preimage_mem_nhds
      (Ioi_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hc
  set A := ((C : ℝ) ^ 2 + 1) * unitBallVolume n
  set c := (n : ℝ) * unitBallVolume n * (u x / 2) ^ 2
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hcpos : 0 < c := by have := unitBallVolume_pos n; positivity
  have hbound : ∀ r ∈ Ioo 0 (min (min δ R) 1), monotonicityM u χ x r ≤ A - c * r⁻¹ := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hrδ : r < δ := hr.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hrR : r < R := hr.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hr1 : r < 1 := hr.2.trans_le (min_le_right _ _)
    have hD := h.energyD_le hr0 ((ball_subset_ball hrR.le).trans hR)
    have hSI : sphereIntegral (fun _ => (u x / 2) ^ 2) x r ≤
        sphereIntegral (fun y => u y ^ 2) x r :=
      sphereIntegral_mono hr0.le (continuous_const.sphereIntegrable x r)
        (h.sphereIntegrable_u_sq hR hr0.le hrR) fun y hy => by
          have hyδ : y ∈ ball x δ := mem_ball.2 ((mem_sphere.1 hy).trans_lt hrδ)
          have := hδsub hyδ
          exact pow_le_pow_left₀ (by linarith) this.le 2
    rw [sphereIntegral_const] at hSI
    have hH : c * (r ^ 2)⁻¹ ≤ heightH u x r := by
      rw [heightH]
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
      have e : c * (r ^ 2)⁻¹ =
          (r ^ (n + 1))⁻¹ * (n * unitBallVolume n * r ^ (n - 1) * (u x / 2) ^ 2) := by
        simp only [c]; rw [hm]; simp only [Nat.add_sub_cancel]; push_cast; field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hSI (by positivity)
    have hrr : c * r⁻¹ ≤ c * (r ^ 2)⁻¹ := by
      refine mul_le_mul_of_nonneg_left ?_ hcpos.le
      rw [inv_le_inv₀ hr0 (by positivity)]
      nlinarith
    rw [monotonicityM]
    linarith
  have hlim : Tendsto (fun r => A - c * r⁻¹) (𝓝[>] 0) atBot := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hcpos
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_left _ A (tendsto_neg_atTop_atBot.comp this)
  refine tendsto_atBot_mono' _ ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hδ hR0) one_pos)] with r hr using hbound r hr

/-- `M_x(0+) = −∞` when `u(x) > 0` (Proposition 3.5). -/
theorem Mzero_eq_bot_of_pos [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hpos : 0 < u x) : Mzero u χ x = ⊥ :=
  tendsto_nhds_unique (h.tendsto_Mzero hx)
    (EReal.tendsto_coe_atBot.comp (h.tendsto_monotonicityM_atBot_of_pos hx hpos))

/-- If `u(x) = 0`, `M_x(0+)` is finite and is the limit of `M_x(r)` in `ℝ` (proof of
Proposition 3.5). -/
theorem exists_tendsto_monotonicityM_of_eq_zero [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hux : u x = 0) :
    ∃ m : ℝ, Mzero u χ x = m ∧ Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m) := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  have hlow : ((-((C : ℝ) ^ 2 * (n * unitBallVolume n)) : ℝ) : EReal) ≤ Mzero u χ x :=
    (h.le_Mzero_iff hR0 hR).2 fun r hr =>
      EReal.coe_le_coe_iff.2 (h.neg_le_monotonicityM_of_eq_zero hR hr.1 hr.2 hux)
  have hup : Mzero u χ x ≤ monotonicityM u χ x (R / 2) :=
    h.Mzero_le hR (half_pos hR0) (half_lt_self hR0)
  have hne_bot : Mzero u χ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  have hne_top : Mzero u χ x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  refine ⟨(Mzero u χ x).toReal, (EReal.coe_toReal hne_top hne_bot).symm, ?_⟩
  have := h.tendsto_Mzero hx
  rw [← EReal.coe_toReal hne_top hne_bot] at this
  exact EReal.tendsto_coe.1 this

/-- **Proposition 3.5**: `M_x(u; 0+) = −∞` if and only if `u(x) > 0`. -/
theorem Mzero_eq_bot_iff [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    Mzero u χ x = ⊥ ↔ 0 < u x := by
  refine ⟨fun hbot => ?_, h.Mzero_eq_bot_of_pos hx⟩
  by_contra hpos
  have hux : u x = 0 := le_antisymm (not_lt.1 hpos) (h.nonneg x hx)
  obtain ⟨m, hm, -⟩ := h.exists_tendsto_monotonicityM_of_eq_zero hx hux
  rw [hm] at hbot
  exact EReal.coe_ne_bot m hbot

/-! ### Upper semicontinuity -/

/-- For fixed `r > 0`, `y ↦ M_y(u; r)` is continuous at `x₀` when `B̄_r(x₀) ⊆ Ω`. -/
theorem continuousAt_monotonicityM_center [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {x₀ : Rn n} {r : ℝ} (hr : 0 < r) (hball : closedBall x₀ r ⊆ Ω) :
    ContinuousAt (fun y => monotonicityM u χ y r) x₀ := by
  obtain ⟨R', hR', hR'Ω⟩ := exists_gt_ball_subset h.isOpen hr.le hball
  set g : Rn n → ℝ := Ω.indicator fun y => ‖gradient u y‖ ^ 2 + χ y with hgdef
  have hgm : Measurable g := by
    have : g = Ω.indicator (fun y => ‖gradient u y‖ ^ 2) + Ω.indicator χ := by
      ext y; by_cases hy : y ∈ Ω <;> simp [hgdef, hy]
    rw [this]
    exact (((measurable_gradient u).norm.pow_const 2).indicator h.isOpen.measurableSet).add
      h.measurable_chi
  have hgb : ∀ y, |g y| ≤ (C : ℝ) ^ 2 + 1 := by
    intro y
    by_cases hy : y ∈ Ω
    · rw [hgdef, indicator_of_mem hy]
      have a1 := h.sq_norm_gradient_le hy
      have a2 := h.abs_chi_le_one hy
      have a3 : 0 ≤ ‖gradient u y‖ ^ 2 := sq_nonneg _
      rw [abs_le] at a2 ⊢
      constructor <;> linarith
    · rw [hgdef, indicator_of_notMem hy, abs_zero]; positivity
  have hgl : LocallyIntegrable g := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact IntegrableOn.of_bound hK.measure_lt_top hgm.aestronglyMeasurable ((C : ℝ) ^ 2 + 1)
      (.of_forall fun y => by rw [Real.norm_eq_abs]; exact hgb y)
  have hD : ContinuousAt (fun y => (r ^ n)⁻¹ * ∫ z in ball y r, g z) x₀ :=
    ((continuous_integral_ball hgl r).continuousAt).const_mul _
  have hD' : (fun y => energyD u χ y r) =ᶠ[𝓝 x₀] fun y => (r ^ n)⁻¹ * ∫ z in ball y r, g z := by
    filter_upwards [ball_mem_nhds x₀ (sub_pos.2 hR')] with y hy
    rw [energyD]
    congr 1
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    have hzΩ : z ∈ Ω := hR'Ω (mem_ball.2 (by
      have := dist_triangle z y x₀
      rw [mem_ball] at hy hz
      linarith))
    rw [hgdef, indicator_of_mem hzΩ]
  have hSI := continuousAt_sphereIntegral h.isOpen (h.continuousOn.pow 2)
    (x := x₀) (s := r) (by rwa [abs_of_pos hr])
  have hc : ContinuousAt (fun y : Rn n => (y, r)) x₀ :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hH : ContinuousAt (fun y => heightH u y r) x₀ :=
    (ContinuousAt.comp (f := fun y : Rn n => (y, r)) hSI hc).const_mul _
  exact (hD.congr hD'.symm).sub hH

/-- **Proposition 3.5**: `x ↦ M_x(u; 0+)` is upper semicontinuous on `Ω`. -/
theorem upperSemicontinuousOn_Mzero [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    UpperSemicontinuousOn (Mzero u χ) Ω := by
  intro x₀ hx₀ y hy
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx₀
  have hev : ∀ᶠ r in 𝓝[>] 0, (monotonicityM u χ x₀ r : EReal) < y :=
    (h.tendsto_Mzero hx₀).eventually (gt_mem_nhds hy)
  obtain ⟨r, hr, hr0, hrR⟩ : ∃ r, (monotonicityM u χ x₀ r : EReal) < y ∧ 0 < r ∧ r < R / 2 :=
    (hev.and (Ioo_mem_nhdsGT (half_pos hR0))).exists.imp fun r h => ⟨h.1, h.2.1, h.2.2⟩
  have hcb : closedBall x₀ r ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hR
  have hcont := h.continuousAt_monotonicityM_center hr0 hcb
  have h1 : ∀ᶠ x in 𝓝 x₀, (monotonicityM u χ x r : EReal) < y :=
    (continuous_coe_real_ereal.continuousAt.comp hcont).eventually (gt_mem_nhds hr)
  have h2 : ∀ᶠ x in 𝓝 x₀, closedBall x r ⊆ Ω := by
    filter_upwards [ball_mem_nhds x₀ (half_pos hR0)] with x hx
    intro z hz
    apply hR
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hz
    have := dist_triangle z x x₀
    linarith
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with x hx1 hx2
  exact (h.Mzero_le_of_closedBall hr0 hx2).trans_lt hx1

end IsVariationalSolution

end InnerVariational
