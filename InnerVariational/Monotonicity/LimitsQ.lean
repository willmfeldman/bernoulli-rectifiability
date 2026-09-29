/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.RadialQ
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Basic.Polar

/-!
# The Weiss energy with a Lipschitz coefficient: almost-monotonicity and `M(0+)`

Let `(u, χ)` be a variational solution on `Ω` for a coefficient `Q` with `QBounds Ω Q L c C'`, and
let `B_R(x) ⊆ Ω`. This file proves the analogues of Proposition 3.4 (monotonicity) and of the
parts of Proposition 3.5 of Kriventsov–Weiss that do not use blow-ups.

* `monotoneOn_weightedMonotonicityM_add`: the weighted Weiss energy `M^w_x` of
  `Monotonicity/RadialQ.lean` is almost-monotone: `s ↦ M^w_x(s) + A s` is nondecreasing on
  `(0, R)`, with `A = weissConst n L c C'`.
* `abs_monotonicityMq_sub_le`: the Weiss energy with the coefficient frozen at `q = Q(x)`,
  `M^q_x(s) = s^{-n} ∫_{B_s(x)} (|∇u|² + q² χ) − H_x(s)` (`monotonicityMq`), differs from
  `M^w_x(s)` by at most `B s`, `B = 2 C' L |B_1|`.
* `tendsto_MzeroQ`: hence the limit `M^{Q(x)}_x(0+)` (`MzeroQ (Q x) u χ x`) exists in `[−∞, ∞)`
  for every `x ∈ Ω`, and `MzeroQ_le`: `M^{Q(x)}_x(0+) ≤ M^{Q(x)}_x(r) + (A + B) r` for
  `0 < r < R`, uniformly in `x`.
* `MzeroQ_eq_bot_iff`: `M^{Q(x)}_x(0+) = −∞` if and only if `u(x) > 0`;
  `exists_tendsto_monotonicityMq_of_eq_zero`: for `u(x) = 0` the limit is a real number.
* `upperSemicontinuousOn_MzeroQ`: `x ↦ M^{Q(x)}_x(0+)` is upper semicontinuous on `Ω`.

The paper treats `Q ≡ 1`, where `A = B = 0` and `M` is monotone (`Monotonicity/Limits.lean`).

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

/-- The constant `B = 2 C' L |B_1|` in the comparison of `M^{Q(x)}` and `M^w`. -/
def weissCompConst (n : ℕ) (L : ℝ≥0) (C' : ℝ) : ℝ := 2 * C' * L * unitBallVolume n

/-- A real perturbation tending to `0` does not change an `EReal` limit. -/
theorem tendsto_ereal_add_of_tendsto_zero {α : Type*} {l : Filter α} {f g : α → ℝ} {a : EReal}
    (hf : Tendsto (fun r => (f r : EReal)) l (𝓝 a)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun r => ((f r + g r : ℝ) : EReal)) l (𝓝 a) := by
  have hg' : Tendsto (fun r => (g r : EReal)) l (𝓝 0) := by
    simpa using (continuous_coe_real_ereal.tendsto 0).comp hg
  have := (EReal.continuousAt_add (p := (a, 0)) (Or.inr (by simp)) (Or.inr (by simp))).tendsto.comp
    (hf.prodMk_nhds hg')
  simpa [Function.comp_def, EReal.coe_add] using this

theorem tendsto_const_mul_nhdsGT_zero (A : ℝ) :
    Tendsto (fun r : ℝ => A * r) (𝓝[>] 0) (𝓝 0) := by
  have h := (continuous_const_mul A).tendsto 0
  rw [mul_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

namespace QBounds

variable {Ω : Set (Rn n)} {Q : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

theorem weissKappa_nonneg (hQ : QBounds Ω Q L c C') (hx : x ∈ Ω) : 0 ≤ weissKappa L c C' := by
  have := hQ.nonneg_of_mem hx
  rw [weissKappa]; positivity

theorem weissConst_nonneg (hQ : QBounds Ω Q L c C') (hx : x ∈ Ω) : 0 ≤ weissConst n L c C' := by
  have := hQ.weissKappa_nonneg hx
  have := unitBallVolume_pos n
  rw [weissConst]; positivity

theorem weissCompConst_nonneg (hQ : QBounds Ω Q L c C') (hx : x ∈ Ω) :
    0 ≤ weissCompConst n L C' := by
  have := hQ.nonneg_of_mem hx
  have := unitBallVolume_pos n
  rw [weissCompConst]; positivity

end QBounds

namespace IsVariationalSolutionQ

open Kernel IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {R : ℝ} {L : ℝ≥0}
  {c C' : ℝ}

/-! ### Almost-monotonicity of the weighted Weiss energy -/

/-- `ω − chiInt s / sⁿ = s^{-n} W_Q(s) ≤ C'² |B_1|`. -/
theorem volume_term_le [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR : ball x R ⊆ Ω) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    ∀ s ∈ Ioo a b, Q x ^ 2 * unitBallVolume n -
      (h.radialDataErr hQ hR ha hab hbR).chiInt s / s ^ n ≤ C' ^ 2 * unitBallVolume n := by
  intro s hs
  have hs0 : 0 < s := ha.trans hs.1
  have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR).le).trans hR
  have hW := h.integral_weight_le hQ hs0 hsΩ
  change Q x ^ 2 * unitBallVolume n -
    (Q x ^ 2 * unitBallVolume n * s ^ n - ∫ y in ball x s, Q y ^ 2 * (1 - χ y)) / s ^ n ≤ _
  have hsn : 0 < s ^ n := pow_pos hs0 n
  rw [sub_div, mul_div_assoc, div_self hsn.ne', mul_one, sub_sub_cancel, div_le_iff₀ hsn]
  linarith

/-- **Almost-monotonicity** (the analogue of Proposition 3.4): `s ↦ M^w_x(s) + A s` is
nondecreasing on `(0, R)` when `B_R(x) ⊆ Ω`, with `A = weissConst n L c C'`. -/
theorem monotoneOn_weightedMonotonicityM_add [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) :
    MonotoneOn (fun s => weightedMonotonicityM Q u χ x s + weissConst n L c C' * s) (Ioo 0 R) := by
  intro s hs t ht hst
  have := (h.radialDataErr hQ hR hs.1 hst ht.2).monotoneOn_monotonicityM_add
    (h.volume_term_le hQ hR hs.1 hst ht.2) ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simpa only [radialDataErr_monotonicityM, weissConst, mul_assoc] using this

/-- **Integrated Weiss formula with error**: for `0 < s₁ ≤ s₂ < R`,
`∫_{s₁}^{s₂} (2 / s^{n+2}) ∫_{∂B_s(x)} (u − ∇u·(y−x))² ≤ M^w_x(s₂) − M^w_x(s₁) + A (s₂ − s₁)`. -/
theorem integral_sphere_sub_inner_sq_le [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (h12 : s₁ ≤ s₂) (hs₂ : s₂ < R) :
    ∫ s in s₁..s₂, 2 / s ^ (n + 2) *
        sphereIntegral (fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2) x s ≤
      weightedMonotonicityM Q u χ x s₂ - weightedMonotonicityM Q u χ x s₁ +
        weissConst n L c C' * (s₂ - s₁) := by
  set d := h.radialDataErr hQ hR hs₁ h12 hs₂
  have key := d.integral_monotonicityM_sq_term_le (h.volume_term_le hQ hR hs₁ h12 hs₂)
    ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  have e : ∫ s in s₁..s₂, 2 / s ^ (n + 2) *
      sphereIntegral (fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2) x s =
      ∫ s in s₁..s₂, 2 / s ^ (n + 2) * (d.sphRad s - 2 * d.sphMix s + d.sphSq s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le h12] at hs
    have hs0 : 0 < s := hs₁.trans_le hs.1
    change _ = 2 / s ^ (n + 2) * (sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
      2 * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
      sphereIntegral (fun y => u y ^ 2) x s)
    rw [h.sphereIntegral_sub_inner_sq hR hs0.le (hs.2.trans_lt hs₂)]
  rw [e]
  simpa only [radialDataErr_monotonicityM, weissConst, mul_assoc] using key

/-! ### Comparison with the frozen coefficient -/

/-- `|Q(y)² − Q(x)²| ≤ 2 C' L |y − x|` on `Ω`. -/
theorem abs_sq_sub_sq_le (hQ : QBounds Ω Q L c C') {y : Rn n} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    |Q y ^ 2 - Q x ^ 2| ≤ 2 * C' * L * ‖y - x‖ := by
  have h1 := hQ.lipschitzOnWith_sq.dist_le_mul y hy x hx
  have hC' := hQ.nonneg_of_mem hx
  rwa [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm] at h1

/-- **Comparison of the two normalisations**: for `0 < s` and `B_s(x) ⊆ Ω`,
`|M^{Q(x)}_x(s) − M^w_x(s)| ≤ 2 C' L |B_1| s`. Indeed the difference is
`s^{-n} ∫_{B_s(x)} (Q² − Q(x)²)(1 − χ)`. -/
theorem abs_monotonicityMq_sub_le (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) {s : ℝ} (hs0 : 0 < s) (hs : ball x s ⊆ Ω) :
    |monotonicityMq (Q x) u χ x s - weightedMonotonicityM Q u χ x s| ≤
      weissCompConst n L C' * s := by
  have hx : x ∈ Ω := hs (mem_ball_self hs0)
  have hC' := hQ.nonneg_of_mem hx
  set q := Q x
  have hG := h.integrableOn_norm_gradient_sq hQ hs
  have hW := h.integrableOn_weight hQ hs
  have h1 := h.integrableOn_one_sub_chi hs
  have hχ : IntegrableOn χ (ball x s) :=
    IntegrableOn.of_bound measure_ball_lt_top (h.aestronglyMeasurable_chi measurableSet_ball hs) 1
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hs hy)))
  have hc : IntegrableOn (fun _ : Rn n => q ^ 2) (ball x s) :=
    integrableOn_const measure_ball_lt_top.ne
  have hD : IntegrableOn (fun y => Q y ^ 2 * (1 - χ y) - q ^ 2 * (1 - χ y)) (ball x s) :=
    hW.sub (h1.const_mul _)
  -- The integrand identity.
  have hsplit : ∫ y in ball x s, (‖gradient u y‖ ^ 2 + q ^ 2 * χ y) =
      (∫ y in ball x s, (‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y))) +
        (∫ y in ball x s, q ^ 2) +
        ∫ y in ball x s, (Q y ^ 2 * (1 - χ y) - q ^ 2 * (1 - χ y)) := by
    have hGW := h.integrableOn_weightedEnergy (x := x) hQ hs
    have hGWc : IntegrableOn (fun y => (‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) + q ^ 2)
        (ball x s) := hGW.add hc
    rw [← integral_add hGW hc, ← integral_add hGWc hD]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only
    ring
  have hvol : ∫ y in ball x s, q ^ 2 = q ^ 2 * unitBallVolume n * s ^ n := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hs0]
    ring
  -- The bound on the difference integral.
  have hbound : |∫ y in ball x s, (Q y ^ 2 * (1 - χ y) - q ^ 2 * (1 - χ y))| ≤
      2 * C' * L * s * (unitBallVolume n * s ^ n) := by
    have hcst : IntegrableOn (fun _ : Rn n => 2 * C' * L * s) (ball x s) :=
      integrableOn_const measure_ball_lt_top.ne
    refine (abs_integral_le_integral_abs).trans ((setIntegral_mono_on hD.abs hcst
      measurableSet_ball fun y hy => ?_).trans (le_of_eq ?_))
    · have hyΩ := hs hy
      have hy1 : ‖y - x‖ ≤ s := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
      have e : Q y ^ 2 * (1 - χ y) - q ^ 2 * (1 - χ y) = (Q y ^ 2 - q ^ 2) * (1 - χ y) := by ring
      rw [e, abs_mul, abs_of_nonneg (h.one_sub_chi_nonneg hyΩ)]
      calc |Q y ^ 2 - q ^ 2| * (1 - χ y) ≤ (2 * C' * L * s) * 1 :=
            mul_le_mul ((abs_sq_sub_sq_le hQ hx hyΩ).trans (by gcongr))
              (h.one_sub_chi_le_one hyΩ) (h.one_sub_chi_nonneg hyΩ) (by positivity)
        _ = 2 * C' * L * s := mul_one _
    · rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hs0]
      ring
  have hsn : 0 < s ^ n := pow_pos hs0 n
  have e : monotonicityMq q u χ x s - weightedMonotonicityM Q u χ x s =
      (s ^ n)⁻¹ * ∫ y in ball x s, (Q y ^ 2 * (1 - χ y) - q ^ 2 * (1 - χ y)) := by
    rw [monotonicityMq, weightedMonotonicityM, energyDq, weightedEnergyD, hsplit, hvol]
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hsn), weissCompConst]
  calc (s ^ n)⁻¹ * |∫ y in ball x s, (Q y ^ 2 * (1 - χ y) - q ^ 2 * (1 - χ y))|
      ≤ (s ^ n)⁻¹ * (2 * C' * L * s * (unitBallVolume n * s ^ n)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hsn.le)
    _ = 2 * C' * L * unitBallVolume n * s := by field_simp

/-! ### The limit `M(0+)` -/

/-- If `B_R(x) ⊆ Ω`, `s < r < R`, then
`M^{Q(x)}_x(s) ≤ M^{Q(x)}_x(r) + (A + B) r + B s`. -/
theorem monotonicityMq_le [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) {s r : ℝ} (hs : 0 < s)
    (hsr : s ≤ r) (hrR : r < R) :
    monotonicityMq (Q x) u χ x s ≤ monotonicityMq (Q x) u χ x r +
      (weissConst n L c C' + weissCompConst n L C') * r + weissCompConst n L C' * s := by
  have hr : 0 < r := hs.trans_le hsr
  have hx : x ∈ Ω := hR (mem_ball_self (hr.trans hrR))
  have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hsr.trans hrR.le)).trans hR
  have hrΩ : ball x r ⊆ Ω := (ball_subset_ball hrR.le).trans hR
  have h1 := (abs_le.1 (h.abs_monotonicityMq_sub_le hQ hs hsΩ)).2
  have h2 := (abs_le.1 (h.abs_monotonicityMq_sub_le hQ hr hrΩ)).1
  have h3 := h.monotoneOn_weightedMonotonicityM_add hQ hR ⟨hs, hsr.trans_lt hrR⟩ ⟨hr, hrR⟩ hsr
  have hA := hQ.weissConst_nonneg (n := n) hx
  simp only at h3
  nlinarith

/-- The limit of `M^w_x(r)` as `r → 0+` exists in `EReal`. -/
theorem exists_tendsto_weightedMonotonicityM [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) :
    ∃ ℓ : EReal, Tendsto (fun r => (weightedMonotonicityM Q u χ x r : EReal)) (𝓝[>] 0) (𝓝 ℓ) := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  have hmono : MonotoneOn (fun r => ((weightedMonotonicityM Q u χ x r +
      weissConst n L c C' * r : ℝ) : EReal)) (Ioo 0 R) :=
    fun s hs t ht hst => EReal.coe_le_coe_iff.2
      (h.monotoneOn_weightedMonotonicityM_add hQ hR hs ht hst)
  have ht := hmono.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hR0) (OrderBot.bddBelow _)
  refine ⟨_, (tendsto_ereal_add_of_tendsto_zero ht
    (g := fun r => -(weissConst n L c C' * r)) ?_).congr fun r => ?_⟩
  · simpa using (tendsto_const_mul_nhdsGT_zero (weissConst n L c C')).neg
  · simp

/-- **The limit `M^{Q(x)}_x(0+)` exists** in `[−∞, ∞)` for every `x ∈ Ω`
(the analogue of Proposition 3.4). -/
theorem tendsto_MzeroQ [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) :
    Tendsto (fun r => (monotonicityMq (Q x) u χ x r : EReal)) (𝓝[>] 0)
      (𝓝 (MzeroQ (Q x) u χ x)) := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  obtain ⟨ℓ, hℓ⟩ := h.exists_tendsto_weightedMonotonicityM hQ hx
  set g : ℝ → ℝ := fun r => monotonicityMq (Q x) u χ x r - weightedMonotonicityM Q u χ x r
  have hg : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have hB := tendsto_const_mul_nhdsGT_zero (weissCompConst n L C')
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [Ioo_mem_nhdsGT hR0] with r hr
    rw [Real.norm_eq_abs]
    exact h.abs_monotonicityMq_sub_le hQ hr.1 ((ball_subset_ball hr.2.le).trans hR)
  have hlim : Tendsto (fun r => (monotonicityMq (Q x) u χ x r : EReal)) (𝓝[>] 0) (𝓝 ℓ) :=
    (tendsto_ereal_add_of_tendsto_zero hℓ hg).congr fun r => by simp [g]
  rw [MzeroQ, hlim.limUnder_eq]
  exact hlim

/-- `M^{Q(x)}_x(0+) ≤ M^{Q(x)}_x(r) + (A + B) r` for `0 < r < R`, `B_R(x) ⊆ Ω`. -/
theorem MzeroQ_le [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR : ball x R ⊆ Ω) {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    MzeroQ (Q x) u χ x ≤
      ((monotonicityMq (Q x) u χ x r + (weissConst n L c C' + weissCompConst n L C') * r : ℝ) :
        EReal) := by
  have hx : x ∈ Ω := hR (mem_ball_self (hr.trans hrR))
  set K := monotonicityMq (Q x) u χ x r + (weissConst n L c C' + weissCompConst n L C') * r
  have hlim : Tendsto (fun s => ((K + weissCompConst n L C' * s : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (K : EReal)) := by
    have : Tendsto (fun s : ℝ => K + weissCompConst n L C' * s) (𝓝[>] 0) (𝓝 K) := by
      simpa using tendsto_const_nhds.add (tendsto_const_mul_nhdsGT_zero (weissCompConst n L C'))
    exact (continuous_coe_real_ereal.tendsto K).comp this
  refine le_of_tendsto_of_tendsto (h.tendsto_MzeroQ hQ hx) hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with s hs
  exact EReal.coe_le_coe_iff.2 (h.monotonicityMq_le hQ hR hs.1 hs.2.le hrR)

/-- `c ≤ M^{Q(x)}_x(0+)` as soon as `c ≤ M^{Q(x)}_x(r)` for all small `r > 0`. -/
theorem le_MzeroQ_of_eventually_le [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) {m : EReal}
    (hm : ∀ᶠ r in 𝓝[>] 0, m ≤ monotonicityMq (Q x) u χ x r) : m ≤ MzeroQ (Q x) u χ x :=
  ge_of_tendsto (h.tendsto_MzeroQ hQ hx) hm

/-! ### Bounds on `D` and `H` -/

/-- `0 ≤ D^q_x(r)` when `B_r(x) ⊆ Ω`. -/
theorem energyDq_nonneg (h : IsVariationalSolutionQ Ω C Q u χ) (q : ℝ) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ Ω) : 0 ≤ energyDq q u χ x r :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) (setIntegral_nonneg_of_ae_restrict
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun _ hy =>
      add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (h.chi_nonneg (hball hy))))))

/-- `D^q_x(r) ≤ (C_V² + q²) |B_1|` when `B_r(x) ⊆ Ω`. -/
theorem energyDq_le (h : IsVariationalSolutionQ Ω C Q u χ) (q : ℝ) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ Ω) : energyDq q u χ x r ≤ ((C : ℝ) ^ 2 + q ^ 2) * unitBallVolume n := by
  have h1 : IntegrableOn (fun _ : Rn n => (C : ℝ) ^ 2 + q ^ 2) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have hχ : IntegrableOn χ (ball x r) :=
    IntegrableOn.of_bound measure_ball_lt_top
      (h.aestronglyMeasurable_chi measurableSet_ball hball) 1
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hball hy)))
  have hint : IntegrableOn (fun y => ‖gradient u y‖ ^ 2 + q ^ 2 * χ y) (ball x r) :=
    (IntegrableOn.of_bound measure_ball_lt_top
      ((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable ((C : ℝ) ^ 2)
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h.sq_norm_gradient_le (hball hy)))).add (hχ.const_mul _)
  have hle : ∫ y in ball x r, (‖gradient u y‖ ^ 2 + q ^ 2 * χ y) ≤
      ∫ y in ball x r, ((C : ℝ) ^ 2 + q ^ 2) :=
    setIntegral_mono_on hint h1 measurableSet_ball fun y hy =>
      add_le_add (h.sq_norm_gradient_le (hball hy))
        (by nlinarith [h.chi_le_one (hball hy), sq_nonneg q])
  rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hr] at hle
  rw [energyDq]
  calc (r ^ n)⁻¹ * ∫ y in ball x r, (‖gradient u y‖ ^ 2 + q ^ 2 * χ y)
      ≤ (r ^ n)⁻¹ * (r ^ n * unitBallVolume n * ((C : ℝ) ^ 2 + q ^ 2)) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (pow_nonneg hr.le n))
    _ = _ := by field_simp

/-- If `u(x) = 0`, then `H_x(r) ≤ C_V² n |B_1|` for `0 < r < R`, `B_R(x) ⊆ Ω`. -/
theorem heightH_le_of_eq_zero [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ) {r : ℝ}
    (hR : ball x R ⊆ Ω) (hr : 0 < r) (hrR : r < R) (hux : u x = 0) :
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

/-! ### `M(0+) = −∞` if and only if `u(x) > 0` -/

/-- If `u(x) > 0`, then `M^q_x(r) → −∞` as `r → 0+`. -/
theorem tendsto_monotonicityMq_atBot_of_pos [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (q : ℝ) (hx : x ∈ Ω) (hpos : 0 < u x) :
    Tendsto (monotonicityMq q u χ x) (𝓝[>] 0) atBot := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  have hc : {y | u x / 2 < u y} ∈ 𝓝 x :=
    (h.continuousOn.continuousAt (h.isOpen.mem_nhds hx)).preimage_mem_nhds
      (Ioi_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hc
  set A := ((C : ℝ) ^ 2 + q ^ 2) * unitBallVolume n
  set c := (n : ℝ) * unitBallVolume n * (u x / 2) ^ 2
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hcpos : 0 < c := by have := unitBallVolume_pos n; positivity
  have hbound : ∀ r ∈ Ioo 0 (min (min δ R) 1), monotonicityMq q u χ x r ≤ A - c * r⁻¹ := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hrδ : r < δ := hr.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hrR : r < R := hr.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hr1 : r < 1 := hr.2.trans_le (min_le_right _ _)
    have hD := h.energyDq_le q hr0 ((ball_subset_ball hrR.le).trans hR)
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
    rw [monotonicityMq]
    linarith
  have hlim : Tendsto (fun r => A - c * r⁻¹) (𝓝[>] 0) atBot := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hcpos
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_left _ A (tendsto_neg_atTop_atBot.comp this)
  refine tendsto_atBot_mono' _ ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (lt_min (lt_min hδ hR0) one_pos)] with r hr using hbound r hr

/-- `M^{Q(x)}_x(0+) = −∞` when `u(x) > 0`. -/
theorem MzeroQ_eq_bot_of_pos [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hpos : 0 < u x) :
    MzeroQ (Q x) u χ x = ⊥ :=
  tendsto_nhds_unique (h.tendsto_MzeroQ hQ hx)
    (EReal.tendsto_coe_atBot.comp (h.tendsto_monotonicityMq_atBot_of_pos (Q x) hx hpos))

/-- If `u(x) = 0`, `M^{Q(x)}_x(0+)` is a real number `m` and `M^{Q(x)}_x(r) → m` in `ℝ`. -/
theorem exists_tendsto_monotonicityMq_of_eq_zero [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hux : u x = 0) :
    ∃ m : ℝ, MzeroQ (Q x) u χ x = m ∧
      Tendsto (monotonicityMq (Q x) u χ x) (𝓝[>] 0) (𝓝 m) := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  have hlow : ((-((C : ℝ) ^ 2 * (n * unitBallVolume n)) : ℝ) : EReal) ≤ MzeroQ (Q x) u χ x := by
    refine h.le_MzeroQ_of_eventually_le hQ hx ?_
    filter_upwards [Ioo_mem_nhdsGT hR0] with r hr
    have h1 := h.energyDq_nonneg (Q x) hr.1 ((ball_subset_ball hr.2.le).trans hR)
    have h2 := h.heightH_le_of_eq_zero hR hr.1 hr.2 hux
    exact EReal.coe_le_coe_iff.2 (by rw [monotonicityMq]; linarith)
  have hup := h.MzeroQ_le hQ hR (half_pos hR0) (half_lt_self hR0)
  have hne_bot : MzeroQ (Q x) u χ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  have hne_top : MzeroQ (Q x) u χ x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  refine ⟨(MzeroQ (Q x) u χ x).toReal, (EReal.coe_toReal hne_top hne_bot).symm, ?_⟩
  have := h.tendsto_MzeroQ hQ hx
  rw [← EReal.coe_toReal hne_top hne_bot] at this
  exact EReal.tendsto_coe.1 this

/-- **`M^{Q(x)}_x(0+) = −∞` if and only if `u(x) > 0`** (the analogue of Proposition 3.5). -/
theorem MzeroQ_eq_bot_iff [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) :
    MzeroQ (Q x) u χ x = ⊥ ↔ 0 < u x := by
  refine ⟨fun hbot => ?_, h.MzeroQ_eq_bot_of_pos hQ hx⟩
  by_contra hpos
  have hux : u x = 0 := le_antisymm (not_lt.1 hpos) (h.nonneg x hx)
  obtain ⟨m, hm, -⟩ := h.exists_tendsto_monotonicityMq_of_eq_zero hQ hx hux
  rw [hm] at hbot
  exact EReal.coe_ne_bot m hbot

/-! ### Upper semicontinuity -/

/-- For fixed `r > 0`, `y ↦ M^{Q(y)}_y(u; r)` is continuous at `x₀` when `B̄_r(x₀) ⊆ Ω`. -/
theorem continuousAt_monotonicityMq_center [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) {x₀ : Rn n} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x₀ r ⊆ Ω) :
    ContinuousAt (fun y => monotonicityMq (Q y) u χ y r) x₀ := by
  obtain ⟨R', hR', hR'Ω⟩ := exists_gt_ball_subset h.isOpen hr.le hball
  have hx₀ : x₀ ∈ Ω := hball (mem_closedBall_self hr.le)
  set g₁ : Rn n → ℝ := Ω.indicator fun y => ‖gradient u y‖ ^ 2 with hg₁def
  set g₂ : Rn n → ℝ := Ω.indicator χ with hg₂def
  have hloc : ∀ g : Rn n → ℝ, Measurable g → ∀ M, (∀ y, |g y| ≤ M) → LocallyIntegrable g := by
    intro g hg M hM
    rw [locallyIntegrable_iff]
    intro K hK
    exact IntegrableOn.of_bound hK.measure_lt_top hg.aestronglyMeasurable M
      (.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  have hg₁ : LocallyIntegrable g₁ := by
    refine hloc _ (((measurable_gradient u).norm.pow_const 2).indicator
      h.isOpen.measurableSet) ((C : ℝ) ^ 2) fun y => ?_
    by_cases hy : y ∈ Ω
    · rw [hg₁def, indicator_of_mem hy, abs_of_nonneg (sq_nonneg _)]
      exact h.sq_norm_gradient_le hy
    · rw [hg₁def, indicator_of_notMem hy, abs_zero]; positivity
  have hg₂ : LocallyIntegrable g₂ := by
    refine hloc _ h.measurable_chi 1 fun y => ?_
    by_cases hy : y ∈ Ω
    · rw [hg₂def, indicator_of_mem hy]; exact h.abs_chi_le_one hy
    · rw [hg₂def, indicator_of_notMem hy, abs_zero]; positivity
  have hQc : ContinuousAt Q x₀ := hQ.continuousOn.continuousAt (h.isOpen.mem_nhds hx₀)
  have hD : ContinuousAt (fun y => (r ^ n)⁻¹ *
      ((∫ z in ball y r, g₁ z) + Q y ^ 2 * ∫ z in ball y r, g₂ z)) x₀ :=
    continuousAt_const.mul ((continuous_integral_ball hg₁ r).continuousAt.add
      ((hQc.pow 2).mul (continuous_integral_ball hg₂ r).continuousAt))
  have hD' : (fun y => energyDq (Q y) u χ y r) =ᶠ[𝓝 x₀] fun y => (r ^ n)⁻¹ *
      ((∫ z in ball y r, g₁ z) + Q y ^ 2 * ∫ z in ball y r, g₂ z) := by
    filter_upwards [ball_mem_nhds x₀ (sub_pos.2 hR')] with y hy
    have hsub : ball y r ⊆ Ω := by
      intro z hz
      apply hR'Ω
      rw [mem_ball] at hy hz ⊢
      linarith [dist_triangle z y x₀]
    have e₁ : ∫ z in ball y r, g₁ z = ∫ z in ball y r, ‖gradient u z‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_ball fun z hz => by
        rw [hg₁def, indicator_of_mem (hsub hz)]
    have e₂ : ∫ z in ball y r, g₂ z = ∫ z in ball y r, χ z :=
      setIntegral_congr_fun measurableSet_ball fun z hz => by
        rw [hg₂def, indicator_of_mem (hsub hz)]
    have hI₁ : IntegrableOn (fun z => ‖gradient u z‖ ^ 2) (ball y r) :=
      (hg₁.integrableOn_isCompact (isCompact_closedBall y r)).mono_set ball_subset_closedBall
        |>.congr_fun (fun z hz => by rw [hg₁def, indicator_of_mem (hsub hz)]) measurableSet_ball
    have hI₂ : IntegrableOn χ (ball y r) :=
      (hg₂.integrableOn_isCompact (isCompact_closedBall y r)).mono_set ball_subset_closedBall
        |>.congr_fun (fun z hz => by rw [hg₂def, indicator_of_mem (hsub hz)]) measurableSet_ball
    rw [energyDq, e₁, e₂, integral_add hI₁ (hI₂.const_mul _), integral_const_mul]
  have hSI := continuousAt_sphereIntegral h.isOpen (h.continuousOn.pow 2)
    (x := x₀) (s := r) (by rwa [abs_of_pos hr])
  have hc : ContinuousAt (fun y : Rn n => (y, r)) x₀ :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hH : ContinuousAt (fun y => heightH u y r) x₀ :=
    (ContinuousAt.comp (f := fun y : Rn n => (y, r)) hSI hc).const_mul _
  exact (hD.congr hD'.symm).sub hH

/-- **Upper semicontinuity** (the analogue of Proposition 3.5): `x ↦ M^{Q(x)}_x(u; 0+)` is upper
semicontinuous on `Ω`. -/
theorem upperSemicontinuousOn_MzeroQ [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    UpperSemicontinuousOn (fun x => MzeroQ (Q x) u χ x) Ω := by
  intro x₀ hx₀ y hy
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x₀ hx₀
  set A := weissConst n L c C' + weissCompConst n L C'
  -- Choose `r` with `M(x₀, r) + A r < y`.
  have hev : ∀ᶠ r in 𝓝[>] 0,
      (((monotonicityMq (Q x₀) u χ x₀ r + A * r : ℝ)) : EReal) < y := by
    have hA := tendsto_const_mul_nhdsGT_zero A
    exact (tendsto_ereal_add_of_tendsto_zero (h.tendsto_MzeroQ hQ hx₀) hA).eventually
      (gt_mem_nhds hy)
  obtain ⟨r, hr, hr0, hrR⟩ : ∃ r, (((monotonicityMq (Q x₀) u χ x₀ r + A * r : ℝ)) : EReal) < y ∧
      0 < r ∧ r < R / 2 :=
    (hev.and (Ioo_mem_nhdsGT (half_pos hR0))).exists.imp fun r h => ⟨h.1, h.2.1, h.2.2⟩
  have hcb : closedBall x₀ r ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hR
  have hcont := (h.continuousAt_monotonicityMq_center hQ hr0 hcb).add
    (continuousAt_const (y := A * r))
  have h1 : ∀ᶠ x in 𝓝 x₀, ((monotonicityMq (Q x) u χ x r + A * r : ℝ) : EReal) < y :=
    (continuous_coe_real_ereal.continuousAt.comp hcont).eventually (gt_mem_nhds hr)
  have h2 : ∀ᶠ x in 𝓝 x₀, ball x (R / 2) ⊆ Ω := by
    filter_upwards [ball_mem_nhds x₀ (half_pos hR0)] with x hx
    intro z hz
    apply hR
    rw [mem_ball] at hx hz ⊢
    linarith [dist_triangle z x x₀]
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with x hx1 hx2
  exact (h.MzeroQ_le hQ hx2 hr0 hrR).trans_lt hx1

end IsVariationalSolutionQ

end InnerVariational
